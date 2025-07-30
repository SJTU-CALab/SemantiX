
import json
import os
from utils import params
import logging

logger = logging.getLogger(__name__)

class SymbolicTracePrinter:
    def __init__(self, trace_path, cfg):
        self.trace_path = trace_path
        # 指令列表, 格式为字典类型pc:"opcode operand"若没有operand，则为pc:"opcode",比如 {0: "push1 10}, {2: "RETURN}
        self.instructions = cfg.instructions 
        self.source_map = cfg.source_map

    def print_trace_html_with_source_map(self, filename="symbolic_trace.html"):
        """
        生成符号执行可视化HTML，支持路径选择、逐步执行、回退、结束等交互。
        """
        if self.source_map is None:
            self.print_trace_html()
            return
        # 读取trace.jsonl   
        with open(self.trace_path, 'r') as f:
            lines = f.readlines()
        # 解析所有状态和最后的路径信息
        states = []
        for line in lines:
            line = line.strip()
            if not line:
                continue
            try:
                obj = json.loads(line.replace("\\n", "").replace(" ", ""))
                states.append(obj)
            except Exception:
                continue
        # 最后一个json为路径信息
        path_info = states[-1]
        all_paths = path_info.get('all_paths', [])
        exception_paths = path_info.get('exception_paths', [])
        dynamic_paths = path_info.get('dynamic_paths', [])
        states = states[:-1]

        # 构建HTML
        html = '''
<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <title>符号执行可视化</title>
    <style>
        body { font-family: 'Segoe UI', 'PingFang SC', 'Microsoft YaHei', Arial, sans-serif; margin: 0; padding: 0; background: #f4f6fa; }
        .container { max-width: 1280px; margin: 0 auto; padding: 32px 24px; overflow-y: auto; max-height: 100vh; }
        .section { background: #fff; border-radius: 14px; box-shadow: 0 4px 24px #e3e8f0; margin-bottom: 32px; padding: 32px 28px; }
        .section-title { font-size: 1.25em; font-weight: 600; margin-bottom: 18px; color: #1a237e; letter-spacing: 1px; }
        #graph {
            height: 420px;
            min-height: 420px;
            width: 100%;
            border: 1.5px solid #e3e8f0;
            border-radius: 10px;
            background: #fafdff;
            margin-bottom: 18px;
            box-shadow: 0 2px 8px #f0f4fa;
            position: relative;
        }
        #runtime { font-size: 1em; color: #263238; background: #f7f9fb; border-radius: 8px; padding: 18px; box-shadow: 0 1px 4px #e3e8f0; }
        #controls { display: flex; gap: 16px; margin-top: 16px; }
        #controls button { padding: 10px 24px; border: none; border-radius: 6px; background: linear-gradient(90deg, #1976d2 60%, #42a5f5 100%); color: #fff; cursor: pointer; font-size: 1.05em; font-weight: 500; box-shadow: 0 2px 8px #e3e8f0; transition: background 0.2s, box-shadow 0.2s; }
        #controls button:disabled { background: #b0b0b0; cursor: not-allowed; box-shadow: none; }
        #controls button:not(:disabled):hover { background: linear-gradient(90deg, #1565c0 60%, #1976d2 100%); }
        #path-select { margin-bottom: 0; padding: 8px 16px; border-radius: 6px; border: 1.5px solid #e3e8f0; font-size: 1em; background: #fafdff; color: #263238; }
        .instruction-highlight {
            background: #ffe082 !important;
            color: #d84315 !important;
            font-weight: bold;
        }
        /* 侧边栏美化 */
        #instruction-bar { width: 300px; height: 100vh; background: linear-gradient(180deg, #23272e 80%, #2c3140 100%); color: #fff; padding: 28px 10px 28px 28px; overflow-y: auto; font-size: 15px; border-right: 2px solid #e3e8f0; box-shadow: 2px 0 12px #e3e8f0; }
        #instruction-bar::-webkit-scrollbar { width: 8px; background: #23272e; }
        #instruction-bar::-webkit-scrollbar-thumb { background: #3a3f4b; border-radius: 4px; }
        #instruction-bar .instruction-highlight { background: #ffd54f !important; color: #c62828 !important; border-radius: 4px; }
        #instruction-list { margin-top: 8px; }
        #dragbar { width: 8px; cursor: ew-resize; background: #e3e8f0; height: 100vh; transition: background 0.2s; }
        #dragbar:hover { background: #b0bec5; }
        /* 交互细节 */
        details[open] > summary { color: #1976d2; font-weight: 500; }
        details > summary { cursor: pointer; outline: none; }
        details { margin-bottom: 6px; }
        /* 响应式 */
        @media (max-width: 900px) {
            .container { padding: 12px 2vw; }
            #instruction-bar { width: 180px; padding: 16px 4px 16px 12px; font-size: 13px; }
        }
        @media (max-width: 600px) {
            .container { padding: 2px 0; }
            #instruction-bar { display: none; }
            #dragbar { display: none; }
        }
        .source-sidebar {
            width: 420px;
            background: #f8f9fa;
            border-left: 2px solid #e3e8f0;
            height: 100vh;
            overflow-y: auto;
            font-size: 15px;
            font-family: 'Fira Mono', 'Consolas', 'Menlo', monospace;
            padding: 24px 12px 24px 24px;
            box-sizing: border-box;
            transition: width 0.2s;
        }
        .source-dragbar {
            width: 8px;
            cursor: ew-resize;
            background: #e3e8f0;
            height: 100vh;
            transition: background 0.2s;
            z-index: 10;
        }
        .source-dragbar:hover { background: #b0bec5; }
        .source-title {
            font-weight: bold;
            font-size: 17px;
            margin-bottom: 16px;
            color: #1a237e;
        }
        .source-line {
            white-space: pre;
            line-height: 1.6;
            padding: 0 0 0 8px;
        }
        .src-char {
            transition: background 0.2s;
        }
        .src-char-highlight {
            background: #ffe082;
            color: #d84315;
            border-radius: 2px;
        }
        .src-char-focus {
            background: #ffd54f;
            color: #c62828;
            border-radius: 2px;
        }
        @media (max-width: 1200px) {
            .source-sidebar { width: 220px; font-size: 12px; padding: 12px 2px 12px 8px; }
        }
        /* 路径下拉框高亮样式 */
        #path-select option.exception-path {
            background: #ffebee !important;
            color: #c62828 !important;
            font-weight: bold;
        }
        #path-select option.dynamic-path {
            background: #e8f5e9 !important;
            color: #2e7d32 !important;
            font-weight: bold;
        }
        /* 浮动操作栏样式 */
        #floating-controls {
            position: fixed;
            top: 0;
            left: 0;
            width: 100vw;
            z-index: 9999;
            background: rgba(255,255,255,0.98);
            box-shadow: 0 2px 12px #e3e8f0;
            display: flex;
            justify-content: center;
            align-items: center;
            gap: 18px;
            padding: 12px 0 8px 0;
            border-bottom: 1.5px solid #e3e8f0;
        }
        #floating-controls button {
            padding: 10px 24px;
            border: none;
            border-radius: 6px;
            background: linear-gradient(90deg, #1976d2 60%, #42a5f5 100%);
            color: #fff;
            cursor: pointer;
            font-size: 1.05em;
            font-weight: 500;
            box-shadow: 0 2px 8px #e3e8f0;
            transition: background 0.2s, box-shadow 0.2s;
        }
        #floating-controls button:disabled {
            background: #b0b0b0;
            cursor: not-allowed;
            box-shadow: none;
        }
        #floating-controls button:not(:disabled):hover {
            background: linear-gradient(90deg, #1565c0 60%, #1976d2 100%);
        }
        .main-content-with-padding {
            padding-top: 60px;
        }
    </style>
    <script src="https://unpkg.com/vis-network/standalone/umd/vis-network.min.js"></script>
</head>
<body>
<div id="floating-controls">
    <button id="prev-btn" disabled>上一步</button>
    <button id="next-btn" disabled>下一步</button>
    <button id="end-btn" disabled>结束</button>
    <button id="last-btn" disabled>最后一步</button>
</div>
<div style="display: flex; min-height: 100vh; background: #f4f6fa;">
    <div id="instruction-bar">
        <div style="font-weight:bold; font-size:18px; margin-bottom:18px; letter-spacing:1px;">指令信息</div>
        <div id="instruction-list"></div>
    </div>
    <div id="dragbar"></div>
    <div id="main-content" class="main-content-with-padding" style="flex: 1; min-width:0; display:flex;">
        <div class="container" style="flex:1; min-width:0;">
            <div class="section" style="display:flex; align-items:center; gap:32px; flex-wrap:wrap;">
                <div style="flex:1; min-width:220px;">
                    <div class="section-title">路径选择</div>
                    <select id="path-select">
                        <option value="">请选择路径</option>
'''
        for path in all_paths:
            option_class = ""
            # 文本标注
            display_path = path
            if path in exception_paths:
                display_path = f'**{path}**'
            elif path in dynamic_paths:
                display_path = f'++{path}++'
            html += f'            <option value="{path}" class="{option_class}">{display_path}</option>\\n'
        html += '''
                    </select>
                </div>
                <div id="controls" style="flex:2; display: flex; gap: 16px; align-items:center;">
                    <button id="start-btn">开始符号执行</button>
                </div>
            </div>
            <div class="section">
                <div class="section-title" style="display:flex;align-items:center;gap:16px;">
                    符号执行图（Graph）
                    <button id="graph-reset-btn" style="margin-left:12px;padding:4px 16px;border-radius:5px;border:none;background:#1976d2;color:#fff;cursor:pointer;font-size:0.95em;">还原</button>
                    <button id="graph-fullscreen-btn" style="margin-left:8px;padding:4px 16px;border-radius:5px;border:none;background:#ffb300;color:#fff;cursor:pointer;font-size:0.95em;">全图查看</button>
                </div>
                <div id="graph"></div>
            </div>
            <div class="section">
                <div class="section-title">Runtime 信息</div>
                <div id="runtime"></div>
            </div>
        </div>
        <div id="source-dragbar" class="source-dragbar"></div>
        <div class="source-sidebar" id="source-sidebar">
            <div class="source-title">合约源代码</div>
            <div id="source-code-block">
'''
        # 获取源代码内容
        source_content = self.source_map.source.content if hasattr(self, 'source_map') and self.source_map else ''
        source_lines = source_content.split('\n')
        # 为每行源代码添加id和data属性，支持字符级高亮
        source_lines_html = []
        for i, line in enumerate(source_lines):
            line_with_spans = ''.join([f'<span class="src-char" id="src-char-{i}-{j}" data-line="{i}" data-char="{j}">{char}</span>' for j, char in enumerate(line)])
            source_lines_html.append(f'<div class="source-line" id="source-line-{i}" data-line="{i}">{i+1}: {line_with_spans}</div>')
        source_html = "\n".join(source_lines_html)
        html += source_html
        html += '''
            </div>
        </div>
    </div>
</div>
<div id="graph-fullscreen-modal" style="display:none;position:fixed;z-index:9999;top:0;left:0;width:100vw;height:100vh;background:rgba(30,32,40,0.92);align-items:center;justify-content:center;">
    <div style="position:absolute;top:24px;right:36px;z-index:10001;">
        <button id="graph-fullscreen-close" style="padding:8px 22px;border-radius:6px;border:none;background:#1976d2;color:#fff;font-size:1.1em;cursor:pointer;box-shadow:0 2px 8px #222;">关闭</button>
        <button id="graph-fullscreen-reset" style="margin-left:12px;padding:8px 22px;border-radius:6px;border:none;background:#ffb300;color:#fff;font-size:1.1em;cursor:pointer;box-shadow:0 2px 8px #222;">还原</button>
    </div>
    <div id="graph-fullscreen-canvas" style="width:90vw;height:88vh;background:#fafdff;border-radius:12px;box-shadow:0 4px 32px #111;"></div>
</div>
<script>
// Mermaid初始化
// mermaid.initialize({ startOnLoad: false });

// vis-network渲染函数
function renderGraphWithVis(graph, containerId) {
    var container = document.getElementById(containerId);
    if (!graph || !graph.nodes || graph.nodes.length === 0) {
        container.innerHTML = '<div style="color:#bbb; text-align:center; padding:60px 0; font-size:1.2em;">暂无图数据</div>';
        if(containerId === 'graph') window._symbolicTraceNetwork = null;
        if(containerId === 'graph-fullscreen-canvas') window._symbolicTraceNetworkFullscreen = null;
        return;
    }
    // 1. 只保留有边连接的节点
    var edgeNodeSet = new Set();
    (graph.edges || []).forEach(e => {
        edgeNodeSet.add(e.source);
        edgeNodeSet.add(e.target);
    });
    var filteredNodes = graph.nodes.filter(n => edgeNodeSet.has(n.id));
    var filteredNodeIds = new Set(filteredNodes.map(n => n.id));
    var filteredEdges = (graph.edges || []).filter(e => filteredNodeIds.has(e.source) && filteredNodeIds.has(e.target));

    // 2. 连通分量分组（每个子图树状排布）
    var adj = {};
    filteredNodes.forEach(n => { adj[n.id] = []; });
    filteredEdges.forEach(e => { adj[e.source].push(e.target); adj[e.target].push(e.source); });
    var visited = new Set();
    var components = [];
    filteredNodes.forEach(n => {
        if (!visited.has(n.id)) {
            var queue = [n.id], comp = [];
            visited.add(n.id);
            while (queue.length) {
                var cur = queue.shift();
                comp.push(cur);
                adj[cur].forEach(nb => {
                    if (!visited.has(nb)) { visited.add(nb); queue.push(nb); }
                });
            }
            components.push(comp);
        }
    });
    // 3. 生成vis-network数据，分组树状排布，节点内容超长省略，悬浮显示完整内容
    function ellipsis(str, maxLen) {
        if (typeof str !== 'string') str = String(str);
        return str.length > maxLen ? str.slice(0, maxLen - 1) + '…' : str;
    }
    function getNodeColor(kind) {
        if (kind === 'constraint') {
            return { background: '#ede7f6', border: '#7e57c2', highlight: { background: '#ede7f6', border: '#7e57c2' } };
        } else if (kind === 'return') {
            return { background: '#e8f5e9', border: '#43a047', highlight: { background: '#e8f5e9', border: '#43a047' } };
        } else if (kind === 'revert') {
            return { background: '#ffebee', border: '#e53935', highlight: { background: '#ffebee', border: '#e53935' } };
        } else if (kind === 'inputdata') {
            return { background: '#fffde7', border: '#ffd600', highlight: { background: '#fffde7', border: '#ffd600' } };
        } else {
            return { background: '#e3f2fd', border: '#1976d2', highlight: { background: '#fffde7', border: '#fbc02d' } };
        }
    }
    var nodes = [], edges = [];
    var nodeIdSet = new Set();
    var edgeKeySet = new Set();
    components.forEach((comp, idx) => {
        if (comp.length < 2) return;
        var subNodes = filteredNodes.filter(n => comp.includes(n.id));
        var subEdges = filteredEdges.filter(e => comp.includes(e.source) && comp.includes(e.target));
        subNodes.forEach(n => {
            if (!nodeIdSet.has(n.id)) {
                var fullLabel = n.kind + ':' + n.id;
                nodes.push({
                    id: n.id,
                    label: ellipsis(fullLabel, 14),
                    title: fullLabel,
                    shape: 'box',
                    widthConstraint: { minimum: 120, maximum: 120 },
                    heightConstraint: { minimum: 36 }, // 只保留minimum，去掉maximum
                    font: { size: 16, multi: false, align: 'center' },
                    color: getNodeColor(n.kind),
                    group: idx
                });
                nodeIdSet.add(n.id);
            }
        });
        subEdges.forEach(e => {
            let edgeKey = e.source + '->' + e.target + ':' + e.label;
            if (!edgeKeySet.has(edgeKey)) {
                let edgeColor = (String(e.label) === 'contr')
                    ? { color: '#ab47bc', highlight: '#8e24aa' } // 紫色
                    : { color: '#90caf9', highlight: '#fbc02d' };
                edges.push({
                    from: e.source,
                    to: e.target,
                    label: String(e.label),
                    arrows: 'to',
                    font: { align: 'middle', size: 13 },
                    color: edgeColor,
                    group: idx
                });
                edgeKeySet.add(edgeKey);
            }
        });
    });
    var data = { nodes: new vis.DataSet(nodes), edges: new vis.DataSet(edges) };
    var options = {
        layout: {
            hierarchical: {
                enabled: true,
                direction: 'UD',
                sortMethod: 'directed',
                nodeSpacing: 180,
                levelSeparation: 180,
                treeSpacing: 300
            }
        },
        nodes: {
            borderWidth: 2,
            size: 24,
            widthConstraint: { minimum: 120, maximum: 120 },
            heightConstraint: { minimum: 36 }, // 只保留minimum，去掉maximum
            font: { size: 16, multi: false, align: 'center' },
            shape: 'box',
            margin: 6
        },
        edges: { smooth: true },
        physics: false,
        interaction: { hover: true, tooltipDelay: 100, zoomView: false } // 初始禁用缩放
    };
    container.innerHTML = '';
    var network = new vis.Network(container, data, options);
    if(containerId === 'graph') window._symbolicTraceNetwork = network;
    if(containerId === 'graph-fullscreen-canvas') window._symbolicTraceNetworkFullscreen = network;
    setTimeout(() => {
        network.fit({ animation: { duration: 500, easingFunction: 'easeInOutQuad' } });
        setTimeout(() => { network.redraw(); }, 200);
    }, 200);
    // 只在悬停且点击激活后允许缩放
    let zoomActive = false;
    container.addEventListener('mouseenter', function() {
        if (zoomActive) network.setOptions({ interaction: { zoomView: true } });
    });
    container.addEventListener('mouseleave', function() {
        zoomActive = false;
        network.setOptions({ interaction: { zoomView: false } });
    });
    container.addEventListener('mousedown', function(e) {
        if (e.button === 0) { // 左键点击激活
            zoomActive = true;
            network.setOptions({ interaction: { zoomView: true } });
        }
    });
    document.addEventListener('mousedown', function(e) {
        if (!container.contains(e.target)) {
            zoomActive = false;
            network.setOptions({ interaction: { zoomView: false } });
        }
    });
}

// 还原按钮事件
setTimeout(function() {
    var btn = document.getElementById('graph-reset-btn');
    if (btn) {
        btn.onclick = function() {
            if (window._symbolicTraceNetwork) {
                window._symbolicTraceNetwork.fit({ animation: { duration: 400, easingFunction: 'easeInOutQuad' } });
            }
        };
    }
}, 500);

// 全图查看按钮事件
setTimeout(function() {
    var btn = document.getElementById('graph-fullscreen-btn');
    if (btn) {
        btn.onclick = function() {
            var modal = document.getElementById('graph-fullscreen-modal');
            modal.style.display = 'flex';
            // 渲染全屏graph，使用当前filteredStates[currentStep]的graph
            if(typeof filteredStates !== 'undefined' && filteredStates.length > 0 && typeof currentStep !== 'undefined') {
                var state = filteredStates[currentStep];
                renderGraphWithVis(state.graph, 'graph-fullscreen-canvas');
            }
        };
    }
    // 关闭按钮
    var closeBtn = document.getElementById('graph-fullscreen-close');
    if (closeBtn) {
        closeBtn.onclick = function() {
            var modal = document.getElementById('graph-fullscreen-modal');
            modal.style.display = 'none';
            // 清空全屏graph内容
            document.getElementById('graph-fullscreen-canvas').innerHTML = '';
            window._symbolicTraceNetworkFullscreen = null;
        };
    }
    // 全屏还原按钮
    var resetBtn = document.getElementById('graph-fullscreen-reset');
    if (resetBtn) {
        resetBtn.onclick = function() {
            if(window._symbolicTraceNetworkFullscreen) {
                window._symbolicTraceNetworkFullscreen.fit({ animation: { duration: 400, easingFunction: 'easeInOutQuad' } });
            }
        };
    }
}, 500);

// 解析trace数据
const allStates = JSON.parse(`''' + json.dumps(states, ensure_ascii=False) + '''`);
const allPaths = JSON.parse(`''' + json.dumps(all_paths, ensure_ascii=False) + '''`);
const instructions = JSON.parse(`''' + json.dumps(self.instructions, ensure_ascii=False) + '''`);

let currentPath = null;
let filteredStates = [];
let currentStep = 0;

function isSubPath(label, path) {
    return path.startsWith(label);
}
function filterStatesByPath(path) {
    return allStates.filter(s => {
        if (!s.runtime || !s.runtime.path_label) return false;
        return path.startsWith(s.runtime.path_label);
    });
}
function renderGraph(graph, prevGraph) {
    let mermaidStr = 'graph TD\\n';
    if (!graph || !graph.nodes) return '';
    let nodeMap = {};
    let prevNodeIds = new Set();
    let prevEdgeKeys = new Set();
    if (prevGraph && prevGraph.nodes) {
        prevGraph.nodes.forEach(n => prevNodeIds.add(n.id));
    }
    if (prevGraph && prevGraph.edges) {
        prevGraph.edges.forEach(e => prevEdgeKeys.add(e.source + '->' + e.target + ':' + e.label));
    }
    let highlightNodes = [];
    let highlightEdges = [];
    graph.nodes.forEach(n => {
        nodeMap[n.id] = n.kind + ':' + n.id;
        mermaidStr += `    ${n.id}[${n.kind}: ${n.id}]\\n`;
        if (!prevNodeIds.has(n.id)) {
            highlightNodes.push(n.id);
        }
    });
    if (graph.edges) {
        graph.edges.forEach(e => {
            mermaidStr += `    ${e.source}-->|${e.label}|${e.target}\\n`;
            let key = e.source + '->' + e.target + ':' + e.label;
            if (!prevEdgeKeys.has(key)) {
                highlightEdges.push([e.source, e.target, e.label]);
            }
        });
    }
    if (highlightNodes.length > 0) {
        mermaidStr += '    classDef highlight fill:#ffeb3b,stroke:#f44336,stroke-width:3px;\\n';
        highlightNodes.forEach(nid => {
            mermaidStr += `    class ${nid} highlight;\\n`;
        });
    }
    return mermaidStr;
}
function renderRuntime(runtime) {
    if (!runtime) return '';
    let html = '<b>PC:</b> <span style="color:#1976d2">' + runtime.pc + '</span><br/>';
    html += '<b>Stack:</b>' + renderExpandableArray(runtime.stack, 'stack') + '<br/>';
    html += '<b>Memory:</b>' + renderExpandableArray(runtime.memory, 'memory') + '<br/>';
    html += '<b>Storage:</b>' + renderExpandableDict(runtime.storage, 'storage') + '<br/>';
    html += '<b>Balance:</b>' + renderExpandableDict(runtime.balance, 'balance') + '<br/>';
    html += '<b>Path:</b>' + renderExpandableArray(runtime.path, 'path') + '<br/>';
    html += '<b>Path Label:</b> <span style="color:#1976d2">' + runtime.path_label + '</span><br/>';
    return html;
}
function renderExpandableArray(arr, id) {
    const minRows = 10;
    let html = `<div style='max-height:240px; min-height:240px; overflow-y:auto; border:1.5px solid #e3e8f0; border-radius:6px; background:#fff; padding:4px 8px; margin:4px 0; display:flex; flex-direction:column; justify-content:flex-start;'>`;
    if (!arr || arr.length === 0) {
        for (let i = 0; i < minRows; i++) {
            html += `<div style='height:20px; color:#bbb; font-style:italic; border-bottom:1px solid #f0f0f0; font-family:monospace;'>[${i}] (空)</div>`;
        }
    } else {
        let count = Math.max(arr.length, minRows);
        for (let i = 0; i < count; i++) {
            if (i < arr.length) {
                html += `<div style='border-bottom:1px solid #f0f0f0; padding:2px 0; font-family:monospace;'>[${i}] ${JSON.stringify(arr[i])}</div>`;
            } else {
                html += `<div style='height:20px; color:#bbb; font-style:italic; border-bottom:1px solid #f0f0f0; font-family:monospace;'>[${i}] (空)</div>`;
            }
        }
    }
    html += '</div>';
    return html;
}
function renderExpandableDict(obj, id) {
    const minRows = 10;
    let keys = obj ? Object.keys(obj) : [];
    let html = `<div style='max-height:240px; min-height:240px; overflow-y:auto; border:1.5px solid #e3e8f0; border-radius:6px; background:#fff; padding:4px 8px; margin:4px 0; display:flex; flex-direction:column; justify-content:flex-start;'>`;
    if (!obj || keys.length === 0) {
        for (let i = 0; i < minRows; i++) {
            html += `<div style='height:20px; color:#bbb; font-style:italic; border-bottom:1px solid #f0f0f0; font-family:monospace;'>{空}</div>`;
        }
    } else {
        let count = Math.max(keys.length, minRows);
        for (let i = 0; i < count; i++) {
            if (i < keys.length) {
                let k = keys[i];
                html += `<div style='border-bottom:1px solid #f0f0f0; padding:2px 0; font-family:monospace;'>${k}: ${JSON.stringify(obj[k])}</div>`;
            } else {
                html += `<div style='height:20px; color:#bbb; font-style:italic; border-bottom:1px solid #f0f0f0; font-family:monospace;'>{空}</div>`;
            }
        }
    }
    html += '</div>';
    return html;
}
function renderInstructionList(highlightPc = null) {
    let html = '';
    const pcs = Object.keys(instructions).map(x => parseInt(x)).sort((a, b) => a - b);
    pcs.forEach(pc => {
        const highlightClass = (highlightPc !== null && pc === highlightPc) ? "instruction-highlight" : "";
        html += `<div class="${highlightClass}" style="padding:3px 0; border-bottom:1px solid #333; font-family:monospace; border-radius:3px; margin-bottom:1px;">
            <span style="color:#ffd600;">[${pc}]</span> <span>${instructions[pc]}</span>
        </div>`;
    });
    document.getElementById('instruction-list').innerHTML = html;
}
renderInstructionList();
// 高亮源代码函数
function highlightSourceForPc(pc) {
    // 依赖 states[currentStep] 的 pc
    if (!window.pcToSourceMap) return;
    var info = window.pcToSourceMap[pc];
    // 先清除所有高亮
    document.querySelectorAll('.src-char-highlight, .src-char-focus').forEach(e => e.classList.remove('src-char-highlight', 'src-char-focus'));
    if (!info) return;
    for (let i = info.begin_line - 1; i <= info.end_line - 1; i++) {
        for (let j = info.begin_char || 0; j < (i === info.end_line - 1 ? (info.end_char || 9999) : 9999); j++) {
            let el = document.getElementById(`src-char-${i}-${j}`);
            if (el) el.classList.add('src-char-highlight');
        }
    }
}
// 构建pc到源代码区间的映射
window.pcToSourceMap = {};
(function() {
    try {
        var pcToSource = {};
        var sourceMap = ''' + ("true" if hasattr(self, 'source_map') and self.source_map else "false") + ''';
        if (sourceMap) {
            var pyPcToSource = {};
            // 由python生成的pc到源代码区间的映射
            pyPcToSource = ''' + json.dumps({pc: (self.source_map.get_position_with_pc(pc) if hasattr(self, 'source_map') and self.source_map and hasattr(self.source_map, 'get_position_with_pc') and pc in self.source_map.pc_to_index else None) for pc in self.instructions.keys()}, ensure_ascii=False) + ''';
            // 转换为js对象
            for (let pc in pyPcToSource) {
                let info = pyPcToSource[pc];
                if (info && info.begin !== undefined && info.end !== undefined) {
                    // 计算begin/end对应的行号和列号
                    let begin = info.begin, end = info.end;
                    let begin_line = 1, end_line = 1, begin_char = 0, end_char = 0;
                    let content = `''' + source_content.replace('`', '\`') + '''`;
                    let lineBreaks = [-1];
                    for (let i = 0; i < content.length; i++) if (content[i] === '\\n') lineBreaks.push(i);
                    for (let i = 1; i < lineBreaks.length; i++) {
                        if (begin > lineBreaks[i-1] && begin <= lineBreaks[i]) {
                            begin_line = i;
                            begin_char = begin - lineBreaks[i-1] - 1;
                        }
                        if (end > lineBreaks[i-1] && end <= lineBreaks[i]) {
                            end_line = i;
                            end_char = end - lineBreaks[i-1] - 1;
                        }
                    }
                    pcToSource[pc] = { begin_line, end_line, begin_char, end_char };
                }
            }
        }
        window.pcToSourceMap = pcToSource;
    } catch(e) { window.pcToSourceMap = {}; }
})();
function updateUI() {
    if (filteredStates.length === 0 || currentStep < 0 || currentStep >= filteredStates.length) {
        document.getElementById('graph').innerHTML = '<div style="color:#bbb; text-align:center; padding:60px 0; font-size:1.2em;">暂无图数据</div>';
        document.getElementById('runtime').innerHTML = '<div style="color:#bbb; text-align:center; padding:40px 0; font-size:1.1em;">暂无Runtime信息</div>';
        document.getElementById('prev-btn').disabled = true;
        document.getElementById('next-btn').disabled = true;
        document.getElementById('end-btn').disabled = true;
        document.getElementById('last-btn').disabled = true;
        renderInstructionList();
        return;
    }
    const state = filteredStates[currentStep];
    const prevState = currentStep > 0 ? filteredStates[currentStep - 1] : null;
    // 用vis-network渲染graph
    renderGraphWithVis(state.graph, 'graph');
    document.getElementById('runtime').innerHTML = renderRuntime(state.runtime);
    document.getElementById('prev-btn').disabled = currentStep === 0;
    document.getElementById('next-btn').disabled = currentStep === filteredStates.length - 1;
    document.getElementById('end-btn').disabled = false;
    document.getElementById('last-btn').disabled = filteredStates.length === 0 || currentStep === filteredStates.length - 1;
    renderInstructionList(state.runtime && typeof state.runtime.pc === 'number' ? state.runtime.pc : null);
    if (state.runtime && typeof state.runtime.pc === 'number') {
        highlightSourceForPc(state.runtime.pc);
    }
}
document.getElementById('start-btn').onclick = function() {
    const path = document.getElementById('path-select').value;
    if (!path) { alert('请选择路径'); return; }
    currentPath = path;
    filteredStates = filterStatesByPath(path);
    currentStep = 0;
    updateUI();
};
document.getElementById('prev-btn').onclick = function() {
    if (currentStep > 0) {
        currentStep--;
        updateUI();
    }
};
document.getElementById('next-btn').onclick = function() {
    if (currentStep < filteredStates.length - 1) {
        currentStep++;
        updateUI();
    }
};
document.getElementById('end-btn').onclick = function() {
    filteredStates = [];
    currentStep = 0;
    updateUI();
};
document.getElementById('last-btn').onclick = function() {
    if (filteredStates.length > 0) {
        currentStep = filteredStates.length - 1;
        updateUI();
    }
};
const dragbar = document.getElementById('dragbar');
const instructionBar = document.getElementById('instruction-bar');
let isDragging = false;
dragbar.addEventListener('mousedown', function(e) {
    isDragging = true;
    document.body.style.cursor = 'ew-resize';
});
document.addEventListener('mousemove', function(e) {
    if (!isDragging) return;
    let minWidth = 120, maxWidth = 600;
    let newWidth = e.clientX;
    if (newWidth < minWidth) newWidth = minWidth;
    if (newWidth > maxWidth) newWidth = maxWidth;
    instructionBar.style.width = newWidth + 'px';
});
document.addEventListener('mouseup', function(e) {
    isDragging = false;
    document.body.style.cursor = '';
});
// 右侧源代码栏拖动分界线
(function() {
    var dragbar = document.getElementById('source-dragbar');
    var sidebar = document.getElementById('source-sidebar');
    var mainContent = document.getElementById('main-content');
    var isDragging = false;
    dragbar.addEventListener('mousedown', function(e) {
        isDragging = true;
        document.body.style.cursor = 'ew-resize';
    });
    document.addEventListener('mousemove', function(e) {
        if (!isDragging) return;
        let minWidth = 180, maxWidth = 800;
        let newWidth = window.innerWidth - e.clientX;
        if (newWidth < minWidth) newWidth = minWidth;
        if (newWidth > maxWidth) newWidth = maxWidth;
        sidebar.style.width = newWidth + 'px';
    });
    document.addEventListener('mouseup', function(e) {
        isDragging = false;
        document.body.style.cursor = '';
    });
})();
</script>
</body>
</html>
'''
        # 输出HTML到文件
        output_path = os.path.join(params.OUTPUT_PATH, filename)
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(html)
        logger.info(f"symbolic trace HTML已生成: {output_path}")
    
    def print_trace_html(self, filename="symbolic_trace.html"):
        """
        生成符号执行可视化HTML，支持路径选择、逐步执行、回退、结束等交互。
        """
        # 读取trace.jsonl   
        with open(self.trace_path, 'r') as f:
            lines = f.readlines()
        # 解析所有状态和最后的路径信息
        states = []
        for line in lines:
            line = line.strip()
            if not line:
                continue
            try:
                obj = json.loads(line.replace("\\n", "").replace(" ", ""))
                states.append(obj)
            except Exception:
                continue
        # 最后一个json为路径信息
        path_info = states[-1]
        all_paths = path_info.get('all_paths', [])
        exception_paths = path_info.get('exception_paths', {})
        dynamic_paths = path_info.get('dynamic_paths', {})
        states = states[:-1]

        # 构建HTML
        html = '''
<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <title>符号执行可视化</title>
    <style>
        body { font-family: 'Segoe UI', 'PingFang SC', 'Microsoft YaHei', Arial, sans-serif; margin: 0; padding: 0; background: #f4f6fa; }
        .container { max-width: 1280px; margin: 0 auto; padding: 32px 24px; overflow-y: auto; max-height: 100vh; }
        .section { background: #fff; border-radius: 14px; box-shadow: 0 4px 24px #e3e8f0; margin-bottom: 32px; padding: 32px 28px; }
        .section-title { font-size: 1.25em; font-weight: 600; margin-bottom: 18px; color: #1a237e; letter-spacing: 1px; }
        #graph {
            height: 420px;
            min-height: 420px;
            width: 100%;
            border: 1.5px solid #e3e8f0;
            border-radius: 10px;
            background: #fafdff;
            margin-bottom: 18px;
            box-shadow: 0 2px 8px #f0f4fa;
            position: relative;
        }
        #runtime { font-size: 1em; color: #263238; background: #f7f9fb; border-radius: 8px; padding: 18px; box-shadow: 0 1px 4px #e3e8f0; }
        #controls { display: flex; gap: 16px; margin-top: 16px; }
        #controls button { padding: 10px 24px; border: none; border-radius: 6px; background: linear-gradient(90deg, #1976d2 60%, #42a5f5 100%); color: #fff; cursor: pointer; font-size: 1.05em; font-weight: 500; box-shadow: 0 2px 8px #e3e8f0; transition: background 0.2s, box-shadow 0.2s; }
        #controls button:disabled { background: #b0b0b0; cursor: not-allowed; box-shadow: none; }
        #controls button:not(:disabled):hover { background: linear-gradient(90deg, #1565c0 60%, #1976d2 100%); }
        #path-select { margin-bottom: 0; padding: 8px 16px; border-radius: 6px; border: 1.5px solid #e3e8f0; font-size: 1em; background: #fafdff; color: #263238; }
        .instruction-highlight {
            background: #ffe082 !important;
            color: #d84315 !important;
            font-weight: bold;
        }
        /* 侧边栏美化 */
        #instruction-bar { width: 300px; height: 100vh; background: linear-gradient(180deg, #23272e 80%, #2c3140 100%); color: #fff; padding: 28px 10px 28px 28px; overflow-y: auto; font-size: 15px; border-right: 2px solid #e3e8f0; box-shadow: 2px 0 12px #e3e8f0; }
        #instruction-bar::-webkit-scrollbar { width: 8px; background: #23272e; }
        #instruction-bar::-webkit-scrollbar-thumb { background: #3a3f4b; border-radius: 4px; }
        #instruction-bar .instruction-highlight { background: #ffd54f !important; color: #c62828 !important; border-radius: 4px; }
        #instruction-list { margin-top: 8px; }
        #dragbar { width: 8px; cursor: ew-resize; background: #e3e8f0; height: 100vh; transition: background 0.2s; }
        #dragbar:hover { background: #b0bec5; }
        /* 交互细节 */
        details[open] > summary { color: #1976d2; font-weight: 500; }
        details > summary { cursor: pointer; outline: none; }
        details { margin-bottom: 6px; }
        /* 响应式 */
        @media (max-width: 900px) {
            .container { padding: 12px 2vw; }
            #instruction-bar { width: 180px; padding: 16px 4px 16px 12px; font-size: 13px; }
        }
        @media (max-width: 600px) {
            .container { padding: 2px 0; }
            #instruction-bar { display: none; }
            #dragbar { display: none; }
        }
        /* 路径下拉框高亮样式 */
        #path-select option.exception-path {
            background: #ffebee !important;
            color: #c62828 !important;
            font-weight: bold;
        }
        #path-select option.dynamic-path {
            background: #e8f5e9 !important;
            color: #2e7d32 !important;
            font-weight: bold;
        }
    </style>
    <script src="https://unpkg.com/vis-network/standalone/umd/vis-network.min.js"></script>
</head>
<body>
<div id="floating-controls">
    <button id="prev-btn" disabled>上一步</button>
    <button id="next-btn" disabled>下一步</button>
    <button id="end-btn" disabled>结束</button>
    <button id="last-btn" disabled>最后一步</button>
</div>
<div style="display: flex; min-height: 100vh; background: #f4f6fa;">
    <div id="instruction-bar">
        <div style="font-weight:bold; font-size:18px; margin-bottom:18px; letter-spacing:1px;">指令信息</div>
        <div id="instruction-list"></div>
    </div>
    <div id="dragbar"></div>
    <div class="main-content-with-padding" style="flex: 1; min-width:0;">
        <div class="container">
            <div class="section" style="display:flex; align-items:center; gap:32px; flex-wrap:wrap;">
                <div style="flex:1; min-width:220px;">
                    <div class="section-title">路径选择</div>
                    <select id="path-select">
                        <option value="">请选择路径</option>
'''
        for path in all_paths:
            option_class = ""
            # 文本标注
            display_path = path
            if path in exception_paths:
                display_path = f'**{path}**'
            elif path in dynamic_paths:
                display_path = f'++{path}++'
            html += f'            <option value="{path}" class="{option_class}">{display_path}</option>\\n'
        html += '''
                    </select>
                </div>
                <div id="controls" style="flex:2; display: flex; gap: 16px; align-items:center;">
                    <button id="start-btn">开始符号执行</button>
                </div>
            </div>
            <div class="section">
                <div class="section-title" style="display:flex;align-items:center;gap:16px;">
                    符号执行图（Graph）
                    <button id="graph-reset-btn" style="margin-left:12px;padding:4px 16px;border-radius:5px;border:none;background:#1976d2;color:#fff;cursor:pointer;font-size:0.95em;">还原</button>
                    <button id="graph-fullscreen-btn" style="margin-left:8px;padding:4px 16px;border-radius:5px;border:none;background:#ffb300;color:#fff;cursor:pointer;font-size:0.95em;">全图查看</button>
                </div>
                <div id="graph"></div>
            </div>
            <div class="section">
                <div class="section-title">Runtime 信息</div>
                <div id="runtime"></div>
            </div>
        </div>
    </div>
</div>
<div id="graph-fullscreen-modal" style="display:none;position:fixed;z-index:9999;top:0;left:0;width:100vw;height:100vh;background:rgba(30,32,40,0.92);align-items:center;justify-content:center;">
    <div style="position:absolute;top:24px;right:36px;z-index:10001;">
        <button id="graph-fullscreen-close" style="padding:8px 22px;border-radius:6px;border:none;background:#1976d2;color:#fff;font-size:1.1em;cursor:pointer;box-shadow:0 2px 8px #222;">关闭</button>
        <button id="graph-fullscreen-reset" style="margin-left:12px;padding:8px 22px;border-radius:6px;border:none;background:#ffb300;color:#fff;font-size:1.1em;cursor:pointer;box-shadow:0 2px 8px #222;">还原</button>
    </div>
    <div id="graph-fullscreen-canvas" style="width:90vw;height:88vh;background:#fafdff;border-radius:12px;box-shadow:0 4px 32px #111;"></div>
</div>
<script>
// Mermaid初始化
// mermaid.initialize({ startOnLoad: false });

// vis-network渲染函数
function renderGraphWithVis(graph, containerId) {
    var container = document.getElementById(containerId);
    if (!graph || !graph.nodes || graph.nodes.length === 0) {
        container.innerHTML = '<div style="color:#bbb; text-align:center; padding:60px 0; font-size:1.2em;">暂无图数据</div>';
        if(containerId === 'graph') window._symbolicTraceNetwork = null;
        if(containerId === 'graph-fullscreen-canvas') window._symbolicTraceNetworkFullscreen = null;
        return;
    }
    // 1. 只保留有边连接的节点
    var edgeNodeSet = new Set();
    (graph.edges || []).forEach(e => {
        edgeNodeSet.add(e.source);
        edgeNodeSet.add(e.target);
    });
    var filteredNodes = graph.nodes.filter(n => edgeNodeSet.has(n.id));
    var filteredNodeIds = new Set(filteredNodes.map(n => n.id));
    var filteredEdges = (graph.edges || []).filter(e => filteredNodeIds.has(e.source) && filteredNodeIds.has(e.target));

    // 2. 连通分量分组（每个子图树状排布）
    var adj = {};
    filteredNodes.forEach(n => { adj[n.id] = []; });
    filteredEdges.forEach(e => { adj[e.source].push(e.target); adj[e.target].push(e.source); });
    var visited = new Set();
    var components = [];
    filteredNodes.forEach(n => {
        if (!visited.has(n.id)) {
            var queue = [n.id], comp = [];
            visited.add(n.id);
            while (queue.length) {
                var cur = queue.shift();
                comp.push(cur);
                adj[cur].forEach(nb => {
                    if (!visited.has(nb)) { visited.add(nb); queue.push(nb); }
                });
            }
            components.push(comp);
        }
    });
    // 3. 生成vis-network数据，分组树状排布，节点内容超长省略，悬浮显示完整内容
    function ellipsis(str, maxLen) {
        if (typeof str !== 'string') str = String(str);
        return str.length > maxLen ? str.slice(0, maxLen - 1) + '…' : str;
    }
    function getNodeColor(kind) {
        if (kind === 'constraint') {
            return { background: '#ede7f6', border: '#7e57c2', highlight: { background: '#ede7f6', border: '#7e57c2' } };
        } else if (kind === 'return') {
            return { background: '#e8f5e9', border: '#43a047', highlight: { background: '#e8f5e9', border: '#43a047' } };
        } else if (kind === 'revert') {
            return { background: '#ffebee', border: '#e53935', highlight: { background: '#ffebee', border: '#e53935' } };
        } else if (kind === 'inputdata') {
            return { background: '#fffde7', border: '#ffd600', highlight: { background: '#fffde7', border: '#ffd600' } };
        } else {
            return { background: '#e3f2fd', border: '#1976d2', highlight: { background: '#fffde7', border: '#fbc02d' } };
        }
    }
    var nodes = [], edges = [];
    var nodeIdSet = new Set();
    var edgeKeySet = new Set();
    components.forEach((comp, idx) => {
        if (comp.length < 2) return;
        var subNodes = filteredNodes.filter(n => comp.includes(n.id));
        var subEdges = filteredEdges.filter(e => comp.includes(e.source) && comp.includes(e.target));
        subNodes.forEach(n => {
            if (!nodeIdSet.has(n.id)) {
                var fullLabel = n.kind + ':' + n.id;
                nodes.push({
                    id: n.id,
                    label: ellipsis(fullLabel, 14),
                    title: fullLabel,
                    shape: 'box',
                    widthConstraint: { minimum: 120, maximum: 120 },
                    heightConstraint: { minimum: 36 }, // 只保留minimum，去掉maximum
                    font: { size: 16, multi: false, align: 'center' },
                    color: getNodeColor(n.kind),
                    group: idx
                });
                nodeIdSet.add(n.id);
            }
        });
        subEdges.forEach(e => {
            let edgeKey = e.source + '->' + e.target + ':' + e.label;
            if (!edgeKeySet.has(edgeKey)) {
                let edgeColor = (String(e.label) === 'contr')
                    ? { color: '#ab47bc', highlight: '#8e24aa' } // 紫色
                    : { color: '#90caf9', highlight: '#fbc02d' };
                edges.push({
                    from: e.source,
                    to: e.target,
                    label: String(e.label),
                    arrows: 'to',
                    font: { align: 'middle', size: 13 },
                    color: edgeColor,
                    group: idx
                });
                edgeKeySet.add(edgeKey);
            }
        });
    });
    var data = { nodes: new vis.DataSet(nodes), edges: new vis.DataSet(edges) };
    var options = {
        layout: {
            hierarchical: {
                enabled: true,
                direction: 'UD',
                sortMethod: 'directed',
                nodeSpacing: 180,
                levelSeparation: 180,
                treeSpacing: 300
            }
        },
        nodes: {
            borderWidth: 2,
            size: 24,
            widthConstraint: { minimum: 120, maximum: 120 },
            heightConstraint: { minimum: 36 }, // 只保留minimum，去掉maximum
            font: { size: 16, multi: false, align: 'center' },
            shape: 'box',
            margin: 6
        },
        edges: { smooth: true },
        physics: false,
        interaction: { hover: true, tooltipDelay: 100, zoomView: false } // 初始禁用缩放
    };
    container.innerHTML = '';
    var network = new vis.Network(container, data, options);
    if(containerId === 'graph') window._symbolicTraceNetwork = network;
    if(containerId === 'graph-fullscreen-canvas') window._symbolicTraceNetworkFullscreen = network;
    setTimeout(() => {
        network.fit({ animation: { duration: 500, easingFunction: 'easeInOutQuad' } });
        setTimeout(() => { network.redraw(); }, 200);
    }, 200);
    // 只在悬停且点击激活后允许缩放
    if(containerId === 'graph') {
        let zoomActive = false;
        container.addEventListener('mouseenter', function() {
            if (zoomActive) network.setOptions({ interaction: { zoomView: true } });
        });
        container.addEventListener('mouseleave', function() {
            zoomActive = false;
            network.setOptions({ interaction: { zoomView: false } });
        });
        container.addEventListener('mousedown', function(e) {
            if (e.button === 0) { // 左键点击激活
                zoomActive = true;
                network.setOptions({ interaction: { zoomView: true } });
            }
        });
        document.addEventListener('mousedown', function(e) {
            if (!container.contains(e.target)) {
                zoomActive = false;
                network.setOptions({ interaction: { zoomView: false } });
            }
        });
    }
}

// 还原按钮事件
setTimeout(function() {
    var btn = document.getElementById('graph-reset-btn');
    if (btn) {
        btn.onclick = function() {
            if (window._symbolicTraceNetwork) {
                window._symbolicTraceNetwork.fit({ animation: { duration: 400, easingFunction: 'easeInOutQuad' } });
            }
        };
    }
}, 500);

// 全图查看按钮事件
setTimeout(function() {
    var btn = document.getElementById('graph-fullscreen-btn');
    if (btn) {
        btn.onclick = function() {
            var modal = document.getElementById('graph-fullscreen-modal');
            modal.style.display = 'flex';
            // 渲染全屏graph，使用当前filteredStates[currentStep]的graph
            if(typeof filteredStates !== 'undefined' && filteredStates.length > 0 && typeof currentStep !== 'undefined') {
                var state = filteredStates[currentStep];
                renderGraphWithVis(state.graph, 'graph-fullscreen-canvas');
            }
        };
    }
    // 关闭按钮
    var closeBtn = document.getElementById('graph-fullscreen-close');
    if (closeBtn) {
        closeBtn.onclick = function() {
            var modal = document.getElementById('graph-fullscreen-modal');
            modal.style.display = 'none';
            // 清空全屏graph内容
            document.getElementById('graph-fullscreen-canvas').innerHTML = '';
            window._symbolicTraceNetworkFullscreen = null;
        };
    }
    // 全屏还原按钮
    var resetBtn = document.getElementById('graph-fullscreen-reset');
    if (resetBtn) {
        resetBtn.onclick = function() {
            if(window._symbolicTraceNetworkFullscreen) {
                window._symbolicTraceNetworkFullscreen.fit({ animation: { duration: 400, easingFunction: 'easeInOutQuad' } });
            }
        };
    }
}, 500);

// 解析trace数据
const allStates = JSON.parse(`''' + json.dumps(states, ensure_ascii=False) + '''`);
const allPaths = JSON.parse(`''' + json.dumps(all_paths, ensure_ascii=False) + '''`);
const instructions = JSON.parse(`''' + json.dumps(self.instructions, ensure_ascii=False) + '''`);

let currentPath = null;
let filteredStates = [];
let currentStep = 0;

function isSubPath(label, path) {
    return path.startsWith(label);
}
function filterStatesByPath(path) {
    return allStates.filter(s => {
        if (!s.runtime || !s.runtime.path_label) return false;
        return path.startsWith(s.runtime.path_label);
    });
}
function renderGraph(graph, prevGraph) {
    let mermaidStr = 'graph TD\\n';
    if (!graph || !graph.nodes) return '';
    let nodeMap = {};
    let prevNodeIds = new Set();
    let prevEdgeKeys = new Set();
    if (prevGraph && prevGraph.nodes) {
        prevGraph.nodes.forEach(n => prevNodeIds.add(n.id));
    }
    if (prevGraph && prevGraph.edges) {
        prevGraph.edges.forEach(e => prevEdgeKeys.add(e.source + '->' + e.target + ':' + e.label));
    }
    let highlightNodes = [];
    let highlightEdges = [];
    graph.nodes.forEach(n => {
        nodeMap[n.id] = n.kind + ':' + n.id;
        mermaidStr += `    ${n.id}[${n.kind}: ${n.id}]\\n`;
        if (!prevNodeIds.has(n.id)) {
            highlightNodes.push(n.id);
        }
    });
    if (graph.edges) {
        graph.edges.forEach(e => {
            mermaidStr += `    ${e.source}-->|${e.label}|${e.target}\\n`;
            let key = e.source + '->' + e.target + ':' + e.label;
            if (!prevEdgeKeys.has(key)) {
                highlightEdges.push([e.source, e.target, e.label]);
            }
        });
    }
    if (highlightNodes.length > 0) {
        mermaidStr += '    classDef highlight fill:#ffeb3b,stroke:#f44336,stroke-width:3px;\\n';
        highlightNodes.forEach(nid => {
            mermaidStr += `    class ${nid} highlight;\\n`;
        });
    }
    return mermaidStr;
}
function renderRuntime(runtime) {
    if (!runtime) return '';
    let html = '<b>PC:</b> <span style="color:#1976d2">' + runtime.pc + '</span><br/>';
    html += '<b>Stack:</b>' + renderExpandableArray(runtime.stack, 'stack') + '<br/>';
    html += '<b>Memory:</b>' + renderExpandableArray(runtime.memory, 'memory') + '<br/>';
    html += '<b>Storage:</b>' + renderExpandableDict(runtime.storage, 'storage') + '<br/>';
    html += '<b>Balance:</b>' + renderExpandableDict(runtime.balance, 'balance') + '<br/>';
    html += '<b>Path:</b>' + renderExpandableArray(runtime.path, 'path') + '<br/>';
    html += '<b>Path Label:</b> <span style="color:#1976d2">' + runtime.path_label + '</span><br/>';
    return html;
}
function renderExpandableArray(arr, id) {
    const minRows = 10;
    let html = `<div style='max-height:240px; min-height:240px; overflow-y:auto; border:1.5px solid #e3e8f0; border-radius:6px; background:#fff; padding:4px 8px; margin:4px 0; display:flex; flex-direction:column; justify-content:flex-start;'>`;
    if (!arr || arr.length === 0) {
        for (let i = 0; i < minRows; i++) {
            html += `<div style='height:20px; color:#bbb; font-style:italic; border-bottom:1px solid #f0f0f0; font-family:monospace;'>[${i}] (空)</div>`;
        }
    } else {
        let count = Math.max(arr.length, minRows);
        for (let i = 0; i < count; i++) {
            if (i < arr.length) {
                html += `<div style='border-bottom:1px solid #f0f0f0; padding:2px 0; font-family:monospace;'>[${i}] ${JSON.stringify(arr[i])}</div>`;
            } else {
                html += `<div style='height:20px; color:#bbb; font-style:italic; border-bottom:1px solid #f0f0f0; font-family:monospace;'>[${i}] (空)</div>`;
            }
        }
    }
    html += '</div>';
    return html;
}
function renderExpandableDict(obj, id) {
    const minRows = 10;
    let keys = obj ? Object.keys(obj) : [];
    let html = `<div style='max-height:240px; min-height:240px; overflow-y:auto; border:1.5px solid #e3e8f0; border-radius:6px; background:#fff; padding:4px 8px; margin:4px 0; display:flex; flex-direction:column; justify-content:flex-start;'>`;
    if (!obj || keys.length === 0) {
        for (let i = 0; i < minRows; i++) {
            html += `<div style='height:20px; color:#bbb; font-style:italic; border-bottom:1px solid #f0f0f0; font-family:monospace;'>{空}</div>`;
        }
    } else {
        let count = Math.max(keys.length, minRows);
        for (let i = 0; i < count; i++) {
            if (i < keys.length) {
                let k = keys[i];
                html += `<div style='border-bottom:1px solid #f0f0f0; padding:2px 0; font-family:monospace;'>${k}: ${JSON.stringify(obj[k])}</div>`;
            } else {
                html += `<div style='height:20px; color:#bbb; font-style:italic; border-bottom:1px solid #f0f0f0; font-family:monospace;'>{空}</div>`;
            }
        }
    }
    html += '</div>';
    return html;
}
function renderInstructionList(highlightPc = null) {
    let html = '';
    const pcs = Object.keys(instructions).map(x => parseInt(x)).sort((a, b) => a - b);
    pcs.forEach(pc => {
        const highlightClass = (highlightPc !== null && pc === highlightPc) ? "instruction-highlight" : "";
        html += `<div class="${highlightClass}" style="padding:3px 0; border-bottom:1px solid #333; font-family:monospace; border-radius:3px; margin-bottom:1px;">
            <span style="color:#ffd600;">[${pc}]</span> <span>${instructions[pc]}</span>
        </div>`;
    });
    document.getElementById('instruction-list').innerHTML = html;
}
renderInstructionList();
function updateUI() {
    if (filteredStates.length === 0 || currentStep < 0 || currentStep >= filteredStates.length) {
        document.getElementById('graph').innerHTML = '<div style="color:#bbb; text-align:center; padding:60px 0; font-size:1.2em;">暂无图数据</div>';
        document.getElementById('runtime').innerHTML = '<div style="color:#bbb; text-align:center; padding:40px 0; font-size:1.1em;">暂无Runtime信息</div>';
        document.getElementById('prev-btn').disabled = true;
        document.getElementById('next-btn').disabled = true;
        document.getElementById('end-btn').disabled = true;
        document.getElementById('last-btn').disabled = true;
        renderInstructionList();
        return;
    }
    const state = filteredStates[currentStep];
    const prevState = currentStep > 0 ? filteredStates[currentStep - 1] : null;
    // 用vis-network渲染graph
    renderGraphWithVis(state.graph, 'graph');
    document.getElementById('runtime').innerHTML = renderRuntime(state.runtime);
    document.getElementById('prev-btn').disabled = currentStep === 0;
    document.getElementById('next-btn').disabled = currentStep === filteredStates.length - 1;
    document.getElementById('end-btn').disabled = false;
    document.getElementById('last-btn').disabled = filteredStates.length === 0 || currentStep === filteredStates.length - 1;
    renderInstructionList(state.runtime && typeof state.runtime.pc === 'number' ? state.runtime.pc : null);
}
document.getElementById('start-btn').onclick = function() {
    const path = document.getElementById('path-select').value;
    if (!path) { alert('请选择路径'); return; }
    currentPath = path;
    filteredStates = filterStatesByPath(path);
    currentStep = 0;
    updateUI();
};
document.getElementById('prev-btn').onclick = function() {
    if (currentStep > 0) {
        currentStep--;
        updateUI();
    }
};
document.getElementById('next-btn').onclick = function() {
    if (currentStep < filteredStates.length - 1) {
        currentStep++;
        updateUI();
    }
};
document.getElementById('end-btn').onclick = function() {
    filteredStates = [];
    currentStep = 0;
    updateUI();
};
document.getElementById('last-btn').onclick = function() {
    if (filteredStates.length > 0) {
        currentStep = filteredStates.length - 1;
        updateUI();
    }
};
const dragbar = document.getElementById('dragbar');
const instructionBar = document.getElementById('instruction-bar');
let isDragging = false;
dragbar.addEventListener('mousedown', function(e) {
    isDragging = true;
    document.body.style.cursor = 'ew-resize';
});
document.addEventListener('mousemove', function(e) {
    if (!isDragging) return;
    let minWidth = 120, maxWidth = 600;
    let newWidth = e.clientX;
    if (newWidth < minWidth) newWidth = minWidth;
    if (newWidth > maxWidth) newWidth = maxWidth;
    instructionBar.style.width = newWidth + 'px';
});
document.addEventListener('mouseup', function(e) {
    isDragging = false;
    document.body.style.cursor = '';
});
</script>
</body>
</html>
'''
        # 输出HTML到文件
        output_path = os.path.join(params.OUTPUT_PATH, filename)
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(html)
        logger.info(f"symbolic trace HTML已生成: {output_path}")
