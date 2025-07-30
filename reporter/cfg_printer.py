import logging
import json
import os
from utils import params

logger = logging.getLogger()

class CFGPrinter:
    def __init__(self, cfg):
        self.cfg = cfg

    def _calculate_node_positions(self):
        """计算节点的初始位置，按照树状结构从上到下排列"""
        positions = {}
        
        # 按start地址排序节点
        sorted_nodes = sorted(self.cfg.vertices.keys())
        
        # 计算每个节点的层级（基于拓扑排序）
        levels = self._calculate_node_levels()
        
        # 为每个层级分配y坐标
        max_level = max(levels.values()) if levels else 0
        y_spacing = 150  # 层级间距
        
        # 为每个节点分配位置
        for node_id in sorted_nodes:
            level = levels.get(node_id, 0)
            y = level * y_spacing + 50  # 50是顶部边距
            
            # 在同一层级内，按节点ID排序分配x坐标
            same_level_nodes = [n for n in sorted_nodes if levels.get(n, 0) == level]
            node_index = same_level_nodes.index(node_id)
            x_spacing = 200  # 同级节点间距
            x = node_index * x_spacing + 100  # 100是左边距
            
            positions[node_id] = {"x": x, "y": y}
        
        return positions
    
    def _calculate_node_levels(self):
        """计算每个节点的层级，使用拓扑排序"""
        levels = {}
        in_degree = {}
        
        # 初始化入度
        for node_id in self.cfg.vertices:
            in_degree[node_id] = 0
        
        # 计算入度
        for src, targets in self.cfg.edges.items():
            for target in targets:
                if target in in_degree:
                    in_degree[target] += 1
        
        # 拓扑排序
        queue = [node_id for node_id, degree in in_degree.items() if degree == 0]
        level = 0
        
        while queue:
            next_queue = []
            for node_id in queue:
                levels[node_id] = level
                
                # 更新邻居的入度
                if node_id in self.cfg.edges:
                    for neighbor in self.cfg.edges[node_id]:
                        in_degree[neighbor] -= 1
                        if in_degree[neighbor] == 0:
                            next_queue.append(neighbor)
            
            queue = next_queue
            level += 1
        
        # 处理孤立节点（没有入边也没有出边的节点）
        for node_id in self.cfg.vertices:
            if node_id not in levels:
                levels[node_id] = level
        
        return levels

    def print_cfg_html_with_source_map(self, filename="cfg_source_map.html"):
        if not self.cfg.source_map:
            logger.warning("No source map provided, falling back to basic HTML generation")
            self.print_cfg_html_without_source_map(filename)
            return
            
        nodes = []
        edges = []
        pc_to_block = {}
        for start, block in self.cfg.vertices.items():
            label = f"{start}-{block.end}"
            if block.instructions[0].startswith("JUMPDEST") and len(block.instructions) > 1:
                node = {
                "id": start,
                "pc_start": block.start+1,
                "pc_end": block.end,
                "label": label,
                "type": block.get_block_type().name,
                "instructions": block.instructions,
            }
            else:
                node = {
                    "id": start,
                    "pc_start": block.start,
                    "pc_end": block.end,
                    "label": label,
                    "type": block.get_block_type().name,
                    "instructions": block.instructions,
                }
            nodes.append(node)
            # 记录每个block包含的pc
            for i in range(block.start, block.end + 1):
                pc_to_block[i] = start
        for src, targets in self.cfg.edges.items():
            block = self.cfg.vertices[src]
            for tgt in targets:
                edge_type = "fall" if hasattr(block, 'falls_to') and block.falls_to == tgt else "jump"
                edges.append({
                    "from": src,
                    "to": tgt,
                    "type": edge_type
                })

        # 按pc顺序展示所有字节码
        all_pcs = sorted(self.cfg.instructions.keys())
        bytecode_lines = []
        for pc in all_pcs:
            # 每行加唯一id，方便高亮，并添加点击事件
            bytecode_lines.append(f'<div class="bytecode-line" id="bytecode-{pc}" data-block="{pc_to_block.get(pc, -1)}" data-pc="{pc}" onclick="highlightSourceForPc({pc})">{pc}: {self.cfg.instructions[pc]}</div>')
        bytecode_html = "\n".join(bytecode_lines)

        # 获取源代码内容
        source_content = self.cfg.source_map.source.content
        source_lines = source_content.split('\n')
        
        # 为每行源代码添加id和data属性，支持精确位置高亮
        source_lines_html = []
        for i, line in enumerate(source_lines):
            # 为每行添加字符级别的span，支持精确位置高亮
            line_with_spans = ''.join([f'<span class="char-{i}-{j}" data-line="{i}" data-char="{j}">{char}</span>' for j, char in enumerate(line)])
            source_lines_html.append(f'<div class="source-line" id="source-line-{i}" data-line="{i}">{i+1}: {line_with_spans}</div>')
        source_html = "\n".join(source_lines_html)

        # 计算节点位置
        node_positions = self._calculate_node_positions()

        # 计算每个pc对应的精确源代码位置
        pc_to_source_positions = {}
        for start, block in self.cfg.vertices.items():
            source_lines_set = set()
            for pc in range(block.start, block.end + 1):
                if pc in self.cfg.instructions:
                    try:
                        position = self.cfg.source_map.get_position_with_pc(pc)
                        if 'begin' in position and 'end' in position:
                            # 根据begin和end位置计算对应的源代码行号
                            begin_pos = position['begin']
                            end_pos = position['end']
                            
                            # 计算begin和end位置对应的行号
                            begin_line = self.cfg.source_map.get_line_number_from_position(begin_pos)
                            end_line = self.cfg.source_map.get_line_number_from_position(end_pos)
                            
                            # 添加这个范围内的所有行
                            for line_num in range(begin_line, end_line + 1):
                                source_lines_set.add(line_num)
                            
                            # 记录精确位置信息
                            pc_to_source_positions[pc] = {
                                'begin_pos': begin_pos,
                                'end_pos': end_pos,
                                'begin_line': begin_line,
                                'end_line': end_line
                            }
                    except (KeyError, IndexError):
                        pass

        html = f"""
<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<title>EVM CFG Interactive Visualization with Source Code</title>
<script src="https://unpkg.com/vis-network/standalone/umd/vis-network.min.js"></script>
<style>
    body {{ 
        display: flex; 
        flex-direction: row; 
        margin: 0; 
        padding: 0; 
        height: 100vh; 
        overflow: hidden; 
    }}
    .panel {{
        display: flex;
        flex-direction: column;
        height: 100%;
    }}
    #bytecode-list {{ 
        width: 300px; 
        height: 100%; 
        overflow-y: auto; 
        border: 1px solid #ccc; 
        margin-right: 5px; 
        font-family: monospace; 
        font-size: 12px; 
        resize: horizontal;
        overflow: auto;
        min-width: 200px;
    }}
    #mynetwork {{ 
        flex: 1; 
        height: 100%; 
        border: 1px solid lightgray; 
        margin-right: 5px; 
        resize: horizontal;
        overflow: auto;
        min-width: 300px;
    }}
    #source-list {{ 
        width: 400px; 
        height: 100%; 
        overflow-y: auto; 
        border: 1px solid #ccc; 
        font-family: monospace; 
        font-size: 12px; 
        resize: horizontal;
        overflow: auto;
        min-width: 250px;
    }}
    .bytecode-line {{ padding: 2px 6px; }}
    .bytecode-line.selected {{ background: #ffe066; font-weight: bold; }}
    .source-line {{ padding: 2px 6px; }}
    .source-line.selected {{ background: #ffe066; font-weight: bold; }}
    .source-char.highlighted {{ background: #ff6b6b; color: white; font-weight: bold; }}
    span.highlighted {{ background: #ff6b6b !important; color: white !important; font-weight: bold !important; }}
    .char-0-0.highlighted, .char-0-1.highlighted, .char-0-2.highlighted {{ background: #ff6b6b !important; color: white !important; font-weight: bold !important; }}
    
    /* 分隔线样式 */
    .resizer {{
        width: 5px;
        background: #f0f0f0;
        cursor: col-resize;
        border-left: 1px solid #ccc;
        border-right: 1px solid #ccc;
    }}
    .resizer:hover {{
        background: #ddd;
    }}
    
    /* 面板标题 */
    .panel-header {{
        background: #f5f5f5;
        padding: 5px 10px;
        border-bottom: 1px solid #ccc;
        font-weight: bold;
        font-size: 14px;
    }}
</style>
</head>
<body>
<div class="panel">
    <div class="panel-header">Bytecode</div>
    <div id="bytecode-list">
{bytecode_html}
    </div>
</div>
<div class="resizer" id="resizer1"></div>
<div class="panel">
    <div class="panel-header">Control Flow Graph</div>
    <div id="mynetwork"></div>
</div>
<div class="resizer" id="resizer2"></div>
<div class="panel">
    <div class="panel-header">Source Code</div>
    <div id="source-list">
{source_html}
    </div>
</div>

<script>
const cfgData = {json.dumps({'nodes': nodes, 'edges': edges})};
const nodePositions = {json.dumps(node_positions)};
const pcToSourcePositions = {json.dumps(pc_to_source_positions)};
const nodes = new vis.DataSet(cfgData.nodes.map(n => ({{
    id: n.id,
    label: n.label,
    pc_start: n.pc_start,
    pc_end: n.pc_end,
    type: n.type,
    x: nodePositions[n.id] ? nodePositions[n.id].x : 0,
    y: nodePositions[n.id] ? nodePositions[n.id].y : 0,
    color: {{
        CONDITIONAL: '#90EE90',
        TERMINAL: '#FFB6C1',
        FALLS_JUMPDEST: '#D3D3D3',
        UNCONDITIONAL: '#87CEEB'
    }}[n.type] || '#FFFFFF'
}})));
const edges = new vis.DataSet(cfgData.edges.map(e => ({{
    from: e.from,
    to: e.to,
    color: e.type === 'fall' ? 'blue' : 'red',
    dashes: e.type === 'jump'
}})));
const container = document.getElementById('mynetwork');
const data = {{ nodes, edges }};
const options = {{
    nodes: {{ shape: 'box', font: {{ multi: 'html' }} }},
    edges: {{ arrows: 'to' }},
    physics: {{ enabled: false }},
    layout: {{ improvedLayout: false }}
}};
const network = new vis.Network(container, data, options);

// 点击节点高亮对应字节码和源代码
network.on("click", function (params) {{
    // 先移除所有高亮
    document.querySelectorAll('.bytecode-line.selected').forEach(e => e.classList.remove('selected'));
    document.querySelectorAll('.source-line.selected').forEach(e => e.classList.remove('selected'));
    document.querySelectorAll('.source-char.highlighted').forEach(e => {{
        e.classList.remove('highlighted');
        e.style.backgroundColor = '';
        e.style.color = '';
        e.style.fontWeight = '';
    }});
    document.querySelectorAll('span.highlighted').forEach(e => {{
        e.classList.remove('highlighted');
        e.style.backgroundColor = '';
        e.style.color = '';
        e.style.fontWeight = '';
    }});
    
    if (params.nodes.length) {{
        const nodeId = params.nodes[0];
        
        // 获取node的label信息
        const node = cfgData.nodes.find(n => n.id == nodeId);
        
        // 高亮属于该block的所有字节码
        document.querySelectorAll('.bytecode-line').forEach(e => {{
            if (e.getAttribute('data-block') == nodeId) {{
                e.classList.add('selected');
            }}
        }});
        
        
        // 计算该block所有指令的位置并集
        const allPositions = [];
        for (let pc = node.pc_start; pc <= node.pc_end; pc++) {{
            if (pcToSourcePositions[pc]) {{
                allPositions.push(pcToSourcePositions[pc]);
            }}
        }}
        
        console.log('All positions for node', nodeId, ':', allPositions);
        
        if (allPositions.length > 0) {{
            // 计算并集：找到所有位置的最小begin和最大end
            const minBegin = Math.min(...allPositions.map(p => p.begin_pos));
            const maxEnd = Math.max(...allPositions.map(p => p.end_pos));
            
            console.log('Union range:', minBegin, 'to', maxEnd);
            
            // 根据并集范围进行精确高亮
            const sourceContent = {json.dumps(source_content)};
            const lines = sourceContent.split('\\n');
            
            let currentPos = 0;
            for (let lineNum = 0; lineNum < lines.length; lineNum++) {{
                const line = lines[lineNum];
                const lineLength = line.length + 1; // +1 for newline
                
                // 计算当前行的范围
                const lineStart = currentPos;
                const lineEnd = currentPos + line.length;
                
                // 检查当前行是否与并集范围有重叠
                if (lineStart <= maxEnd && lineEnd >= minBegin) {{
                    let startChar, endChar;
                    
                    // 情况1: 并集范围完全在当前行内
                    if (minBegin >= lineStart && maxEnd <= lineEnd) {{
                        startChar = minBegin - lineStart;
                        endChar = maxEnd - lineStart;
                    }}
                    // 情况2: 并集范围从当前行开始
                    else if (minBegin >= lineStart && maxEnd > lineEnd) {{
                        startChar = minBegin - lineStart;
                        endChar = line.length;
                    }}
                    // 情况3: 并集范围在当前行结束
                    else if (minBegin < lineStart && maxEnd <= lineEnd) {{
                        startChar = 0;
                        endChar = maxEnd - lineStart;
                    }}
                    // 情况4: 并集范围完全包含当前行
                    else if (minBegin < lineStart && maxEnd > lineEnd) {{
                        startChar = 0;
                        endChar = line.length;
                    }}
                    
                    console.log('Line', lineNum, 'highlighting chars', startChar, 'to', endChar, 'for union range');
                    
                    // 高亮该行中的精确字符范围
                    for (let charPos = startChar; charPos < endChar; charPos++) {{
                        const charSpan = document.querySelector(`.char-${{lineNum}}-${{charPos}}`);
                        if (charSpan) {{
                            charSpan.classList.add('highlighted');
                            // 添加内联样式确保高亮效果
                            charSpan.style.backgroundColor = '#ff6b6b';
                            charSpan.style.color = 'white';
                            charSpan.style.fontWeight = 'bold';
                            console.log('Highlighted char at line', lineNum, 'position', charPos);
                        }}
                    }}
                }}
                
                currentPos += lineLength;
            }}
        }}
    }}
}});

// 点击字节码高亮对应的精确源代码位置
function highlightSourceForPc(pc) {{
    console.log('Clicking bytecode pc:', pc);
    
    // 先移除所有高亮
    document.querySelectorAll('.bytecode-line.selected').forEach(e => e.classList.remove('selected'));
    document.querySelectorAll('.source-line.selected').forEach(e => e.classList.remove('selected'));
    document.querySelectorAll('.source-char.highlighted').forEach(e => {{
        e.classList.remove('highlighted');
        e.style.backgroundColor = '';
        e.style.color = '';
        e.style.fontWeight = '';
    }});
    document.querySelectorAll('span.highlighted').forEach(e => {{
        e.classList.remove('highlighted');
        e.style.backgroundColor = '';
        e.style.color = '';
        e.style.fontWeight = '';
    }});
    
    // 高亮选中的字节码行
    const bytecodeLine = document.getElementById(`bytecode-${{pc}}`);
    if (bytecodeLine) {{
        bytecodeLine.classList.add('selected');
    }}
    
    // 高亮对应的精确源代码位置
    const position = pcToSourcePositions[pc];
    console.log('Position for pc', pc, ':', position);
    
    if (position) {{
        const beginPos = position.begin_pos;
        const endPos = position.end_pos;
        const sourceContent = {json.dumps(source_content)};
        const lines = sourceContent.split('\\n');
        
        console.log('Highlighting from position', beginPos, 'to', endPos);
        
        // 计算精确的字符位置并高亮
        let currentPos = 0;
        for (let lineNum = 0; lineNum < lines.length; lineNum++) {{
            const line = lines[lineNum];
            const lineLength = line.length + 1; // +1 for newline
            
            // 计算当前行的范围
            const lineStart = currentPos;
            const lineEnd = currentPos + line.length;
            
            // 检查当前行是否与高亮范围有重叠
            if (lineStart <= endPos && lineEnd >= beginPos) {{
                let startChar, endChar;
                
                // 情况1: 高亮范围完全在当前行内
                if (beginPos >= lineStart && endPos <= lineEnd) {{
                    startChar = beginPos - lineStart;
                    endChar = endPos - lineStart;
                }}
                // 情况2: 高亮范围从当前行开始
                else if (beginPos >= lineStart && endPos > lineEnd) {{
                    startChar = beginPos - lineStart;
                    endChar = line.length;
                }}
                // 情况3: 高亮范围在当前行结束
                else if (beginPos < lineStart && endPos <= lineEnd) {{
                    startChar = 0;
                    endChar = endPos - lineStart;
                }}
                // 情况4: 高亮范围完全包含当前行
                else if (beginPos < lineStart && endPos > lineEnd) {{
                    startChar = 0;
                    endChar = line.length;
                }}
                
                console.log('Line', lineNum, 'highlighting chars', startChar, 'to', endChar, 'lineStart:', lineStart, 'lineEnd:', lineEnd, 'beginPos:', beginPos, 'endPos:', endPos);
                
                // 高亮该行中的精确字符范围
                for (let charPos = startChar; charPos < endChar; charPos++) {{
                    const charSpan = document.querySelector(`.char-${{lineNum}}-${{charPos}}`);
                    if (charSpan) {{
                        charSpan.classList.add('highlighted');
                        // 添加内联样式确保高亮效果
                        charSpan.style.backgroundColor = '#ff6b6b';
                        charSpan.style.color = 'white';
                        charSpan.style.fontWeight = 'bold';
                        console.log('Highlighted char at line', lineNum, 'position', charPos);
                    }}
                }}
            }}
            
            currentPos += lineLength;
        }}
    }} else {{
        console.log('No position found for pc:', pc);
    }}
}}

// 可调节宽度功能
function initResizers() {{
    const resizer1 = document.getElementById('resizer1');
    const resizer2 = document.getElementById('resizer2');
    const bytecodePanel = document.querySelector('.panel');
    const cfgPanel = document.querySelectorAll('.panel')[1];
    const sourcePanel = document.querySelectorAll('.panel')[2];
    
    console.log('Found panels:', {{
        resizer1: !!resizer1,
        resizer2: !!resizer2,
        bytecodePanel: !!bytecodePanel,
        cfgPanel: !!cfgPanel,
        sourcePanel: !!sourcePanel
    }});
    
    if (!resizer1 || !resizer2 || !bytecodePanel || !cfgPanel || !sourcePanel) {{
        console.error('Some panel elements not found');
        return;
    }}
    
    let isResizing1 = false;
    let isResizing2 = false;
    let startX, startWidth1, startWidth2;
    
    resizer1.addEventListener('mousedown', function(e) {{
        isResizing1 = true;
        startX = e.clientX;
        startWidth1 = bytecodePanel.offsetWidth;
        document.body.style.cursor = 'col-resize';
        e.preventDefault();
    }});
    
    resizer2.addEventListener('mousedown', function(e) {{
        isResizing2 = true;
        startX = e.clientX;
        startWidth2 = cfgPanel.offsetWidth;
        document.body.style.cursor = 'col-resize';
        e.preventDefault();
    }});
    
    document.addEventListener('mousemove', function(e) {{
        if (!isResizing1 && !isResizing2) return;
        
        if (isResizing1) {{
            const deltaX = e.clientX - startX;
            const newWidth = Math.max(200, startWidth1 + deltaX);
            bytecodePanel.style.width = newWidth + 'px';
            // 同时调整字节码列表的宽度
            document.getElementById('bytecode-list').style.width = (newWidth - 20) + 'px';
        }}
        
        if (isResizing2) {{
            const deltaX = e.clientX - startX;
            const newWidth = Math.max(300, startWidth2 + deltaX);
            cfgPanel.style.width = newWidth + 'px';
            // 同时调整CFG图的宽度
            document.getElementById('mynetwork').style.width = (newWidth - 20) + 'px';
            
            // 重新计算源代码面板的宽度，确保占满剩余空间
            const totalWidth = window.innerWidth;
            const bytecodeWidth = bytecodePanel.offsetWidth;
            const cfgWidth = newWidth;
            const resizerWidth = 10; // 两个分隔线的总宽度
            const sourceWidth = totalWidth - bytecodeWidth - cfgWidth - resizerWidth;
            
            if (sourceWidth > 250 && sourcePanel) {{
                sourcePanel.style.width = sourceWidth + 'px';
                // 确保源代码文本框占满整个面板宽度
                document.getElementById('source-list').style.width = '100%';
                document.getElementById('source-list').style.maxWidth = 'none';
            }}
        }}
    }});
    
    document.addEventListener('mouseup', function() {{
        isResizing1 = false;
        isResizing2 = false;
        document.body.style.cursor = 'default';
    }});
    
    // 监听浏览器窗口大小变化，自动调整面板宽度
    window.addEventListener('resize', function() {{
        const totalWidth = window.innerWidth;
        const resizerWidth = 10; // 两个分隔线的总宽度
        const availableWidth = totalWidth - resizerWidth;
        
        // 按比例分配宽度
        const bytecodeWidth = Math.max(200, availableWidth * 0.25);
        const cfgWidth = Math.max(300, availableWidth * 0.5);
        const sourceWidth = Math.max(250, availableWidth * 0.25);
        
        bytecodePanel.style.width = bytecodeWidth + 'px';
        cfgPanel.style.width = cfgWidth + 'px';
        if (sourcePanel) {{
            sourcePanel.style.width = sourceWidth + 'px';
        }}
        
        // 同步调整内部元素宽度
        document.getElementById('bytecode-list').style.width = (bytecodeWidth - 20) + 'px';
        document.getElementById('mynetwork').style.width = (cfgWidth - 20) + 'px';
        // 确保源代码文本框占满整个面板宽度
        document.getElementById('source-list').style.width = '100%';
        document.getElementById('source-list').style.maxWidth = 'none';
    }});
}}

// 初始化可调节宽度功能
initResizers();
</script>
</body>
</html>
"""
        # 输出到output目录
        output_path = os.path.join(params.OUTPUT_PATH, filename)
        with open(output_path, "w", encoding="utf-8") as f:
            f.write(html)
        logger.info(f"print cfg to: {output_path}")


    def print_cfg_html_without_source_map(self, filename="cfg.html"):
        nodes = []
        edges = []
        pc_to_block = {}
        for start, block in self.cfg.vertices.items():
            label = f"{start}-{block.end}"
            node = {
                "id": start,
                "label": label,
                "type": block.get_block_type().name,
                "instructions": block.instructions,
            }
            nodes.append(node)
            # 记录每个block包含的pc
            for i in range(block.start, block.end + 1):
                pc_to_block[i] = start
        for src, targets in self.cfg.edges.items():
            block = self.cfg.vertices[src]
            for tgt in targets:
                edge_type = "fall" if hasattr(block, 'falls_to') and block.falls_to == tgt else "jump"
                edges.append({
                    "from": src,
                    "to": tgt,
                    "type": edge_type
                })

        # 按pc顺序展示所有字节码
        all_pcs = sorted(self.cfg.instructions.keys())
        bytecode_lines = []
        for pc in all_pcs:
            # 每行加唯一id，方便高亮
            bytecode_lines.append(f'<div class="bytecode-line" id="bytecode-{pc}" data-block="{pc_to_block.get(pc, -1)}">{pc}: {self.cfg.instructions[pc]}</div>')
        bytecode_html = "\n".join(bytecode_lines)

        # 计算节点位置
        node_positions = self._calculate_node_positions()

        html = f"""
<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<title>EVM CFG Interactive Visualization</title>
<script src="https://unpkg.com/vis-network/standalone/umd/vis-network.min.js"></script>
<style>
    body {{ display: flex; flex-direction: row; }}
    #bytecode-list {{ width: 350px; height: 800px; overflow-y: auto; border: 1px solid #ccc; margin-right: 10px; font-family: monospace; font-size: 15px; }}
    #mynetwork {{ flex: 1; height: 800px; border: 1px solid lightgray; }}
    .bytecode-line {{ padding: 2px 6px; }}
    .bytecode-line.selected {{ background: #ffe066; font-weight: bold; }}
</style>
</head>
<body>
<div id="bytecode-list">
{bytecode_html}
</div>
<div id="mynetwork"></div>
<script>
const cfgData = {json.dumps({'nodes': nodes, 'edges': edges})};
const nodePositions = {json.dumps(node_positions)};
const nodes = new vis.DataSet(cfgData.nodes.map(n => ({{
    id: n.id,
    label: n.label,
    type: n.type,
    x: nodePositions[n.id] ? nodePositions[n.id].x : 0,
    y: nodePositions[n.id] ? nodePositions[n.id].y : 0,
    color: {{
        CONDITIONAL: '#90EE90',
        TERMINAL: '#FFB6C1',
        FALLS_JUMPDEST: '#D3D3D3',
        UNCONDITIONAL: '#87CEEB'
    }}[n.type] || '#FFFFFF'
}})));
const edges = new vis.DataSet(cfgData.edges.map(e => ({{
    from: e.from,
    to: e.to,
    color: e.type === 'fall' ? 'blue' : 'red',
    dashes: e.type === 'jump'
}})));
const container = document.getElementById('mynetwork');
const data = {{ nodes, edges }};
const options = {{
    nodes: {{ shape: 'box', font: {{ multi: 'html' }} }},
    edges: {{ arrows: 'to' }},
    physics: {{ enabled: false }},
    layout: {{ improvedLayout: false }}
}};
const network = new vis.Network(container, data, options);

// 点击节点高亮对应字节码
network.on("click", function (params) {{
    // 先移除所有高亮
    document.querySelectorAll('.bytecode-line.selected').forEach(e => e.classList.remove('selected'));
    if (params.nodes.length) {{
        const nodeId = params.nodes[0];
        // 高亮属于该block的所有字节码
        document.querySelectorAll('.bytecode-line').forEach(e => {{
            if (e.getAttribute('data-block') == nodeId) {{
                e.classList.add('selected');
            }}
        }});
    }}
}});
</script>
</body>
</html>
"""
        # 输出到output目录
        output_path = os.path.join(params.OUTPUT_PATH, filename)
        with open(output_path, "w", encoding="utf-8") as f:
            f.write(html)
        logger.info(f"print cfg to: {output_path}")
