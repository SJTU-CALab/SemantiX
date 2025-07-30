from utils.util import get_vars
import networkx as nx
from detectors import common
from s_graph.SGraph import SStoreNode
import z3

class TodDetector:
    def __init__(self, graph):
        self.s_graph = graph
        self.n_graph = self.s_graph.graph

    def detect(self):
        """
        检测图中是否存在TOD漏洞
        """
        tod_pcs = []
        for call_node_list in self.s_graph.call_nodes.values():
            for call_node in call_node_list:
                # 检查是否有路径call节点的value是否有storage变量
                vars = get_vars(call_node.operands[2])
                for v in vars:
                    if v in self.s_graph.mapping_storage_node:
                        storage_node = self.s_graph.mapping_storage_node[v]
                        # 检查该是否有sstore指令节点指向该storage node
                        for sstore_node_list in self.s_graph.sstore_nodes.values():
                            for sstore_node in sstore_node_list:
                                if storage_node in list(self.n_graph.successors(sstore_node)):
                                    # 检查是否有路径从sstore节点的constraint节点到return节点, 并收集所有的路径上的sstore节点
                                    for return_node_list in self.s_graph.return_nodes.values():
                                        for return_node in return_node_list:
                                            for path in nx.all_simple_paths(self.n_graph, source=sstore_node.n_constraint, target=return_node.n_constraint):
                                                if common.is_ctrl_path(self.n_graph, path):
                                                    # 检查路径上是否有sstore节点并收集
                                                    constraints = []
                                                    for i in range(len(path) - 1):
                                                        ctr_node = path[i]                                                          
                                                        successors = self.n_graph.successors(ctr_node)
                                                        for succ in successors:
                                                            if isinstance(succ, SStoreNode):
                                                                if ctr_node == sstore_node.n_constraint:
                                                                    if succ == sstore_node or succ.pc < sstore_node.pc:
                                                                        continue
                                                                position = succ.operands[0]
                                                                for storage in self.s_graph.mapping_storage_node:
                                                                    solver = z3.Solver()
                                                                    solver.add(position != self.s_graph.mapping_storage_node[storage].position)
                                                                    result = solver.check()
                                                                    if result == z3.unsat:
                                                                        constraints.append(self.s_graph.mapping_storage_node[storage].value == succ.value)
                                                    # 检查收集的constraint和call节点的constraint是否可满足, TODO:该检测逻辑有问题
                                                    if common.solve_constraint(self.s_graph, call_node.n_constraint, z3.And(*constraints)):
                                                        tod_pcs.append(call_node.pc)
                                    for return_node_list in self.s_graph.stop_nodes.values():
                                        for return_node in return_node_list:
                                            for path in nx.all_simple_paths(self.n_graph, source=sstore_node.n_constraint, target=return_node.n_constraint):
                                                if common.is_ctrl_path(self.n_graph, path):
                                                    # 检查路径上是否有sstore节点并收集
                                                    constraints = []
                                                    for i in range(len(path)):
                                                        ctr_node = path[i]                                                          
                                                        successors = self.n_graph.successors(ctr_node)
                                                        for succ in successors:
                                                            if isinstance(succ, SStoreNode):
                                                                if ctr_node == sstore_node.n_constraint:
                                                                    if succ == sstore_node or succ.pc < sstore_node.pc:
                                                                        continue
                                                                position = succ.operands[0]
                                                                for storage in self.s_graph.mapping_storage_node:
                                                                    solver = z3.Solver()
                                                                    solver.add(position != self.s_graph.mapping_storage_node[storage].position)
                                                                    result = solver.check()
                                                                    if result == z3.unsat:
                                                                        constraints.append(self.s_graph.mapping_storage_node[storage].value == succ.value)
                                                    # 检查收集的constraint和call节点的constraint是否可满足
                                                    if common.solve_constraint(self.s_graph, call_node.n_constraint, z3.And(*constraints)):
                                                        tod_pcs.append(call_node.pc)
        return tod_pcs

                                                

                        
                