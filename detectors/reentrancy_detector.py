from detectors import common
import z3
import networkx as nx

class ReentrancyDetector:
    
    def __init__(self, s_graph):
        self.s_graph = s_graph
        self.n_graph = self.s_graph.graph

    def detect(self):
        reentrancy_pc = []
        for call_node_list in self.s_graph.call_nodes.values():
            for call_node in call_node_list:
                # 基于第一次重入的状态，检查是否可以第二次重新进入call指令
                # 先收集当前路径所有对storage的更改
                constraints = []
                for sstore_node_list in self.s_graph.sstore_nodes.values():
                    for sstore_node in sstore_node_list:
                        if common.instrs_is_up_down_ctr_path(sstore_node, call_node):
                            position = sstore_node.operands[0]
                            for storage in self.s_graph.mapping_storage_node:
                                solver = z3.Solver()
                                solver.add(position != self.s_graph.mapping_storage_node[storage].position)
                                result = solver.check()
                                if result == z3.unsat:
                                    constraints.append(self.s_graph.mapping_storage_node[storage].value == sstore_node.value)
                if common.solve_constraint(self.s_graph, call_node.n_constraint, z3.And(*constraints)):
                    # 查找是否有路径从call节点到return节点
                    for ss_node_list in self.s_graph.sstore_nodes.values():
                        for s_node in ss_node_list:
                            if common.instrs_is_up_down_ctr_path(call_node, s_node): # 检查call后面是否有sstore
                                # 检查sstore是否可达到并且顺利执行
                                for r_node_list in self.s_graph.return_nodes.values():
                                    for r_node in r_node_list:
                                        return_paths = [path for path in nx.all_simple_paths(self.n_graph, source=s_node.n_constraint, target=r_node)]
                                        if len(return_paths) > 0:
                                            if common.solve_constraint(self.s_graph, r_node.n_constraint): # return节点的约束是否可满足
                                                reentrancy_pc.append(call_node.pc)
                                for r_node_list in self.s_graph.stop_nodes.values():
                                    for r_node in r_node_list:
                                        return_paths = [path for path in nx.all_simple_paths(self.n_graph, source=s_node.n_constraint, target=r_node)]
                                        if len(return_paths) > 0:
                                            if common.solve_constraint(self.s_graph, r_node.n_constraint): # return节点的约束是否可满足
                                                reentrancy_pc.append(call_node.pc)
        return reentrancy_pc

                                
                        