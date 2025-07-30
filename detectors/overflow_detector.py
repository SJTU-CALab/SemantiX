import networkx as nx
import logging
from detectors import common
import z3

logger = logging.getLogger(__name__)
INT_MAX = z3.BitVecVal(2**256 - 1, 256)

class OverflowDetector:
    def __init__(self, s_graph):
        self.s_graph = s_graph
        self.n_graph = self.s_graph.graph

    def detect(self):
        inputdata_node = self.s_graph.inputdata_node
        overflow_pc = []
        for s_node_list in self.s_graph.sstore_nodes.values():
            for s_node in s_node_list:
                for a_node_list in self.s_graph.arith_nodes.values():
                    for a_node in a_node_list:
                        # 先查找是否有路径从inputdata到sstore，并且经过可能导致overflow的arith操作
                        paths_through_overflow_arith = [path for path in nx.all_simple_paths(self.n_graph, source=inputdata_node, target=s_node) if a_node in path]
                        if len(paths_through_overflow_arith) > 0:
                            a_constraint = a_node.n_constraint
                            s_constraint = s_node.n_constraint
                            deep_constraint = common.get_deep_constraint(self.n_graph, a_constraint, s_constraint)
                            # 在查找是否有路径正确返回让overflow的arith操作成功
                            for r_node_list in self.s_graph.return_nodes.values():
                                for r_node in r_node_list:
                                    return_paths = [path for path in nx.all_simple_paths(self.n_graph, source=deep_constraint, target=r_node)]
                                    if len(return_paths) > 0:
                                        r_constraint = r_node.n_constraint
                                        overflow_constraint = self.get_overflow_constraint(a_node)
                                        result = common.solve_constraint(self.s_graph, r_constraint, overflow_constraint)
                                        if result: 
                                            overflow_pc.append(a_node.pc)
                                
                                                
                            for r_node_list in self.s_graph.stop_nodes.values():
                                for r_node in r_node_list:
                                    return_paths = [path for path in nx.all_simple_paths(self.n_graph, source=deep_constraint, target=r_node)]
                                    if len(return_paths) > 0:
                                        r_constraint = r_node.n_constraint
                                        overflow_constraint = self.get_overflow_constraint(a_node)
                                        result = common.solve_constraint(self.s_graph, r_constraint, overflow_constraint)
                                        if result: 
                                            overflow_pc.append(a_node.pc)
        return overflow_pc


    
    def get_overflow_constraint(self, a_node):
        if "ADD" in a_node.name:
            return z3.And(z3.ULT(a_node.n_result.from_value,a_node.operands[0]), z3.ULT(a_node.n_result.from_value, a_node.operands[1]))
        elif "SUB" in a_node.name:
            return z3.UGT(a_node.n_result.from_value, a_node.operands[0])
        elif "MUL" in a_node.name:
            return z3.UGT(INT_MAX/a_node.operands[1], a_node.operands[0])
       

    

                    

                
                    

        

