import networkx as nx
import z3
from detectors import common

class PrngDetector:
    def __init__(self, s_graph):
        self.s_graph = s_graph
        self.n_graph = self.s_graph.graph

    def detect(self):
        """
        Detects PRNG usage in the smart contract.
        """
        prng_pcs = []
        
        for blockhash_node in self.s_graph.mapping_blockhash_node.values():
            # 检查blockhash_node计算的区块的number与是否在当前区块的前10-256个区块，以这种方式认定安全
            block_num = blockhash_node.blocknumber
            current_num = self.s_graph.current_number_node.value
            constraint = z3.And(
                block_num >= current_num - 256,
                block_num <= current_num - 10
            )
            # 检查blockhash是会会影响到call/sstore等指令
            for call_node_list in self.s_graph.call_nodes.values():
                for call_node in call_node_list:
                    if nx.has_path(self.n_graph, blockhash_node, call_node):
                        if common.solve_constraint(self.s_graph, call_node.n_constraint, constraint):
                            prng_pcs.append(call_node.pc)
            for sstore_node_list in self.s_graph.sstore_nodes.values():
                for sstore_node in sstore_node_list:
                    if nx.has_path(self.n_graph, blockhash_node, sstore_node):
                        if common.solve_constraint(self.s_graph, sstore_node.n_constraint, constraint):
                            prng_pcs.append(sstore_node.pc)
                        
        return prng_pcs