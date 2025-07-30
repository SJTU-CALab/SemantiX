from utils import params
import logging
import copy

logger = logging.getLogger(__name__)

class DosDetector:
    def __init__(self, graph):
        self.s_graph = graph
        self.n_graph = self.s_graph.graph

    def detect(self):
        dos_pcs = []
        current = self.s_graph.init_constraint
        path = {}
        self.deep_first_search(current, path, dos_pcs)
            
        return dos_pcs
    
    def deep_first_search(self, current, path, dos_pcs):
        logger.info(f"DFS current node: {current.name.split('_')[-1]} at pc: {current.pc}")
        pc = current.pc
        if pc not in path:
            path[pc] = 1
        else:
            path[pc] += 1
        if(current is not None and len(current.children) > 0):
            if len(current.children) == 1:
                self.deep_first_search(current.children[0], path, dos_pcs)
            else:
                for child in current.children:
                    self.deep_first_search(child, copy.deepcopy(path), dos_pcs)
        else:
            for pc in path:
                if path[pc] >= params.LOOP_LIMIT:
                    dos_pcs.append(pc)


        
        
    
    