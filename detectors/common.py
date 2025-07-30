import networkx as nx
import z3
from utils import params
import logging

logger = logging.getLogger(__name__)

def get_deep_constraint(graph, a, b):
        if a == b:
            return a
        elif nx.has_path(graph, a, b):
            return b
        elif nx.has_path(graph, b, a):
            return a
        else:
            raise Exception(f"two constraints {a} and {b} have no path")

def solve_constraint(graph, constraint_node, constraint=None):
    path_constraints = [substitute_constraint(graph,constraint_node.constraints)]
    p_node = constraint_node.parent
    names = [constraint_node.name]
    while p_node is not None:
        names.append(p_node.name)
        path_constraints.append(substitute_constraint(graph, p_node.constraints))
        p_node = p_node.parent
    solver = z3.Solver()
    solver.set("timeout", params.Z3_TIMEOUT)
    for path_constraint in path_constraints:
        solver.add(path_constraint)
    if constraint is not None:
        solver.add(substitute_constraint(graph, constraint))
    result = solver.check()
    if result == z3.sat: # TODO: 对求解结果进行利用
        logger.debug("【constraints path】： \n")
        for name in names:
            logger.debug(name)
        logger.debug("【Constraints model】：")
        m = solver.model()
        for d in m.decls():
            logger.debug(f"{d.name()} = {m[d]}")
        return True
    elif result == z3.unsat:
        return False
    elif result == z3.unknown:
        constraints = [c for c in solver.assertions()]
        logger.warning(f"unknown result for constraints {constraints}")
        return False


def substitute_constraint(graph, origin_expr):
    new_expr = origin_expr
    for media_node in graph.mapping_media_node.values():
        new_expr = z3.substitute(new_expr, (media_node.value, media_node.from_value))
    return new_expr

def instrs_is_up_down_ctr_path(a_node, b_node): # 检查b_node是否在a_node的后续执行路径上
    a_constraint = a_node.n_constraint
    b_constraint = b_node.n_constraint
    if a_constraint == b_constraint:
        if a_node.pc > b_node.pc:
            return False
        else:
            return True
    current = b_constraint.parent
    while current is not None:
        if a_constraint == current:
            return True
        current = current.parent
    return False

def is_ctrl_path(graph, path):
    # 检查给定路径上的每条边是否都有kind='ctrl'
    for i in range(len(path) - 1):
        if not graph[path[i]][path[i + 1]].get('kind') == 'contr':
            return False
    return True