import networkx
import json
from networkx.readwrite import json_graph
from utils.util import get_vars
import z3

class Node:
    def __init__(self, name):
        self.name = name

    def __str__(self):
        return "N_" + self.name


class ConstraintNode(Node):
    def __init__(self, name, constraints, pc):
        super().__init__(name)
        self.pc = pc
        self.constraints = constraints
        self.parent = None
        self.children = []

    def set_parent(self, parent):
        self.parent = parent

    def add_child(self, child):
        if self.children is None:
            self.children = []
        self.children.append(child)

    def __str__(self):
        return "CN_" + self.name


class VariableNode(Node):
    def __init__(self, name, value):
        super().__init__(name)
        self.value = value

    def __str__(self):
        return "VN_" + self.name


class InstructionNode(Node):
    def __init__(self, pc, name, operands, n_constraint):
        super().__init__(name)
        self.pc = pc
        self.n_constraint = n_constraint
        self.operands = operands

    def get_constraints(self):
        return self.n_constraint

    def get_operands(self):
        return self.operands

    def __str__(self):
        return "IN_" + self.name + "_" + str(self.pc)


class ArithNode(InstructionNode):
    def __init__(self, pc, name, operands, n_constraint, n_result):
        super().__init__(pc, name, operands, n_constraint)
        self.n_result = n_result

    def __str__(self):
        return "Arith_" + str(self.name) + "_" + str(self.pc)

class ExprNode(InstructionNode):
    def __init__(self, pc, name, operands, n_constraint, n_var):
        super().__init__(pc, name, operands, n_constraint)
        self.var = n_var
    
    def __str__(self):
        return "Expr_" + str(self.name) + "_" + str(self.pc)

class CallNode(InstructionNode):
    def __init__(self, pc, name, operands, n_constraint, args_node, status_node, ret_data_node, ret_size_node):
        super().__init__(pc, name, operands, n_constraint)
        self.args_node = args_node
        self.status_node = status_node
        self.ret_data_node = ret_data_node
        self.ret_size_node = ret_size_node
    
    def __str__(self):
        return "Call_" + str(self.name)

class CallCodeNode(InstructionNode):
    def __init__(self, pc, name, operands, n_constraint, args_node, status_node, ret_data_node, ret_size_node):
        super().__init__(pc, name, operands, n_constraint)
        self.args_node = args_node
        self.status_node = status_node
        self.ret_data_node = ret_data_node
        self.ret_size_node = ret_size_node
    
    def __str__(self):
        return "CallCode_" + str(self.name)

class DelegateCallCodeNode(InstructionNode):
    def __init__(self, pc, name, operands, n_constraint, args_node, status_node, ret_data_node, ret_size_node):
        super().__init__(pc, name, operands, n_constraint)
        self.args_node = args_node
        self.status_node = status_node
        self.ret_data_node = ret_data_node
        self.ret_size_node = ret_size_node
    
    def __str__(self):
        return "DelegateCallCode_" + str(self.name)

class StaticCallCodeNode(InstructionNode):
    def __init__(self, pc, name, operands, n_constraint, args_node, status_node, ret_data_node, ret_size_node):
        super().__init__(pc, name, operands, n_constraint)
        self.args_node = args_node
        self.status_node = status_node
        self.ret_data_node = ret_data_node
        self.ret_size_node = ret_size_node
    
    def __str__(self):
        return "StaticCallCode_" + str(self.name)

class ReturnNode(InstructionNode):
    def __init__(self, pc, name, operands, n_constraint):
        super().__init__(pc, name, operands, n_constraint)

    def __str__(self):
        return "Return_" + str(self.name)

class StopNode(InstructionNode):
    def __init__(self, pc, name, operands, n_constraint):
        super().__init__(pc, name, operands, n_constraint)
    
    def __str__(self):
        return "Stop_" + str(self.name)

class RevertNode(InstructionNode):
    def __init__(self, pc, name, operands, n_constraint):
        super().__init__(pc, name, operands, n_constraint)
    
    def __str__(self):
        return "Revert_" + str(self.name)

class SelfDestructNode(InstructionNode):
    def __init__(self, pc, name, operands, n_constraint):
        super().__init__(pc, name, operands, n_constraint)
    
    def __str__(self):
        return "SelfDestruct_" + str(self.name)

class SStoreNode(InstructionNode):
    def __init__(self, pc, name, operands, n_constraint, value):
        super().__init__(pc, name, operands, n_constraint)
        self.value = value
    
    def __str__(self):
        return "SStore_" + str(self.name)

class InputDataNode(VariableNode):
    def __init__(self, name, value):
        super().__init__(name, value)

    def __str__(self):
        return "ID_" + self.name


class BalanceNode(VariableNode):
    def __init__(self, name, value, address):
        super().__init__(name, value)
        self.address = address

    def __str__(self):
        return "B_" + self.name


class ValueNode(VariableNode):
    def __init__(self, name, value):
        super().__init__(name, value)

    def __str__(self):
        return "V_" + self.name


class SenderNode(VariableNode):
    def __init__(self, name, value):
        super().__init__(name, value)

    def __str__(self):
        return "S_" + self.name


class ReceiverNode(VariableNode):
    def __init__(self, name, value):
        super().__init__(name, value)

    def __str__(self):
        return "R_" + self.name

class ContractNode(VariableNode):
    def __init__(self, name, value):
        super().__init__(name, value)

    def __str__(self):
        return "C_" + self.name

class AddressNode(VariableNode):
    def __init__(self, name, value):
        super().__init__(name, value)
    
    def __str__(self):
        return "A_" + self.name


class InputDataSizeNode(VariableNode):
    def __init__(self, name, value):
        super().__init__(name, value)

    def __str__(self):
        return "IDS_" + self.name


class OriginNode(VariableNode):
    def __init__(self, name, value):
        super().__init__(name, value)

    def __str__(self):
        return "O_" + self.name


class CoinbaseNode(VariableNode):
    def __init__(self, name, value):
        super().__init__(name, value)

    def __str__(self):
        return "C_" + self.name


class CurrentNumberNode(VariableNode):
    def __init__(self, name, value):
        super().__init__(name, value)

    def __str__(self):
        return "BN_" + self.name


class GasPriceNode(VariableNode):
    def __init__(self, name, value):
        super().__init__(name, value)
    
    def __str__(self):
        return "GP_" + self.name


class DifficultyNode(VariableNode):
    def __init__(self, name, value):
        super().__init__(name, value)

    def __str__(self):
        return "BD_" + self.name

class RandaoNode(VariableNode):
    def __init__(self, name, value):
        super().__init__(name, value)
    
    def __str__(self):
        return "RD_" + self.name


class GasLimitNode(VariableNode):
    def __init__(self, name, value):
        super().__init__(name, value)
    
    def __str__(self):
        return "GL_" + self.name


class BaseFeeNode(VariableNode):
    def __init__(self, name, value):
        super().__init__(name, value)
    
    def __str__(self):
        return "BF_" + self.name


class BlobBaseFeeNode(VariableNode):
    def __init__(self, name, value):
        super().__init__(name, value)
    
    def __str__(self):
        return "BBF_" + self.name


class BlobHashNode(VariableNode):
    def __init__(self, name, index, value):
        super().__init__(name, value)
        self.index = index

    def __str__(self):
        return "BBH_" + self.name


class ChainIDNode(VariableNode):
    def __init__(self, name, value):
        super().__init__(name, value)
    
    def __str__(self):
        return "CI_" + self.name


class TimeStampNode(VariableNode):
    def __init__(self, name, value):
        super().__init__(name, value)

    def __str__(self):
        return "BT_" + self.name

class BlockHashNode(VariableNode):
    def __init__(self, name, blocknumber, value):
        super().__init__(name, value)
        self.blocknumber = blocknumber
    
    def __str__(self):
        return "BH_" + self.name


class StorageNode(VariableNode):
    def __init__(self, name, value, position):
        super().__init__(name, value)
        self.position = position

    def __str__(self):
        return "ST_" + self.name


class GasNode(VariableNode):
    def __init__(self, name, value):
        super().__init__(name, value)
    
    def __str__(self):
        return "G_" + self.name

class CallStatusNode(VariableNode):
    def __init__(self, name, value, pc):
        super().__init__(name, value)
        self.pc = pc
    
    def __str__(self):
        return "CS_" + self.name

class ReturnDataSizeNode(VariableNode):
    def __init__(self, name, value, pc):
        super().__init__(name, value)
        self.pc = pc
    
    def __str__(self):
        return "RDS_" + self.name

class ReturnDataNode(VariableNode):
    def __init__(self, name, value, pc):
        super().__init__(name, value)
        self.pc = pc
    
    def __str__(self):
        return "RD_" + self.name

class CallArgsNode(VariableNode):
    def __init__(self, name, value, pc):
        super().__init__(name, value)
        self.pc = pc
    
    def __str__(self):
        return "CA_" + self.name

class MediaNode(VariableNode):
    def __init__(self, name, value, from_value):
        super().__init__(name, value)
        self.from_value = from_value

    def __str__(self):
        return "M_" + self.name




class SGraph:
    def __init__(self):
        self.graph = networkx.DiGraph()
        self.mapping_var_node = {}  # var -> Node
        self.mapping_address_node = {}  # var -> Node
        self.mapping_blockhash_node = {}  # var -> Node
        self.mapping_storage_node = {}  # var -> Node
        self.init_constraint = None
        self.inputdata_node = None
        self.mapping_media_node = {}  # var -> Node

        self.arith_nodes = {}  # pc -> ArithNodes
        self.expr_nodes = {}  # pc -> ExprNodes
        self.call_nodes = {}  # pc -> CallNodes
        self.call_code_nodes = {}  # pc -> CallCodeNodes
        self.delegate_call_code_nodes = {}  # pc -> DelegateCallCodeNodes
        self.static_call_code_nodes = {}  # pc -> StaticCallCodeNodes
        self.return_nodes = {}  # pc -> ReturnNodes
        self.stop_nodes = {}  # pc -> StopNodes
        self.revert_nodes = {}  # pc -> RevertNodes
        self.selfdestruct_nodes = {}  # pc -> SelfDestructNodes
        self.sstore_nodes = {}  # pc -> SStoreNodes

    def add_var_node(self, var, node):
        self.graph.add_node(node, kind="var")
        self.mapping_var_node[var] = node

    def set_current_number_node(self, var, node):
        self.current_number_node = node
        self.add_var_node(var, node)

    def add_media_node(self, var, node):
        self.graph.add_node(node, kind="media")
        self.mapping_var_node[var] = node
        self.mapping_media_node[var] = node

    def add_address_node(self, is_var, expr, node):
        self.graph.add_node(node, kind="address")
        if is_var:
            self.mapping_var_node[expr] = node
        self._add_data_edge(node, expr)
        self.mapping_address_node[expr] = node
        

    def add_constraint_node(self, node, current):
        self.graph.add_node(node, kind="constraint")
        self._add_data_edge(node, node.constraints)
        self.graph.add_edge(current, node, label="contr")

    def set_init_constraint(self, node):
        self.graph.add_node(node, kind="constraint")
        self.init_constraint = node
        self._add_data_edge(node, node.constraints)

    def set_inputdata_node(self,var, node):
        self.graph.add_node(node, kind="inputdata")
        self.mapping_var_node[var] = node
        self.inputdata_node = node

    def add_blockhash_node(self, var, node, blocknum):
        self.graph.add_node(node, kind="blockhash")
        self.mapping_blockhash_node[var] = node
        self.mapping_var_node[var] = node
        self._add_data_edge(node, blocknum)

    def add_arith_node(self, pc, node):
        self.graph.add_node(node, kind="arith")
        if pc not in self.arith_nodes:
            self.arith_nodes[pc] = [node]
        else:
            self.arith_nodes[pc].append(node)
        self.graph.add_edge(node.n_constraint, node, label="contr")
        for operand in node.operands:
            self._add_data_edge(node, operand)
        self.graph.add_edge(node, node.n_result, label="data")

    def add_sstore_node(self, pc, node):
        self.graph.add_node(node, kind="sstore")
        if pc not in self.sstore_nodes:
            self.sstore_nodes[pc] = [node]
        else:
            self.sstore_nodes[pc].append(node)
        # for operand in node.operands:
        #     self._add_data_edge(node, operand)
        position = node.operands[0]
        storage_node = None
        for storage in self.mapping_storage_node:
            solver = z3.Solver()
            solver.add(position != self.mapping_storage_node[storage].position)
            result = solver.check()
            if result == z3.unsat:
                storage_node = self.mapping_storage_node[storage]
                break
        if storage_node is None:
            raise Exception(f"Storage node for position {position} not found in mapping_storage_node")
        self.graph.add_edge(node, storage_node, label="data")

        self._add_data_edge(node, node.value)
        self.graph.add_edge(node.n_constraint, node, label="contr")

    def add_expr_node(self, pc, node):
        self.graph.add_node(node, kind="expr")
        if pc not in self.expr_nodes:
            self.expr_nodes[pc] = [node]
        else:
            self.expr_nodes[pc].append(node)
        for operand in node.operands:
            self._add_data_edge(node.var, operand)

    def add_storage_node(self, var, node):
        self.graph.add_node(node, kind="storage")
        self.mapping_storage_node[var] = node
        self.mapping_var_node[var] = node
        self._add_data_edge(node, node.position)

    def add_call_args_node(self, node):
        self.graph.add_node(node, kind="call_args")
        self._add_data_edge(node, node.value)

    def add_call_node(self, pc, node):
        self.graph.add_node(node, kind="call")
        if pc not in self.call_nodes:
            self.call_nodes[pc] = [node]
        else:
            self.call_nodes[pc].append(node)
        
        self.add_data_edge(node.args_node, node)
        self.add_data_edge(node, node.status_node)
        self.add_data_edge(node, node.ret_data_node)
        self.add_data_edge(node, node.ret_size_node)
        self._add_data_edge(node, node.operands[2])
        self.graph.add_edge(node.n_constraint, node, label="contr")

    def add_call_code_node(self, pc, node):
        self.graph.add_node(node, kind="call_code")
        if pc not in self.call_code_nodes:
            self.call_code_nodes[pc] = [node]
        else:
            self.call_code_nodes[pc].append(node)
        
        self.add_data_edge(node.args_node, node)
        self.add_data_edge(node, node.status_node)
        self.add_data_edge(node, node.ret_data_node)
        self.add_data_edge(node, node.ret_size_node)

        self.graph.add_edge(node.n_constraint, node, label="contr")

    def add_delegate_call_code_node(self, pc, node):
        self.graph.add_node(node, kind="delegate_call_code")
        if pc not in self.delegate_call_code_nodes:
            self.delegate_call_code_nodes[pc] = [node]
        else:
            self.delegate_call_code_nodes[pc].append(node)
        
        self.add_data_edge(node.args_node, node)
        self.add_data_edge(node, node.status_node)
        self.add_data_edge(node, node.ret_data_node)
        self.add_data_edge(node, node.ret_size_node)

        self.graph.add_edge(node.n_constraint, node, label="contr")

    def add_static_call_code_node(self, pc, node):
        self.graph.add_node(node, kind="static_call_code")
        if pc not in self.static_call_code_nodes:
            self.static_call_code_nodes[pc] = [node]
        else:
            self.static_call_code_nodes[pc].append(node)
        
        self.add_data_edge(node.args_node, node)
        self.add_data_edge(node, node.status_node)
        self.add_data_edge(node, node.ret_data_node)
        self.add_data_edge(node, node.ret_size_node)

        self.graph.add_edge(node.n_constraint, node, label="contr")

    def add_return_node(self, pc, node):
        self.graph.add_node(node, kind="return")
        if pc not in self.return_nodes:
            self.return_nodes[pc] = [node]
        else:
            self.return_nodes[pc].append(node)
        
        self.graph.add_edge(node.n_constraint, node, label="contr")

    def add_stop_node(self, pc, node):
        self.graph.add_node(node, kind="stop")
        if pc not in self.stop_nodes:
            self.stop_nodes[pc] = [node]
        else:
            self.stop_nodes[pc].append(node)
        
        self.graph.add_edge(node.n_constraint, node, label="contr")

    def add_revert_node(self, pc, node):
        self.graph.add_node(node, kind="revert")
        if pc not in self.revert_nodes:
            self.revert_nodes[pc] = [node]
        else:
            self.revert_nodes[pc].append(node)
        
        self.graph.add_edge(node.n_constraint, node, label="contr")

    def add_selfdestruct_node(self, pc, node):
        if pc not in self.selfdestruct_nodes:
            self.selfdestruct_nodes[pc] = [node]
        else:
            self.selfdestruct_nodes[pc].append(node)
        


    def add_data_edge(self, from_node, to_node):
        self.graph.add_edge(from_node, to_node, label="data")


    def _add_data_edge(self, node, expression):
        if expression is None:
            return
        vars = get_vars(expression)
        for v in vars:
            if v not in self.mapping_var_node:
                raise Exception(f"Variable {v} not found in mapping_var_node")
            n = self.mapping_var_node[v]
            if n is not None:
                self.graph.add_edge(n, node, label="data")

    def to_json(self):
        # 转为node-link格式的dict
        json_dict = {"nodes": [], "edges": []}
        data = json_graph.node_link_data(self.graph, edges="links")
        for node in data["nodes"]:
            if "kind" not in node:
                raise Exception(f"Node {node['id']} has no kind")
            json_dict["nodes"].append({"kind": node["kind"], "id": str(node["id"])})
        for link in data["links"]:
            json_dict["edges"].append({"source": str(link["source"]), "target": str(link["target"]), "label": link["label"]})

        return json_dict
        

    
