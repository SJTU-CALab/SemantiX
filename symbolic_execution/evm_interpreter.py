import logging
import math
import z3
import json
import os
from input_helper import input_aggregator
from symbolic_execution.name_generator import NameGenerator
from s_graph.SGraph import (SGraph, SenderNode, ReceiverNode, ValueNode, BalanceNode, InputDataSizeNode,
                            OriginNode, CoinbaseNode, CurrentNumberNode, DifficultyNode, TimeStampNode,
                            ConstraintNode, ArithNode, VariableNode, ExprNode, ContractNode, AddressNode,
                            InputDataNode, GasPriceNode, BlockHashNode, RandaoNode, GasLimitNode, ChainIDNode,
                            BaseFeeNode, BlobHashNode, BlobBaseFeeNode, StorageNode, GasNode, CallStatusNode,
                            ReturnDataSizeNode, ReturnDataNode, CallArgsNode, CallNode, CallCodeNode,
                            ReturnNode, RevertNode, DelegateCallCodeNode, StaticCallCodeNode, SelfDestructNode,
                            MediaNode, SStoreNode, StopNode)
from collections import namedtuple
from utils import params
from utils.util import convert_result, custom_deepcopy, ceil32, get_vars
from symbolic_execution.evm_cfg import BlockType

logger = logging.getLogger(__name__)

Edge = namedtuple("Edge", ["v1", "v2"])


class EVMInterpreter:
    def __init__(self, cfg, bytecode, contract):
        self.gen = NameGenerator()
        self.cfg = cfg
        self.bytecode = bytecode
        self.graph = SGraph()
        self.solver = z3.Solver()
        self.solver.set("timeout", 1000)
        self.contract = contract

        self.paths = {}
        self.path_id = 0

    def run(self, input=None, extcode={}): # input is a hex string; extcode is a dict of address and code, key is address in hex, value is code in hex string
        path_condition_nodes = []
        self.paths["exception_paths"] = {}
        self.paths["dynamic_paths"] = {}
        self.paths["all_paths"] = []

        global_state = {"pc": 0, "code": {}, "code_hash": {}, "block_hash": {}}
        self._init_global_state(path_condition_nodes, global_state)
        self.extcode = extcode

        # 注意，inputdata是是bitvec表示，其offset=0对应bitvec的低位，但是在evm的模型中对应inputdata高位
        if input is None:
            var_name = self.gen.gen_input_data(self.contract)
            input_data = z3.BitVec(var_name, params.INPUT_SIZE) 
            input_data_node = InputDataNode(var_name, input_data)
            self.graph.set_inputdata_node(input_data, input_data_node)

            var_name = self.gen.gen_data_size(self.contract)
            input_size = z3.BitVec(var_name, 256)
            input_size_node = InputDataSizeNode(var_name, input_size)
            self.graph.add_var_node(input_size, input_size_node)
        else:
            if input.startswith("0x") or input.startswith("0X"):
                input = input[2:]
            input_size_value = math.ceil(len(input) / 2)
            input_size = z3.BitVecVal(input_size_value, 256)
            input_data = z3.BitVecVal(int(input, 16), params.INPUT_SIZE)

        var_name = self.gen.gen_gas(self.contract)
        gas = z3.BitVec(var_name, 256)
        gas_node = GasNode(var_name, gas)
        self.graph.add_var_node(gas, gas_node)

        runtime = Runtime(path_condition_nodes=path_condition_nodes, global_state=global_state, input_data=input_data, input_size=input_size,
          balances={global_state["sender"]: global_state["balance_sender"]-global_state["value"],
          global_state["receiver"]: global_state["balance_receiver"]+global_state["value"]}, gas=gas)

        self._run_block(runtime, 0, 0)

        json_dict = {"all_paths": self.paths["all_paths"], "exception_paths": list(self.paths["exception_paths"].keys()), "dynamic_paths": list(self.paths["dynamic_paths"].keys())}
        with open(os.path.join(params.OUTPUT_PATH, "trace.jsonl"), "a") as f:
            f.write(json.dumps(json_dict) + "\n")
        return runtime
    

    def _run_block(self, runtime, block, pre_block):
        """
        Run the block of code starting from the given block index.
        :param runtime: Runtime object containing the current state.
        :param block: The block index to start execution from.
        :param pre_block: The previous block index.
        :return: True if execution is successful, False otherwise.
        """
        global_state = runtime.global_state
        visited = runtime.visited_edges
        runtime.path.append(block)

        if block < 0 or block not in self.cfg.vertices:
            logger.error(f"Unknown jump address {block}. Terminating this path ...")
            raise Exception(f"Unknown jump address {block}")

        logger.debug(f"Reach block address {block}")

        current_edge = Edge(pre_block, block)
        if current_edge in visited:
            count_number = visited[current_edge] + 1
            visited.update({current_edge: count_number})
        else:
            visited.update({current_edge: 1})

        # TODO: how to deal with loop better with invariant and loop dectection
        if visited[current_edge] > params.LOOP_LIMIT:
            logger.warning("Overcome a number of loop limit. Terminating this path ...")
            self.paths["exception_paths"][runtime.path_label] = runtime.path.copy()
            self.paths["all_paths"].append(runtime.path_label)
            return

        b_block = self.cfg.vertices[block]
        instructions = b_block.get_instructions()
        runtime.pc = b_block.get_start_address()
        try:
            for instr in instructions:
                self._run_instruction(runtime, b_block, instr)
        except (StackError,CodeError,ReturnDataError,MemoryError) as error:
            logger.error(f"This path results in an exception: {str(error)}, Terminating this path ...")
            raise Exception(f"This path results in an exception: {str(error)}")
        except DivError as error:
            self.paths["exception_paths"][runtime.path_label] = runtime.path.copy()
            self.paths["all_paths"].append(runtime.path_label)
            logger.warning(f"This path results in an div by zero: {str(error)}, Terminating this path ...")
            return
        except IndexError as error:
            self.paths["exception_paths"][runtime.path_label] = runtime.path.copy()
            self.paths["all_paths"].append(runtime.path_label)
            logger.warning(f"This path results in an symbolic index: {str(error)}, Terminating this path ...")
            return


        block_type = b_block.get_block_type()
        if block_type == BlockType.TERMINAL:
            logger.debug("TERMINATING A PATH ...")
            self.paths["all_paths"].append(runtime.path_label)
        elif block_type == BlockType.UNCONDITIONAL:
            successor = runtime.jump_dest
            if not z3.is_bv(successor):
                self._run_block(runtime, successor, block)
            else:
                self.paths["dynamic_paths"][runtime.path_label] = runtime.path.copy()
                self.paths["all_paths"].append(runtime.path_label)
                logger.warning(f"Encounting symbolic jump address {successor}. Terminating this path ...")
        elif block_type == BlockType.FALLS_JUMPDEST:
            successor = b_block.get_falls_to()
            if successor is not None:
                self._run_block(runtime, successor, block)
            else:
                logger.error(f"Encounting unknown falls to jump address {successor}. Terminating this path ...")
                raise Exception(f"Encounting unknown falls to jump address {successor}")
        elif block_type == BlockType.CONDITIONAL:
            successor = runtime.jump_dest
            if z3.is_bv(successor):
                self.paths["dynamic_paths"][runtime.path_label] = runtime.path.copy()
                self.paths["all_paths"].append(runtime.path_label)
                logger.warning(f"Encounting symbolic jump address {successor}. Terminating this path ...")
                return

            condition = runtime.condition

            # deep first visit and visit true branch
            self.solver.push()
            self.solver.add(condition != 0)
            result = self.solver.check()
            self.solver.pop()
            if result == z3.unsat:  # the condition is definitely false
                logger.info(f"Encounting unsat condition for pc {b_block.get_end_address()} for branch true, skipping this branch ...")
            else:
                t_constraint = convert_result(condition != 0)
                new_name = self.gen.gen_constraint(b_block.get_end_address(), t_constraint)
                t_node = ConstraintNode(new_name, t_constraint, b_block.get_end_address())
                self.graph.add_constraint_node(t_node, runtime.path_condition_nodes[-1])
                runtime.path_condition_nodes[-1].add_child(t_node)
                t_node.set_parent(runtime.path_condition_nodes[-1])

                new_runtime = runtime.copy()
                self.path_id += 1
                new_runtime.path_label = new_runtime.path_label + f"_{self.path_id}"
                new_runtime.path_condition_nodes.append(t_node)
                self._run_block(new_runtime, successor, block)
            # deep first visit and visit false branch
            self.solver.push()
            self.solver.add(condition == 0)
            result = self.solver.check()
            self.solver.pop()
            if result == z3.unsat:  # the condition is definitely false
                logger.info(f"Encounting unsat condition for pc {b_block.get_end_address()} for branch false, skipping this branch ...")
            else:
                f_constraint = convert_result(condition == 0)
                new_name = self.gen.gen_constraint(b_block.get_end_address(), f_constraint)
                f_node = ConstraintNode(new_name, f_constraint, b_block.get_end_address())
                self.graph.add_constraint_node(f_node, runtime.path_condition_nodes[-1])
                runtime.path_condition_nodes[-1].add_child(f_node)
                f_node.set_parent(runtime.path_condition_nodes[-1])

                self.path_id += 1
                runtime.path_label = runtime.path_label + f"_{self.path_id}"
                runtime.path_condition_nodes.append(f_node)
                self._run_block(runtime, b_block.get_falls_to(), block)

        return

    def _run_instruction(self, runtime, block, instruction):
        """
        Run a single instruction in the current block.
        :param runtime: Runtime object containing the current state.
        :param block: The current block being executed.
        :param instruction: The instruction to execute.
        """
        stack = runtime.stack
        global_state = runtime.global_state
        memory = runtime.memory
        pc = runtime.pc
        pc_step = 1
        constraint_node = runtime.path_condition_nodes[-1]

        instr_parts = str.split(instruction, ' ')
        opcode = instr_parts[0]
        if len(instr_parts) > 1:
            operand = instr_parts[1]
        else:
            operand = None

        if opcode == "STOP":
            node = StopNode(pc, f"stop_{pc}", [], constraint_node)
            self.graph.add_stop_node(pc, node)
            return
        elif opcode == "ADD":
            if len(stack) > 1:
                first = stack.pop()
                second = stack.pop()
                computed = convert_result((first + second))

                vars = get_vars(computed)
                if self.graph.inputdata_node.value in vars: # 说明该运算可能溢出，需要特殊处理，用中间结果表示
                    var_name = self.gen.gen_var(pc, "add")
                    var = z3.BitVec(var_name, 256)
                    var_node = MediaNode(var_name, var, computed)
                    self.graph.add_media_node(var, var_node)
                    node = ArithNode(pc, f"ADD_{self.path_id}", [first, second], constraint_node, var_node)
                    self.graph.add_arith_node(pc, node)
                    stack.append(var)
                else:
                    stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "MUL":
            if len(stack) > 1:
                first = stack.pop()
                second = stack.pop()
                computed = convert_result(first * second)

                vars = get_vars(computed)
                if self.graph.inputdata_node.value in vars: # 说明该运算可能溢出，需要特殊处理，用中间结果表示
                    var_name = self.gen.gen_var(pc, "mul")
                    var = z3.BitVec(var_name, 256)
                    var_node = MediaNode(var_name, var, computed)
                    self.graph.add_media_node(var, var_node)
                    node = ArithNode(pc, f"MUL_{self.path_id}", [first, second], constraint_node, var_node)
                    self.graph.add_arith_node(pc, node)
                    stack.append(var)
                else:
                    stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "SUB":
            if len(stack) > 1:
                first = stack.pop()
                second = stack.pop()

                computed = convert_result(first - second)

                vars = get_vars(computed)
                if self.graph.inputdata_node.value in vars: # 说明该运算可能溢出，需要特殊处理，用中间结果表示
                    var_name = self.gen.gen_var(pc, "sub")
                    var = z3.BitVec(var_name, 256)
                    var_node = MediaNode(var_name, var, computed)
                    self.graph.add_media_node(var, var_node)
                    node = ArithNode(pc, f"SUB_{self.path_id}", [first, second], constraint_node, var_node)
                    self.graph.add_arith_node(pc, node)
                    stack.append(var)
                else:
                    stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "DIV":
            if len(stack) > 1:
                first = stack.pop()
                second = stack.pop()

                self.solver.push()
                self.solver.add(second != 0)
                result = self.solver.check()
                self.solver.pop()
                if result == z3.unsat:
                    raise DivError('DIV by zero')
                else:
                    computed = convert_result(z3.UDiv(first, second))
                    stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "SDIV":
            if len(stack) > 1:
                first = stack.pop()
                second = stack.pop()

                self.solver.push()
                self.solver.add(second != 0)
                result = self.solver.check()
                self.solver.pop()
                if result == z3.unsat:
                    raise DivError('SDIV by zero')
                else:
                    computed = convert_result(first / second)
                    stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "MOD":
            if len(stack) > 1:
                first = stack.pop()
                second = stack.pop()

                self.solver.push()
                self.solver.add(second != 0)
                result = self.solver.check()
                self.solver.pop()
                if result == z3.unsat:
                    raise DivError('MOD by zero')
                else:
                    computed = convert_result(z3.URem(first,second))
                    stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "SMOD":
            if len(stack) > 1:
                first = stack.pop()
                second = stack.pop()

                self.solver.push()
                self.solver.add(second != 0)
                result = self.solver.check()
                self.solver.pop()
                if result == z3.unsat:
                    raise DivError('SMOD by zero')
                else:
                    computed = convert_result(z3.SRem(first, second))
                    stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "ADDMOD":
            if len(stack) > 2:
                first = stack.pop()
                second = stack.pop()
                third = stack.pop()

                self.solver.push()
                self.solver.add(third != 0)
                result = self.solver.check()
                self.solver.pop()
                if result == z3.unsat:
                    raise DivError('ADDMOD by zero')
                else:
                    computed = convert_result(z3.URem(first + second, third))
                    stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "MULMOD":
            if len(stack) > 2:
                first = stack.pop()
                second = stack.pop()
                third = stack.pop()

                self.solver.push()
                self.solver.add(third != 0)
                result = self.solver.check()
                self.solver.pop()
                if result == z3.unsat:
                    raise DivError('ADDMOD by zero')
                else:
                    computed = convert_result(z3.URem(first*second, third))
                    stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "EXP":
            if len(stack) > 1:
                base = stack.pop()
                exponent = stack.pop()
                # Type conversion is needed when they are mismatched
                if z3.is_bv_value(base) and z3.is_bv_value(exponent):
                    computed = z3.BitVecVal(base.as_long() ** exponent.as_long(), 256)
                else:
                    new_var_name = self.gen.gen_var(pc, "exp")
                    new_var = z3.BitVec(new_var_name, 256)
                    var_node = VariableNode(new_var_name, new_var)
                    self.graph.add_var_node(new_var, var_node)
                    node = ExprNode(pc, "EXP", [base, exponent], constraint_node, var_node)
                    self.graph.add_expr_node(pc, node)
                    computed = new_var

                stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "SIGNEXTEND":
            if len(stack) > 1:
                b = stack.pop()
                x = stack.pop()
                if z3.is_bv_value(b):
                    computed = convert_result(z3.SignExt(256-(b.as_long()+1)*8, z3.Extract((b.as_long()+1)*8-1, 0, x)))
                else:
                    new_var_name = self.gen.gen_var(pc, "signextend")
                    new_var = z3.BitVec(new_var_name, 256)
                    var_node = VariableNode(new_var_name, new_var)
                    self.graph.add_var_node(new_var, var_node)
                    node = ExprNode(pc, "SIGNEXTEND", [b, x], constraint_node, var_node)
                    self.graph.add_expr_node(pc, node)
                    computed = new_var

                stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "LT":
            if len(stack) > 1:
                first = stack.pop()
                second = stack.pop()

                computed = convert_result(z3.If(z3.ULT(first, second), z3.BitVecVal(1, 256), z3.BitVecVal(0, 256)))

                stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "GT":
            if len(stack) > 1:
                first = stack.pop()
                second = stack.pop()

                computed = convert_result(z3.If(z3.UGT(first, second), z3.BitVecVal(1, 256), z3.BitVecVal(0, 256)))
                stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "SLT":
            if len(stack) > 1:
                first = stack.pop()
                second = stack.pop()
                computed = convert_result(z3.If(first < second, z3.BitVecVal(1, 256), z3.BitVecVal(0, 256)))
                stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "SGT":
            if len(stack) > 1:
                first = stack.pop()
                second = stack.pop()
                computed = convert_result(z3.If(first > second, z3.BitVecVal(1, 256), z3.BitVecVal(0, 256)))
                stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "EQ":
            if len(stack) > 1:
                first = stack.pop()
                second = stack.pop()
                computed = convert_result(z3.If(first == second, z3.BitVecVal(1, 256), z3.BitVecVal(0, 256)))
                stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "ISZERO":
            if len(stack) > 0:
                first = stack.pop()
                computed = convert_result(z3.If(first == 0, z3.BitVecVal(1, 256), z3.BitVecVal(0, 256)))
                stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "AND":
            if len(stack) > 1:
                first = stack.pop()
                second = stack.pop()
                computed = convert_result(first & second)
                stack.append(computed)
            else:   
                raise StackError('STACK underflow')
        elif opcode == "OR":
            if len(stack) > 1:
                first = stack.pop()
                second = stack.pop()
                computed = convert_result(first | second)
                stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "XOR":
            if len(stack) > 1:
                first = stack.pop()
                second = stack.pop()
                computed = convert_result(first ^ second)
                stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "NOT":
            if len(stack) > 0:
                first = stack.pop()
                computed = convert_result(~first)
                stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "BYTE":
            if len(stack) > 1:
                first = stack.pop()
                byte_index = 31 - first
                second = stack.pop()

                computed = convert_result(z3.LShR(second, (8 * byte_index)) & 0xFF)
                stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "SHL":
            if len(stack) > 1:
                first = stack.pop()
                second = stack.pop()
                computed = convert_result(second << first)
                stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "SHR":
            if len(stack) > 1:
                first = stack.pop()
                second = stack.pop()
                computed = convert_result(z3.LShR(second, first))
                stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "SAR":
            if len(stack) > 1:
                first = stack.pop()
                second = stack.pop()
                computed = convert_result(second >> first)
                stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "SHA3":
            if len(stack) > 1:
                offset = stack.pop()
                length = stack.pop()
                if z3.is_bv_value(offset) and z3.is_bv_value(length):
                    offset = offset.as_long()
                    length = length.as_long()
                    data = [x for x in memory[offset: offset + length]]
                    value = data[0]
                    for x in data[1:]:
                        value = z3.Concat(value, x)
                    value = convert_result(value)
                    new_var_name = self.gen.gen_sha3(value)
                    new_var = z3.BitVec(new_var_name, 256)
                    var_node = VariableNode(new_var_name, new_var)
                    self.graph.add_var_node(new_var, var_node)
                    node = ExprNode(pc, "SHA3", [value], constraint_node, var_node)
                    self.graph.add_expr_node(pc, node)
                    computed = new_var
                else:
                    raise IndexError('SHA3 with symbolic offset or length')
                stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "ADDRESS":
            computed = convert_result(z3.ZeroExt(96, global_state["this"]))
            stack.append(computed)
        elif opcode == "BALANCE":
            if len(stack) > 0:
                address = stack.pop()
                std_address = convert_result(z3.Extract(159, 0, address))
                if std_address in runtime.balances:
                    computed = runtime.balances[std_address]
                else:
                    if isinstance(std_address, z3.BitVecRef) and std_address in self.graph.mapping_address_node:
                        a_node = self.graph.mapping_address_node[std_address]
                    else:
                        new_var_name = self.gen.gen_address(pc)
                        a_node = AddressNode(new_var_name, std_address)
                        self.graph.add_address_node(False, std_address, a_node)
                    new_var_name = self.gen.gen_balance(std_address)
                    balance = z3.BitVec(new_var_name, 256)
                    balance_node = BalanceNode(new_var_name, balance, std_address)
                    self.graph.add_var_node(balance, balance_node)
                    self.graph.add_data_edge(a_node, balance_node)
                    computed = balance 
                stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "ORIGIN":
            computed = convert_result(z3.ZeroExt(96, global_state["origin"]))
            stack.append(computed)
        elif opcode == "CALLER":
            computed = convert_result(z3.ZeroExt(96, global_state["sender"]))
            stack.append(computed)
        elif opcode == "CALLVALUE":
            computed = global_state["value"]
            stack.append(computed)
        elif opcode == "CALLDATALOAD":
            if len(stack) > 0:
                start = stack.pop()

                if z3.is_bv_value(start):
                    start = start.as_long()
                    value = convert_result(z3.Extract(params.INPUT_SIZE-start*8-1, params.INPUT_SIZE-256-start*8, runtime.input_data))
                    stack.append(value)
                else:
                    raise IndexError('CALLDATASIZE with symbolic start')
            else:
                raise StackError('STACK underflow')
        elif opcode == "CALLDATASIZE":
            computed = runtime.input_size
            stack.append(computed)
        elif opcode == "CALLDATACOPY":  # TODO: miu会怎么变化呢？变换inputdata
            if len(stack) > 2:
                mem_start = stack.pop()
                input_start = stack.pop()
                input_length = stack.pop()

                if z3.is_bv_value(mem_start) and z3.is_bv_value(input_start) and z3.is_bv_value(input_length):
                    mem_start = mem_start.as_long()
                    input_start = input_start.as_long()
                    input_length = input_length.as_long()
                    value = z3.Extract(params.INPUT_SIZE-input_start*8-1, params.INPUT_SIZE-input_length*8-input_start*8, runtime.input_data)
                    self._write_memory(mem_start, mem_start + input_length - 1, value, runtime)
                else:
                    raise IndexError(f'CALLDATACOPY with symbolic {mem_start}, {input_start} or {input_length}')
            else:
                raise StackError('STACK underflow')
        elif opcode == "CODESIZE":
            computed = z3.BitVecVal(math.ceil(len(self.bytecode)/2), 256)
            stack.append(computed)
        elif opcode == "CODECOPY":
            if len(stack) > 2:
                mem_start = stack.pop()
                code_start = stack.pop()
                code_length = stack.pop()

                if z3.is_bv_value(mem_start) and z3.is_bv_value(code_start) and z3.is_bv_value(code_length):
                    bytecode = self.bytecode
                    if bytecode.startswith("0x"):
                        bytecode = self.bytecode[2:]
                    start_pos = code_start.as_long() * 2  # 每个字节在十六进制字符串中占2个字符
                    end_pos = start_pos + code_length.as_long() * 2
                    hex_slice = bytecode[start_pos:end_pos]
                    int_value = int(hex_slice, 16)
                    value = z3.BitVecVal(int_value, code_length.as_long() * 8)
                    self._write_memory(mem_start.as_long(), mem_start.as_long() + code_length.as_long() - 1, value, runtime)
                else:
                    raise IndexError(f'CODECOPY with symbolic {mem_start}, {code_start} or {code_length}')
            else:
                raise StackError('STACK underflow')
        elif opcode == "GASPRICE":
            computed = global_state["gas_price"]
            stack.append(computed)
        elif opcode == "EXTCODESIZE":
            if len(stack) > 0:
                address = stack.pop()
                std_address = convert_result(z3.Extract(159, 0, address))
                if z3.is_bv_value(std_address) and std_address.as_long() in self.extcode:
                    computed = z3.BitVecVal(math.ceil(len(self.extcode[std_address.as_long()])/2), 256)
                elif std_address in global_state["code"]:
                    computed = global_state["code"][std_address]
                else:
                    raise CodeError(f'EXTCODESIZE with unknown address: {address}')
                stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "EXTCODECOPY":
            if len(stack) > 3:
                address = stack.pop()
                mem_start = stack.pop()
                code_start = stack.pop()
                code_length = stack.pop()

                if z3.is_bv_value(mem_start) and z3.is_bv_value(code_start) and z3.is_bv_value(code_length):
                    std_address = convert_result(z3.Extract(159, 0, address))
                    if z3.is_bv_value(std_address) and std_address.as_long() in self.extcode:
                        bytecode = self.extcode[std_address.as_long()]
                        if bytecode.startswith("0x"):
                            bytecode = self.bytecode[2:]
                        start_pos = code_start.as_long() * 2  # 每个字节在十六进制字符串中占2个字符
                        end_pos = start_pos + code_length.as_long() * 2
                        hex_slice = bytecode[start_pos:end_pos]
                        int_value = int(hex_slice, 16)
                        value = z3.BitVecVal(int_value, code_length.as_long() * 8)
                        self._write_memory(mem_start.as_long(), mem_start.as_long() + code_length.as_long() - 1, value, runtime)
                    else:
                        raise CodeError(f'EXTCODESIZE with unknown address: {address}')
                    
                else:
                    raise IndexError(f'EXTCODECOPY with symbolic {mem_start}, {code_start} or {code_length}')
            else:
                raise StackError('STACK underflow')
        elif opcode == "RETURNDATASIZE":
            if runtime.return_size is None:
                raise ReturnDataError('RETURNDATASIZE with unknown return data size')
            computed = runtime.return_size
            stack.append(computed)
        elif opcode == "RETURNDATACOPY":
            if len(stack) > 2:
                mem_start = stack.pop()
                return_start = stack.pop()
                return_length = stack.pop()

                if z3.is_bv_value(mem_start) and z3.is_bv_value(return_start) and z3.is_bv_value(return_length):
                    return_start = return_start.as_long()
                    return_length = return_length.as_long()
                    mem_start = mem_start.as_long()
                    value = z3.Extract((return_start + return_length)*8-1, return_start*8, runtime.return_data)
                    self._write_memory(mem_start, mem_start + return_length - 1, value, runtime)
                else:
                    raise IndexError(f'{pc} RETURNDATACOPY with symbolic {mem_start}, {return_start} or {return_length}')
            else:
                raise StackError('STACK underflow')
        elif opcode == "EXTCODEHASH":
            if len(stack) > 0:
                address = stack.pop()
                std_address = convert_result(z3.Extract(159, 0, address))
                if std_address in global_state["code_hash"]:
                    computed = global_state["code_hash"][std_address]
                else:
                    raise CodeError(f'EXTCODEHASH with unknown address: {address}')
                stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "BLOCKHASH":
            if len(stack) > 0:
                block_number = stack.pop()
                if block_number in global_state["block_hash"]:
                    computed = global_state["block_hash"][block_number]
                else:
                    new_var_name = self.gen.gen_block_hash(block_number)
                    var = z3.BitVec(new_var_name, 256)
                    node = BlockHashNode(new_var_name, block_number, var)
                    self.graph.add_blockhash_node(var, node, block_number)
                    computed = var
                stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "COINBASE":
            computed = global_state["coinbase"]
            stack.append(computed)
        elif opcode == "TIMESTAMP":
            computed = global_state["timestamp"]
            stack.append(computed)
        elif opcode == "NUMBER":
            computed = global_state["number"]
            stack.append(computed)
        elif opcode == "DIFFICULTY": # difficulty is meanningless after pos merge
            computed = global_state["difficulty"]
            stack.append(computed)
        elif opcode == "PREVRANDAO":
            computed = global_state["prev_rand"]
            stack.append(computed)
        elif opcode == "GASLIMIT":
            computed = global_state["gas_limit"]
            stack.append(computed)
        elif opcode == "CHAINID":
            computed = global_state["chain_id"]
            stack.append(computed)
        elif opcode == "SELFBALANCE":
            if global_state["this"] in runtime.balances:
                computed = runtime.balances[global_state["this"]]
            else:
                balance_this = z3.BitVec("bt", 256)  # balance of this
                node = BalanceNode("bt", balance_this, global_state["this"])
                self.graph.add_var_node(balance_this, node)
                computed = balance_this
            stack.append(computed)
        elif opcode == "BASEFEE":
            computed = global_state["base_fee"]
            stack.append(computed)
        elif opcode == "BLOBHASH":
            if len(stack) > 0:
                index = stack.pop()
                if z3.is_bv_value(index):
                    int_index = index.as_long()
                    if int_index in range(6):
                        computed = global_state["blob_hashs"][int_index]
                    else:
                        computed = z3.BitVecVal(0, 256)
                else:
                    raise IndexError(f'BLOBHASH with unknown index: {index}')
                stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "BLOBBASEFEE":
            computed = global_state["bb_base_fee"]
            stack.append(computed)
        elif opcode == "POP":
            if len(stack) > 0:
                stack.pop()
            else:
                raise StackError('STACK underflow')
        elif opcode == "MLOAD":
            if len(stack) > 0:
                offset = stack.pop()
                if z3.is_bv_value(offset):
                    computed = self._load_memory(offset.as_long(), 32, runtime)
                else:
                    raise IndexError(f'MLOAD with symbolic offset: {offset}')
                stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "MSTORE":
            if len(stack) > 1:
                offset = stack.pop()
                value = stack.pop()
                if z3.is_bv_value(offset):
                    self._write_memory(offset.as_long(), offset.as_long() + 31, value, runtime)
                else:
                    raise IndexError(f'MSTORE with symbolic offset: {offset}')
            else:
                raise StackError('STACK underflow')
        elif opcode == "MSTORE8":
            if len(stack) > 1:
                offset = stack.pop()
                value = stack.pop()
                if z3.is_bv_value(offset):
                    self._write_memory(offset.as_long(), offset.as_long(), z3.Extract(7, 0, value), runtime)
                else:
                    raise IndexError(f'MSTORE8 with symbolic offset: {offset}')
            else:
                raise StackError('STACK underflow')
        elif opcode == "SLOAD":
            if len(stack) > 0:
                position = stack.pop()
                computed = None
                for key in runtime.storages:
                    self.solver.push()
                    self.solver.add(position != key)
                    result = self.solver.check()
                    self.solver.pop()
                    if result == z3.unsat:
                        computed = runtime.storages[key]
                        break
                for storage_node in self.graph.mapping_storage_node.values():
                    old_position = storage_node.position
                    self.solver.push()
                    self.solver.add(position != old_position)
                    result = self.solver.check()
                    self.solver.pop()
                    if result == z3.unsat:
                        computed = storage_node.value
                        break
                if computed is None:
                    new_var_name = self.gen.gen_storage_index(position)
                    var = z3.BitVec(new_var_name, 256)
                    node = StorageNode(new_var_name, var, position)
                    self.graph.add_storage_node(var, node)
                    runtime.storages[position] = var
                    computed = var
                stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "SSTORE":
            if len(stack) > 1:
                position = stack.pop()
                value = stack.pop()
                exist = False
                for key in runtime.storages:
                    self.solver.push()
                    self.solver.add(position != key)
                    result = self.solver.check()
                    self.solver.pop()
                    if result == z3.unsat:
                        runtime.storages[key] = value
                        exist = True
                        break
                if not exist:
                    new_var_name = self.gen.gen_storage_index(position)
                    var = z3.BitVec(new_var_name, 256)
                    node = StorageNode(new_var_name, var, position)
                    self.graph.add_storage_node(var, node)
                    runtime.storages[position] = value
                sstore_name = self.gen.gen_sstore(pc, position)
                node = SStoreNode(pc, sstore_name, [position], constraint_node, value)
                self.graph.add_sstore_node(pc, node)
            else:
                raise StackError('STACK underflow')
        elif opcode == "JUMP":
            if len(stack) > 0:
                destination = stack.pop()
                if z3.is_bv_value(destination):
                    destination = destination.as_long()
                    if destination != block.jump_static_to:
                        block.jump_dynamic_to.add(destination)
                else:
                    block.jump_dynamic_to.add(destination)
                runtime.jump_dest = destination
        elif opcode == "JUMPI":
            if len(stack) > 1:
                destination = stack.pop()
                condition = stack.pop()
                if z3.is_bv_value(destination):
                    destination = destination.as_long()
                    if destination != block.jump_static_to:
                        block.jump_dynamic_to.add(destination)
                else:
                    block.jump_dynamic_to.add(destination)
                runtime.jump_dest = destination
                runtime.condition = condition
        elif opcode == "PC":
            computed = z3.BitVecVal(pc, 256)
            stack.append(computed)
        elif opcode == "MSIZE":
            computed = runtime.miu
            stack.append(computed)
        elif opcode == "GAS":
            computed = runtime.gas
            stack.append(computed)
        elif opcode == "JUMPDEST":
            pass
        elif opcode == "TLOAD":
            if len(stack) > 0:
                position = stack.pop()
                computed = None
                for key in runtime.t_storages:
                    self.solver.push()
                    self.solver.add(position != key)
                    result = self.solver.check()
                    self.solver.pop()
                    if result == z3.unsat:
                        computed = runtime.t_storages[key]
                        break
                if computed is None:
                    computed = z3.BitVecVal(0, 256)
                stack.append(computed)
            else:
                raise StackError('STACK underflow')
        elif opcode == "TSTORE":
            if len(stack) > 1:
                position = stack.pop()
                value = stack.pop()
                exist = False
                for key in runtime.t_storages:
                    self.solver.push()
                    self.solver.add(position != key)
                    result = self.solver.check()
                    self.solver.pop()
                    if result == z3.unsat:
                        runtime.t_storages[key] = value
                        exist = True
                        break
                if not exist:
                    runtime.t_storages[position] = value
            else:
                raise StackError('STACK underflow')
        elif opcode == "MCOPY":
            if len(stack) > 2:
                dest_start = stack.pop()
                from_start = stack.pop()
                length = stack.pop()

                if z3.is_bv_value(dest_start) and z3.is_bv_value(from_start) and z3.is_bv_value(length):
                    dest_start = dest_start.as_long()
                    from_start = from_start.as_long()
                    length = length.as_long()
                    value = self._load_memory(from_start, length, runtime)
                    self._write_memory(dest_start, dest_start + length - 1, value, runtime)
                else:
                    raise IndexError(f'MCOPY with symbolic {dest_start}, {from_start} or {length}')
            else:
                raise StackError('STACK underflow')
        elif opcode.startswith("PUSH", 0):
            position = int(opcode[4:], 10)
            pc_step += position
            if position == 0:
                stack.append(z3.BitVecVal(0, 256))
            else:
                if operand is None:
                    raise OperandError('PUSH with no operand')
                push_value = z3.BitVecVal(int(operand, 10), 256)
                stack.append(push_value)
        elif opcode.startswith("DUP", 0):
            position = int(opcode[3:], 10) - 1
            stack_size = len(stack)
            if stack_size > position:
                duplicate = stack[stack_size - position - 1]
                stack.append(duplicate)
            else:
                raise StackError('STACK underflow')
        elif opcode.startswith("SWAP", 0):
            position = int(opcode[4:], 10)
            stack_size = len(stack)
            if stack_size > position:
                temp = stack[stack_size - position - 1]
                stack[stack_size - position - 1] = stack[stack_size - 1]
                stack[stack_size - 1] = temp
            else:
                raise StackError('STACK underflow')
        elif opcode in ("LOG0", "LOG1", "LOG2", "LOG3", "LOG4"):
            params_num = int(opcode[3:])
            stack.pop()
            stack.pop()
            while params_num > 0:
                stack.pop()
                params_num -= 1
        elif opcode == "CREATE":
            if len(stack) > 2:
                stack.pop()
                stack.pop()
                stack.pop()

                new_var_name = self.gen.gen_address(pc)
                new_var = z3.BitVec(new_var_name, 256)
                node = AddressNode(new_var_name, new_var)
                self.graph.add_address_node(True, new_var, node)

                stack.append(new_var)
                raise NotSupportedError('CREATE is not implemented')
            else:
                raise StackError('STACK underflow')
        elif opcode == "CALL":
            if len(stack) > 6:
                gas = stack.pop()
                addr = stack.pop()
                value = stack.pop()
                args_offset = stack.pop()
                args_length = stack.pop()
                ret_offset= stack.pop()
                ret_length = stack.pop()

                new_var_name = self.gen.gen_call_status(pc)
                ret_status = z3.BitVec(new_var_name, 256)
                status_node = CallStatusNode(new_var_name, ret_status, pc)
                self.graph.add_var_node(ret_status, status_node)

                stack.append(ret_status)

                new_var_name = self.gen.gen_ret_data_size(pc)
                return_data_size = z3.BitVec(new_var_name, 256)
                ret_size_node = ReturnDataSizeNode(new_var_name, return_data_size, pc)
                self.graph.add_var_node(return_data_size, ret_size_node)
                runtime.return_size = return_data_size

                new_var_name = self.gen.gen_ret_data(pc)
                return_data = z3.BitVec(new_var_name, 256*10) # 10 is the max return data size
                ret_data_node = ReturnDataNode(new_var_name, return_data, pc)
                self.graph.add_var_node(return_data, ret_data_node)
                runtime.return_data = return_data

                if z3.is_bv_value(args_offset) and z3.is_bv_value(args_length) and z3.is_bv_value(ret_offset) and z3.is_bv_value(ret_length):
                    args_offset = args_offset.as_long()
                    args_length = args_length.as_long()
                    ret_offset = ret_offset.as_long()
                    ret_length = ret_length.as_long()

                    args = self._load_memory(args_offset, args_length, runtime)
                    new_var_name = self.gen.gen_call_args(pc)
                    args_node = CallArgsNode(new_var_name, args, pc)
                    self.graph.add_call_args_node(args_node)

                    self._write_memory(ret_offset, ret_offset + ret_length - 1, return_data, runtime)

                    new_var_name = self.gen.gen_call(pc)
                    call_node = CallNode(pc, new_var_name, [gas, addr, value, args_offset, args_length, ret_offset, ret_length], constraint_node, args_node, status_node, ret_data_node, ret_size_node)
                    self.graph.add_call_node(pc, call_node)

                else:
                    raise IndexError(f'CALL with symbolic {args_offset}, {args_length}, {ret_offset} or {ret_length}')
            else:
                raise StackError('STACK underflow')
        elif opcode == "CALLCODE":
            if len(stack) > 6:
                gas = stack.pop()
                addr = stack.pop()
                value = stack.pop()
                args_offset = stack.pop()
                args_length = stack.pop()
                ret_offset= stack.pop()
                ret_length = stack.pop()

                new_var_name = self.gen.gen_call_status(pc)
                ret_status = z3.BitVec(new_var_name, 256)
                status_node = CallStatusNode(new_var_name, ret_status, pc)
                self.graph.add_var_node(ret_status, status_node)

                stack.append(ret_status)

                new_var_name = self.gen.gen_ret_data_size(pc)
                return_data_size = z3.BitVec(new_var_name, 256)
                ret_size_node = ReturnDataSizeNode(new_var_name, return_data_size, pc)
                self.graph.add_var_node(return_data_size, ret_size_node)
                runtime.return_size = return_data_size

                new_var_name = self.gen.gen_ret_data(pc)
                return_data = z3.BitVec(new_var_name, 256*10) # 10 is the max return data size
                ret_data_node = ReturnDataNode(new_var_name, return_data, pc)
                self.graph.add_var_node(return_data, ret_data_node)
                runtime.return_data = return_data

                if z3.is_bv_value(args_offset) and z3.is_bv_value(args_length) and z3.is_bv_value(ret_offset) and z3.is_bv_value(ret_length):
                    args_offset = args_offset.as_long()
                    args_length = args_length.as_long()
                    ret_offset = ret_offset.as_long()
                    ret_length = ret_length.as_long()
                    args = self._load_memory(args_offset, args_length, runtime)

                    new_var_name = self.gen.gen_call_args(pc)
                    args_node = CallArgsNode(new_var_name, args, pc)
                    self.graph.add_call_args_node(args_node)

                    self._write_memory(ret_offset, ret_offset + ret_length - 1, return_data, runtime)

                    new_var_name = self.gen.gen_call(pc)
                    call_node = CallCodeNode(pc, new_var_name, [gas, addr, value, args_offset, args_length, ret_offset, ret_length], constraint_node, args_node, status_node, ret_data_node, ret_size_node)
                    self.graph.add_call_code_node(pc, call_node)
            else:
                raise StackError('STACK underflow')
        elif opcode == "RETURN":
            if len(stack) > 1:
                stack.pop()
                stack.pop()

                node = ReturnNode(pc, f"return_{pc}", [], constraint_node)
                self.graph.add_return_node(pc, node)
            else:
                raise StackError('STACK underflow')
        elif opcode == "DELEGATECALL":
            if len(stack) > 5:
                gas = stack.pop()
                addr = stack.pop()
                args_offset = stack.pop()
                args_length = stack.pop()
                ret_offset = stack.pop()
                ret_length = stack.pop()

                new_var_name = self.gen.gen_call_status(pc)
                ret_status = z3.BitVec(new_var_name, 256)
                status_node = CallStatusNode(new_var_name, ret_status, pc)
                self.graph.add_var_node(ret_status, status_node)

                stack.append(ret_status)

                new_var_name = self.gen.gen_ret_data_size(pc)
                return_data_size = z3.BitVec(new_var_name, 256)
                ret_size_node = ReturnDataSizeNode(new_var_name, return_data_size, pc)
                self.graph.add_var_node(return_data_size, ret_size_node)
                runtime.return_size = return_data_size

                new_var_name = self.gen.gen_ret_data(pc)
                return_data = z3.BitVec(new_var_name, 256*10) # 10 is the max return data size
                ret_data_node = ReturnDataNode(new_var_name, return_data, pc)
                self.graph.add_var_node(return_data, ret_data_node)
                runtime.return_data = return_data

                if z3.is_bv_value(args_offset) and z3.is_bv_value(args_length) and z3.is_bv_value(ret_offset) and z3.is_bv_value(ret_length):
                    args_offset = args_offset.as_long()
                    args_length = args_length.as_long()
                    ret_offset = ret_offset.as_long()
                    ret_length = ret_length.as_long()
                    args = self._load_memory(args_offset, args_length, runtime)

                    
                    new_var_name = self.gen.gen_call_args(pc)
                    args_node = CallArgsNode(new_var_name, args, pc)
                    self.graph.add_call_args_node(args_node)

                    self._write_memory(ret_offset, ret_offset + ret_length - 1, return_data, runtime)

                    new_var_name = self.gen.gen_call(pc)
                    call_node = DelegateCallCodeNode(pc, new_var_name, [gas, addr, args_offset, args_length, ret_offset, ret_length], constraint_node, args_node, status_node, ret_data_node, ret_size_node)
                    self.graph.add_delegate_call_code_node(pc, call_node)
            else:
                raise StackError('STACK underflow')
        elif opcode == "CREATE2":
            if len(stack) > 3:
                stack.pop()
                stack.pop()
                stack.pop()
                stack.pop()

                new_var_name = self.gen.gen_address(pc)
                new_var = z3.BitVec(new_var_name, 256)
                node = AddressNode(new_var_name, new_var)
                self.graph.add_address_node(True, new_var, node)

                stack.append(new_var)
                raise NotSupportedError('CREATE2 is not implemented')
            else:
                raise StackError('STACK underflow')
        elif opcode == "STATICCALL":
            if len(stack) > 5:
                gas = stack.pop()
                addr = stack.pop()
                args_offset = stack.pop()
                args_length = stack.pop()
                ret_offset = stack.pop()
                ret_length = stack.pop()

                new_var_name = self.gen.gen_call_status(pc)
                ret_status = z3.BitVec(new_var_name, 256)
                status_node = CallStatusNode(new_var_name, ret_status, pc)
                self.graph.add_var_node(ret_status, status_node)

                stack.append(ret_status)

                new_var_name = self.gen.gen_ret_data_size(pc)
                return_data_size = z3.BitVec(new_var_name, 256)
                ret_size_node = ReturnDataSizeNode(new_var_name, return_data_size, pc)
                self.graph.add_var_node(return_data_size, ret_size_node)
                runtime.return_size = return_data_size

                new_var_name = self.gen.gen_ret_data(pc)
                return_data = z3.BitVec(new_var_name, 256*10) # 10 is the max return data size
                ret_data_node = ReturnDataNode(new_var_name, return_data, pc)
                self.graph.add_var_node(return_data, ret_data_node)
                runtime.return_data = return_data

                if z3.is_bv_value(args_offset) and z3.is_bv_value(args_length) and z3.is_bv_value(ret_offset) and z3.is_bv_value(ret_length):
                    args_offset = args_offset.as_long()
                    args_length = args_length.as_long()
                    ret_offset = ret_offset.as_long()
                    ret_length = ret_length.as_long()
                    args = self._load_memory(args_offset, args_length, runtime)

                    new_var_name = self.gen.gen_call_args(pc)
                    args_node = CallArgsNode(new_var_name, args, pc)
                    self.graph.add_call_args_node(args_node)

                    self._write_memory(ret_offset, ret_offset + ret_length - 1, return_data, runtime)

                    new_var_name = self.gen.gen_call(pc)
                    call_node = StaticCallCodeNode(pc, new_var_name, [gas, addr, args_offset, args_length, ret_offset, ret_length], constraint_node, args_node, status_node, ret_data_node, ret_size_node)
                    self.graph.add_static_call_code_node(pc, call_node)
            else:
                raise StackError('STACK underflow')
        elif opcode == "REVERT":
            if len(stack) > 1:
                stack.pop()
                stack.pop()

                node = RevertNode(pc, f"revert_{pc}", [], constraint_node)
                self.graph.add_revert_node(pc, node)
            else:
                raise StackError('STACK underflow')
        elif opcode == "SELFDESTRUCT":
            if len(stack) > 0:
                addr = stack.pop()
                # TODO: add balance influence
                new_var_name = self.gen.gen_selfdestruct(pc)
                node = SelfDestructNode(pc, f"selfdestruct_{pc}", [addr], constraint_node)
                self.graph.add_selfdestruct_node(pc, node)
            else:
                raise StackError('STACK underflow')
        else:
            raise NotSupportedError(f'{opcode} is not recognized')

        # 打印stack和memory信息
        logger.debug("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++")
        logger.debug(f"PC: {runtime.pc}, Opcode: {opcode}, Operand: {operand}")
        logger.debug(f"Stack: {runtime.stack}")
        logger.debug(f"Memory: {runtime.memory}")
        logger.debug("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++")
        self.add_trace(runtime, self.graph)

        runtime.pc += pc_step
        
        return


    def add_trace(self, runtime, graph):
        json_dict = {}
        runtime_json = runtime.to_json()
        graph_json = graph.to_json()
        json_dict["pc"] = runtime.pc
        json_dict["runtime"] = runtime_json
        json_dict["graph"] = graph_json
        # 添加到output路径下的trace.jsonl，如果文件不存在，则创建，如果存在则添加到后面
        with open(os.path.join(params.OUTPUT_PATH, "trace.jsonl"), "a") as f:
            f.write(json.dumps(json_dict) + "\n")
        


    def _init_global_state(self, path_condition_nodes, global_state):
        sender = z3.BitVec("ts", 160)  # transaction sender address
        node = SenderNode("ts", sender)
        self.graph.add_address_node(True, sender, node)

        receiver = z3.BitVec("tr", 160)  # transaction receiver address
        node = ReceiverNode("tr", receiver)
        self.graph.add_address_node(True, receiver, node)

        contract = z3.BitVec("this", 160)  # transaction receiver address
        node = ContractNode(self.contract, contract)
        self.graph.add_address_node(True, contract, node)

        value = z3.BitVec("tv", 256)  # value to transfer
        node = ValueNode("tv", value)
        self.graph.add_var_node(value, node)

        var_name = self.gen.gen_balance(sender)
        balance_sender = z3.BitVec(var_name, 256)  # balance of sender
        node = BalanceNode(var_name, balance_sender, sender)
        self.graph.add_var_node(balance_sender, node)

        var_name = self.gen.gen_balance(receiver)
        balance_receiver = z3.BitVec(var_name, 256)  # balance of receiver
        node = BalanceNode(var_name, balance_receiver, receiver)
        self.graph.add_var_node(balance_receiver, node)

        var_name = self.gen.gen_origin_var()
        origin = z3.BitVec(var_name, 160)
        node = OriginNode(var_name, origin)
        self.graph.add_var_node(origin, node)

        var_name = self.gen.gen_coin_base()
        coinbase = z3.BitVec(var_name, 256)
        node = CoinbaseNode(var_name, coinbase)
        self.graph.add_var_node(coinbase, node)

        var_name = self.gen.gen_number()
        b_number = z3.BitVec(var_name, 256)
        node = CurrentNumberNode(var_name, b_number)
        self.graph.set_current_number_node(b_number, node)

        gas_price = z3.BitVec("gp", 256)
        node = GasPriceNode("gp", gas_price)
        self.graph.add_var_node(gas_price, node)

        gas_limit = z3.BitVec("gl", 256)
        node = GasLimitNode("gl", gas_limit)
        self.graph.add_var_node(gas_price, node)

        base_fee = z3.BitVec("bf", 256)
        node = BaseFeeNode("bf", base_fee)
        self.graph.add_var_node(base_fee, node)

        bb_base_fee = z3.BitVec("bbf", 256)
        node = BlobBaseFeeNode("bbf", bb_base_fee)
        self.graph.add_var_node(bb_base_fee, node)

        chain_id = z3.BitVec("ci", 256)
        node = ChainIDNode("ci", chain_id)
        self.graph.add_var_node(chain_id, node)

        var_name = self.gen.gen_difficult()
        difficulty = z3.BitVec(var_name, 256)
        node = DifficultyNode(var_name, difficulty)
        self.graph.add_var_node(difficulty, node)

        var_name = self.gen.gen_randao()
        randao = z3.BitVec(var_name, 256)
        node = RandaoNode(var_name, randao)
        self.graph.add_var_node(randao, node)

        var_name = self.gen.gen_timestamp()
        timestamp = z3.BitVec(var_name, 256)
        node = TimeStampNode(var_name, timestamp)
        self.graph.add_var_node(timestamp, node)

        blob_hashs = []
        for i in range(6):
            var_name = self.gen.gen_blob_hash(i)
            blob_hash = z3.BitVec(var_name, 256)
            node = BlobHashNode(var_name, i, blob_hash)
            self.graph.add_var_node(blob_hash, node)
            blob_hashs.append(blob_hash)

        global_state["value"] = value
        global_state["sender"] = sender
        global_state["receiver"] = receiver
        global_state["this"] = contract
        global_state["origin"] = origin
        global_state["coinbase"] = coinbase
        global_state["timestamp"] = timestamp
        global_state["number"] = b_number
        global_state["difficulty"] = difficulty
        global_state["prev_rand"] = randao
        global_state["gas_price"] = gas_price
        global_state["gas_limit"] = gas_limit
        global_state["chain_id"] = chain_id
        global_state["base_fee"] = base_fee
        global_state["bb_base_fee"] = bb_base_fee
        global_state["blob_hashs"] = blob_hashs
        global_state["balance_sender"] = balance_sender
        global_state["balance_receiver"] = balance_receiver

        constraint = z3.And(value >= z3.BitVecVal(0, 256), balance_sender >= value, balance_receiver >= z3.BitVecVal(0, 256))
        node = ConstraintNode("initial_consts", constraint, 0)
        self.graph.set_init_constraint(node)
        path_condition_nodes.append(node)

        return


    def _write_memory(self, start, end, value, runtime):
        if end < 0:
            return
        memory = runtime.memory
        old_size = math.ceil(len(memory) / 32)
        new_size = math.ceil((end+1) / 32)
        runtime.miu = z3.BitVecVal(max(runtime.miu.as_long(),ceil32(end)), 256)
        mem_extend = (new_size - old_size) * 32
        memory.extend([z3.BitVecVal(0, 8)] * mem_extend)
        size = end - start + 1
        for i in range(size-1, -1, -1):
             memory[start + i] = convert_result(z3.Extract(8 * (size-i-1) + 7, 8 * (size-i-1), value))
        return

    def _load_memory(self, offset, length, runtime):
        if length == 0:
            return None
        data = []
        for i in range(0,length):  # [length-1, length-2, ..., 0]
            if (offset+i) < len(runtime.memory):
                value = runtime.memory[offset+i]
            else:
                raise MemoryError('Memory overflow')
            data.append(value)
        result = data[0]
        for i in range(1, length):
            result = z3.Concat(result, data[i])
        return convert_result(result)


class Runtime:
    def __init__(self, **kwargs):
        attr_defaults = {
            # symbolic elements in stack should be bitvec256, concrete elements in bitvecval256
            "stack": [],
            # elements located with concrete address and length are stored in memory, the value is bitvec256
            "memory": [],
            # elements located with symbolic address or length are stored in mem
            "mem": {},
            # the size of memory in use, 1 == 32 bytes == 256 bits
            "miu": z3.BitVecVal(0, 256),

            # used to show all calls of current path, every element is the real int representing pc of call instruction
            "calls": [],

            # the return data of every call instruction, {pc: {start: value}}
            "return_data": None,
            "return_size": None,
            # the input data 
            "input_data": None,
            "input_size": None,

            # current path
            "path": [],
            "path_label": "0", # the label of the current path
            # mark all the visited edges of current path
            "visited_edges": {},

            "path_condition_nodes": [],
            "global_state": {},

            "function": None,

            "storages": {}, # the storage of the current contract
            "t_storages": {}, # the transient storage of the current contract
            "balances": {}, # the balance of the current contract

            "gas": None, # the gas of the current contract
            "pc": 0, # the pc of the current instruction

            "jump_dest": None, # the jump destination of the last jump/jumpi instruction
            "condition": None, # the condition of the last jumpi instruction
        }

        for attr, default in attr_defaults.items():
            val = kwargs.get(attr, default)
            setattr(self, attr, val)

    def copy(self):
        _kwargs = custom_deepcopy(self.__dict__)
        return Runtime(**_kwargs)

    def to_json(self):
        # 将所有的属性输出为json，如果为z3的BitVec，则输出为其string形式，如果为数组则输出数组的json，如果为dict则输出dict的json，注意数组和dict的key以及element都可能是bitvec
        json_dict = {}
        json_dict["pc"] = self.pc

        json_dict["stack"] = [str(v) for v in self.stack[::-1]]
        json_dict["memory"] = [str(v) for v in self.memory]
        json_dict["return_data"] = str(self.return_data)
        json_dict["return_size"] = str(self.return_size)

        json_dict["path"] = [str(v) for v in self.path]
        json_dict["path_label"] = self.path_label
        json_dict["storage"] = {str(k): str(v) for k, v in self.storages.items()}
        json_dict["t_storage"] = {str(k): str(v) for k, v in self.t_storages.items()}
        json_dict["balance"] = {str(k): str(v) for k, v in self.balances.items()}
        return json_dict
        
        
       




class StackError(Exception):
    def __init__(self, message):
        self.message = message
        super().__init__(self.message)


class DivError(Exception):
    def __init__(self, message):
        self.message = message
        super().__init__(self.message)

class IndexError(Exception):
    def __init__(self, message):
        self.message = message
        super().__init__(self.message)

class CodeError(Exception):
    def __init__(self, message):
        self.message = message
        super().__init__(self.message)

class ReturnDataError(Exception):
    def __init__(self, message):
        self.message = message
        super().__init__(self.message)

class MemoryError(Exception):
    def __init__(self, message):
        self.message = message
        super().__init__(self.message)

class OperandError(Exception):
    def __init__(self, message):
        self.message = message
        super().__init__(self.message)

class NotSupportedError(Exception):
    def __init__(self, message):
        self.message = message
        super().__init__(self.message)



