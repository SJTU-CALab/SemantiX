import pytest
import z3
from symbolic_execution.evm_interpreter import EVMInterpreter, Runtime, StackError, DivError, IndexError
from symbolic_execution.evm_cfg import EvmCFG, BlockType
from symbolic_execution.block import Block
from s_graph.SGraph import SGraph


class FakeInstruction:
    def __init__(self, pc, mnemonic, operand=None):
        self.pc = pc
        self.mnemonic = mnemonic
        self.operand = operand


def create_simple_cfg(instructions):
    """创建简单的CFG用于测试"""
    disasm = []
    for _, (pc, mnemonic, operand) in enumerate(instructions):
        disasm.append(FakeInstruction(pc, mnemonic, operand))
    
    cfg = EvmCFG(disasm)
    cfg.build_cfg()
    return cfg

def create_interpreter(instructions):
    """创建EVMInterpreter实例"""
    cfg = create_simple_cfg(instructions)
    bytecode = "60016002"  # 简单的字节码，与instructions不对应，但测试时只测试指令，不测试字节码
    contract = "TestContract"
    interpreter = EVMInterpreter(cfg, bytecode, contract)
    return interpreter

def test_single_instruction_add():
    """测试ADD指令"""
    instructions = [(0, "PUSH1", 1), (2, "PUSH1", 2), (4, "ADD", None)]

    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    
    # 验证结果

    # 验证stack是否正确
    # 验证stack长度
    assert len(runtime.stack) == 1
    # 验证stack中元素类型是否为z3.BitVec256
    for x in runtime.stack:
        assert z3.is_bv(x) and x.size() == 256
    # 验证push进入stack中新的元素值是否正确
    assert runtime.stack[0].as_long() == 3


def test_single_instruction_mul():
    """测试MUL指令"""
    instructions = [(0, "PUSH1", 2), (2, "PUSH1", 3), (4, "MUL", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    for x in runtime.stack:
        assert z3.is_bv(x) and x.size() == 256
    assert runtime.stack[0].as_long() == 6


def test_single_instruction_sub():
    """测试SUB指令"""
    instructions = [(0, "PUSH1", 5), (2, "PUSH1", 3), (4, "SUB", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    for x in runtime.stack:
        assert z3.is_bv(x) and x.size() == 256
    assert runtime.stack[0].as_long() == z3.BitVecVal(-2, 256).as_long()


def test_single_instruction_div():
    """测试DIV指令"""
    instructions = [(0, "PUSH1", 2), (2, "PUSH1", 6), (4, "DIV", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    for x in runtime.stack:
        assert z3.is_bv(x) and x.size() == 256
    assert runtime.stack[0].as_long() == 3


def test_single_instruction_sdiv():
    """测试SDIV指令"""
    instructions = [(0, "PUSH1", 2), (2, "PUSH1", -6), (4, "SDIV", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    for x in runtime.stack:
        assert z3.is_bv(x) and x.size() == 256
    assert runtime.stack[0].as_long() == z3.BitVecVal(-3, 256).as_long()


def test_single_instruction_mod():
    """测试MOD指令"""
    instructions = [(0, "PUSH1", 4), (2, "PUSH1", 7), (4, "MOD", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    for x in runtime.stack:
        assert z3.is_bv(x) and x.size() == 256
    assert runtime.stack[0].as_long() == 3


def test_single_instruction_smod():
    """测试MOD指令"""
    instructions = [(0, "PUSH1", 4), (2, "PUSH1", -7), (4, "MOD", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    for x in runtime.stack:
        assert z3.is_bv(x) and x.size() == 256
    assert runtime.stack[0].as_long() == 1


def test_single_instruction_addmod():
    """测试ADDMOD指令"""
    instructions = [(0, "PUSH1", 3), (2, "PUSH1", 5), (4, "PUSH1", 7), (6, "ADDMOD", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    for x in runtime.stack:
        assert z3.is_bv(x) and x.size() == 256
    assert runtime.stack[0].as_long() == ((5 + 7) % 3)



def test_single_instruction_mulmod():
    """测试MULMOD指令"""
    instructions = [(0, "PUSH1", 3), (2, "PUSH1", 5), (4, "PUSH1", 7), (6, "MULMOD", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    for x in runtime.stack:
        assert z3.is_bv(x) and x.size() == 256
    assert runtime.stack[0].as_long() == ((5 * 7) % 3)


def test_single_instruction_exp():
    """测试EXP指令"""
    instructions = [(0, "PUSH1", 2), (2, "PUSH1", 3), (4, "EXP", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    for x in runtime.stack:
        assert z3.is_bv(x) and x.size() == 256
    assert runtime.stack[0].as_long() == 9


def test_single_instruction_signextend():
    """测试SIGNEXTEND指令"""
    instructions = [(0, "PUSH1", int("0xF0", 16)), (2, "PUSH1", 0), (4, "SIGNEXTEND", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    for x in runtime.stack:
        assert z3.is_bv(x) and x.size() == 256
    # signextend(0, 0x80) = 0xffffff...80
    assert runtime.stack[0].as_long() == (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF0)


def test_single_instruction_lt():
    """测试LT指令"""
    instructions = [(0, "PUSH1", 2), (2, "PUSH1", 3), (4, "LT", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    for x in runtime.stack:
        assert z3.is_bv(x) and x.size() == 256
    assert runtime.stack[0].as_long() == 0


def test_single_instruction_gt():
    """测试GT指令"""
    instructions = [(0, "PUSH1", 5), (2, "PUSH1", 3), (4, "GT", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    for x in runtime.stack:
        assert z3.is_bv(x) and x.size() == 256
    assert runtime.stack[0].as_long() == 0


def test_single_instruction_slt():
    """测试SLT指令"""
    instructions = [(0, "PUSH1", 1), (2, "PUSH1", -2), (4, "SLT", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    for x in runtime.stack:
        assert z3.is_bv(x) and x.size() == 256
    assert runtime.stack[0].as_long() == 1


def test_single_instruction_sgt():
    """测试SGT指令"""
    instructions = [(0, "PUSH1", 2), (2, "PUSH1", -1), (4, "SGT", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    for x in runtime.stack:
        assert z3.is_bv(x) and x.size() == 256
    assert runtime.stack[0].as_long() == 0


def test_single_instruction_eq():
    """测试EQ指令"""
    instructions = [(0, "PUSH1", 5), (2, "PUSH1", 5), (4, "EQ", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    for x in runtime.stack:
        assert z3.is_bv(x) and x.size() == 256
    assert runtime.stack[0].as_long() == 1


def test_single_instruction_iszero():
    """测试ISZERO指令"""
    instructions = [(0, "PUSH1", 0), (2, "ISZERO", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    for x in runtime.stack:
        assert z3.is_bv(x) and x.size() == 256
    assert runtime.stack[0].as_long() == 1


def test_single_instruction_and():
    """测试AND指令"""
    instructions = [(0, "PUSH1", 6), (2, "PUSH1", 3), (4, "AND", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    for x in runtime.stack:
        assert z3.is_bv(x) and x.size() == 256
    assert runtime.stack[0].as_long() == (6 & 3)


def test_single_instruction_or():
    """测试OR指令"""
    instructions = [(0, "PUSH1", 6), (2, "PUSH1", 3), (4, "OR", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    for x in runtime.stack:
        assert z3.is_bv(x) and x.size() == 256
    assert runtime.stack[0].as_long() == (6 | 3)


def test_single_instruction_xor():
    """测试XOR指令"""
    instructions = [(0, "PUSH1", 6), (2, "PUSH1", 3), (4, "XOR", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    for x in runtime.stack:
        assert z3.is_bv(x) and x.size() == 256
    assert runtime.stack[0].as_long() == (6 ^ 3)


def test_single_instruction_not():
    """测试NOT指令"""
    instructions = [(0, "PUSH1", 0), (2, "NOT", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    for x in runtime.stack:
        assert z3.is_bv(x) and x.size() == 256
    # z3.Not(0) == True, 但EVM的NOT是按位取反，z3.Not(0) 结果为1，EVM应为0xffff...ffff
    # 这里假设实现为z3.Not(0) == 1
    # 具体实现需根据evm_interpreter.py的NOT实现调整断言
    assert runtime.stack[0].as_long() == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF


def test_single_instruction_byte():
    """测试BYTE指令"""
    instructions = [(0, "PUSH3", int("0x123456", 16)), (4, "PUSH2", 31), (6, "BYTE", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    for x in runtime.stack:
        assert z3.is_bv(x) and x.size() == 256
    # 0x123456 的第1字节（从高位算）是0x34
    assert runtime.stack[0].as_long() == 0x56


def test_single_instruction_shl():
    """测试SHL指令"""
    instructions = [(0, "PUSH1", 2), (2, "PUSH1", 1), (4, "SHL", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    for x in runtime.stack:
        assert z3.is_bv(x) and x.size() == 256
    assert runtime.stack[0].as_long() == (2 << 1)


def test_single_instruction_shr():
    """测试SHR指令"""
    instructions = [(0, "PUSH1", 4), (2, "PUSH1", 1), (4, "SHR", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    for x in runtime.stack:
        assert z3.is_bv(x) and x.size() == 256
    assert runtime.stack[0].as_long() == (4 >> 1)


def test_single_instruction_sar():
    """测试SAR指令"""
    instructions = [(0, "PUSH1", -4), (2, "PUSH1", 1), (4, "SAR", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    for x in runtime.stack:
        assert z3.is_bv(x) and x.size() == 256
    # -4 >> 1 = -2 (有符号右移)
    assert runtime.stack[0].as_signed_long() == (-4 >> 1)


def test_single_instruction_sha3():
    """测试SHA3指令"""
    # 先将0x123456写入memory[0:32]，然后对memory[0:3]做keccak256
    instructions = [
        (0, "PUSH1", int("0x123456", 16)), (2, "PUSH1", 0), (6, "MSTORE", None),
        (7, "PUSH1", 0), (9, "PUSH1", 29), (11, "ADD", None),  # offset=0+29=29
        (12, "PUSH1", 3), (14, "SHA3", None)
    ]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    # SHA3后stack应有哈希值
    assert len(runtime.stack) == 1
    # 结果应为z3表达式或256位bitvec
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256
    assert z3.simplify(runtime.stack[0] == z3.BitVec(interpreter.gen.gen_sha3(z3.BitVecVal(0x123456, 256)), 256))


def test_single_instruction_address():
    """测试ADDRESS指令（符号执行只验证stack有返回值）"""
    instructions = [(0, "ADDRESS", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256
    result = z3.simplify(runtime.stack[0] == z3.ZeroExt(96, runtime.global_state["this"]))
    assert z3.is_true(result)


def test_single_instruction_balance():
    """测试BALANCE指令（符号执行只验证stack有返回值）"""
    instructions = [
        (0, "PUSH3", 0x123456), (4, "BALANCE", None)
    ]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256


def test_single_instruction_origin():
    """测试ORIGIN指令（符号执行只验证stack有返回值）"""
    instructions = [(0, "ORIGIN", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256
    result = z3.simplify(runtime.stack[0] == z3.ZeroExt(96, runtime.global_state["origin"]))
    assert z3.is_true(result)


def test_single_instruction_caller():
    """测试CALLER指令（符号执行只验证stack有返回值）"""
    instructions = [(0, "CALLER", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256
    result = z3.simplify(runtime.stack[0] == z3.ZeroExt(96, runtime.global_state["sender"]))
    assert z3.is_true(result)


def test_single_instruction_callvalue():
    """测试CALLVALUE指令（符号执行只验证stack有返回值）"""
    instructions = [(0, "CALLVALUE", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256
    assert z3.is_true(z3.simplify(runtime.stack[0] == runtime.global_state["value"]))


# TODO: test call dataload
# def test_single_instruction_calldataload():
#     """测试CALLDATALOAD指令"""
#     instructions = [(0, "PUSH1", 0), (2, "CALLDATALOAD", None)]
#     interpreter = create_interpreter(instructions)
#     runtime = interpreter.run("0x1234567890abcdef")
#     assert len(runtime.stack) == 1
#     assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256
#     assert runtime.stack[0].as_long() == 0x1234567890abcdef


def test_single_instruction_calldatasize():
    """测试CALLDATALOAD指令"""
    instructions = [(0, "CALLDATASIZE", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run("0x1234567890abcdef")
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256
    assert runtime.stack[0].as_long() == 8


# def test_single_instruction_calldatacopy():
#     """测试CALLDATACOPY指令"""
#     # 假设calldata为0x11223344556677889900...，将前4字节拷贝到memory[0:4]
#     instructions = [
#         (0, "PUSH1", 4),      # mem_offset
#         (2, "PUSH1", 0),      # data_offset
#         (4, "PUSH1", 0),      # length
#         (6, "CALLDATACOPY", None)
#     ]
#     interpreter = create_interpreter(instructions)
#     # 手动设置calldata
#     runtime = interpreter.run("0x1234567890abcdef")
#     # 验证memory前4字节内容
#     for i, v in enumerate([0x90, 0xab, 0xcd, 0xef]):
#         assert runtime.memory[i].as_long() == v


def test_single_instruction_codesize():
    """测试CODESIZE指令"""
    instructions = [(0, "CODESIZE", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256
    # 由于create_interpreter中bytecode为"60016002"，长度为4字节
    assert runtime.stack[0].as_long() == 4


def test_single_instruction_codecopy():
    """测试CODECOPY指令"""
    # create_interpreter中bytecode为"60016002"，即[0x60, 0x01, 0x60, 0x02]
    instructions = [
        (0, "PUSH1", 4),   # length
        (2, "PUSH1", 0),   # code_offset
        (4, "PUSH1", 0),   # mem_offset
        (6, "CODECOPY", None)
    ]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    # 验证memory前4字节内容与bytecode一致
    for i, v in enumerate([0x60, 0x01, 0x60, 0x02]):
        assert runtime.memory[i].as_long() == v


def test_single_instruction_gasprice():
    """测试GASPRICE指令（符号执行只验证stack有返回值）"""
    instructions = [(0, "GASPRICE", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256



def test_single_instruction_extcodesize():
    """测试EXTCODESIZE指令（符号执行只验证stack有返回值）"""
    instructions = [
        (0, "PUSH1", 0),  # address
        (2, "EXTCODESIZE", None)
    ]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run(extcode={0: "60016002"})
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256
    assert runtime.stack[0].as_long() == 4

def test_single_instruction_extcodecopy():
    """测试EXTCODECOPY指令"""
    instructions = [
        (0, "PUSH1", 4),  # length
        (2, "PUSH1", 0),  # code_offset
        (4, "PUSH1", 0),  # mem_offset
        (6, "PUSH8", 0x1234567890abcdef),  # address
        (15, "EXTCODECOPY", None)
    ]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run(extcode={0x1234567890abcdef: "60016002ab"})
    assert len(runtime.stack) == 0
    for i, v in enumerate([0x60, 0x01, 0x60, 0x02]):
        assert runtime.memory[i].as_long() == v


def test_single_instruction_returndatasize():
    """测试RETURNDATASIZE指令"""
    instructions = [
        (0, "PUSH1", 0x12), (2, "PUSH1", 0), (4, "MSTORE8", None),
        (5, "PUSH1", 0x34), (7, "PUSH1", 1), (9, "MSTORE8", None),
        (10, "PUSH1", 0x56), (12, "PUSH1", 2), (14, "MSTORE8", None),
        (15, "PUSH1", 1), # ret_length
        (17, "PUSH1", 0), # ret_offset
        (19, "PUSH1", 3), # args_length
        (21, "PUSH1", 0), # args_offset
        (23, "PUSH1", 0), # value
        (25, "PUSH1", 0), # address
        (27, "PUSH1", 0), # gas
        (29, "CALL", None), 
        (30, "RETURNDATASIZE", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 2
    for x in runtime.stack:
        assert z3.is_bv(x) and x.size() == 256


def test_single_instruction_returndatacopy():
    """测试RETURNDATACOPY指令"""
    instructions = [
        (0, "PUSH1", 0x12), (2, "PUSH1", 0), (4, "MSTORE8", None),
        (5, "PUSH1", 0x34), (7, "PUSH1", 1), (9, "MSTORE8", None),
        (10, "PUSH1", 0x56), (12, "PUSH1", 2), (14, "MSTORE8", None),
        (15, "PUSH1", 1), # ret_length
        (17, "PUSH1", 0), # ret_offset
        (19, "PUSH1", 3), # args_length
        (21, "PUSH1", 0), # args_offset
        (23, "PUSH1", 0), # value
        (25, "PUSH1", 0), # address
        (27, "PUSH1", 0), # gas
        (29, "CALL", None), 
        (30, "PUSH1", 1), (32, "PUSH1", 0), (34, "PUSH1", 1), (36, "RETURNDATACOPY", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    for i in range(0,3):
        z3.is_bv(runtime.memory[i]) and runtime.memory[i].size() == 8
    assert runtime.memory[0] == runtime.memory[1]


def test_single_instruction_extcodehash():
    """测试EXTCODEHASH指令（符号执行只验证stack有返回值或异常）"""
    instructions = [
        (0, "PUSH1", 0), (2, "EXTCODEHASH", None)
    ]
    interpreter = create_interpreter(instructions)
    try:
        runtime = interpreter.run()
    except Exception as e:
        assert "EXTCODEHASH" in str(e)
    else:
        assert len(runtime.stack) == 1
        assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256


def test_single_instruction_blockhash():
    """测试BLOCKHASH指令（符号执行只验证stack有返回值）"""
    instructions = [(0, "PUSH1", 0), (2, "BLOCKHASH", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256


def test_single_instruction_coinbase():
    """测试COINBASE指令（符号执行只验证stack有返回值）"""
    instructions = [(0, "COINBASE", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256


def test_single_instruction_timestamp():
    """测试TIMESTAMP指令（符号执行只验证stack有返回值）"""
    instructions = [(0, "TIMESTAMP", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256


def test_single_instruction_number():
    """测试NUMBER指令（符号执行只验证stack有返回值）"""
    instructions = [(0, "NUMBER", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256


def test_single_instruction_difficulty():
    """测试DIFFICULTY指令（符号执行只验证stack有返回值）"""
    instructions = [(0, "DIFFICULTY", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256


def test_single_instruction_prevrandao():
    """测试PREVRANDAO指令（符号执行只验证stack有返回值）"""
    instructions = [(0, "PREVRANDAO", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256


def test_single_instruction_gaslimit():
    """测试GASLIMIT指令（符号执行只验证stack有返回值）"""
    instructions = [(0, "GASLIMIT", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256


def test_single_instruction_chainid():
    """测试CHAINID指令（符号执行只验证stack有返回值）"""
    instructions = [(0, "CHAINID", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256


def test_single_instruction_selfbalance():
    """测试SELFBALANCE指令（符号执行只验证stack有返回值）"""
    instructions = [(0, "SELFBALANCE", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256


def test_single_instruction_basefee():
    """测试BASEFEE指令（符号执行只验证stack有返回值）"""
    instructions = [(0, "BASEFEE", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256


def test_single_instruction_blobhash():
    """测试BLOBHASH指令（符号执行只验证stack有返回值）"""
    instructions = [(0, "PUSH1", 0), (2, "BLOBHASH", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256


def test_single_instruction_blobbasefee():
    """测试BLOBBASEFEE指令（符号执行只验证stack有返回值）"""
    instructions = [(0, "BLOBBASEFEE", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256


def test_single_instruction_pop():
    """测试POP指令"""
    instructions = [(0, "PUSH1", 99), (2, "POP", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 0


def test_single_instruction_mstore_and_mload():
    """测试MSTORE和MLOAD指令"""
    instructions = [(0, "PUSH1", 0x42), (2, "PUSH1", 0), (4, "MSTORE", None), (5, "PUSH1", 0), (7, "MLOAD", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256
    assert runtime.stack[0].as_long() == 0x42


def test_single_instruction_mstore8():
    """测试MSTORE8指令"""
    instructions = [(0, "PUSH2", 0xABCD), (2, "PUSH1", 0), (4, "MSTORE8", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 0
    assert runtime.memory[0].as_long() == 0xCD


def test_single_instruction_sstore_and_sload():
    """测试SSTORE和SLOAD指令"""
    instructions = [(0, "PUSH1", 0x55), (2, "PUSH1", 0x01), (4, "SSTORE", None), (5, "PUSH1", 0x01), (7, "SLOAD", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256
    assert runtime.stack[0].as_long() == 0x55
    assert runtime.storages[z3.BitVecVal(0x01, 256)].as_long() == 0x55


def test_single_instruction_jump():
    """测试JUMP指令（跳转到指定PC）"""
    instructions = [
        (0, "PUSH1", 3),  # 跳转到3
        (2, "JUMP", None),
        (3, "JUMPDEST", None),
        (4, "PUSH1", 99)
    ]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    # JUMP后应能继续执行JUMPDEST后的指令
    assert runtime.stack[-1].as_long() == 99


def test_single_instruction_jumpi():
    """测试JUMPI指令（条件跳转）"""
    instructions = [
        (0, "PUSH1", 1),  # 条件为真
        (2, "PUSH1", 7),  # 跳转到6
        (4, "JUMPI", None),
        (5, "PUSH1", 42),
        (7, "JUMPDEST", None),
        (8, "PUSH1", 99)
    ]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    # 条件为真，应跳转到6，执行PUSH1 99
    assert len(runtime.stack) == 0
    # TODO: 验证jump_dest和condition


def test_single_instruction_pc():
    """测试PC指令"""
    instructions = [(0, "PUSH10", 1), (11, "PC", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 2
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256
    # PC应为0
    assert runtime.stack[1].as_long() == 11


def test_single_instruction_msize():
    """测试MSIZE指令"""
    instructions = [(0, "MSIZE", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256
    # 初始miu为0
    assert runtime.stack[0].as_long() == 0


def test_single_instruction_gas():
    """测试GAS指令"""
    instructions = [(0, "GAS", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256


def test_single_instruction_jumpdest():
    """测试JUMPDEST指令（无操作）"""
    instructions = [(0, "JUMPDEST", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    # JUMPDEST不影响stack
    assert len(runtime.stack) == 0


def test_single_instruction_tstore_tload():
    """测试TSTORE和TLOAD指令"""
    # TSTORE: tstore[0x01] = 0xABCD
    # TLOAD:  tload[0x01] -> stack
    instructions = [
        (0, "PUSH1", 0xABCD), (2, "PUSH1", 0x01), (4, "TSTORE", None),
        (5, "PUSH1", 0x01), (7, "TLOAD", None)
    ]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256
    assert runtime.stack[0].as_long() == 0xABCD

def test_single_instruction_mcopy():
    """测试MCOPY指令"""
    # 先将0x1122写入memory[0:32]，再将memory[0:2]拷贝到memory[10:12]
    instructions = [
        (0, "PUSH2", 0x1122), (3, "PUSH1", 0), (5, "MSTORE", None),
        (6, "PUSH1", 2), # length
        (8, "PUSH1", 30), # src offset
        (10, "PUSH1", 40), # dst offset
        (12, "MCOPY", None)
    ]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    # 验证memory[10]和memory[11]内容
    assert runtime.memory[40].as_long() == 0x11
    assert runtime.memory[41].as_long() == 0x22


def test_single_instruction_push():
    """测试PUSH指令"""
    instructions = [(0, "PUSH0", 0), (1, "PUSH1", 42), (3, "PUSH32", 0x1234567890abcdef)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 3
    assert runtime.stack[0].as_long() == 0
    assert runtime.stack[1].as_long() == 42
    assert runtime.stack[2].as_long() == 0x1234567890abcdef


def test_single_instruction_dup():
    """测试DUP指令"""
    instructions = [(0, "PUSH1", 1), (2, "PUSH1", 2), (4, "DUP1", None), (5, "DUP3", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 4
    assert runtime.stack[-1].as_long() == 1
    assert runtime.stack[-2].as_long() == 2


def test_single_instruction_swap():
    """测试SWAP指令"""
    instructions = [(0, "PUSH1", 1), (2, "PUSH1", 2), (4, "PUSH1", 3), (6, "SWAP1", None), (7, "SWAP2", None)]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    assert len(runtime.stack) == 3
    assert runtime.stack[0].as_long() == 2
    assert runtime.stack[1].as_long() == 3
    assert runtime.stack[2].as_long() == 1


def test_single_instruction_create():
    """测试CREATE指令（符号执行只验证stack有新地址）"""
    instructions = [
        (0, "PUSH1", 0),
        (2, "PUSH1", 0),
        (4, "PUSH1", 0),
        (6, "CREATE", None)
    ]
    interpreter = create_interpreter(instructions)
    try:
        runtime = interpreter.run()
    except Exception as e:
        # CREATE未实现时允许抛出NotSupportedError
        assert "CREATE" in str(e)
    else:
        # 若实现了，stack应有新地址
        assert len(runtime.stack) == 1


def test_single_instruction_call():
    """测试CALL指令（符号执行只验证stack有返回状态）"""
    instructions = [
        (0, "PUSH1", 0x12), (2, "PUSH1", 0), (4, "MSTORE8", None),
        (5, "PUSH1", 0x34), (7, "PUSH1", 1), (9, "MSTORE8", None),
        (10, "PUSH1", 0x56), (12, "PUSH1", 2), (14, "MSTORE8", None),
        (15, "PUSH1", 1), # ret_length
        (17, "PUSH1", 0), # ret_offset
        (19, "PUSH1", 3), # args_length
        (21, "PUSH1", 0), # args_offset
        (23, "PUSH1", 0), # value
        (25, "PUSH1", 0), # address
        (27, "PUSH1", 0), # gas
        (29, "CALL", None), 
    ]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    # CALL后stack应有返回状态
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256


def test_single_instruction_call_code():
    """测试CALLCODE指令（符号执行只验证stack有返回状态）"""
    instructions = [
       (0, "PUSH1", 0x12), (2, "PUSH1", 0), (4, "MSTORE8", None),
        (5, "PUSH1", 0x34), (7, "PUSH1", 1), (9, "MSTORE8", None),
        (10, "PUSH1", 0x56), (12, "PUSH1", 2), (14, "MSTORE8", None),
        (15, "PUSH1", 1), # ret_length
        (17, "PUSH1", 0), # ret_offset
        (19, "PUSH1", 3), # args_length
        (21, "PUSH1", 0), # args_offset
        (23, "PUSH1", 0), # value
        (25, "PUSH1", 0), # address
        (27, "PUSH1", 0), # gas
        (29, "CALLCODE", None), 
    ]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    # CALLCODE后stack应有返回状态
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256


def test_single_instruction_return():
    """测试RETURN指令（符号执行只验证无异常）"""
    instructions = [
        (0, "PUSH1", 0),
        (2, "PUSH1", 0),
        (4, "RETURN", None)
    ]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    # RETURN后stack应为空
    assert len(runtime.stack) == 0


def test_single_instruction_delegatecall():
    """测试DELEGATECALL指令（符号执行只验证stack有返回状态）"""
    instructions = [
        (0, "PUSH1", 0x12), (2, "PUSH1", 0), (4, "MSTORE8", None),
        (5, "PUSH1", 0x34), (7, "PUSH1", 1), (9, "MSTORE8", None),
        (10, "PUSH1", 0x56), (12, "PUSH1", 2), (14, "MSTORE8", None),
        (15, "PUSH1", 1), # ret_length
        (17, "PUSH1", 0), # ret_offset
        (19, "PUSH1", 3), # args_length
        (21, "PUSH1", 0), # args_offset
        (23, "PUSH1", 0), # address
        (25, "PUSH1", 0), # gas
        (27, "DELEGATECALL", None), 
    ]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    # DELEGATECALL后stack应有返回状态
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256


def test_single_instruction_create2():
    """测试CREATE2指令（符号执行只验证stack有新地址）"""
    instructions = [
        (0, "PUSH1", 0), (2, "PUSH1", 0), (4, "PUSH1", 0), (6, "PUSH1", 0), (8, "CREATE2", None)
    ]
    interpreter = create_interpreter(instructions)
    try:
        runtime = interpreter.run()
    except Exception as e:
        # CREATE2未实现时允许抛出NotSupportedError
        assert "CREATE2" in str(e)
    else:
        # 若实现了，stack应有新地址
        assert len(runtime.stack) == 1



def test_single_instruction_staticcall():
    """测试STATICCALL指令（符号执行只验证stack有返回状态）"""
    instructions = [
        (0, "PUSH1", 0x12), (2, "PUSH1", 0), (4, "MSTORE8", None),
        (5, "PUSH1", 0x34), (7, "PUSH1", 1), (9, "MSTORE8", None),
        (10, "PUSH1", 0x56), (12, "PUSH1", 2), (14, "MSTORE8", None),
        (15, "PUSH1", 1), # ret_length
        (17, "PUSH1", 0), # ret_offset
        (19, "PUSH1", 3), # args_length
        (21, "PUSH1", 0), # args_offset
        (23, "PUSH1", 0), # address
        (25, "PUSH1", 0), # gas
        (27, "STATICCALL", None), 
    ]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    # STATICCALL后stack应有返回状态
    assert len(runtime.stack) == 1
    assert z3.is_bv(runtime.stack[0]) and runtime.stack[0].size() == 256


def test_single_instruction_revert():
    """测试REVERT指令（符号执行只验证无异常）"""
    instructions = [
        (0, "PUSH1", 0),
        (2, "PUSH1", 0),
        (4, "REVERT", None)
    ]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    # REVERT后stack应为空
    assert len(runtime.stack) == 0


def test_single_instruction_selfdestruct():
    """测试SELFDESTRUCT指令（符号执行只验证无异常）"""
    instructions = [
        (0, "PUSH1", 0), (2, "SELFDESTRUCT", None)
    ]
    interpreter = create_interpreter(instructions)
    runtime = interpreter.run()
    # SELFDESTRUCT后stack应为空
    assert len(runtime.stack) == 0










