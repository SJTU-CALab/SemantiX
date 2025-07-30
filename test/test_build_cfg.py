import pytest
from symbolic_execution.evm_cfg import EvmCFG, BlockType


class FakeInstruction:
    def __init__(self, pc, mnemonic, operand=None):
        self.pc = pc
        self.mnemonic = mnemonic
        self.operand = operand

def test_build_cfg_simple():
    # 构造伪disasm输入
    disasm = [
        FakeInstruction(0, "PUSH1", 96),
        FakeInstruction(2, "PUSH1", 64),
        FakeInstruction(4, "MSTORE"),
        FakeInstruction(5, "JUMPDEST"),
        FakeInstruction(6, "STOP"),
    ]
    cfg = EvmCFG(disasm)
    cfg.build_cfg()

    # 检查block分割
    assert set(cfg.vertices.keys()) == {0, 5}
    # 检查block类型
    assert cfg.vertices[0].get_block_type() == BlockType.FALLS_JUMPDEST
    assert cfg.vertices[5].get_block_type() == BlockType.TERMINAL
    # 检查edges
    assert cfg.edges[0] == [5]
    assert cfg.edges[5] == []

    # 检查指令内容
    assert cfg.vertices[0].instructions == [
        "PUSH1 96",
        "PUSH1 64",
        "MSTORE"
    ]
    assert cfg.vertices[5].instructions == [
        "JUMPDEST",
        "STOP"
    ]

def test_terminal_block():
    disasm = [FakeInstruction(0, "STOP")]
    cfg = EvmCFG(disasm)
    cfg.build_cfg()
    assert set(cfg.vertices.keys()) == {0}
    assert cfg.vertices[0].get_block_type() == BlockType.TERMINAL
    assert cfg.edges[0] == []

def test_sequential_to_stop():
    disasm = [
        FakeInstruction(0, "PUSH1", 1),
        FakeInstruction(2, "PUSH1", 2),
        FakeInstruction(4, "STOP"),
    ]
    cfg = EvmCFG(disasm)
    cfg.build_cfg()
    assert set(cfg.vertices.keys()) == {0}
    assert cfg.vertices[0].get_block_type() == BlockType.TERMINAL
    assert cfg.edges[0] == []

def test_two_jumpdest_split():
    disasm = [
        FakeInstruction(0, "PUSH1", 1),
        FakeInstruction(2, "JUMPDEST"),
        FakeInstruction(3, "JUMPDEST"),
        FakeInstruction(4, "STOP"),
    ]
    cfg = EvmCFG(disasm)
    cfg.build_cfg()
    assert set(cfg.vertices.keys()) == {0, 2, 3}
    assert cfg.vertices[0].get_block_type() == BlockType.FALLS_JUMPDEST
    assert cfg.vertices[2].get_block_type() == BlockType.FALLS_JUMPDEST
    assert cfg.vertices[3].get_block_type() == BlockType.TERMINAL
    assert cfg.edges[0] == [2]
    assert cfg.edges[2] == [3]
    assert cfg.edges[3] == []

def test_unconditional_jump():
    disasm = [
        FakeInstruction(0, "PUSH1", 5),
        FakeInstruction(2, "JUMP"),
        FakeInstruction(3, "PUSH1", 5),
        FakeInstruction(5, "JUMPDEST"),
        FakeInstruction(6, "STOP"),
    ]
    cfg = EvmCFG(disasm)
    cfg.build_cfg()
    assert set(cfg.vertices.keys()) == {0, 3, 5}
    assert cfg.vertices[0].get_block_type() == BlockType.UNCONDITIONAL
    assert cfg.vertices[3].get_block_type() == BlockType.FALLS_JUMPDEST
    assert cfg.vertices[5].get_block_type() == BlockType.TERMINAL
    assert cfg.edges[0] == [5]
    assert cfg.edges[3] == [5]
    assert cfg.edges[5] == []

def test_conditional_jumpi():
    disasm = [
        FakeInstruction(0, "PUSH1", 5),
        FakeInstruction(2, "JUMPI"),
        FakeInstruction(3, "JUMPDEST"),
        FakeInstruction(4, "STOP"),
        FakeInstruction(5, "JUMPDEST"),
        FakeInstruction(6, "RETURN"),
    ]
    cfg = EvmCFG(disasm)
    cfg.build_cfg()
    assert set(cfg.vertices.keys()) == {0, 3, 5}
    assert cfg.vertices[0].get_block_type() == BlockType.CONDITIONAL
    assert cfg.vertices[3].get_block_type() == BlockType.TERMINAL
    assert cfg.vertices[5].get_block_type() == BlockType.TERMINAL
    assert cfg.edges[0] == [3,5]
    assert cfg.edges[3] == []
    assert cfg.edges[5] == []
    

def test_return_terminal():
    disasm = [
        FakeInstruction(0, "PUSH1", 0),
        FakeInstruction(2, "RETURN"),
    ]
    cfg = EvmCFG(disasm)
    cfg.build_cfg()
    assert set(cfg.vertices.keys()) == {0}
    assert cfg.vertices[0].get_block_type() == BlockType.TERMINAL
    assert cfg.edges[0] == []

def test_multiple_jumpdest():
    disasm = [
        FakeInstruction(0, "JUMPDEST"),
        FakeInstruction(1, "PUSH1", 1),
        FakeInstruction(3, "JUMPDEST"),
        FakeInstruction(4, "STOP"),
    ]
    cfg = EvmCFG(disasm)
    cfg.build_cfg()
    assert set(cfg.vertices.keys()) == {0, 3}
    assert cfg.vertices[0].get_block_type() == BlockType.FALLS_JUMPDEST
    assert cfg.vertices[3].get_block_type() == BlockType.TERMINAL
    assert cfg.edges[0] == [3]
    assert cfg.edges[3] == []

def test_suicide_terminal():
    disasm = [
        FakeInstruction(0, "PUSH1", 0),
        FakeInstruction(2, "SUICIDE"),
    ]
    cfg = EvmCFG(disasm)
    cfg.build_cfg()
    assert set(cfg.vertices.keys()) == {0}
    assert cfg.vertices[0].get_block_type() == BlockType.TERMINAL
    assert cfg.edges[0] == []

def test_revert_terminal():
    disasm = [
        FakeInstruction(0, "PUSH1", 0),
        FakeInstruction(2, "REVERT"),
    ]
    cfg = EvmCFG(disasm)
    cfg.build_cfg()
    assert set(cfg.vertices.keys()) == {0}
    assert cfg.vertices[0].get_block_type() == BlockType.TERMINAL
    assert cfg.edges[0] == []
   
def test_multiple_terminal_ops():
    disasm = [
        FakeInstruction(0, "STOP"),
        FakeInstruction(1, "RETURN"),
        FakeInstruction(2, "REVERT"),
    ]
    cfg = EvmCFG(disasm)
    cfg.build_cfg()
    assert set(cfg.vertices.keys()) == {0, 1, 2}
    assert all(cfg.vertices[i].get_block_type() == BlockType.TERMINAL for i in [0, 1, 2])
    assert all(cfg.edges[i] == [] for i in [0, 1, 2])

def test_jump_to_non_jumpdest():
    disasm = [
        FakeInstruction(0, "PUSH1", 2),
        FakeInstruction(2, "JUMP"),
        FakeInstruction(3, "STOP"),
    ]
    cfg = EvmCFG(disasm)
    cfg.build_cfg()
    assert 0 in cfg.vertices
    assert 2 not in cfg.vertices

def test_jumpdest_at_start_and_end():
    disasm = [
        FakeInstruction(0, "JUMPDEST"),
        FakeInstruction(1, "PUSH1", 1),
        FakeInstruction(2, "STOP"),
        FakeInstruction(3, "JUMPDEST"),
    ]
    cfg = EvmCFG(disasm)
    cfg.build_cfg()
    assert 0 in cfg.vertices
    assert 3 in cfg.vertices
    assert cfg.vertices[0].get_block_type() == BlockType.TERMINAL
    assert cfg.vertices[3].get_block_type() == BlockType.TERMINAL

def test_unknown_opcode():
    disasm = [
        FakeInstruction(0, "PUSH1", 1),
        FakeInstruction(1, "FOOOP"),  # 假设FOOOP是未知操作码
        FakeInstruction(2, "STOP"),
    ]
    cfg = EvmCFG(disasm)
    cfg.build_cfg()
    assert 0 in cfg.vertices
    assert cfg.vertices[0].instructions[1].startswith("FOOOP")

def test_no_terminal_op():
    disasm = [
        FakeInstruction(0, "PUSH1", 1),
        FakeInstruction(1, "PUSH1", 2),
    ]
    cfg = EvmCFG(disasm)
    cfg.build_cfg()
    assert set(cfg.vertices.keys()) == {0}
    assert cfg.vertices[0].get_end_address() == 1
    assert cfg.vertices[0].get_block_type() == BlockType.TERMINAL

def test_jumpi_no_fallthrough():
    disasm = [
        FakeInstruction(0, "JUMPI"),
    ]
    cfg = EvmCFG(disasm)
    cfg.build_cfg()
    assert 0 in cfg.vertices
    assert cfg.vertices[0].get_end_address() == 0
    assert cfg.vertices[0].get_block_type() == BlockType.CONDITIONAL

def test_single_jumpdest_block():
    disasm = [
        FakeInstruction(0, "JUMPDEST"),
    ]
    cfg = EvmCFG(disasm)
    cfg.build_cfg()
    assert 0 in cfg.vertices
    assert cfg.vertices[0].instructions == ["JUMPDEST"]
    assert cfg.vertices[0].get_end_address() == 0
    assert cfg.vertices[0].get_block_type() == BlockType.TERMINAL

def test_multiple_jumpdest_in_block():
    disasm = [
        FakeInstruction(0, "JUMPDEST"),
        FakeInstruction(1, "JUMPDEST"),
        FakeInstruction(2, "STOP"),
    ]
    cfg = EvmCFG(disasm)
    cfg.build_cfg()
    assert 0 in cfg.vertices
    assert 1 in cfg.vertices
    assert 2 not in cfg.vertices

def test_jump_and_jumpi_priority():
    disasm = [
        FakeInstruction(0, "JUMPI"),
        FakeInstruction(1, "JUMP"),
        FakeInstruction(2, "STOP"),
    ]
    cfg = EvmCFG(disasm)
    cfg.build_cfg()
    assert cfg.vertices[0].get_block_type() == BlockType.CONDITIONAL
    assert cfg.vertices[1].get_block_type() == BlockType.UNCONDITIONAL
    assert cfg.vertices[2].get_block_type() == BlockType.TERMINAL