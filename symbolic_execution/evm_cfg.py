import logging
import json
import os
from enum import Enum
from symbolic_execution.block import Block


logger = logging.getLogger()


class BlockType(Enum):
    TERMINAL = "terminal"
    CONDITIONAL = "conditional"
    UNCONDITIONAL = "unconditional"
    FALLS_JUMPDEST = "falls_jumpdest"


class EvmCFG:
    TERMINAL_OP = {"STOP", "RETURN", "SUICIDE", "REVERT", "SELFDESTRUCT"}

    def __init__(self, disasm, source_map=None):
        self.disasm = disasm
        self.source_map = source_map

    def build_cfg(self):
        self._collect_vertices(self.disasm)
        self._construct_bb()
        self._construct_static_edges()

        if self.source_map:
            self.source_map.set_pc_to_index(sorted(self.instructions.keys()))

    def _collect_vertices(self, disasm):
        self.instructions = {}
        self.end_inst = {}
        self.block_type = {}

        current_block = 0
        is_new_block = True

        pc = 0
        for instruction in disasm:
            opcode = instruction.mnemonic
            pc = instruction.pc
            if instruction.operand is not None: 
                self.instructions[pc] = f"{opcode} {instruction.operand}"
            else:
                self.instructions[pc] = f"{opcode}"

            if is_new_block:
                current_block = pc
                is_new_block = False

            if opcode in self.TERMINAL_OP:
                self.block_type[current_block] = BlockType.TERMINAL
                self.end_inst[current_block] = pc
                is_new_block = True
            elif opcode == "JUMP":
                self.block_type[current_block] = BlockType.UNCONDITIONAL
                self.end_inst[current_block] = pc
                is_new_block = True
            elif opcode == "JUMPI":
                self.block_type[current_block] = BlockType.CONDITIONAL
                self.end_inst[current_block] = pc
                is_new_block = True
            elif opcode == "JUMPDEST":
                if current_block != pc:
                    self.end_inst[current_block] = pc - 1
                    self.block_type[current_block] = BlockType.FALLS_JUMPDEST
                    current_block = pc
        if current_block not in self.block_type:
            self.block_type[current_block] = BlockType.TERMINAL
            self.end_inst[current_block] = pc

    def _construct_bb(self):
        self.vertices = {}
        self.edges = {}

        for start in self.end_inst:
            end = self.end_inst[start]

            block = Block(start, end)

            for i in range(start, end + 1):
                if i in self.instructions:
                    block.add_instruction(self.instructions[i])

            block.set_block_type(self.block_type[start])

            self.vertices[start] = block
            self.edges[start] = []

    def _construct_static_edges(self):
        for v in self.vertices:
            block = self.vertices[v]
            block_type = block.get_block_type()
            end = block.get_end_address()

            if block_type == BlockType.TERMINAL:
                continue

            if block_type == BlockType.FALLS_JUMPDEST or block_type == BlockType.CONDITIONAL:
                next_pc = end + 1
                if next_pc in self.vertices:
                    block.set_falls_to(next_pc)
                    self.edges[v].append(next_pc)
                else:
                    logger.warning(f"unknown static jump target {next_pc} in block {v}")

            if block_type == BlockType.UNCONDITIONAL or block_type == BlockType.CONDITIONAL:
                static_jump = block.get_static_target()
                if static_jump:
                    if static_jump in self.vertices:
                        self.edges[v].append(static_jump)
                    else:
                        logger.warning(f"unknown static jump target {static_jump} in block {v}")

    

    


