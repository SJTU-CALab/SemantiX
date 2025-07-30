import re
from pyevmasm import evmasm
from binascii import hexlify, unhexlify


class EvmDisassembler:
    def __init__(self, bytecodes):
        self.bytecodes = bytecodes

    def prepare_disasm(self):
        evm = re.sub(r"a165627a7a72305820\S{64}0029$", "", self.bytecodes)
        instructions = evmasm.disassemble_all(unhexlify(evm))
        return instructions
