class Block:
    def __init__(self, start_address, end_address):
        self.start = start_address

        self.end = end_address

        self.instructions = []  # each instruction is a string

        self.jump_from = []  # all blocks from which can jump to or fall to this block

        self.jump_dynamic_to = set()  # jump_to list

        self.jump_static_to = None

        self.falls_to = None

        self.type = None

        self.branch_expression = None

    def add_instruction(self, instruction):
        self.instructions.append(instruction)

    def get_instructions(self):
        return self.instructions

    def set_block_type(self, b_type):
        self.type = b_type

    def get_block_type(self):
        return self.type

    def get_start_address(self):
        return self.start

    def get_end_address(self):
        return self.end

    def set_falls_to(self, falls_to):
        self.falls_to = falls_to
    
    def get_falls_to(self):
        return self.falls_to

    def get_static_target(self):
        instrs = self.instructions
        if len(instrs) > 1 and "PUSH" in instrs[-2]:
            self.jump_static_to = int(instrs[-2].split(" ")[1], 10)
        return self.jump_static_to