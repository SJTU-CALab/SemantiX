class NameGenerator:
    def __init__(self):
        self.count = 0

    def gen_data_size(self, contract):
        return f"is_{contract}"

    def gen_input_data(self, contract):
        return f"id_{contract}"

    def gen_origin_var(self):
        return "origin"

    def gen_coin_base(self):
        return "bs_c"

    def gen_number(self):
        return "bs_n"

    def gen_difficult(self):
        return "bs_d"

    def gen_randao(self):
        return "bs_r"

    def gen_timestamp(self):
        return "bs_t"

    def gen_var(self, pc, name):
        self.count += 1
        return f"var_{name}_{pc}_{self.count}"

    def gen_sha3(self, value):
        return f"sha3_{value}"
    
    def gen_block_hash(self, number):
        return f"bh_{number}"

    def gen_blob_hash(self, index):
        return f"bbh_{index}"
    
    def gen_storage_index(self, position):
        return f"si_{position}"

    def gen_gas(self, contract):
        self.count += 1
        return f"gas_{contract}_{self.count}"

    def gen_address(self, pc):
        self.count += 1
        return f"addr_{pc}_{self.count}"
    
    def gen_call_status(self, pc):
        self.count += 1
        return f"cs_{pc}_{self.count}"

    def gen_ret_data_size(self, pc):
        self.count += 1
        return f"rds_{pc}_{self.count}"

    def gen_ret_data(self, pc):
        self.count += 1
        return f"rd_{pc}_{self.count}"

    def gen_call_args(self, pc):
        self.count += 1
        return f"ca_{pc}_{self.count}"

    def gen_call(self, pc):
        self.count += 1
        return f"call_{pc}_{self.count}"
    
    def gen_selfdestruct(self, pc):
        self.count += 1
        return f"sd_{pc}_{self.count}"
    
    def gen_balance(self, address):
        return f"bal_{address}"

    def gen_constraint(self, pc, expr):
        self.count += 1
        return f"c_{pc}_{str(expr)}_{self.count}"

    def gen_sstore(self, pc, position):
        self.count += 1
        return f"ss_{pc}_{position}_{self.count}"
        
