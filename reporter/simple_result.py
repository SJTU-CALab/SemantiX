class SimpleResult:
    warning_str = {
        "overflow": "Security Warning: IntegerOverflow/Underflow Vulnerability",
        "reentrancy": "Security Warning: Reentrancy Vulnerability",
        "prng": "Security Warning: Pesudo Randomness Generation Vlunerability",
        "dos": "Correctness Warning: Deny of Service",
        "tod": "Correctness Warning: Transaction Ordering Dependency"
    }

    def __init__(self):
        self.results = {
            'evm_code_coverage': '',
            'vulnerabilities': {
                'overflow': [],
                'reentrancy': [],
                'prng': [],
                'dos': [],
                'tod': []
            },
            'run_time': 0
        }
        self.start_time = 0
        self.end_time = 0
        self.source_map = None
        self.instructions = None

    
    def set_start_time(self, start_time):
        self.start_time = start_time

    def set_end_time(self, end_time):
        self.end_time = end_time

    def set_evm_code_coverage(self, evm_code_coverage):
        self.results['evm_code_coverage'] = evm_code_coverage

    def set_source_map(self, source_map):
        self.source_map = source_map

    def set_instructions(self, instructions):
        self.instructions = instructions

    def set_vulnerabilities(self, type, pcs):
        if self.source_map:
            for pc in set(pcs):
                position = self.source_map.get_position_with_pc(pc)
                self.results["vulnerabilities"][type].append(f"{pc}: {self.instructions[pc]}: {self.source_map.source.get_content_with_position(position)}: {self.warning_str[type]}")
        else:
            for pc in set(pcs):
                self.results['vulnerabilities'][type].append(f"{pc}: {self.instructions[pc]}: {self.warning_str[type]}")

    def get_result(self):
        return self.results
        