from input_helper.solidity_compiler import SolidityCompiler
from utils import params
from input_helper.evm_disassembler import EvmDisassembler
from input_helper.source_map import SoliditySourceMap
import os


class InputAggregator:
    WASM = 0
    SOL = 1

    def __init__(self, input_type, **kwargs):
        self.input_type = input_type

        if input_type == InputAggregator.SOL:
            attr_defaults = {
                'source': None,
                'evm': False,
                'root_path': "",
                'compiled_contracts': [],
                'compilation_err': True,
                'remap': "",
                'allow_paths': ""
            }
        else:
            attr_defaults = {
                'source': None
            }

        for attr, default in attr_defaults.items():
            val = kwargs.get(attr, default)
            setattr(self, attr, val)

    def get_aggregated_results(self):
        inputs = []
        if self.input_type == InputAggregator.SOL:
            compiler = SolidityCompiler(self.source, self.root_path, self.allow_paths, self.remap,
                                        self.compilation_err, params.TMP_PATH)
            contracts = compiler.get_compiled_contracts()
            for contract in contracts:
                contract_path = contract.split(':')[0]
                contract_name = contract.split(':')[-1]
                disassembler = EvmDisassembler(contracts[contract]['bin-runtime'])
                disasm = disassembler.prepare_disasm()

                source_map = SoliditySourceMap(contract_path, contract_name, contracts[contract])

                inputs.append({
                    'contract': contract,
                    'source_map': source_map,
                    'source': contract_path,
                    'c_name': contract_name,
                    'disasm': disasm,
                    'evm': contracts[contract]['bin-runtime']
                })
        return inputs


