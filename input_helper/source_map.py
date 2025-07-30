
class Source:
    def __init__(self, filename):
        self.filename = filename
        self.content = self._load_content()
        self.line_break_positions = self._load_line_break_positions()

    def _load_content(self):
        with open(self.filename, 'r') as f:
            content = f.read()
        return content

    def _load_line_break_positions(self):
        return [i for i, letter in enumerate(self.content) if letter == '\n']

    def get_content_with_position(self, position):
        return self.content[position["begin"]:position["end"]]


class SoliditySourceMap:
    sources = {}

    def __init__(self, c_source, c_name, contract):
        self.source = self._get_source(c_source)
        self.c_name = c_name
        self.contract = contract

        self.func_to_sig = contract['hashes']
        self.sig_to_func = self._get_sig_to_func()

        self.position = self._get_positions(contract['asm']['.data']['0']['.code'])

        self.pc_to_index = {}

    def _get_sig_to_func(self):
        return {sig: func for func, sig in self.func_to_sig.items()}

    def _get_source(self, f_name):
        if f_name not in SoliditySourceMap.sources:
            SoliditySourceMap.sources[f_name] = Source(f_name)
        return SoliditySourceMap.sources[f_name]

    def _get_positions(self, asm):
        positions = []
        for pos in asm:
            if pos['name'] != 'tag':
                positions.append(pos)
        return positions

    def set_pc_to_index(self, keys):
        for index, key in enumerate(keys):
            self.pc_to_index[key] = index

    def get_position_with_pc(self, pc):
        index = self.pc_to_index[pc]
        if index >= len(self.position):
            return {"begin": 0, "end": 0, "name": "STOP"}
        return self.position[index]

    def get_line_number_from_position(self, position):
        for i, line_break_position in enumerate(self.source.line_break_positions):
            if line_break_position > position:
                return i+1  # 行号从1开始
        return len(self.source.line_break_positions)


