#!/usr/bin/env python3
import argparse
import shutil
import os.path
import time
from utils import params, util
from input_helper.input_aggregator import InputAggregator
from symbolic_execution.evm_cfg import EvmCFG
from symbolic_execution.evm_interpreter import EVMInterpreter
import logging
from reporter.cfg_printer import CFGPrinter
from reporter.symbolic_trace_printer import SymbolicTracePrinter
from detectors.overflow_detector import OverflowDetector
from detectors.reentrancy_detector import ReentrancyDetector
from reporter.simple_result import SimpleResult
from detectors.prng_detector import PrngDetector
from detectors.tod_detector import TodDetector
from detectors.dos_detector import DosDetector
import json

logger = logging.getLogger(__name__)


def entry():
    global logger
    parser = argparse.ArgumentParser(prog="cryptoS")

    parser.add_argument("input", help="the file path of input file")

    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("-sol", "--solidity", help="input file type of  solidity source code", action="store_true")
    # 输入是evm bytecode
    group.add_argument("-evm", "--evm_bytecode", help="input file type of evm bytecode", action="store_true")

    parser.add_argument("-v", "--version", action="version", version="0.0.1")

    parser.add_argument("-to", "--timeout", help="time of analysis", action="store", type=int)
    parser.add_argument("-o", "--output", help="file path for results", type=str)
    # 添加是否保留tmp目录
    parser.add_argument("-k", "--keep", help="keep tmp directory", action="store_true")
    # 是否打印cfg
    parser.add_argument("-cfg", "--print_cfg", help="print cfg", action="store_true")
    # 是否打印符号执行trace
    parser.add_argument("-trace", "--print_trace", help="print trace", action="store_true")

    args = parser.parse_args()

    if args.print_trace:
        params.TRACE = True

    if args.timeout:
        params.TIMEOUT = args.timeout

    params.TMP_PATH = os.path.join("./tmp", str(int(time.time())))
    if not os.path.exists(params.TMP_PATH):
        os.makedirs(params.TMP_PATH, exist_ok=True)

    # 设置并创建output目录
    if args.output:
        params.OUTPUT_PATH = args.output
    else:
        params.OUTPUT_PATH = os.path.join("./output", str(int(time.time())))
    if not os.path.exists(params.OUTPUT_PATH):
        os.makedirs(params.OUTPUT_PATH, exist_ok=True)
    
    logger = util.get_logger()
    if args.solidity:
        analyze_solidity(args.input, args.print_cfg, args.print_trace)
    elif args.evm_bytecode:
        analyze_evm_bytecode(args.input, args.print_cfg, args.print_trace)

    # 删除tmp目录
    if not args.keep:
        shutil.rmtree(params.TMP_PATH)


def analyze_solidity(input_src, print_cfg=False, print_trace=False):
    inputs = InputAggregator(InputAggregator.SOL, source=input_src).get_aggregated_results()
    results = SimpleResult()
    for input in inputs:
        logger.info(f"Start Analysing contract: {input['contract']}")
        cfg = EvmCFG(input['disasm'], source_map=input['source_map'])
        cfg.build_cfg()
        if print_cfg:
            cfg_printer = CFGPrinter(cfg)
            cfg_printer.print_cfg_html_with_source_map()

        interpreter = EVMInterpreter(cfg, input['evm'], input['contract'].split(':')[-1])
        interpreter.run()

        if print_trace:
            trace_printer = SymbolicTracePrinter(os.path.join(params.OUTPUT_PATH, "trace.jsonl"), cfg)
            trace_printer.print_trace_html_with_source_map()

        results.set_source_map(input['source_map'])
        results.set_instructions(cfg.instructions)
        detect(interpreter.graph, results)

        logger.info(f"End Analyze contract: {input['contract']}")
    with open(os.path.join(params.OUTPUT_PATH, "results.json"), "a") as f:
        f.write(json.dumps(results.results, indent=4))


def analyze_evm_bytecode(input_evm, print_cfg=False, print_trace=False):
    pass

def detect(graph, results):
    overflow_detector = OverflowDetector(graph)
    results.set_vulnerabilities("overflow", overflow_detector.detect())

    reentrancy_detector = ReentrancyDetector(graph)
    results.set_vulnerabilities("reentrancy", reentrancy_detector.detect())

    prng_detector = PrngDetector(graph)
    results.set_vulnerabilities("prng", prng_detector.detect())

    tod_detector = TodDetector(graph)
    results.set_vulnerabilities("tod", tod_detector.detect())

    dos_detector = DosDetector(graph)
    results.set_vulnerabilities("dos", dos_detector.detect())


if __name__ == '__main__':
    entry()

