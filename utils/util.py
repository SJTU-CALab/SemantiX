import logging
from utils import params
import os
import z3


def get_logger(name=None):
    logger = logging.getLogger(name)
    logger.setLevel(logging.DEBUG)

    if not logger.handlers:
        # 创建一个 file handler，写入日志文件
        file_handler = logging.FileHandler(os.path.join(params.OUTPUT_PATH, 'running.log'))
        file_handler.setLevel(logging.DEBUG)
        file_formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
        file_handler.setFormatter(file_formatter)

        # 创建一个 console handler，输出到控制台
        console_handler = logging.StreamHandler()
        console_handler.setLevel(logging.INFO)
        console_formatter = logging.Formatter('%(levelname)s - %(message)s')
        console_handler.setFormatter(console_formatter)

        # 添加 handler 到 logger
        logger.addHandler(file_handler)
        logger.addHandler(console_handler)
    return logger


def custom_deepcopy(input):
    output = {}
    for key in input:
        if isinstance(input[key], list):
            output[key] = list(input[key])
        elif isinstance(input[key], dict):
            output[key] = custom_deepcopy(input[key])
        else:
            output[key] = input[key]
    return output


def convert_result(value):
    return z3.simplify(value)


def get_vars(expr):
    result = set()
    def collect(e):
        if z3.is_const(e) and e.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            result.add(e)
        # 否则，如果是表达式，则递归地处理它的每个子节点
        elif z3.is_expr(e):
            for ch in e.children():
                collect(ch)
    collect(expr)
    return result

def ceil32(x):
    return x if x % 32 == 0 else x + 32 - (x % 32)