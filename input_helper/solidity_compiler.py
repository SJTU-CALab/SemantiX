import os
import solcx
import re
from utils import params
import logging


logger = logging.getLogger(__name__)


class SolidityCompiler:
    def __init__(self, source, root_path, allow_paths, remap, compilation_err, output_path):
        self.compiled_contracts = []
        self.source = source
        self.root_path = root_path
        self.allow_paths = allow_paths
        self.remap = remap
        self.compilation_err = compilation_err
        self.path = os.path.join(output_path, "compilation")
        if not os.path.exists(self.path):
            os.makedirs(self.path, exist_ok=True)

        self.compiled = False

        self.compiler_version = self._get_compiler_version()
        if self.compiler_version is None:
            self.compiler_version = params.SOLIDITY_COMPILER_VERSION  # default version

        try:
            solcx.install_solc(self.compiler_version)
        except Exception as e:
            logger.warning(f"Failed to set Solidity compiler version {self.compiler_version}: {e}")

    def get_compiled_contracts(self):
        if not self.compiled:
            self.compiled_contracts = self._compile_solidity()
        self.compiled = True
        return self.compiled_contracts

    def _get_compiler_version(self):
        # 正则匹配 Solidity 版本声明，例如：pragma solidity ^0.8.0;
        version_pattern = re.compile(r'pragma\s+solidity\s+(?:\^|>=)?\s*([0-9]+\.[0-9]+\.[0-9]+);?')

        try:
            with open(self.source, 'r', encoding='utf-8') as file:
                content = file.read()
                match = version_pattern.search(content)
                if match:
                    version_spec = match.group(1).strip()
                    logger.info(f"Found Solidity version requirement: {version_spec}")
                    return version_spec
                else:
                    logger.warning("Solidity version not found in the file.")
                    return None
        except FileNotFoundError:
            logger.warning(f"File not found: {self.source}")
        except Exception as e:
            logger.warning(f"An error occurred while parse compiler version: {e}")

    def _compile_solidity(self):
        try:
            output = solcx.compile_files([self.source],
                                         # output_values=["bin-runtime"],
                                         solc_version=self.compiler_version,
                                         allow_empty=True,
                                         # TODO: deal with allow_paths and improt_remapping with multiple files
                                        #  allow_paths=self.allow_paths, 
                                        #  import_remappings=self.remap
                                         )
        except Exception as e:
            logger.error(f"An error occurred while compiler solidity: {e}")
            return {}
        logger.info(f"Solidity compilation completed successfully for {self.source}.")
        return output

