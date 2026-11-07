"""Run the independent referee checks and write results.json beside this file."""

import importlib
import json
import sys
from pathlib import Path

sys.dont_write_bytecode = True

MODULES = ('check_source', 'check_exterior', 'check_ideal', 'check_rigidity', 'check_coset_parity')


def main():
    if not __debug__:
        raise SystemExit('Run without -O so assertions remain active.')
    results = {}
    for module in MODULES:
        print(f'Running {module}', flush=True)
        results[module] = importlib.import_module(module).run()
        print(f'Passed {module}', flush=True)
    path = Path(__file__).with_name('results.json')
    path.write_text(json.dumps(results, indent=2, sort_keys=True) + '\n', encoding='utf-8')
    print(f'Wrote {path}')


if __name__ == '__main__':
    main()
