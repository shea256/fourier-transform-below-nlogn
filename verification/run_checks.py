#!/usr/bin/env python3
"""Run all incorporated finite verifiers and check the living result registry.

Works from any working directory. Standard-library Python >=3.10 only.
"""
from pathlib import Path
import subprocess
import sys

BASE = Path(__file__).resolve().parent


def run(program, log_name):
    print(f"Running {program} ...", flush=True)
    process = subprocess.run([sys.executable, program], cwd=BASE,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             text=True, check=False)
    output_dir = BASE / 'outputs'
    output_dir.mkdir(exist_ok=True)
    (output_dir / log_name).write_text(process.stdout, encoding='utf-8')
    print(process.stdout, end='', flush=True)
    if process.returncode:
        raise SystemExit(f"FAILED {program}: exit code {process.returncode}; see outputs/{log_name}")


def main():
    if sys.version_info < (3, 10):
        raise SystemExit('Python 3.10 or later required')
    run('verify_extension.py', 'extension_run.txt')
    run('clean_room_audit.py', 'clean_room_run.txt')
    run('compare_certificates.py', 'comparison_run.txt')
    run('verify_round6.py', 'round6_run.txt')
    run('verify_round10.py', 'round10_run.txt')
    run('verify_round11.py', 'round11_run.txt')
    process = subprocess.run([sys.executable, str(BASE.parent / 'scripts/build_manuscript.py'), '--check'], check=False)
    if process.returncode:
        raise SystemExit('Result registry or generated paper text is inconsistent.')
    print('All finite checks passed and reference certificates matched.')


if __name__ == '__main__':
    main()
