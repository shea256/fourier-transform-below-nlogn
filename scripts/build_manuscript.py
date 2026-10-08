#!/usr/bin/env python3
"""Rebuild the current manuscript's LaTeX and PDF from its Markdown source.

Requires pandoc and pdflatex. The archived manuscript and short fallback PDF
are intentionally separate artifacts with their own unchanged sources.
"""
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / 'tex' / 'build'


def run(command, log):
    result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, check=False)
    (BUILD / log).write_text(result.stdout)
    if result.returncode:
        raise SystemExit(f'{command[0]} failed:\n{result.stdout[-6000:]}')


def main():
    BUILD.mkdir(exist_ok=True)
    source = (ROOT / 'manuscript.md').read_text()
    body = source.split('\n', 2)[2]
    body = body.replace('**Research draft, October 8, 2026. Round-six complex-network transfer.**\n', '', 1)
    # Keep the three small proof tables together rather than splitting them
    # after a few rows at the bottom of a page.
    for heading, lines in (('| Step |', 24), ('| Class |', 12), ('| $r$ |', 20)):
        body = body.replace('\n' + heading, f'\n\\Needspace{{{lines}\\baselineskip}}\n\n' + heading, 1)
    input_path = BUILD / 'body.md'
    input_path.write_text(body)
    run(['pandoc', str(input_path), '--standalone', '--from=markdown+tex_math_single_backslash',
         '--to=latex', '--output=tex/manuscript.tex', '--include-in-header=tex/preamble.tex',
         '--metadata=title:An Improved Exponent Bound for the Exact Discrete Fourier Transform',
         '--metadata=subtitle:Research draft: round-six complex-network transfer',
         '--metadata=date:October 8, 2026', '--variable=fontsize:11pt',
         '--variable=geometry:margin=1in', '--variable=colorlinks:true',
         '--variable=urlcolor:blue', '--variable=linkcolor:blue'], 'pandoc.log')
    for pass_number in (1, 2):
        run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
             '-output-directory=tex/build', 'tex/manuscript.tex'], f'latex-pass-{pass_number}.log')
    shutil.copyfile(BUILD / 'manuscript.pdf', ROOT / 'manuscript.pdf')
    print('Rebuilt tex/manuscript.tex and manuscript.pdf.')


if __name__ == '__main__':
    main()
