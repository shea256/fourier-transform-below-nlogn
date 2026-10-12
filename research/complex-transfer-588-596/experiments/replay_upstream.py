#!/usr/bin/env python3
"""Fetch pinned source packages and run their unchanged upstream verifier.

Python 3.11+. All caches and large outputs stay outside this research directory.
This checks the upstream finite witness, not an all-length DFT theorem.
"""
import argparse
import io
import json
from pathlib import Path
import subprocess
import sys
import tarfile

PINS = {
    588: ("6d0e53b66c29abd17981881a09eaff41ac862d85", "complex-571-free4fc8"),
    596: ("7732dd5e46863ff294b5e443661cb9d99abf4e01", "complex-571-hpeq5"),
}


def prepare(repo, root, number, commit, package):
    if subprocess.run(["git", "-C", str(repo), "cat-file", "-e", commit],
                      capture_output=True).returncode:
        subprocess.run(["git", "-C", str(repo), "fetch", "--depth", "1",
                        "origin", commit], check=True)
    destination = root / f"pr{number}"
    path = destination / "research" / package
    if not path.exists():
        raw = subprocess.check_output(["git", "-C", str(repo), "archive", commit,
                                       "research/" + package])
        destination.mkdir(parents=True, exist_ok=True)
        with tarfile.open(fileobj=io.BytesIO(raw)) as archive:
            archive.extractall(destination, filter="data")
    return path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pr", type=int, choices=PINS)
    parser.add_argument("--git-cache", type=Path, required=True)
    parser.add_argument("--inputs", type=Path, required=True)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--check-pins", action="store_true")
    args = parser.parse_args()
    if sys.version_info < (3, 11):
        parser.error("Python 3.11+ is required by upstream")
    repo, root, work = (p.resolve() for p in (args.git_cache, args.inputs, args.work))
    if not repo.exists():
        subprocess.run(["git", "clone", "--filter=blob:none", "--depth", "1",
                        "--no-checkout", "https://github.com/CrocSwap/integer-mult-bounds.git",
                        str(repo)], check=True)
    commit, name = PINS[args.pr]
    package = prepare(repo, root, args.pr, commit, name)
    spec = json.loads((package / "data/SPEC.json").read_text())
    command = [sys.executable, "-B", str(package / "verify.py"),
               "--work", str(work), "--jobs", "3"]
    for name, pin in spec["build"]["sources"].items():
        source = prepare(repo, root, pin["pr"], pin["commit"], pin["dir"])
        command.extend(["--source", name + "=" + str(source)])
    if args.check_pins:
        command.append("--check-pins")
    work.parent.mkdir(parents=True, exist_ok=True)
    work.with_suffix(".command.json").write_text(json.dumps(command, indent=2) + "\n")
    with work.with_suffix(".log").open("w") as stream:
        result = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT)
    print(f"exit={result.returncode}; log={work.with_suffix('.log')}")
    raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
