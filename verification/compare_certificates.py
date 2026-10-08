#!/usr/bin/env python3
"""Compare regenerated *finite-check* certificates with archival reference data.

This is an exact JSON comparison, not a proof checker for the asymptotic theorem.
The clean-room certificate includes elapsed wall time, which is non-reproducible.
"""
from pathlib import Path
import json
import sys

BASE = Path(__file__).resolve().parent


def load(path):
    with path.open(encoding="utf-8") as f:
        return json.load(f)


def main():
    checks = [
        ("original suite", BASE / "certificate.json", BASE / "certificates/extension_reference.json"),
        ("second implementation", BASE / "clean_room_certificate.json", BASE / "certificates/clean_room_reference.json"),
    ]
    for name, current, reference in checks:
        if not current.exists():
            print(f"FAIL {name}: missing {current.name}. Run the verifier first.", file=sys.stderr)
            return 1
        actual, expected = load(current), load(reference)
        if name == "second implementation":
            actual.pop("wall_seconds", None)
            expected.pop("wall_seconds", None)
        if actual != expected:
            differing = sorted(k for k in set(actual) | set(expected) if actual.get(k) != expected.get(k))
            print(f"FAIL {name}: certificate differs in {differing}", file=sys.stderr)
            return 1
        print(f"PASS {name}: regenerated certificate matches archived reference")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
