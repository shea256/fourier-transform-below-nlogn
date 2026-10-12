#!/usr/bin/env python3
"""Check source, generator, witness and original-import provenance hashes."""
import hashlib
import json
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parents[1]


def main():
    manifest=json.loads((ROOT/"SOURCE_MANIFEST.json").read_text())
    for rel,digest in manifest["files"].items():
        p=REPO/rel
        assert hashlib.sha256(p.read_bytes()).hexdigest()==digest,rel
    for rel,origin in manifest["lean_origins"].items():
        if origin["kind"]!="verifier-import-prefix":continue
        data=(ROOT/rel).read_text()
        restored=re.sub(r"^(import\s+)((?:OAI|Work|WHTCheck)\.)",r"\1Submission.\2",data,flags=re.M)
        assert hashlib.sha256(restored.encode()).hexdigest()==origin["original_sha256"],rel
    print(f"PASS: {len(manifest['files'])} hashes and all upstream Lean import-prefix identities")


if __name__=="__main__":main()
