# Pinned five-stage sources

`SOURCE.json` hashes the unmodified PR256 package by Chafik Boukhalfa and a complete source archive of his Fourier proof instantiation in Jacob Sussman's framework. The two immutable revisions are `db3f75cdc5f03f3131d48fb220f6bf1958404ff3` and `fd19e46b728faa414cbfbf91b01a6a0b7903375d`. The archive is produced by `git archive` at that commit and compressed with a fixed gzip timestamp; it contains no compiled Lean objects or dependency cache.

The package's own `SOURCE.json`, `NOTICE`, proof notes, verifier, certificates and baseline tarball are preserved byte for byte under `gcert-program-233/`. `FOURIER_NOTICE` is the proof repository's unmodified notice. Both sources use Apache-2.0; the license and contributor-specific assistance disclosures are retained.

The two certificates used by the Python package and the Lean source have identical mathematical data. Only their descriptive `derived_from` string differs. The local finite verifier checks this explicitly.

The proof's 89 imported OpenAI modules, original Fourier challenge and toolchain were also compared directly with OpenAI commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. All 91 files match. The [origin ledger](../../certificates/five_stage_openai_origin.json) records their hashes, and the finite verifier binds them to this archive. The [proof audit](../../FIVE_STAGE_AUDIT.md) describes the separate Lean reproduction.

Attribution clarification: the package notice associates `rohanarun` with `PR209/237`; #209 is Jacob Sussman's and #237 is Rohan Arun's. Its nested #233 notice describes an earlier frame-changing revision. The pinned #233 construction retains PR168's frames and changes the pairing. We retain both original notices unmodified and document these distinctions in the root `ATTRIBUTION.md`.

Fast finite check: `python3 verification/verify_five_stage.py` from the project root. Full upstream regeneration additionally requires `numpy==2.3.5 scipy==1.17.0` and runs `python3 -B verification/vendor/five_stage/gcert-program-233/verify.py`. The default project Python suite does not invoke Lean or install dependencies.
