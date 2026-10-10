# Versioned results and updates

The reusable theorem is in [paper/framework.md](../paper/framework.md). Each network has its own result record, exact parameters, source pins, certificate, and verifier. [registry.json](registry.json) is the source of the current selection and [the improvement log](../IMPROVEMENTS.md). The root manuscript is generated from the framework, selected record and [source acknowledgements](../paper/attribution.md). A record's optional `paper_records` list includes inherited construction arguments in reading order, so later refinements need not duplicate them.

`proposed` means that the record has a written conditional transfer and finite checks. `formalized` means that the record incorporates a pinned upstream theorem whose Lean project build, axiom audit and theorem/definition comparisons have been reproduced, with a retained receipt and hashed logs. Neither status means independent human review or practical usefulness. `candidate` is reserved for records whose required transfer or verification is unfinished. `historical-proposed` preserves the older certificate schema without silently reinterpreting it. The current result must be explicitly selected; a larger upstream exponent does not select itself.

For each future update:

1. Pin the complex-network sources, license, notices and complete physical witness. Record the integer headline separately if useful; it is not the Fourier saving. Update [the attribution audit](../ATTRIBUTION.md) and paper acknowledgements with the specific construction, integration and verification contributions, preserving predecessor credit and distinguishing related work from actual dependencies.
2. Add a new result record and verifier. Explain which finite-network contract arguments are inherited and which need new proofs. Do not overwrite an incorporated record to describe a different construction.
3. Rebuild the physical histogram, exact moment and absorption gap. State which checks are universal, exhaustive finite, sampled, imported, or formally verified.
4. Save the reference certificate only after reviewing the finite checks and written argument. Add a `candidate` registry entry while work is incomplete.
5. Once the transfer is written and checks pass, change that entry to `proposed` and explicitly select its ID in `current`. If incorporating an upstream formal Fourier theorem, first reproduce its pinned Lean build, axiom audit and theorem/definition comparisons; preserve the receipt and hashed logs before selecting `formalized`. That status applies to the cited theorem, not automatically to every written argument in this repository. Archive the previous assembled PDF, Markdown and LaTeX before rebuilding. Independent review status remains a separate issue.
6. Add the new verifier to `verification/run_checks.py`, rebuild with `python3 scripts/build_manuscript.py`, and run `python3 verification/run_checks.py`. Inspect the new PDF and refresh the announcement draft. Generated files are checked with `python3 scripts/build_manuscript.py --check`.

Routine witness updates should edit the new record and registry, not the generic theorem. A stronger finite-network interface or a correction to the transfer theorem requires a framework change and review of all affected results. The log records incorporated project results rather than mirroring every upstream announcement.

Historical documents are retained verbatim; their dates and relative links describe their original publication context. Use these records for current navigation.
