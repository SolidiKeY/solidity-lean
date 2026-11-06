# H62 item 1: binding fixtures — preliminary census

Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. The supplementary
lease names 18 `Solidity/Source/Agreement/*Controls.lean` files. None contains
the token `BindingRel` at this base. The audit describes ten controls with
private relations; a textual census finds ten `def BindingRel` declarations
under `Solidity/Lowering/V07` and seven `abbrev BindingRel` declarations under
`Solidity/Lowering/G19`. The ten V07 definitions are syntactically public, not
`private def`; their fixtures may nevertheless be specific to each control.
The original relation files and V07 files are not included in the supplementary
lease. No inference about permission to edit them follows from this census.

Run `python3 scripts/h62/item1/binding-fixtures/census.py` from any directory.
It enumerates tracked Lean source paths using Git and reports matching lines in
stable Git order as JSON. It is a lexical inventory: comments and references
are included, and multiline or differently named declarations are not parsed.
It does not establish semantic equivalence or exhaust all fixture cases. The
census is backfill, not a completed fixture-extraction checkpoint.

Lean 4.24.0 (commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`), Lake
5.0.0-src+797c613. Under the writer lock, with `LEAN_NUM_THREADS=1`,
`lean -j1 Solidity/KeySort.lean` exited 0 with no output. Two census runs
compared byte-for-byte equal, and `python3 -m py_compile` passed. No Lean
statement or proof was changed. No before/after proof timing, extraction, full
validation, independent finder review, or skeptic review has yet occurred.
All four checkpoints remain pending. Exact-file owner coordination remains
necessary before modifying V07 originals; relation unification stays with its
owners. The assigned source controls are separately leased, but they do not
contain the named relations, so their relationship to this extraction needs
careful case-by-case analysis.
