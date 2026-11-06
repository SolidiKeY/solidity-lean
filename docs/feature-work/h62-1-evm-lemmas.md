# H62 item 11: EVM lemma extraction

Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. This is an initial
read-only census, not a completed checkpoint or extraction. Run
`python3 scripts/h62/item1/evm-lemmas/census.py` from any directory; it scans
EVM, Backend, and Lowering Lean source in sorted order and writes no output
files. Its line-based patterns identify candidates, not a complete semantic
proof of all cases; multiline or differently named declarations need manual
review. EVM Examples and MemoryCopies Controls filenames are excluded by assignment.

Independent read-only finder and skeptic reviews (no Lean server) located seven
`run_cons_revert` definitions and seven named `Storage.Loc` inequality sites,
including a nested case; the scan also found an inline proof.
The public `Solidity.Evm.Prog.run_cons_error` in `Evm/Correct.lean` generalizes
the former, but its import cost and dependencies require measurement. The
`Evm.Slot.ne_data` theorem is about a different type. Nested descendants require
separate coverage; symbolic location inequality does not establish inequality
of hashed concrete words without the existing injectivity and coverage premises.
The three allocation-cost definitions do not have identical reductions, and
the fragment certificates belong to different indexed inductives. Preserve
all existing definitions, declarations and signatures when extracting proofs.

The seven cons-revert consumer files and most other consumer files are outside
the supplemental five-file lease. No relay script was found under `/workspace`;
exact-file owner coordination and registration remain outstanding. A census or
unused helper is not a substitute for integration. All four extraction checkpoints,
proofs, baseline/after timing, acceptance, final validation and post-change
independent reviews remain open. No Lean theorem, premise or representation has
been changed by this census.

Post-change read-only finder and skeptic reviews identified the overly broad
filename exclusions and incomplete location count; both were corrected. Neither
review used a Lean server. The initial creation of these two files was performed
without the required writer lock; concurrent writer status was not checked. Subsequent
changes and commit preparation used the lock.

H70 routing: the host-only relay accepted an owner ticket for V14. Exact revert consumers, first-statement and tail revert cases, nested location cases and owner requests are recorded in `tests/h62/item1/evm-lemmas/case-accounting.md`. This is static source accounting; no owner permission, extraction or passing proof gate is inferred.
