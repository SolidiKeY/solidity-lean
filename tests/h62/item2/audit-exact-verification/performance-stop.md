# B-PERFORMANCE-STOP — no further Lean jobs

Source rule: H62 assignment, “Measure before/after same tree/cache/resources;
stop >10% slowdown.” H70 supplied no budget or passing-gate exception.

Final gate command:
`python3 scripts/h62/item2/audit-exact-verification/h70-check.py --run`.
All four bounded subprocess phases exited zero, including the 99 new source
instances and compiler census. The enclosing gate exited 1 at its timing check.

Unchanged `Solidity/Calculus/LinearHypotheses.lean`:
median before 0.520586729 s; after 0.622912645 s; +19.655883%.
Five samples per side, same source hashes, cache, compiler and resource settings.
Raw samples and all other module medians:
`/workspace/h62-audit-h70-evidence/h70-timing.json`.
Proof/log/source provenance: `/workspace/h62-audit-h70-evidence/h70-receipt.json`.

The 0.1-second polling monitor may contribute quantization, but that is an
unproved explanation, not grounds to discard the measurement or relax the rule.
The worker stopped Lean work immediately; no timing retries after this failure.
Only lightweight evidence validation, review and handoff follow the stop.

Coordinator request: diagnose the saved samples/source hashes under the unchanged
10% rule, or retain this blocker pending a separately directed runtime session.
No gate waiver, budget change, statement repair or exclusion is requested.
