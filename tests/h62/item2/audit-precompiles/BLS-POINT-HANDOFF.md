# BLS and PointEval applicability checkpoint

Same goal/branch; fetched master f160e517f before BLS and PointEval, inspected
unchanged source and rebased while preserving all off-git H44 evidence.
18 original BLS cases (5 joint,11data,2closed),2auxiliary general lemmas;
5 PointEval cases (3joint,2data). Actual successful pointEval_result remains
open and cannot be inferred from the abstract Unit bind-success witness.
No original source, statement, budget, exclusion or axiom policy changed.

All25 exact axiom guards pass, standard sets only. BLS pinned0.757838s,
PointEval pinned0.502962s, <=12GiB AS/no swap/4GiBreserve/threads1/-j1.
No module exceeds60s. Lean4.24 pinned; no migration435 acceptance.
Generator check passes and source census unchanged. Raw logs/receipts, hashes
and sizes: bls-point-evidence-manifest.json. Bulk stays off Git.

Separate read-only finder/skeptic pass both areas without Lean/server/builds,
tests or edits. Joint MSM witnesses use positive cost, nonzero constant table
and cap, matching table length, adjacent constraints and index ordering.
General lookup proof covers all lengths/indices/values. Short input samples
show applicability, not valid cryptographic execution. Two closed lengths and
auxiliaries are not fabricated premise witnesses. PointEval lengths use one
same nonempty input; abstract bind-success supplies all premises together.

Ledger remains97/138 pending receipt/full-type/mutation-check integration.
Including earlier Osaka,28 pending cases now have checked payloads;
13 still need implementations (Stipend12 and PointEval successful-result1).
All remain in original queue; no completion or RUNTIME_GATE_PASS claim.
Producer waits: migrate-root-gate435 compatibility/axiom review; G43 actual
compiler-success theorem; host H85/H86 package/allow-rule verification;
Exp/V09 integration. These do not block remaining independent core work.
