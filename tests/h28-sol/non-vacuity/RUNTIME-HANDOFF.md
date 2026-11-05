# H28 serial-runtime checkpoint handoff

Base:6f3eedf0788ee1f8a3bcf230558c712ecdca04d5. Branch:codex/solidity-h28-sol-20261104/non-vacuity. Repository:/workspace/solidity-lean. The commit containing this file is the runtime checkpoint head. No push/merge.

Lean proof sources, Main wrappers, premises, exclusions and producer interfaces are unchanged. This checkpoint corrects runtime serialization and retained generated cache pages; adds a source-bound argv0 worker parser and three external resource controls. All26 Lean modules/414 axiom pins,169 constructor clauses,137 delegated predicates and their existing constructive findings retain their recorded boundaries.

Review snapshot:runtime-reviewed-inputs.json,54 hashes. Separate read-only finder/skeptic artifacts accompany this checkpoint; neither uses Lean/server. Final gates remain pending.

## Actual commands and outcomes

- `accounting-runtime-02`: command `tests/h28-sol/non-vacuity/runtime/accounting`; exit0; elapsed19.356208s; child maxRSS22704KiB; stopNone. Metadata/logs under evidence/runtime-v2; raw preparation path preserved inside metadata.
- `build-reclaim-before-pins`: command `lake env python3 tests/h28-sol/non-vacuity/kernel.py --module Solidity.Assurance.NonVacuityH28.Pins --fresh`; exit0; elapsed101.497881s; child maxRSS1378888KiB; stopNone. Metadata/logs under evidence/runtime-v2; raw preparation path preserved inside metadata.
- `build-reclaim-after-pins`: command `lake env python3 tests/h28-sol/non-vacuity/kernel.py --module Solidity.Assurance.NonVacuityH28.Pins --fresh`; exit0; elapsed100.449539s; child maxRSS1378576KiB; stopNone. Metadata/logs under evidence/runtime-v2; raw preparation path preserved inside metadata.
- `full-preparation`: command `bash scripts/coord-tools/gate.sh full`; exit137; elapsed8970.735529s; child maxRSSunavailableKiB; stop4 GiB VM working-set reserve guard. Metadata/logs under evidence/runtime-v2; raw preparation path preserved inside metadata.
- OS/parser smoke: command `python3 tests/h28-sol/non-vacuity/checker-tests.py AccountingControls.test_worker_argv0_forms AccountingControls.test_probe_shim_serializes_and_preserves_failure`; exit0; child elapsed0.152935s; child maxRSS20912KiB. Controlled OS children only: no Lean proof/output mocked or accepted.

Accounting passed37 tests, structural validation, and intentional refusal of final acceptance without final-gates.json. Same-source/command/runner fresh414Pins checks measured101.365076299→100.243178713 seconds,ratio0.9889321093. Page advice on26011 regular generated files took0.828092997 seconds, changed no inode/size/mtime/ctime and reported no errors; no artifact deletion or byte writes.

The full preparation failed exit137 after8970.735529 seconds at estimated VM reserve4199006208bytes (<4GiB), in immutable Examples/DecisionHashesChecks.lean at progress3150/3474. No Lean proof error was reported. Final child rusage and container peak were unavailable after the guard stopped it, explicitly null; PS RSS is sampled, not exact physical memory. Earlier full03/04 failures remain retained.

Resource policy remains12GiB job/no swap/4GiB estimated VM headroom, one heavy Lean worker, explicit-j1 and unchanged proof budgets. RO page advice on archives plus this checkout .lake/build may reclaim cold generated pages; symlinks are skipped and files opened O_RDONLY|O_NOFOLLOW. A pre-advice observed breach still stops immediately; advice cannot erase recorded minimum.30-second cooldown unchanged. The same existing container was restarted; no VM replaced.

The pinned corpus generator launches probes with Promise.all. The owned shim holds flock through each matching no-build Lake probe, creates its cold lock parent, appends-j1 after the caller separator, preserves stdout/stderr/exit status. Sampling detects observed overlap; flock enforces probe serialization. The parallel-before experiment is prohibited by lane policy and was not run; serial corpus cost is reported without a speedup claim.

Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b; Lake5.0.0-src+797c613. Earlier source KeySort gates passed; a new exact-head KeySort is still required. Remote master89373e34cdfd6bb5db7054b1c204d01edffc5fa7 fetched and ancestry verified without changing frozen base/assigned branch.

Required next steps: freeze reviewed runtime commit; run exact-head toolkit full gate using measured generated-page recovery, then private kernel --all --fresh after baseline build; run final evidence acceptance, combined read-only reviews, toolkit handoff/seal. Final artifacts are prepared under /workspace/solidity-lean/tests/h28-sol/non-vacuity/sealed/final-v2; final-v1 is preparation evidence only. No RUNTIME_GATE_PASS or whole-goal completion claimed at this checkpoint.
