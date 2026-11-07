# H28 contract checkpoint handoff

Base: 6f3eedf0788ee1f8a3bcf230558c712ecdca04d5. Repository: /workspace/solidity-lean. Branch: codex/solidity-h28-sol-20261104/non-vacuity. The commit containing this file is the checkpoint head. No push or merge.

26 private Lean modules;414 names with exact guarded axiom sets;137 delegated contracts;169 constructor clauses (32 constructed,137 durable findings);all36 Stmt dispatch/helper analyses;10 representation/resource limitations. Witness-or-finding accounting is complete, but required final gate acceptance is pending. No whole compiler correctness claim.

## Recorded gates

- `signatures-contracts-03`: command `lake env python3 tests/h28-sol/non-vacuity/kernel.py --module Solidity.Assurance.NonVacuityH28.Signatures`; exit0; elapsed106.679s; child maxRSS1398456KiB; stopNone. Raw evidence: evidence/signatures-contracts-03.json and.log.
- `pins-contracts-03`: command `lake env python3 tests/h28-sol/non-vacuity/kernel.py --module Solidity.Assurance.NonVacuityH28.Pins`; exit0; elapsed107.033s; child maxRSS1379084KiB; stopNone. Raw evidence: evidence/pins-contracts-03.json and.log.
- `accounting-contracts-02`: command `tests/h28-sol/non-vacuity/runtime/accounting`; exit0; elapsed18.148s; child maxRSS22588KiB; stopNone. Raw evidence: evidence/accounting-contracts-02.json and.log.
- `full-repository-03`: command `bash run-lean.sh`; exit137; elapsed571.866s; child maxRSSunavailableKiB; stop4 GiB VM working-set reserve guard. Raw evidence: evidence/full-repository-03.json and.log.
- `full-repository-04`: command `bash run-lean.sh`; exit137; elapsed1629.620s; child maxRSSunavailableKiB; stop4 GiB VM working-set reserve guard. Raw evidence: evidence/full-repository-04.json and.log.

An early Families per-file MCP diagnostic passed (families-diag-02); later MCP startup/diagnostic attempts failed or hung, with raw evidence retained. No current per-file MCP pass is claimed. Private modules have no shared Lake target, so bounded serial kernel commands check their sources; a final --all --fresh after baseline build is still required. Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Lake5.0.0-src+797c613. Earlier KeySort04 source gate passed; final exact-head KeySort remains required.

Full03/full04 were resource-guard failures, not proof falsity. New runner advises read-only cache reclamation for both disposable Lake cache roots and never hides a sampled <4GiB reserve.12GiB task cap/no swap/4GiB VM working-set reserve unchanged. Required next gate: bash scripts/coord-tools/gate.sh full.

Proof boundary: Lean kernel checks typed witnesses, theorem applications and countercontrols. Python checks inventory/evidence completeness and tamper controls; it is not a proof. Independent finder/skeptic inspect source/accounting without Lean/server. Producer/source-to-bytecode, physical adequacy, uninhabited object families and unexercised positive loop/copy/call capacity remain explicitly scoped findings.

Final evidence will be prepared under tests/h28-sol/non-vacuity/sealed/final-v1, without a later evidence-only commit changing the gate head. Seal only after all final evidence/handoff files exist.
