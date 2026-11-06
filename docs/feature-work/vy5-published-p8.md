# VY5 published interface integration, 2026-11-03

Rebased the help branch onto exact master
`8eec153a5670d3153114596f1ccab2b1acbb6afc`, including P1 V3. The pre-rebase
head `50fecbdbf1ad0fe4ea27d88ddae4767416ee9d4a` remains reachable on
`codex/solidity-inline-assembly5-20261031/vy5-composition-help-pre-p8-publication-20261103`;
old seals, original checkout and private source tree are unchanged.

P8a `FrozenInterface`, P8b `Frozen`/`P8aInterface` and Source `FailureResources`
now use the exact published Git bodies. There is no private P8b definition to
replace. Existing generic `Stages` remains a Roadmap certificate consumer;
it neither constructs nor relies on an actual P8a V1 Producer. V1's countable
resource obstruction is retained; H12's premise-only composition pause remains.

Root-import conflicts were resolved by the shared registration generator;
append-only docs retained both published and owned additions. Two duplicate
imports caused by already-published modules were found by the existing strict
registration check and removed through `scripts/register-published-p8.py`.
All unrelated registrations are preserved. Its four regression cases are in
`tests/published-p8/register-tests.py`. Published Source StmtProgress additions
merged automatically alongside the owned immutable case; no foreign theorem
body was manually rewritten.

The focused published-interface and owned proof import closure passed (116
jobs). Exact module hashes, body comparisons and range-diff are in the sealed
integration evidence. This is not a global root/TestSuite pass or a P8a
realization. The known G13/V08 immutable consumer blockers remain separate.

H16 supersedes route(a): VY5 is now the single writer for the measured
Nat × FailurePoints execution extension. No such representation change is
part of this integration checkpoint. Record single-thread baseline checking
of Machine/Eval/Semantics/Session/Horizon/HorizonDeploy/Funds and P8 before
editing the carrier; compare after changes and stop without landing a
noticeable checking-time regression. Copy-recovery will build P8a V2 on the
carrier. Existing budgets, observations and all-plan coverage remain intact.
