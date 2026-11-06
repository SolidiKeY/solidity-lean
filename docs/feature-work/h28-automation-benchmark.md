# H28 opt-in automation: compact integration increment

`Solidity/Automation/H28/Context.lean`, `Prove.lean` and `Chain.lean` are already
published. Their source bytes are unchanged in this delivery. Use
`sol_h28_prove` (optionally with numeric `steps`) and `sol_h28_chain` only when
explicitly opting into scoped evaluator code generation. Original owner search,
refusals and budgets remain in force; no default tactic is replaced.

The integration tests and utilities are self-contained in
`tests/h28-sol/automation-benchmark/README.md`. The seven Lean fixtures cover
Context witnesses, scalar/chain proofs and paired baseline/candidate refusals.
They include exact theorem checks, kernel replays and literal axiom inventories.
The runner has fixed180-second per-file limits and requires a caller-provided
serial, bounded, no-swap environment with OS headroom. Runtime outputs are not
source dependencies. No archived benchmark outputs are needed to run these tests.

This is a small integration increment, not a transport of the complete historical
benchmark. Historical source census, full-sample measurements and rejected runs
remain preserved separately on the worker VM. The original+10.99% prototype
rejection remains binding; historical production medians/p95 do not imply a
uniform speedup or a performance result on a new master. No full compiler,
producer, source, physical or world adequacy claim follows from these helpers.

H41 remains in force: verified cache packs stay on the VM for coordinator pull;
no worker-side cache shipping is authorized. This increment changes no theorem,
premise, exclusion, heartbeat budget or trust policy.

## Compact checkpoint validation and handoff

VM checks pass: serial owned-module builds, twenty Python regressions, all seven
per-file MCP diagnostics, and seven native controls (three positive, four intended
refusals), including literal axiom prints and kernel replays. Actual Lean4.24.0
and Lake5.0.0-src+797c613 precede passing KeySort output and RUNTIME_GATE_PASS.
The clean source checkout contains no historical generated/evidence files; only
public module build cache is shared. Actual validation used one CPU,8GiB memory,
no swap and the unchanged180-second per-file cap under a4GiB headroom guard.

Separate read-only finder and skeptic reviews found refusal-source identity and
axiom-footprint checks missing in the initial validator. Both were fixed, with
regressions and a passing real-control rerun. The first clean-run mount error is
retained as a harness failure, not a proof result. This checkpoint is ready as a
small script/test increment; it does not replace historical full benchmark
evidence or claim that a new whole-master combined integration has been tested.
