# Trust and usability

Status (2026-11-07): **authorized; not yet implemented.** The user asked the
roadmap to make the finished repository trustworthy despite its size, and
usable on real contracts. This document plans that work as groups A
(assurance) and U (usability), in parallel lanes beside the main chain and
the X/O/T lanes of [full-scope.md](full-scope.md). It closes no proof
obligation.

## Principles

- **Trust comes from a small, readable surface, not from the line count.**
  The kernel checks every proof, so a reviewer reads only the definitions the
  headline theorems mention and the statements themselves. Everything else
  (proofs, tactics, examples, printers) only has to be checked by the kernel.
- **The semantics is the real risk.** A proof about the wrong semantics is
  still a valid proof. The semantics is validated against the real world
  (solc, a reference EVM) continuously, not only at G52.
- **The verdict users rely on is solc's output.** Translation validation
  (T01–T08) certifies the bytecode people actually deploy, keeping solc's gas
  costs and ecosystem. This repository's compiler stays as the reference and
  as an option for small, high-assurance contracts.
- **Usability is measured per contract, not per library build.** The library
  build is cached (`lake-cache`); what matters is the time and memory to verify
  one function of a real contract, end to end.
- **Two modes, one rule set.** *Fast mode* runs the proved ⊢ rules as compiled
  code and reports a verdict. *Certified mode* produces a kernel-checked
  theorem. Fast mode additionally trusts Lean's compiler and runtime, the C
  compiler, and every `implemented_by` twin's link theorem. Its verdict is never
  a Lean theorem and never enters the core: `scripts/check-trust.sh` keeps
  rejecting native proof reduction.

## Groups

Each group follows the [VM execution contract](../coverage-plan.md#vm-execution-contract)
and starts with an inventory of existing tools, so it does not rebuild them.

### A — assurance

| Group | Deliverable | Depends on |
|---|---|---|
| A01 | **Trusted surface.** Extend `Solidity/Theorems.lean` into the single statements page: every public headline theorem (calculus soundness, `compile_correct` and its G49/G50 successors, `solc_validated`), with its exact premises. A script computes the definition closure of those statements (everything a reader must believe, excluding proofs) and reports its line count per module. CI fails when the closure grows without a recorded reason. Target: the closure can be read in days, not months. | — |
| A02 | **Honest headline theorems.** Delete the always-revert disjunct (backfill item 4, G24.04) and run the existing headline witnesses and non-vacuity suite in CI (proof-coverage audit items 1–2). Each public theorem gets a nontrivial inhabited witness that pays, reverts and returns. | Codex `Solidity/Evm/**` lanes merged |
| A03 | **Escape-hatch audit.** A CI check that every `implemented_by` / `@[extern]` in `Solidity/` has a link theorem to its proved definition (Gate G0); the list is published with the trust report. Fast mode's extra trust is exactly this list plus the compiler. | — |
| A04 | **Independent kernel re-check.** A nightly CI job re-checks the public closure with an independent checker (`lean4checker`, or a second kernel), outside the core in `scripts/ci/`. Combined with the axiom audit (`scripts/AxiomAudit.lean`). | A01 |
| A05 | **Continuous semantic validation.** From now on, not only at G52: generated and corpus programs run on `Prog.run` and, compiled by solc in all four modes, on a reference EVM (start from `scripts/evm-reference/`, `roadmap-v17-differential.py`); outcomes, storage, returndata and logs are compared, with shrinking. Every disagreement becomes either a semantics fix or a recorded deviation in `solc-alignment.md`. Grows with each X group; G52 completes it. | — |
| A06 | **Trust report.** `docs/trust.md`, one page: what is trusted in certified mode (kernel, A01 closure, D5 premises), what fast mode adds (A03 list, compiler), how to reproduce (commands, revision), the A05 agreement numbers, and the open gaps. A draft first; regenerated per release; G55 publishes the final one. | A01, A03, A05 |

### U — usability

| Group | Deliverable | Depends on |
|---|---|---|
| U01 | **Benchmarks and budgets.** A suite of real contracts: TestSuite.sol functions, upstream semantic tests, the Velvet suite (`scripts/testsuite-performance.mjs`) and a few typical contracts (token, vault, multisig). Each is measured end to end (source to verdict: parse, elaboration, walk, closing, kernel), with wall time and peak RSS, in both modes. A CI job with per-function budgets; a regression fails the job. Proposed targets, calibrated here and approved by the user: fast mode p50 ≤ 1 s and p95 ≤ 10 s per function; certified mode ≤ 60 s and ≤ 4 GiB per function; cost roughly linear in function size. | — |
| U02 | **Fast mode.** The proved ⊢ rule set and closer run as compiled code (generated C, `Tools/`, the extension's native path) and return a verdict marked `native`, with the open branch and source line on failure. It has the same rules and verdicts as certified mode; a differential test checks that both modes agree on the U01 suite. | U01, A03 |
| U03 | **Leaf deciders by reflection.** Proved decision procedures for terminal leaves, which dominate kernel time (`kernel-replay-performance.md`: leaves 119–943 ms against walks of 28–101 ms). Generalize the trimmed-leaf checker (`dropPrem_holds`) to the leaf classes U01 shows are common. | U01 |
| U04 | **Small certificates.** A certificate made of the selected rule applications and local leaf witnesses, checked by the kernel without replaying the search. Kernel time becomes linear in walk length, ending the growing chunk cost (OpenLoops: 3.6 s → 89 s per chunk). | U03 |
| U05 | **Modular verification.** Function specifications and call summaries (`function-specs.md`, `automation.md`) so each function is verified once and reused by its callers. Verdicts are cached by the hash of function, spec and dependencies. A contract's cost is the sum over changed functions. | U01 |
| U06 | **Heavy modules off the critical path.** The three worst modules of the build-speed audit (`OpenLoops` 600 s / 9 GiB, `DecisionGaps` 215 s, `RevertData` 163 s): replace them with U03/U04 certificates or move them to a separate examples target, with ≤ 6 GiB peak per module. Also drop the redundant axiom pins (audit Q1) if the user approves. | U01, U04 for the rewrite |
| U07 | **Tool surface.** One CLI and editor entry point: `verify file.sol --mode fast\|certified`, readable failures (branch, source line, counterexample from a refuted leaf), certified mode running in the background or in CI after a fast pass. A disagreement between the modes is reported as a bug. | U02 |
| U08 | **Validation budgets.** `sol_validate` (T07) under U01-style budgets on the T08 corpus, incremental per contract; this is the user-facing check of solc output. | U01, VT4 |

U01 measurement inventory and prerequisites: [benchmark lane](vu1-bench.md).

## Lanes

Sized by the [sizing rules](../coverage-plan.md#sizing-rules): one 16 GiB VM,
eight to ten hours, a dependency chain of groups; no lone audits.

| Lane | Checkpoints, in order | Starts after |
|---|---|---|
| VA1 | A01, A03, A04 | — |
| VA2 | A02, then A06 draft | Codex `Solidity/Evm/**` lanes (A02); A01, A03 for A06 |
| VA3 | A05 | — (grows with X lanes; G52 completes it) |
| VU1 | U01, U06 (pins, split targets) | — |
| VU2 | U02, U07 | VU1's U01; VA1's A03 |
| VU3 | U03, U04, U06 (rewrite) | VU1's U01 |
| VU4 | U05, U08 | VU1; VT4 for U08 |

### Waves

| Wave | Parallel lanes | Notes |
|---|---|---|
| A | VA1, VA3, VU1 | Start now beside VX1/VO1/VT1. Independent writes: `Solidity/Theorems.lean` and `scripts/ci/` (VA1), `Bridge/` and `scripts/evm-reference/` (VA3), benchmark scripts and the examples target (VU1). |
| B | VA2, VU2, VU3 | After U01's baseline merges, so speed claims are measured against it. VA2 waits for the Codex Evm lanes. |
| C | VU4 | After VU1; U08 after VT4. |

Peak is three concurrent A/U lanes. Gate new Lean agents on memory as for the
other lanes. File ownership: VA lanes own `Solidity/Theorems.lean`,
`docs/trust.md` and new `scripts/ci/trust-*`; VU lanes own new
`Solidity/Automation/Certificate*`, `Solidity/Automation/Leaf*` and
`scripts/bench/**`; edits to `Calculus/` rules stay with their owners (rule
changes go through [rule-repair.md](../rule-repair.md)). Register new modules
with `scripts/coord-tools/register.sh` and add `docs/module-map/` rows.

## Priority

When lanes compete for VMs, order the work by what users rely on:

1. A02, U01 and A05: cheap, and they make the theorems honest and the
   problems measurable.
2. The T lanes (solc validation) and the U lanes ahead of backfill and the
   later X/O work. The full scope stays; this changes order, not scope.
3. The main chain V07–V17 and X/O continue as before.

## Done when

- A01's closure is published with its size, CI guards its growth, and
  A04's independent re-check passes on the release revision.
- Every public theorem is free of the always-revert disjunct and has a
  nontrivial witness in CI.
- A05 runs in CI; every disagreement is fixed or recorded as a deviation.
- U01's budgets hold on the release revision in both modes, and the two modes
  agree on the whole suite.
- `docs/trust.md` is published with the revision, commands and numbers.

## Handoffs

None yet.
