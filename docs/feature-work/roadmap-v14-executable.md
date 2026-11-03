# V14 executable consumers: constructor argument preparation

This checkpoint is an independent G44.01 leaf. It does not close G44, G43,
physical frame lowering, source admission or executable-byte correspondence.
Published development base: `312ed47a9ff23fd6b0e9f0206770e8deac0246e2`.
Original V14 frozen base and helper history remain preserved separately.

## Typed interfaces

- `Solidity.Backend.Executable.ConstructorLocalArguments.sourceArgs` builds
  existing `Source.RConvArgs` from two typed integer locals in declaration
  order. Identity-conversion admission stays explicit.
- `source_actual` derives actual `Source.evalConvArgs` at `fuel+3`, returns
  those values and preserves the complete caller locals/state. Integer widths,
  bounds, populated caller tail, heap, events and journal remain in the statement.
- `targetArgs` builds existing intrinsic `Args`; `target_actual` derives actual
  `Args.evalT` from initial typed local reads. The last argument is innermost:
  Source order `[a,b]` corresponds to intrinsic frame `[b,a]`.
- `ConstructorArgumentObservations.successful_numeric_agreement` derives
  successful numeric projection agreement from these executions and published
  V07 `integer_observe`. `Source.Halt` and `THalt` remain different carriers;
  `toOption` here does not assert error equivalence or replace full observations.
- `ConstructorArgumentObservations.Checks.inhabited` exercises uint8(255) and
  int16(-7), both Source pipelines, exact zero-budget timeout, populated old
  Source memory and target caller aliases, and a wrong-order negative control.
  Its unused fixture hash/ledger is not pinned EVM behavior.

## Evidence and reviews

Per-file and focused import builds run serially under the existing writer
lease, Lean `-j1`, 12 GiB/no-swap cgroup and unchanged 180-second wall limit.
The current-source import build passed (78 jobs, 124.14 seconds). The generic
Source argument proof takes about 92–96 seconds; this checking cost is explicit.
Automation-first attempts and all raw failures are retained outside the tree.
Scoped axiom guards require only propext, Classical.choice and Quot.sound.

Independent read-only finder and skeptic inspected actual statements. The finder
caught the original equal-width fixture wording; the fixture now uses distinct
8/16-bit widths. Their reviews do not establish global integration or EVM execution.
Final combined/import-closure gates are reported separately, with real failures
and pending checks retained. Prior docs/full/touched failures are not waived.

## Remaining obligations

G44.01 still needs complete constructor selection, argument binding, inheritance
initializers/body lowering and source/frame preservation over the admitted profile.
Published P1 V3 CALL/THUNK/REVERT/recursive producers are available; this local
argument leaf uses none of their Pending structures. P1-PROFILE remains an
AdmissionAgreement obligation, not inferred from a producer fixture. P8a-indexed
coverage is not claimed. G43 joint payment/world/history and failure ordering,
G44.02/.03 general artifact/world composition, G45.01/.02 and G45.06 executable
composition remain partial. G36.03 awaits V12 G37 effectful horizon/divergence.
G45.03 is reassigned; G45.04/.05 are master-owned. Earlier Backfill A/B results
remain scoped partial checkpoints.

Eval-dependent G18.04/.05 modules remain on preserved helper bb5c88a8, awaiting
VY5 under H16. The five-file request and dependent inventory are sealed at
`/workspace/v14-master-rebase-artifacts/vy5-eval-request/`; its CalldataLayout
prerequisite is explicit. This checkpoint changes no Source implementation.

## Inherited constructor binding consumer

`ConstructorBaseArguments` adds actual `Source.giveArgs` transport over arbitrary
constructor-local indices. `evaluated` derives the pure local argument run from
initial reads and existing identity-conversion judgments. `bound` then derives
the appended base frame, real `Vals.onto` reversal and unchanged complete state.
Its other premises are actual program metadata (base parameter context) and
absence from the accumulated frames, not a desired execution or simulation.
`lookup_appended` derives the frame subsequently read by `ctorLocalsOf`.
`already_given` proves the existing priority branch skips arbitrary argument
execution, independently of argument effects or budget.

`ConstructorBaseArgumentControls` uses real Base/Derived declarations and
constructor contexts computed from those declarations. Its Program, empty bodies
and baseArgs are manually supplied typed fixtures: this is not a proof of
elaboration, Program.Derived, WellTyped or admitted SourceSpec provenance.
The native controls exercise actual giveArgs, lookup and empty-body construct
in both pipelines, populated old heap/aliases, zero-budget timeout, already-given
priority and exact rejection of deliberately uncertified arity metadata.
That structural `.stuck` refusal is not presented as an admitted-program halt.

Six additional scoped guards require only standard axioms. Per-file/focused
Source checks and automation attempts are recorded with raw failures. Prior
full/import-closure timeout remains unresolved; no unchanged failed heavy gate
is repeated or relabelled passed. No EVM/compiler/World installation claim follows.

On 2026-11-03 the coordinator moved G45.01/.02/.06 to
solidity-parallel-20261103/executable-bytecode (`Backend/Selection/**`). Original
partials remain at 22a1b53ecd0d50272d26e2758bafaead52bf247d for relay; no new G45
implementation was added here. G43/P14, G44.01-.03, G18.04/.05, S02-CD-AGG and
G36.03 remain with V14. Earlier G45 completion obligations are integration
obligations against that producer, not authorization to duplicate its work.

## Argument failure before base-frame installation

`ConstructorArgumentFailure.run_inner` is a concrete native producer: the first
argument writes the bitwise complement of uint8(255), changing the inner local
to zero; checked negation of int16(-32768) in the next argument then returns the
original arithmetic-panic bytes. It runs at the existing Source argument
budget 4, without changing any prior fixture or process/proof budget.

`transport_failure` composes a real failed evalConvArgs run with giveArgs: it
preserves the exact halt and returned Source state, dropping only inner locals.
It does not roll back argument effects on state. The concrete `giveArgs_failed`
discharges that native-run premise with `run_inner`; no simulation oracle or
assumed source/body correctness is introduced. Native constructor controls show
failure propagation in both pipelines, existing-base priority, inner-versus-outer
local separation and arithmetic-versus-division-panic byte separation. Program
fixtures remain manually supplied, without canonical elaboration or profile
provenance. No failed CREATE/account/World rollback or EVM behavior is proved.
Four further scoped guards require only standard axioms. Full/global validation
and the original joint payment/world obligations remain open.
