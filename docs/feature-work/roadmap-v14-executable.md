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
