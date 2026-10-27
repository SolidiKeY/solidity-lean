# Cloud task 10 integration

Integrates task 10's committed handoff `2c3eeed45d0ad83b5a999ecb465271ba2bdb337e`
with master `dc044e71e709276d129b17d3350b0419bb6055f1`, which includes
tasks 01–09 at `a7a35aa5` and the concurrent intrinsic getter-plan changes.
The cloud executor was idle and its working tree was clean at collection.

## Scope and evidence

The lane repairs raw ABI vector adaptation, exact revert/panic observations,
named custom-error operands, typed aggregate custom errors and compound ABI
metadata. Historical results remain historical: the final lane inventory has
189 agreements, 91 failures and 157 blocks, including 248 retained reports.
Its 189 fresh agreements cover 375 pipeline executions and 1,486 observations;
these counts do not mean all 437 fixtures were rerun on this integration.
Original upstream source and expected observation bytes, and the lane evidence
files, are preserved.

## Merge and review

- Retain strict canonical ABI declaration resolution from tasks 01–09. Range
  rows are selected by resolved model identity, or constructor source name,
  rather than by nominal source-signature spelling.
- Preserve scalar address canonicality, scalar enum bounds, transient reset at
  transaction entry, rollback, resource diagnostics and completed-prefix data.
- Raw ABI inputs use task 10's decoder/canonicality path rather than scalar
  argument lists. Nominal ranges not represented by a full primitive byte-width
  range are explicitly refused, including array element ranges. No expected
  outcome chooses decoder admission. Controls check canonical raw uint8 input
  and the exact nominal-enum refusal in both compiler pipelines.
- Memory-returning function dispatch now retains Panic(0x51) under exact external
  entry observation, matching scalar function dispatch. Positive and negative
  controls distinguish the actual bytes from empty data and the wrong code.
  Ordinary calculus entry behavior remains covered by the earlier lane controls.
- Split source-admission setup and helper/deployment preparation out of the
  large import command after a combined elaboration exceeded its existing
  200,000-heartbeat limit. No limit was raised and no representation changed.
- Preserve all three evaluation-order override fields, including modifier-frame
  semantics; an explicit legacy override control pins the flag.
- Extend two earlier abstract-failure controls with exact Panic(0x11) overflow
  and Panic(0x32) discarded-reference bounds bytes. Existing failure flags,
  returned values and rollback assertions remain unchanged; both pipelines pass.
- Refresh the array-length certificate's arithmetic snapshot from the merged
  normalizer: it now reduces directly to `.tt`. The formula, verdicts, validity
  equivalences and definitional `change` check are unchanged. Per-file and full
  build checks pass; both reviewers confirmed that no premise was weakened.
- Preserve current documentation pruning and earlier lane handoffs; append only
  the new task 10 sections. Finder and skeptic review found the range identity
  and memory-dispatch issues above before final integration validation.

## Validation

Per-file MCP diagnostics pass Contract, Import, Upstream, Replay and EnumAbiRanges.
Layering, reachability, strict automation and the trust inventory pass (240
inventoried implementation/recovery sites, zero findings).

The documentation path audit fails with 32 references, including historical
references inside imported evidence and pre-existing absent vendor/test paths.
The failure is retained explicitly; original evidence is not rewritten.

The 27-file serial lane regression set passes, including an isolated successful
retry after one process exit 135 and per-file MCP checks after extending two
panic-data controls. Compiler-backed adapter/importer/getter Node tests pass
49/49 after the dependencies finished rebuilding. The initial Node run's sole
failure was an out-of-date dependency under its no-build runner.

The frozen corpus check passes without updating verdicts or generated pins.
The final `run-lean.sh` passes the default build (684 jobs), SolkeyTestSuite
(259 jobs), and the explicit frozen SolKey sort check (377 taclets, all 131
read-bearing annotations match).

The earlier broad run found the old two-field evaluation-order quotation and
the stale array normalization snapshot. Both corrections were checked per file
and independently reviewed before the successful final full run. The 32 failing
documentation references remain a separate, explicitly failing audit.
