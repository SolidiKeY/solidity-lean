# V09 compiler-pass components (G24–G31)

Backend pass components over the existing memory compiler
(`Backend/Passes/`), from the v09-compiler-passes lane. Headline results are
parameterised over any `Compilation`/`CompiledVal` with explicit link or
budget premises (`MappedBoundaryLink`, `ReachedMappedLink`, reached-cost
budgets), and controls instantiate them (`LinkedControls.concrete_link`,
`terminal_reflection_inhabited`, the `HeapBoundary` links).

## Components

- Values: `ValueCertificate` (`CompiledVal` success/revert over a saved tail),
  `ValueSequence*`, `SharedPair`, `ValueContext*`, `StatefulValues`
  (`binary`/`unary`: checked, division, modular and power operands),
  `ResolvedMetadata*`.
- Captures: `Capture*`, `CapturedValueStability`, `ReferenceCapture*`,
  `ReferenceObjectCertificate`, `ConditionalReferenceCapture`;
  `RuntimeReturnCapture*` (the P1 V3 primitive-return emitter followed by a
  capture, with `NoAliasPromotion` as a premise).
- Heap and allocation: `HeapBoundary*` (branch-indexed physical heap links),
  `HeapPrefix`, `ReindexedMemory`, `MemoryCompilerSequence`, `Allocating*`,
  `AllocatorPreservation`, `PreservedAllocator*`, `TripleAllocation`.
- Composition: `TripleSuffix`, `TripleFailures`, `TerminalReflection`
  (`compilation_{mapped,triple}_reflect_success`), `Reframed*`.
- Divergence and faults: `DivergenceWitness` (`*_fault_witness_iff`),
  `TailDivergence`, `Spin`, `FaultReached`, `FaultTail`.
- Calls and loops: `MemoryCall*`, `LoopCall*`,
  `LoopCallsBoundary.loops_budgeted_memoryCalls_link`, `LoopAllocatingSuffix`.
- Widths and Booleans: `WidthApplication`, `SignedWidthGuard`,
  `SignedWidthCapture`, `ShortCircuitBoundary`, `FixedBoolean*`,
  `FreshBoolean*`, `EntryReception*`.
- `*Pins` modules hold `#guard_msgs` axiom guards only.

About 26 modules (for example `EntryReception`, `ReachedHash`,
`FreshBoolean*`, `FixedBoolean*`, `HeapApplication`,
`PreservedAllocatorApplication`, `TripleSuffix`, `TripleFailures`) are
observations on the single `CompileExamples` fixture, not general pass
results. `WidthApplication`, `ShortCircuitBoundary`,
`ConditionalReferenceCapture` and `ReferenceCaptureCertificate` have no
in-tree control.

## Not merged

`P8Admission` (conditional on the uninhabited P8a V1 `Producer`, unused),
`CheckedCallBoundary` (restatements of `Source.Progress`, unused),
`ReframedTripleWrongOrder` (exceeds the default heartbeat limit on master) and
its `ReframedTriplePins`, and nine `*Pins` modules whose recorded axiom sets do
not match master (`AxiomPins`, `ContinuationPins`, `FixedBooleanPins`,
`FreshBooleanPins`, `LoopPins`, `MemoryCallPins`, `RevertPins`, `TriplePins`,
`ValueContextPins`).

## Open

The whole-program memory/backend composition (the staged controls show the
whole-program entry refuses the mixed program), G24.03 statement freeze, and
the remaining G25–G31 items in the coverage plan.
