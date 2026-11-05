# V09 compiler-pass components

| Modules | Purpose |
|---|---|
| `Backend/Passes/ValueCertificate.lean`, `Backend/Passes/ValueSequence.lean`, `Backend/Passes/SharedPair.lean`, `Backend/Passes/StatefulValues.lean` | `CompiledVal` success/revert over a saved tail; ordered value pairs; state-dependent operands ([V09](../feature-work/roadmap-v09-compiler-passes.md)). |
| `Backend/Passes/CaptureCases.lean`, `Backend/Passes/CapturedValueStability.lean`, `Backend/Passes/RuntimeReturnCapture.lean` | Value and reference captures; P1 V3 primitive return followed by a capture. |
| `Backend/Passes/HeapBoundary.lean`, `Backend/Passes/HeapPrefix.lean`, `Backend/Passes/ReindexedMemory.lean`, `Backend/Passes/MemoryCompilerSequence.lean` | Branch-indexed physical heap links; `compileProg` join. |
| `Backend/Passes/TerminalReflection.lean`, `Backend/Passes/TripleSuffix.lean`, `Backend/Passes/TripleFailures.lean` | Three-stage composition; success reflection. |
| `Backend/Passes/DivergenceWitness.lean`, `Backend/Passes/TailDivergence.lean`, `Backend/Passes/Spin.lean`, `Backend/Passes/FaultReached.lean`, `Backend/Passes/FaultTail.lean` | Divergence witnesses; reached faults. |
| `Backend/Passes/LoopCallsBoundary.lean`, `Backend/Passes/LoopAllocatingSuffix.lean` | Loop-to-call budgeted links. |
| `Backend/Passes/WidthApplication.lean`, `Backend/Passes/SignedWidthGuard.lean`, `Backend/Passes/ShortCircuitBoundary.lean`, `Backend/Passes/EntryReception.lean` | Width masks, signed guards, short-circuit Booleans, ABI word admission (fixture). |
| `Backend/Passes/AssignmentSubtractionControls.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/AssignmentSubtractionPass.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/AssignmentSubtractionPins.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/CapturedReadback.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/ConditionalReferenceInput.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/QueueCompletionControls.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/QueueCompletionPins.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/ReferenceCallArgumentFailure.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/ReferenceCallArgumentPins.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/ReferenceCallArgumentPrefix.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/ReferenceCallCaptureFailure.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/ReferenceCallCaptureFailureControls.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/ReferenceCallCaptureFailurePins.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/ReferenceCallReadback.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/ReferenceCallReadbackControls.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/ReferenceCallReadbackPins.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/RuntimeCaptureReflection.lean` | Typed compiler transport or control proof component. |
| `Backend/Passes/ShortCircuitWitness.lean` | Typed compiler transport or control proof component. |
| Other `Backend/Passes/*Controls.lean` and `*Pins.lean` | Controls on the `CompileExamples` fixture; axiom guards. |
