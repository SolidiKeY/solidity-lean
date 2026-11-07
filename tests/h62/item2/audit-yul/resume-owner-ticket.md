# Resumed baseline import-layer gate ticket

Source: coordinator resume 2026-11-07; baseline 5da4771e63a4278ed53932ac39a032e3d7aea6ed. Route to current coordinator, area producers and H55-G49. No host relay is assumed available and no direct owner message was sent.

`node scripts/check-layers.mjs` exits 1. All graph, checker and allowance files match the baseline exactly (`git diff --exit-code` recorded). The audit helpers remain tests-only and are absent from this graph. This gate is not waived. No theorem vacuity or new premise was established by this import report; no theorem ESCALATE is manufactured.

Remediation choices preserving statements and exclusions: remove unnecessary control/example imports from production module closures; or split the necessary lemmas into minimal modules and redirect imports without changing their statements/definitions. Do not add allowances or change the 95-edge exclusion baseline. Source ownership and coordinator integration remain binding.

Decisive gate output:

```text
901 core modules, 0 reach the elaborator
901 core modules, 0 reach the checked parser adapters
CORE_CLOSURE  Solidity.Roadmap.G49Final.BridgeGoal → Solidity.Roadmap.G49Final.PassCorrectAdapters → Solidity.Lowering.P8b.Frozen
CORE_CLOSURE  Solidity.Yul.Composition.AttemptPhysical → Solidity.Yul.Composition.CatchFunctionPhysical → Solidity.Yul.Composition.RawCatchPhysical → Solidity.Yul.Composition.RecursivePhysical → Solidity.Yul.Composition.FunctionPhysical → Solidity.Yul.Composition.LoopPhysical → Solidity.Yul.Composition.LocalPhysicalControls → Solidity.Yul.Composition.PhysicalControls → Solidity.Yul.Views.OwnedBoolDeclarationControls
CORE_CLOSURE  Solidity.Yul.Composition.AttemptPhysical → Solidity.Yul.Composition.CatchFunctionPhysical → Solidity.Yul.Composition.RawCatchPhysical → Solidity.Yul.Composition.RecursivePhysical → Solidity.Yul.Composition.FunctionPhysical → Solidity.Yul.Composition.LoopPhysical → Solidity.Yul.Composition.LocalPhysicalControls → Solidity.Yul.Composition.LocalPhysicalMemory → Solidity.Yul.Composition.PhysicalMemory → Solidity.Yul.Views.MemoryImages
CORE_CLOSURE  Solidity.Yul.Composition.AttemptPhysical → Solidity.Yul.Composition.CatchFunctionPhysical → Solidity.Yul.Composition.RawCatchPhysical → Solidity.Yul.Composition.RecursivePhysical → Solidity.Yul.Composition.FunctionPhysical → Solidity.Yul.Composition.LoopPhysical → Solidity.Yul.Composition.LocalPhysicalControls → Solidity.Yul.Composition.LocalPhysicalMemory → Solidity.Yul.Composition.PhysicalMemory → Solidity.Yul.Views.MemoryControls
CORE_CLOSURE  Solidity.Yul.Composition.AttemptPhysical → Solidity.Yul.Composition.CatchFunctionPhysical → Solidity.Yul.Composition.RawCatchPhysical → Solidity.Yul.Composition.RecursivePhysical → Solidity.Yul.Composition.FunctionPhysical → Solidity.Yul.Composition.LoopPhysical → Solidity.Yul.Composition.LocalPhysicalControls → Solidity.Yul.Composition.PhysicalControls → Solidity.Yul.Composition.PhysicalFrames → Solidity.Yul.Views.OwnedBoolFrame
CORE_CLOSURE  Solidity.Yul.Composition.AttemptPhysical → Solidity.Yul.Composition.CatchFunctionPhysical → Solidity.Yul.Composition.RawCatchPhysical → Solidity.Yul.Composition.RecursivePhysical → Solidity.Yul.Composition.FunctionPhysical → Solidity.Yul.Composition.LoopPhysical → Solidity.Yul.Composition.LocalPhysicalControls → Solidity.Yul.Composition.PhysicalControls → Solidity.Yul.Composition.PhysicalBytes → Solidity.Yul.Views.Bytes
CORE_CLOSURE  Solidity.Yul.Composition.AttemptPhysical → Solidity.Yul.Composition.CatchFunctionPhysical → Solidity.Yul.Composition.RawCatchPhysical → Solidity.Yul.Composition.RecursivePhysical → Solidity.Yul.Composition.FunctionPhysical → Solidity.Yul.Composition.LoopPhysical → Solidity.Yul.Composition.LocalPhysicalControls → Solidity.Yul.Composition.PhysicalControls → Solidity.Yul.Composition.PhysicalFrames → Solidity.Yul.Composition.Interface → Solidity.Backend.Environment.ByteConstants
CORE_CLOSURE  Solidity.Yul.Composition.Controls → Solidity.Source.StateExamples
CORE_CLOSURE  Solidity.Yul.Composition.MonetaryLifecycleControls → Solidity.Source.StateExamples
CORE_CLOSURE  Solidity.Yul.Composition.P6FrameControls → Solidity.Yul.Composition.P6FrameCorrectness → Solidity.Backend.MemoryOps.PhysicalFrameImage
CORE_CLOSURE  Solidity.Yul.Composition.SourceCatchBinding → Solidity.Lowering.Readonly.SourceTryEffects
CORE_CLOSURE  Solidity.Yul.Composition.SourceCatchBinding → Solidity.Source.FailureRuntimeControls
901 core modules, 12 new core → non-core edges (95 pinned allowances)
```
