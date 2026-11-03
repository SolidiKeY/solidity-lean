# Routine proof queue — current G21 follow-up

Earlier superseded V2/P10 notes remain preserved in refs/checkpoints/v13-before-c467-rebase and the previous sealed exports. They are not silently re-adopted here.

## G21 readback compatibility glue (H14 cascade; not a discharged proof)

| Module/lemma | Why routine and exact prerequisites |
|---|---|
| Original V13 Solidity.Backend.AbiWorld.ReturnedBytes.memory_call_pushes_zero (source at main85d13e5c7db386fd832391be5f7d04970ad31f22) | Existing theorem statement is unchanged; add/refine the three newly published Compiler.Compilation cases memoryCopy/fixedMemory/copyConstruction. Each has isMemoryCalls=false and contradicts hc. Do not weaken hc or any representation/cost bound, edit producer semantics or increase budgets. This is owned compatibility glue for Terra, not work completed by this checkpoint. |
| Future G21 canonical Error packet entry/body composition | Apply existing BytesReadback.roundtrip after source_error codec equality, retaining size<=lim, free+allocationBytes<=lim and original2<=f. BLOCKED until the owned constructor glue above and V12 FrameLaws Binders/RetBinders interface repair are available. No desired verdict premise or new admission policy is allowed. No proof claimed or continuation scheduled. |
