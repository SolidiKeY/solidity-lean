
### P8 Producer merge (H57, H60)

| Module | Purpose |
|---|---|
| `Lowering/P8/PlanWitness.lean` | Inhabitant `planProducer` of the unchanged frozen `P8a.Producer` (H60) over a G07-model source whose resources carry full EVM failure plans, plus the P8b `planLowering`; model reference, not actual-Source adequacy. |
| `Lowering/P8b/Merged.lean` | Merged P8a+P8b `Producer` (H57): additive pairing of both frozen types at one `S`, projections, `nonempty_iff`, H24 variant. |
| `Lowering/P8b/MergedControls.lean` | Merged witness (receipt, execution, failing plan, lowered success) and negative controls (Nat-resource toy, wrong reference, empty source, wrong emitter). |
