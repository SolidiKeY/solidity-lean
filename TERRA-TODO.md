# VY4 routine queue

## Native returndata consumer

- Module `Bridge/SolidityBridge/YulWorld/Returndata.lean`: `step_exact` is the first projection of `CopyInput.agreement`; same Site/valid/fuel. Routine projection.
- Same module: `continuation_exact` rewrites actual `FrozenV1.api.continuation.x_return_copy` using `step_exact`, yielding `EVM.X (fuel+2) valid site.state = EVM.X (fuel+1) valid input.next`. Routine frozen-API composition.
- Native world/buffer projection corollaries follow agreement. Do not strengthen to Source, compiler-origin, transaction, padding/readback or untouched-tail adequacy.

These are requested statements, not admitted declarations or axioms.
