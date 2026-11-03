# P8b frozen consumer interface

Signatures and obligation records only; no production `SourceSpec`, emitter,
`Lowering` or `Cert` inhabitant is supplied. The signatures are frozen.

- `Lowering/P8b/Frozen.lean` (version 1): `SourceInput` wraps the existing G01
  `Roadmap.SourceSpec`; `Admission` is exactly `SourceSpec.Admitted`;
  `Producer` extends the existing G01 `Lowering` unchanged (`lower`, `pass`,
  `dom`, `agrees`, full `cert`). Every field is an undischarged obligation.
- `Lowering/P8b/P8aInterface.lean` (version 1): `SourceProducer` is the exact
  `Lowering.P8.P8a.Producer`; `ProducerOutput` is `Frozen.Producer` at the same
  `S` (`P8a.Spec` is `SourceSpec` by `abbrev`); `CertifiedInput` records a real
  `checkedFrontend.produce input = some (resolved, certificate)` equation.
- `Lowering/P8b/Domain.lean`: structural `pass`/`lower`/`dom`/`agrees` for a
  provided total emitter, environment transport through `SessionEnv`, and
  `assemble` of a `Lowering` from a separately supplied `Cert`.
  `no_certificate_of_wrong_completion` shows `dom`/`agrees` cannot produce a
  `Cert`: a real source completion the emitted world never reaches refutes it.
- `Lowering/P8b/Controls.lean`: on the G07 toy models (`toySource`,
  `toyIntrinsic`; not production), `identityCert` with `success` and `failure`
  completions and `identityLowering`, a wrong emitter `badEmit` with
  `bad_agrees` but `bad_no_certificate`, and `loop_no_failure` divergence only
  under no-failure admissibility. `identityCert` is weak evidence: source and
  intrinsic share the toy language, `Admissible` is `True` and the session maps
  are `id`.

Limits: P8a is itself signatures only (see
[P8a frozen interface](p8-admission.md#frozen-interface), including the open
[`FailureProjection.points_ofPoints` conflict](p8-admission.md#failure-projection-conflict)). No concrete P8a producer,
operational reference, emitter or semantic certificate exists; G18.02/G18.03
and the original G48–G51 obligations remain open.
