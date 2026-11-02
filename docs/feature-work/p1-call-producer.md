# P1-CALL: value-returning ordinary calls (V3 producer)

Owning modules: `Backend/InternalFlow/RuntimeFrameV3CallProducer.lean` and its
`…Controls.lean` (lane compiler10/memory-reference-structs). Scope: primitive
`.val p r (some destination)` calls only; tuple and reference returns are not
claimed. No interface, evaluator, scratch refusal or profile changes.

The plan captures the caller, runs the checked call, copies the reached
destination to the private cell `lo-1`, restores the caller and then exports
that result. The typed physical admission states representation, workspace,
arena, cursor and allocation-capacity conditions; it mentions neither `Entry`
nor source outcomes, so it is not an outcome whitelist.

- `bare_revert`: every represented `Entry` with an actual bare-reverting call
  run reverts on the target (capture/failure transport absorbs the suffix).
- `returns : InterfaceV1.ReturnClaim`, under the static `NoAliasPromotion`
  condition: destination-excepted local agreement is derived from the call
  run; old reference identities are carried by `BaseExtends`, not by assuming
  unchanged heap contents.
- `coverage`: `Entry` for every identical admitted caller, map, machine,
  frame and cursor. `make` assembles the frozen `InterfaceV3.PendingCallProducer`
  from `coverage`, `returns` and `bare_revert`; its other inputs are the
  `AdmissionAgreement` proof `hprof` for an abstract `approved`, the static
  alias flags and real same-domain success and revert witnesses.
- Controls: one array-reading call where index 0 returns 7 and index 2 is an
  actual out-of-bounds bare revert gives exact V3 success and revert
  witnesses at the same admission and code. `Controls.producer` applies
  `make` to them. A represented machine whose arena does not fit is refused.

Limits: `approved` and its provenance stay parameters (V12 owns
approved-profile provenance). The fixture has zero heap-allocation cost and
no storage-alias locals. A source that never bare-reverts cannot use this
dual-outcome class, and a literal `.revert` body is still selector-refused.
The lane's executable test `tests/runtime-frame/ValueCallEvaluation.lean`
was not integrated. Lane full gates did not run because of the TermSize
blocker (see [G37.03/P4 dispatch](roadmap-g37-dispatch-p4.md)).
