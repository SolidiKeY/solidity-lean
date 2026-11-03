
# Routine G19 slot projection (draft statement only)

Module: Solidity.Lowering.G19.AssignmentReturnFlag. boolSlot is a projection
from the actual V07 ContextMap, never an independently chosen target index.
The Source semantic proof and concrete mixed controls stay with Sol.

```lean
theorem boolSlot_spec {srcΓ : Source.RCtx} {Γ : Ctx}
    (m : ContextMap srcΓ Γ) (i : Source.Idx srcΓ .bool)
    (h : (m.slot i).1 = .val .bool) :
    m.slot i = ⟨.val .bool, boolSlot m i h⟩
```

Why routine: dependent-pair projection/cast equality, no run/profile/world or
preservation claim. No placeholder proof exists. Standard automation attempts
are retained; retry after introducing binders, then pair/equality cases if
needed. Keep only the winning proof. After checking, a wrapper may discharge
correct's map_i/map_a; do not count this universal obligation closed beforehand.
Concrete controls close both by rfl. Do not edit V07 or reserved Source modules.


## Conditional statement scalar observation corollary

Module: Solidity/Lowering/G19/ConditionalStatementControls.lean
Lemma: scalar_observation_agrees. Why routine: rewrite the two already proved
source_observation/target_observation endpoints; no new soundness argument.
Use existing module opens and preserve both pipeline/choice parameters.

```lean
theorem scalar_observation_agrees (pipeline : Roadmap.Pipeline) (choice : Bool) :
    sourceObs pipeline choice = observeTarget (code tci tca ti ta tj tb) choice
```

Draft statement only, not a compiled declaration or completed coverage row.
Do not change either observation list, expected result or producer interface.


## Conditional sequence scalar observation corollary

Module: Solidity/Lowering/G19/ConditionalSequenceControls.lean
Lemma: scalar_observation_agrees. Routine: rewrite the existing
source_observation and target_observation endpoints, preserving every field.

```lean
theorem scalar_observation_agrees (pipeline : Roadmap.Pipeline) (choice : Bool) :
    sourceObs pipeline choice = observeTarget (code tci tca ti ta tj tb tb ti) choice
```

Draft only; no placeholder declaration or completed coverage claim.
Soundness, generic reached-context proof and negative controls stay with Sol.
