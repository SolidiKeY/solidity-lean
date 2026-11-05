# Routine handoff status

## NJ1 — completed for the fixed fixture

The exact original decoder equality, packet and compilation/source/model
endpoints are now kernel-proved in the actual module
`SolidityBridge.Yul.StructuredSwitchJsonKernelAttachment`, namespace
`SolidityBridge.Yul.StructuredSwitchJson.KernelControls`:

- `raw_nested_parsed`: `blockAux 20 ast = .ok tree`, with no parser premise.
- `raw_nested_packet`: the original `Packet [] 20 16 (Controls.fixture "1")`.
- `raw_nested_compiles`: exact `checkCompile` equality returning that packet.
- `raw_nested_source`: actual closed-word execution at horizon16.
- `raw_nested_low_fuel`: exact compiler horizon2 refusal for the same fixture.
- `raw_nested_model`: arbitrary mathematical machine/caller, with the real
  represented-stack premise retained.

Bounds20/16, dirty literal, fixture and expected prefix21/999/42/17 are unchanged.
Earlier failed attempts are preserved as evidence. No NJ1 proof remains pending;
this closes only the fixed-fixture obligation, not generic JSON correctness,
Solidity admission, Source/G24/native adequacy or the full original lane.
No earlier excluded Terra tasks or completed work are restored here.


<!-- Preserved V17 lane pending statements; not proof evidence. -->


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


## Return-tail scalar observation corollary

Module: Solidity/Lowering/G19/ReturnTailControls.lean
Lemma: scalar_observation_agrees. Routine: rewrite the two existing complete
scalar observation endpoints; preserve the outcome/selector and every caller field.

```lean
theorem scalar_observation_agrees (pipeline : Roadmap.Pipeline) (choice : Bool) :
    sourceObs pipeline choice = observeTarget (code tci tca ti ta) choice
```

Draft only; no placeholder declaration or completed coverage claim.
Soundness, captured-selector proof and alias negatives stay with Sol.


## Immediate-return while false selector

Module: Solidity/Lowering/G19/WhileReturnControls.lean
Lemma: captured_false. Routine: map the already proved no target endpoint,
then reduce the fresh Boolean head. Preserve the complete target outcome.

```lean
theorem captured_false :
    ((AssignmentReturnFlag.code P.mapping (.there .here) .here rfl rfl : Prog P.C _ _).run P.target).map
      (fun out => TEnv.get .here out.st.env) = .ok false
```

Draft only; no placeholder declaration or completed coverage claim.
The Source loop proof and mapped transport stay with Sol.


## Mapped condition false-branch adapter

Module: Solidity/Backend/StructuredFlow/MappedBranch.lean (new, not created).
Lemma: false_run. Routine: append the fresh-cell load to the checked emitter,
combine run_append_ok/run_exact/upd_same with entry.vals and the initial false
read, then apply the published Branch.false_run. The true arm's exact pending
skip and complete compiler integration remain with Sol.

```lean
namespace Solidity.Backend.StructuredFlow.MappedBranch
open Solidity.Evm Solidity.Lowering.V07
open Solidity.Lowering.G19.AssignmentReturnFlag

def condition {srcΓ : Source.RCtx} {Γ : Ctx} (b : Nat) (m : ContextMap srcΓ Γ)
    (i a : Source.Idx srcΓ .bool) (hi : (m.slot i).1 = .val .bool)
    (ha : (m.slot a).1 = .val .bool) : List Instr :=
  MappedCondition.emit b m i a hi ha ++ [.mload (cell (b + Γ.length))]

theorem false_run {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    {L b : Nat} {F : Frag Γ} {caller : State C Γ} {machine : Machine}
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (entry : Sim C L b F caller machine)
    (read : TEnv.get (boolSlot m a ha) caller.env = false) (left right : List Instr) :
    run (Branch.emit (condition b m i a hi ha) left right) machine =
      run right (MappedCondition.after b m i a hi ha machine)

end Solidity.Backend.StructuredFlow.MappedBranch
```

Draft statement only, not elaborated or counted as proof evidence. Import the
published BranchSelector and the new checked MappedCondition; do not define a
new representation or assume the condition's run.


## MappedBranch interface now implemented

The previously drafted Solidity/Backend/StructuredFlow/MappedBranch.lean
condition signature is now implemented unchanged. code_exact, condition_run,
condition_represented, true_run, true_pending_skip, admitted and correct are
proved by Sol with inhabited compiler/exit controls. The earlier false_run
statement remains the routine Terra item, unimplemented and not counted as
proof evidence. Use condition_represented plus the initial false-read fact and
published Branch.false_run; do not copy condition into a parallel module.
The prior draft is preserved verbatim as historical handoff context.


## ConditionalSourceCompiler source field projection

- Module: Solidity/Backend/StructuredFlow/ConditionalSourceCompilerControls.lean
- Lemma: source_fields (draft below, unimplemented and not evidence).
- Routine: rewrite joined.1, split flag, reduce the three local reads. Do not change joined or any premise. Keep MappedBranch.false_run with its existing Terra owner.

```lean
namespace Solidity.Backend.StructuredFlow.ConditionalSourceCompiler.Controls
open Solidity.Lowering.G19
open Source.SemanticsExamples (G0 F0)
theorem source_fields (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag : Bool) :
    (match (Source.execS (G0 pipeline) F0 (fuel+4) 0 none (R := []) (M := false)
      (ConditionalStatement.statement (k := ⟨false,false⟩) sci sca sci .here sca sci)
      (source flag).1).run (.nil,(source flag).2) with
    | (.ok (.normal ls),_) => [(ls.get sca).key,(ls.get sci).key,(ls.get .here).key]
    | _ => []) = [some (if flag then 1 else 0),some 0,some 0]
end Solidity.Backend.StructuredFlow.ConditionalSourceCompiler.Controls
```


## ConditionalSequenceCompiler Source field projection

- Module: Solidity/Backend/StructuredFlow/ConditionalSequenceCompilerControls.lean
- Lemma: source_sequence_fields (draft only, unimplemented and not proof evidence).
- Routine: rewrite joined.1, split flag and reduce all three reached local reads. Keep the Source/typed/EVM statements and13 premises unchanged; the hard composition is already proved. Do not duplicate the older prefix source_fields or MappedBranch.false_run items.

```lean
namespace Solidity.Backend.StructuredFlow.ConditionalSequenceCompiler.Controls
open Solidity.Lowering.G19
open Source.SemanticsExamples (G0 F0)
open ConditionalSourceCompiler.Controls (source sci sca)
theorem source_sequence_fields (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag : Bool) :
    (match (Source.execS (G0 pipeline) F0 (fuel+6) 0 none (R := []) (M := false)
      (ConditionalSequence.statement (k := ⟨false,false⟩) sci sca sci .here sca sci sca sci)
      (source flag).1).run (.nil,(source flag).2) with
    | (.ok (.normal ls),_) => [(ls.get sca).key,(ls.get sci).key,(ls.get .here).key]
    | _ => []) = [some 0,some 0,some 0]
end Solidity.Backend.StructuredFlow.ConditionalSequenceCompiler.Controls
```

## WhileContinueCompiler routine fragment closure (not proved)

Module: `Solidity/Backend/StructuredFlow/WhileContinueCompiler.lean`.
Lemma: `all_readable`. Routine finite fragment/list bookkeeping for the existing primitive-only reset body; use existing Frag/inFragP definitions. This statement is a draft only, has not been compiled, and does not discharge correct.checked. Do not change the checker or infer a primitive-local refusal from alias flags.

```lean
theorem all_readable {srcΓ : Solidity.Source.RCtx} {C : Solidity.Contract} {Γ : Solidity.Ctx}
    (m : Solidity.Lowering.V07.ContextMap srcΓ Γ) (i a : Solidity.Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool) :
    Solidity.Evm.inFragP (Solidity.Evm.Frag.init Γ)
      (Solidity.Lowering.G19.AssignmentWhileReset.code (C := C) m i a hi ha) =
      some (Solidity.Evm.Frag.init Γ)
```
