import Solidity.Lowering.G19.ConditionalSequence
import Solidity.Lowering.V07.ConditionalControls

namespace Solidity.Lowering.G19.ConditionalSequence.Controls
open Solidity.Lowering.V07
open Source.SemanticsExamples
open P12Controls (C E BindingRel)
open ConditionalControls (SrcCtx TgtCtx source target mapping initial sci sca si sa sj sb tci tca ti ta tj tb)

theorem mapped (pipeline : Roadmap.Pipeline) (fuel : Nat) (choice : Bool) :
    (Source.execS (MixedAssignmentControls.globals pipeline) F0 (fuel+6) 0 none
      (R := []) (M := false) (statement (k := ⟨false,false⟩) sci sca si sa sj sb sb si)
      (source choice).1).run (.nil,(source choice).2) =
      (.ok (Source.Out.normal (sourceAfter (source choice) sci choice si sa sj sb sb si).1),
        (.nil,(source choice).2)) ∧
    (code tci tca ti ta tj tb tb ti).run (target choice) =
      .ok ⟨targetAfter (target choice) tci choice ti ta tj tb tb ti,List.prefix_refl _⟩ ∧
    mapping.Related BindingRel (sourceAfter (source choice) sci choice si sa sj sb sb si).1
      (targetAfter (target choice) tci choice ti ta tj tb tb ti).env := by
  rcases correct (MixedAssignmentControls.globals pipeline) F0 fuel 0 none
    (returns := []) (M := false) (k := ⟨false,false⟩)
    (source choice) (target choice) mapping BindingRel (initial choice) P12Controls.bool_reflect
    sci sca si sa sj sb sb si tci tca ti ta tj tb tb ti rfl rfl rfl rfl rfl rfl rfl rfl with ⟨src,tgt,related,_⟩
  exact ⟨src,tgt,related⟩

def sourceObs (pipeline : Roadmap.Pipeline) (choice : Bool) : List (Option Int) :=
  match (Source.execS (MixedAssignmentControls.globals pipeline) F0 10 0 none
      (R := []) (M := false) (statement (k := ⟨false,false⟩) sci sca si sa sj sb sb si)
      (source choice).1).run (.nil,(source choice).2) with
  | (.ok (.normal ls),_) => [(ls.get sci).key,(ls.get sca).key,(ls.get sb).key,(ls.get sa).key,(ls.get si).key]
  | _ => []

def observeTarget (program : Prog C TgtCtx TgtCtx) (choice : Bool) : List (Option Int) :=
  match program.run (target choice) with
  | .ok out => [some (if TEnv.get tci out.st.env = true then 1 else 0),
      some (if TEnv.get tca out.st.env = true then 1 else 0),PrimTy.num? (TEnv.get tb out.st.env),
      PrimTy.num? (TEnv.get ta out.st.env),PrimTy.num? (TEnv.get ti out.st.env)]
  | _ => []

theorem source_observation (pipeline : Roadmap.Pipeline) (choice : Bool) :
    sourceObs pipeline choice = if choice then [some 1,some 1,some 7,some 7,some 7]
      else [some 0,some 0,some 3,some 11,some 3] := by
  unfold sourceObs
  rw [(mapped pipeline 4 choice).1]
  cases choice <;> rfl

theorem target_observation (choice : Bool) :
    observeTarget (code tci tca ti ta tj tb tb ti) choice =
      if choice then [some 1,some 1,some 7,some 7,some 7]
      else [some 0,some 0,some 3,some 11,some 3] := by
  unfold observeTarget
  rw [(mapped .legacy 0 choice).2.1]
  cases choice <;> rfl

theorem wrong_scope_index_refused :
    observeTarget (code tci tca ti ta tj tb tb tb) false ≠ observeTarget (code tci tca ti ta tj tb tb ti) false := by
  unfold observeTarget
  rw [target_run (target false) tci tca false ti ta tj tb tb tb rfl,
    target_run (target false) tci tca false ti ta tj tb tb ti rfl]
  change [some 0,some 0,some 11,some 11,some 3] ≠ ([some 0,some 0,some 3,some 11,some 3] : List (Option Int))
  decide

/-- Numeric branches followed by a Boolean caller write. -/
def heterogeneousStatement : Source.RStmt E [] false ⟨false,false⟩ ConditionalControls.BSrcCtx ConditionalControls.BSrcCtx :=
  statement (.there .here) (.there (.there .here))
    (.there (.there (.there (.there .here)))) (.there (.there (.there .here)))
    (.there (.there (.there .here))) (.there (.there (.there (.there .here))))
    .here (.there .here)
def heterogeneousCode : Prog C ConditionalControls.BTgtCtx ConditionalControls.BTgtCtx :=
  code (.there .here) (.there (.there .here))
    (.there (.there (.there (.there .here)))) (.there (.there (.there .here)))
    (.there (.there (.there .here))) (.there (.there (.there (.there .here))))
    .here (.there .here)
def heterogeneousSource : Source.EMState E ConditionalControls.BSrcCtx :=
  sourceAfter ConditionalControls.bsource (.there .here) true
    (.there (.there (.there (.there .here)))) (.there (.there (.there .here)))
    (.there (.there (.there .here))) (.there (.there (.there (.there .here))))
    .here (.there .here)
def heterogeneousTarget : State C ConditionalControls.BTgtCtx :=
  targetAfter ConditionalControls.btarget (.there .here) true
    (.there (.there (.there (.there .here)))) (.there (.there (.there .here)))
    (.there (.there (.there .here))) (.there (.there (.there (.there .here))))
    .here (.there .here)

theorem heterogeneous_reached (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    (Source.execS (MixedAssignmentControls.globals pipeline) F0 (fuel+6) 0 none
      heterogeneousStatement ConditionalControls.bsource.1).run (.nil,ConditionalControls.bsource.2) =
      (.ok (Source.Out.normal heterogeneousSource.1),(.nil,heterogeneousSource.2)) ∧
    heterogeneousCode.run ConditionalControls.btarget = .ok ⟨heterogeneousTarget,List.prefix_refl _⟩ ∧
    ConditionalControls.bmapping.Related BindingRel heterogeneousSource.1 heterogeneousTarget.env := by
  rcases correct (MixedAssignmentControls.globals pipeline) F0 fuel 0 none
    (returns := []) (M := false) (k := ⟨false,false⟩)
    ConditionalControls.bsource ConditionalControls.btarget ConditionalControls.bmapping BindingRel
    ConditionalControls.binitial P12Controls.bool_reflect
    (.there .here) (.there (.there .here))
    (.there (.there (.there (.there .here)))) (.there (.there (.there .here)))
    (.there (.there (.there .here))) (.there (.there (.there (.there .here)))) .here (.there .here)
    (.there .here) (.there (.there .here))
    (.there (.there (.there (.there .here)))) (.there (.there (.there .here)))
    (.there (.there (.there .here))) (.there (.there (.there (.there .here)))) .here (.there .here)
    rfl rfl rfl rfl rfl rfl rfl rfl with ⟨src,tgt,related,_⟩
  exact ⟨src,tgt,related⟩

theorem heterogeneous_snapshot :
    (match heterogeneousCode.run ConditionalControls.btarget with
    | .ok out => [some (if TEnv.get .here out.st.env = true then 1 else 0),
        some (if TEnv.get (.there .here) out.st.env = true then 1 else 0),
        PrimTy.num? (TEnv.get (.there (.there (.there (.there .here)))) out.st.env)]
    | _ => []) = [some 1,some 1,some 7] := by
  rw [(heterogeneous_reached .legacy 0).2.1]
  rfl

end Solidity.Lowering.G19.ConditionalSequence.Controls
