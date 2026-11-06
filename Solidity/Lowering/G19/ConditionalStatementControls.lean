import Solidity.Lowering.G19.ConditionalStatement
import Solidity.Lowering.V07.ConditionalControls

namespace Solidity.Lowering.G19.ConditionalStatement.Controls
open Solidity.Lowering.V07
open Source.SemanticsExamples
open P12Controls (C E BindingRel)
open ConditionalControls (SrcCtx TgtCtx source target mapping initial sci sca si sa sj sb tci tca ti ta tj tb)

theorem mapped (pipeline : Roadmap.Pipeline) (fuel : Nat) (choice : Bool) :
    (Source.execS (MixedAssignmentControls.globals pipeline) F0 (fuel+4) 0 none
      (R := []) (M := false) (statement (k := ⟨false,false⟩) sci sca si sa sj sb)
      (source choice).1).run (.nil,(source choice).2) =
      (.ok (Source.Out.normal (ConditionalAssignments.sourceAfter (source choice) sci choice si sa sj sb).1),
        (.nil,(source choice).2)) ∧
    (code tci tca ti ta tj tb).run (target choice) =
      .ok ⟨ConditionalAssignments.targetAfter (target choice) tci choice ti ta tj tb,List.prefix_refl _⟩ ∧
    mapping.Related BindingRel (ConditionalAssignments.sourceAfter (source choice) sci choice si sa sj sb).1
      (ConditionalAssignments.targetAfter (target choice) tci choice ti ta tj tb).env := by
  rcases correct (MixedAssignmentControls.globals pipeline) F0 fuel 0 none
    (returns := []) (M := false) (k := ⟨false,false⟩)
    (source choice) (target choice) mapping BindingRel (initial choice) P12Controls.bool_reflect
    sci sca si sa sj sb tci tca ti ta tj tb rfl rfl rfl rfl rfl rfl with ⟨src,tgt,related,_⟩
  exact ⟨src,tgt,related⟩

def sourceObs (pipeline : Roadmap.Pipeline) (choice : Bool) : List (Option Int) :=
  match (Source.execS (MixedAssignmentControls.globals pipeline) F0 8 0 none
      (R := []) (M := false) (statement (k := ⟨false,false⟩) sci sca si sa sj sb)
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
    sourceObs pipeline choice = if choice then [some 1,some 1,some 11,some 7,some 7]
      else [some 0,some 0,some 11,some 11,some 3] := by
  unfold sourceObs
  rw [(mapped pipeline 4 choice).1]
  cases choice <;> rfl

theorem target_observation (choice : Bool) :
    observeTarget (code tci tca ti ta tj tb) choice =
      if choice then [some 1,some 1,some 11,some 7,some 7]
      else [some 0,some 0,some 11,some 11,some 3] := by
  unfold observeTarget
  rw [(mapped .legacy 0 choice).2.1]
  cases choice <;> rfl

theorem stale_condition_refused :
    observeTarget (code tci tci ti ta tj tb) true ≠ observeTarget (code tci tca ti ta tj tb) true := by
  unfold observeTarget
  rw [target_run (target true) tci tci false ti ta tj tb rfl,
    target_run (target true) tci tca true ti ta tj tb rfl]
  change [some 0,some 1,some 11,some 11,some 3] ≠ ([some 1,some 1,some 11,some 7,some 7] : List (Option Int))
  decide

def aliasStatement : Source.RStmt E [] false ⟨false,false⟩ ConditionalControls.BSrcCtx ConditionalControls.BSrcCtx :=
  statement (.there .here) (.there (.there .here))
    (.there .here) .here (.there (.there .here)) (.there .here)
def aliasCode : Prog C ConditionalControls.BTgtCtx ConditionalControls.BTgtCtx :=
  code (.there .here) (.there (.there .here))
    (.there .here) .here (.there (.there .here)) (.there .here)
def aliasSource : Source.EMState E ConditionalControls.BSrcCtx :=
  ConditionalAssignments.sourceAfter ConditionalControls.bsource (.there .here) true
    (.there .here) .here (.there (.there .here)) (.there .here)
def aliasTarget : State C ConditionalControls.BTgtCtx :=
  ConditionalAssignments.targetAfter ConditionalControls.btarget (.there .here) true
    (.there .here) .here (.there (.there .here)) (.there .here)

theorem alias_reached (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    (Source.execS (MixedAssignmentControls.globals pipeline) F0 (fuel+4) 0 none
      aliasStatement ConditionalControls.bsource.1).run (.nil,ConditionalControls.bsource.2) =
      (.ok (Source.Out.normal aliasSource.1),(.nil,aliasSource.2)) ∧
    aliasCode.run ConditionalControls.btarget = .ok ⟨aliasTarget,List.prefix_refl _⟩ ∧
    ConditionalControls.bmapping.Related BindingRel aliasSource.1 aliasTarget.env := by
  rcases correct (MixedAssignmentControls.globals pipeline) F0 fuel 0 none
    (returns := []) (M := false) (k := ⟨false,false⟩)
    ConditionalControls.bsource ConditionalControls.btarget ConditionalControls.bmapping BindingRel
    ConditionalControls.binitial P12Controls.bool_reflect
    (.there .here) (.there (.there .here)) (.there .here) .here (.there (.there .here)) (.there .here)
    (.there .here) (.there (.there .here)) (.there .here) .here (.there (.there .here)) (.there .here)
    rfl rfl rfl rfl rfl rfl with ⟨src,tgt,related,_⟩
  exact ⟨src,tgt,related⟩

/-- The selected branch can overwrite the caller's condition after selection. -/
theorem alias_snapshot :
    (match aliasCode.run ConditionalControls.btarget with
    | .ok out => [TEnv.get .here out.st.env,TEnv.get (.there .here) out.st.env,
        TEnv.get (.there (.there .here)) out.st.env]
    | _ => []) = [false,false,true] := by
  rw [(alias_reached .legacy 0).2.1]
  rfl

end Solidity.Lowering.G19.ConditionalStatement.Controls
