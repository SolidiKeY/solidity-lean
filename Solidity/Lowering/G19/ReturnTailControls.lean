import Solidity.Lowering.G19.ReturnTail
import Solidity.Lowering.V07.ConditionalControls

namespace Solidity.Lowering.G19.ReturnTail.Controls
open Solidity.Lowering.V07
open Source.SemanticsExamples
open P12Controls (C E BindingRel)
open ConditionalControls (SrcCtx TgtCtx source target mapping initial sci sca si sa tci tca ti ta)

theorem mapped (pipeline : Roadmap.Pipeline) (fuel : Nat) (choice : Bool) :
    (Source.execS (MixedAssignmentControls.globals pipeline) F0 (fuel+6) 0 none
      (statement (M := false) (k := ⟨false,false⟩) sci sca si sa) (source choice).1).run (.nil,(source choice).2) =
      (.ok (if choice then Source.Out.ret (sourceAfter (source choice) sci choice si sa).1
        else Source.Out.normal (sourceAfter (source choice) sci choice si sa).1),(.nil,(source choice).2)) ∧
    (code tci tca ti ta).run (target choice) = .ok ⟨reached (target choice) tci choice ti ta,List.prefix_refl _⟩ ∧
    (mapping.wk (Thin.drop (t := .val .bool) .refl)).Related BindingRel
      (sourceAfter (source choice) sci choice si sa).1 (reached (target choice) tci choice ti ta).env ∧
    TEnv.get .here (reached (target choice) tci choice ti ta).env = choice := by
  rcases correct (MixedAssignmentControls.globals pipeline) F0 fuel 0 none (M := false) (k := ⟨false,false⟩)
    (source choice) (target choice) mapping BindingRel (initial choice) P12Controls.bool_reflect
    sci sca si sa tci tca ti ta rfl rfl rfl rfl with ⟨src,tgt,related,flag,_⟩
  exact ⟨src,tgt,related,flag⟩

def sourceObs (pipeline : Roadmap.Pipeline) (choice : Bool) : List (Option Int) :=
  match (Source.execS (MixedAssignmentControls.globals pipeline) F0 10 0 none
      (statement (M := false) (k := ⟨false,false⟩) sci sca si sa) (source choice).1).run (.nil,(source choice).2) with
  | (.ok (.ret ls),_) => [some 1,(ls.get sci).key,(ls.get sca).key,
      (ls.get ConditionalControls.sb).key,(ls.get sa).key,(ls.get si).key]
  | (.ok (.normal ls),_) => [some 0,(ls.get sci).key,(ls.get sca).key,
      (ls.get ConditionalControls.sb).key,(ls.get sa).key,(ls.get si).key]
  | _ => []

def observeTarget (program : Prog C TgtCtx (.val .bool :: TgtCtx)) (choice : Bool) : List (Option Int) :=
  match program.run (target choice) with
  | .ok out => [some (if TEnv.get .here out.st.env = true then 1 else 0),
      some (if TEnv.get (.there tci) out.st.env = true then 1 else 0),
      some (if TEnv.get (.there tca) out.st.env = true then 1 else 0),
      PrimTy.num? (TEnv.get (.there ConditionalControls.tb) out.st.env),
      PrimTy.num? (TEnv.get (.there ta) out.st.env),PrimTy.num? (TEnv.get (.there ti) out.st.env)]
  | _ => []

theorem source_observation (pipeline : Roadmap.Pipeline) (choice : Bool) :
    sourceObs pipeline choice = if choice then [some 1,some 1,some 1,some 11,some 7,some 3]
      else [some 0,some 0,some 0,some 11,some 7,some 7] := by
  unfold sourceObs
  rw [(mapped pipeline 4 choice).1]
  cases choice <;> rfl

theorem target_observation (choice : Bool) :
    observeTarget (code tci tca ti ta) choice = if choice then [some 1,some 1,some 1,some 11,some 7,some 3]
      else [some 0,some 0,some 0,some 11,some 7,some 7] := by
  unfold observeTarget
  rw [(mapped .legacy 0 choice).2.1]
  cases choice <;> rfl

def eagerCode : Prog C TgtCtx (.val .bool :: TgtCtx) :=
  (assignLocalOperand tci tca).code.join
    (.cons (.assignLocal (.there ti) (.simple (.local (.there ta)))) .nil)

theorem eager_tail_refused : observeTarget eagerCode true ≠ observeTarget (code tci tca ti ta) true := by
  rw [target_observation]
  change [some 1,some 1,some 1,some 11,some 7,some 7] ≠
    ([some 1,some 1,some 1,some 11,some 7,some 3] : List (Option Int))
  decide

/-- Real initial inputs where false fallthrough later writes the caller condition true. -/
def aliasSource : Source.EMState E ConditionalControls.BSrcCtx :=
  ((ConditionalControls.bsource.1.set .here (.bool true)).set (.there (.there .here)) (.bool false),
    ConditionalControls.bsource.2)
def aliasTarget : State C ConditionalControls.BTgtCtx :=
  (ConditionalControls.btarget.setLocal .here true).setLocal (.there (.there .here)) false

theorem alias_initial : ConditionalControls.bmapping.Related BindingRel aliasSource.1 aliasTarget.env := by
  have first : ConditionalControls.bmapping.Related BindingRel
      (ConditionalControls.bsource.1.set .here (.bool true))
      (TEnv.set .here true ConditionalControls.btarget.env) :=
    ContextMap.related_write ConditionalControls.bmapping BindingRel ConditionalControls.bsource.1
      ConditionalControls.btarget.env ConditionalControls.binitial .here .here rfl (.bool true) true rfl
  intro σ i
  exact (ContextMap.related_write ConditionalControls.bmapping BindingRel _ _ first
    (.there (.there .here)) (.there (.there .here)) rfl (.bool false) false rfl) i

def aliasCode : Prog C ConditionalControls.BTgtCtx (.val .bool :: ConditionalControls.BTgtCtx) :=
  code (.there .here) (.there (.there .here)) (.there .here) .here

theorem alias_reached (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    (Source.execS (MixedAssignmentControls.globals pipeline) F0 (fuel+6) 0 none
      (statement (M := false) (k := ⟨false,false⟩) (.there .here) (.there (.there .here))
        (.there .here) .here) aliasSource.1).run (.nil,aliasSource.2) =
      (.ok (Source.Out.normal (sourceAfter aliasSource (.there .here) false (.there .here) .here).1),
        (.nil,aliasSource.2)) ∧
    aliasCode.run aliasTarget =
      .ok ⟨reached aliasTarget (.there .here) false (.there .here) .here,List.prefix_refl _⟩ ∧
    (ConditionalControls.bmapping.wk (Thin.drop (t := .val .bool) .refl)).Related BindingRel
      (sourceAfter aliasSource (.there .here) false (.there .here) .here).1
      (reached aliasTarget (.there .here) false (.there .here) .here).env := by
  rcases correct (MixedAssignmentControls.globals pipeline) F0 fuel 0 none (M := false) (k := ⟨false,false⟩)
    aliasSource aliasTarget ConditionalControls.bmapping BindingRel alias_initial P12Controls.bool_reflect
    (.there .here) (.there (.there .here)) (.there .here) .here
    (.there .here) (.there (.there .here)) (.there .here) .here rfl rfl rfl rfl
    with ⟨src,tgt,related,_,_⟩
  exact ⟨src,tgt,related⟩

theorem alias_snapshot :
    (match aliasCode.run aliasTarget with
    | .ok out => [TEnv.get .here out.st.env,TEnv.get (.there .here) out.st.env,
        TEnv.get (.there (.there .here)) out.st.env,TEnv.get (.there (.there (.there .here))) out.st.env]
    | _ => []) = [false,true,true,false] := by
  rw [(alias_reached .legacy 0).2.1]
  rfl

def recomputedFlagCode : Prog C ConditionalControls.BTgtCtx (.val .bool :: ConditionalControls.BTgtCtx) :=
  aliasCode.join (.cons (.assignLocal .here (.simple (.local (.there (.there .here))))) .nil)

theorem clobbered_flag_refused :
    (match recomputedFlagCode.run aliasTarget with | .ok out => TEnv.get .here out.st.env | _ => false) ≠
    (match aliasCode.run aliasTarget with | .ok out => TEnv.get .here out.st.env | _ => true) := by
  rw [(alias_reached .legacy 0).2.1]
  change true ≠ false
  decide

end Solidity.Lowering.G19.ReturnTail.Controls
