import Solidity.Lowering.V07.AliasRhsSubtraction
import Solidity.Lowering.V07.MixedAssignmentControls
import Solidity.Lowering.V07.Controls
import Solidity.Lowering.V07.DoubleControls

namespace Solidity.Lowering.V07.AllAliasControls
open Source.SemanticsExamples
abbrev SrcCtx : Source.RCtx := [.int .u8,.int .u8,.bytes .memory,.bytes .storage]
abbrev TgtCtx : Ctx := [.val .uint,.val .uint,.mem bytesR,.alias bytesR]
abbrev Keys := Bool × Bool

def si (k : Keys) : Source.Idx SrcCtx (.int .u8) := if k.1 then .there .here else .here
def ti (k : Keys) : Idx TgtCtx (.val .uint) := if k.1 then .there .here else .here

def sourcePost (p : Roadmap.Pipeline) : Source.EMState MixedAssignmentControls.E SrcCtx :=
  let s := MixedAssignmentControls.source
  if p = .legacy then ((s.1.set .here (.int 3 (by decide))).set (.there .here) (.int 3 (by decide)),s.2)
  else ((s.1.set (.there .here) (.int 7 (by decide))).set .here (.int 7 (by decide)),s.2)

def targetPost (p : Roadmap.Pipeline) : State MixedAssignmentControls.C TgtCtx :=
  let s := MixedAssignmentControls.target
  if p = .legacy then (s.setLocal .here (integerValue .u8 3 (by decide))).setLocal (.there .here) (integerValue .u8 3 (by decide))
  else (s.setLocal (.there .here) (integerValue .u8 7 (by decide))).setLocal .here (integerValue .u8 7 (by decide))

def expression : Source.RExpr MixedAssignmentControls.E SrcCtx (.int .u8) :=
  .binary .sub (.assign (.local (.there .here)) (.local .here))
    (.assign (.local .here) (.local (.there .here)))

theorem initial : IntegerLocalFamily .u8 si ti MixedAssignmentControls.source.1 MixedAssignmentControls.target.env := by
  constructor
  · intro k; rcases k with ⟨a,b⟩; cases a <;> cases b <;> rfl
  · intro k l; rcases k with ⟨a,b⟩; rcases l with ⟨c,d⟩
    cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem actual_runs (p : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) :
    (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := checked}
      (fuel+4) expression).run MixedAssignmentControls.source =
      (.ok (.val (.int 0 (integer_zero_range .u8))),sourcePost p) ∧
    (assignAssignSubOperand p .u8 (.there .here) .here (.there .here)).run MixedAssignmentControls.target =
      .ok (⟨targetPost p,by cases p <;> exact List.prefix_refl _⟩,
        .prim (integerValue .u8 0 (integer_zero_range .u8))) ∧
    IntegerLocalFamily .u8 si ti (sourcePost p).1 (targetPost p).env := by
  have h := alias_rhs_sub_transport .u8 si ti (MixedAssignmentControls.globals p)
    {F0 with checked := checked} fuel MixedAssignmentControls.source MixedAssignmentControls.target
    initial (true,false) (false,false) 7 3 (by decide) (by decide) rfl rfl
  cases p <;> exact ⟨h.1,h.2.1,h.2.2.2⟩

theorem caller_observations :
    ((sourcePost .legacy).1.get .here).key = some 3 ∧
    ((sourcePost .legacy).1.get (.there .here)).key = some 3 ∧
    ((sourcePost .viaIR).1.get .here).key = some 7 ∧
    ((sourcePost .viaIR).1.get (.there .here)).key = some 7 ∧
    PrimTy.num? (TEnv.get .here (targetPost .legacy).env) = some 3 ∧
    PrimTy.num? (TEnv.get (.there .here) (targetPost .legacy).env) = some 3 ∧
    PrimTy.num? (TEnv.get .here (targetPost .viaIR).env) = some 7 ∧
    PrimTy.num? (TEnv.get (.there .here) (targetPost .viaIR).env) = some 7 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem mixed_frames (p : Roadmap.Pipeline) :
    (sourcePost p).2 = MixedAssignmentControls.source.2 ∧
    (sourcePost p).1.get (.there (.there .here)) = .memRef rfl 0 ∧
    (sourcePost p).1.get (.there (.there (.there .here))) = .storRef rfl MixedAssignmentControls.path ∧
    (targetPost p).glob = MixedAssignmentControls.target.glob ∧
    (∃ r : HRef (targetPost p).H bytesR,
      TEnv.get (.there (.there .here)) (targetPost p).env = some r ∧
      (targetPost p).heap.len r .dyn = 2) ∧
    TEnv.get (.there (.there (.there .here))) (targetPost p).env = some MixedAssignmentControls.storageRef := by
  cases p <;> exact ⟨rfl,rfl,rfl,rfl,MixedAssignmentControls.live_memory,rfl⟩

theorem initial_rhs_formula_wrong :
    AssignmentControls.observed ((assignAssignSubOperand .viaIR .u8 (.there .here) .here (.there .here)).run
      MixedAssignmentControls.target) = some 0 ∧ (7-3 : Int) ≠ 0 := by
  rw [(actual_runs .viaIR 0 true).2.1]
  exact ⟨rfl,by decide⟩

theorem repeated_aliases_observed (p : Roadmap.Pipeline) :
    IntValueRel .u8 ((sourcePost p).1.get (si (true,false)))
      (TEnv.get (ti (true,true)) (targetPost p).env) :=
  (actual_runs p 0 true).2.2.values (true,false)

theorem fresh_boolean_context (p : Roadmap.Pipeline) :
    ((assignAssignSubOperand p .u8 (.there .here) .here (.there .here)).wk
      (Thin.drop (t := .val .bool) Thin.refl)).run (MixedAssignmentControls.target.push true) =
      liftedT₂ (Thin.drop (t := .val .bool) Thin.refl) (true,MixedAssignmentControls.target.env)
        (.ok ((⟨targetPost p,by cases p <;> exact List.prefix_refl _⟩ :
          Out MixedAssignmentControls.C MixedAssignmentControls.target.H TgtCtx),
          SVal.prim (integerValue .u8 0 (integer_zero_range .u8)))) := by
  have h := alias_rhs_sub_extension p MixedAssignmentControls.target .u8 (.there .here) .here
    7 3 (by decide) (by decide) rfl rfl
    (Thin.drop (t := .val .bool) Thin.refl) (true,MixedAssignmentControls.target.env)
  cases p <;> exact h

def signedSource : Source.EMState E0 [.int Controls.i8,.int Controls.i8] :=
  (.cons (.int (-128) (by decide)) (.cons (.int 127 (by decide)) .nil),s0)
def signedTarget : State (default : Contract) [.val .int,.val .int] :=
  ((State.init default).push (integerValue Controls.i8 127 (by decide))).push
    (integerValue Controls.i8 (-128) (by decide))

theorem signed_boundary_source (p : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) :
    (Source.evalE (G0 p) {F0 with checked := checked} (fuel+4)
      (.binary .sub (.assign (.local (.there .here)) (.local .here))
        (.assign (.local .here) (.local (.there .here))))).run signedSource =
      (.ok (.val (.int 0 (integer_zero_range Controls.i8))),
        (if p = .legacy then
          ((signedSource.1.set .here (.int 127 (by decide))).set (.there .here) (.int 127 (by decide)),signedSource.2)
        else ((signedSource.1.set (.there .here) (.int (-128) (by decide))).set .here (.int (-128) (by decide)),signedSource.2))) :=
  source_alias_rhs_sub_run (G0 p) {F0 with checked := checked} fuel signedSource
    Controls.i8 (.there .here) .here (-128) 127 (by decide) (by decide) rfl rfl

theorem signed_boundary_target (p : Roadmap.Pipeline) :
    (assignAssignSubOperand p Controls.i8 (.there .here) .here (.there .here)).run signedTarget =
      .ok (⟨(if p = .legacy then
          (signedTarget.setLocal .here (integerValue Controls.i8 127 (by decide))).setLocal (.there .here) (integerValue Controls.i8 127 (by decide))
        else (signedTarget.setLocal (.there .here) (integerValue Controls.i8 (-128) (by decide))).setLocal .here (integerValue Controls.i8 (-128) (by decide))),
        by split <;> exact List.prefix_refl _⟩,.prim (integerValue Controls.i8 0 (integer_zero_range Controls.i8))) :=
  alias_rhs_sub_operand_run p signedTarget Controls.i8 (.there .here) .here (-128) 127
    (by decide) (by decide) rfl rfl

theorem all_three_equal (p : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) :
    (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := checked} (fuel+4)
      (.binary .sub (.assign (.local .here) (.local .here))
        (.assign (.local .here) (.local .here)))).run MixedAssignmentControls.source =
      (.ok (.val (.int 0 (integer_zero_range .u8))),MixedAssignmentControls.source) ∧
    (assignAssignSubOperand p .u8 .here .here .here).run MixedAssignmentControls.target =
      .ok (⟨MixedAssignmentControls.target,List.prefix_refl _⟩,
        .prim (integerValue .u8 0 (integer_zero_range .u8))) := by
  have hs := source_alias_rhs_sub_run (MixedAssignmentControls.globals p)
    {F0 with checked := checked} fuel MixedAssignmentControls.source .u8 .here .here
    7 7 (by decide) (by decide) rfl rfl
  have ht := alias_rhs_sub_operand_run p MixedAssignmentControls.target .u8 .here .here
    7 7 (by decide) (by decide) rfl rfl
  cases p <;> exact ⟨hs,ht⟩

theorem separated_pair_application (p : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) :
    (Source.evalPair (G0 p) {F0 with checked := checked} (fuel+3)
      (.assign (.local .here) (.local (.there .here)))
      (.assign (.local (.there .here)) (.local (.there (.there .here))))).run DoubleControls.source =
      (.ok (.val (if p = .legacy then .int 3 (by decide) else .int 7 (by decide)),
        .val (.int 3 (by decide))),DoubleControls.sourcePost p) := by
  have h := source_assign_assign_pair_all_aliases (G0 p) {F0 with checked := checked} fuel
    DoubleControls.source (.here : Source.Idx DoubleControls.SrcCtx (.int .u8))
    (.there .here) (.there (.there .here)) (.int 7 (by decide)) (.int 3 (by decide)) rfl rfl
  cases p <;> exact h

end Solidity.Lowering.V07.AllAliasControls
