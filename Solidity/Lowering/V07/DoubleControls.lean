import Solidity.Lowering.V07.DoubleSubtraction
import Solidity.Lowering.V07.LocalFamilyControls
import Solidity.Lowering.V07.MixedAssignmentControls

namespace Solidity.Lowering.V07.DoubleControls
open Source.SemanticsExamples
abbrev Keys := LocalFamilyControls.Keys
abbrev SrcCtx := LocalFamilyControls.SrcCtx
abbrev TgtCtx := LocalFamilyControls.TgtCtx
abbrev si := LocalFamilyControls.si
abbrev ti := LocalFamilyControls.ti

def source : Source.EMState E0 SrcCtx :=
  (.cons (.int 11 (by decide)) (.cons (.int 7 (by decide)) (.cons (.int 3 (by decide)) .nil)),s0)
def target : State (default : Contract) TgtCtx :=
  (((State.init default).push (integerValue .u8 3 (by decide))).push
    (integerValue .u8 7 (by decide))).push (integerValue .u8 11 (by decide))
def sourcePost (p : Roadmap.Pipeline) : Source.EMState E0 SrcCtx :=
  if p = .legacy then ((source.1.set (.there .here) (.int 3 (by decide))).set .here (.int 3 (by decide)),source.2)
  else ((source.1.set .here (.int 7 (by decide))).set (.there .here) (.int 3 (by decide)),source.2)
def targetPost (p : Roadmap.Pipeline) : State (default : Contract) TgtCtx :=
  if p = .legacy then (target.setLocal (.there .here) (integerValue .u8 3 (by decide))).setLocal .here (integerValue .u8 3 (by decide))
  else (target.setLocal .here (integerValue .u8 7 (by decide))).setLocal (.there .here) (integerValue .u8 3 (by decide))
def expression : Source.RExpr E0 SrcCtx (.int .u8) :=
  .binary .sub (.assign (.local .here) (.local (.there .here)))
    (.assign (.local (.there .here)) (.local (.there (.there .here))))

theorem initial : IntegerLocalFamily .u8 si ti source.1 target.env := by
  constructor
  · intro k; rcases k with ⟨a,b⟩; cases a <;> cases b <;> rfl
  · intro k l; rcases k with ⟨a,b⟩; rcases l with ⟨c,d⟩
    cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem delta_range (p : Roadmap.Pipeline) :
    Source.IntTy.u8.lo ≤ doubleDelta p 7 3 ∧ doubleDelta p 7 3 ≤ Source.IntTy.u8.hi := by
  cases p <;> decide

theorem actual_runs (p : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) :
    (Source.evalE (G0 p) {F0 with checked := checked} (fuel+4) expression).run source =
      (.ok (.val (.int (doubleDelta p 7 3) (delta_range p))),sourcePost p) ∧
    (assignAssignSubOperand p .u8 .here (.there .here) (.there (.there .here))).run target =
      .ok (⟨targetPost p,by cases p <;> exact List.prefix_refl _⟩,
        .prim (integerValue .u8 (doubleDelta p 7 3) (delta_range p))) := by
  have h := double_assignment_transport .u8 si ti (G0 p) {F0 with checked := checked} fuel source target
    initial (false,false) (false,true) (true,false) 7 3 (by decide) (by decide) rfl rfl (by decide) (delta_range p)
  cases p <;> exact ⟨h.1,h.2.1⟩

theorem source_pairs (p : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) :
    (Source.evalPair (G0 p) {F0 with checked := checked} (fuel+3)
      (.assign (.local .here) (.local (.there .here)))
      (.assign (.local (.there .here)) (.local (.there (.there .here))))).run source =
      (.ok (.val (if p = .legacy then .int 3 (by decide) else .int 7 (by decide)),.val (.int 3 (by decide))),sourcePost p) := by
  have h := source_assign_assign_pair (G0 p) {F0 with checked := checked} fuel source
    (.here : Source.Idx SrcCtx (.int .u8)) (.there .here) (.there (.there .here))
    (.int 7 (by decide)) (.int 3 (by decide)) rfl rfl (by decide)
  cases p <;> exact h

theorem target_prefix (p : Roadmap.Pipeline) :
    (assignAssignPrefix p .here (.there .here) (.there (.there .here))).run target =
      .ok (⟨((targetPost p).push (t := .val .uint)
        (if p = .legacy then integerValue .u8 3 (by decide) else integerValue .u8 7 (by decide))).push
          (t := .val .uint) (integerValue .u8 3 (by decide)),
        by cases p <;> exact List.prefix_refl _⟩) := by
  have h := assign_assign_prefix_run p target (.here : Idx TgtCtx (.val .uint))
    (.there .here) (.there (.there .here)) (integerValue .u8 7 (by decide))
    (integerValue .u8 3 (by decide)) rfl rfl (by decide)
  cases p <;> exact h

theorem caller_order_observations :
    (sourcePost .legacy).1.get .here = .int 3 (by decide) ∧
    (sourcePost .viaIR).1.get .here = .int 7 (by decide) ∧
    TEnv.get .here (targetPost .legacy).env = integerValue .u8 3 (by decide) ∧
    TEnv.get .here (targetPost .viaIR).env = integerValue .u8 7 (by decide) ∧
    (sourcePost .legacy).2 = source.2 ∧ (sourcePost .viaIR).2 = source.2 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem repeated_alias_postfamily (p : Roadmap.Pipeline) :
    IntegerLocalFamily .u8 si ti (sourcePost p).1 (targetPost p).env := by
  have h := initial.assign_pair p (false,false) (false,true) (true,false)
    7 3 (by decide) (by decide) rfl rfl (by decide)
  cases p <;> exact h

theorem repeated_alias_observed (p : Roadmap.Pipeline) :
    ((sourcePost p).1.get (si (true,true))).key = some 3 ∧
    PrimTy.num? (TEnv.get (ti (true,true)) (targetPost p).env) = some 3 := by
  cases p <;> exact ⟨rfl,rfl⟩

theorem fresh_context_family :
    IntegerLocalFamily .u8 (fun k => .there (si k)) (fun k => Idx.there (u := .val .bool) (ti k))
      (.cons (.bool false) source.1) ((false : Bool),target.env) :=
  initial.under_binders (.bool false) (u := .val .bool) false

/-- A caller Boolean binder is structurally distinct from both capture
binders, irrespective of their printed names. -/
theorem fresh_target_extension (p : Roadmap.Pipeline) :
    ((assignAssignSubOperand p .u8 .here (.there .here) (.there (.there .here))).wk
      (Thin.drop (t := .val .bool) .refl)).run
        (target.lift (Thin.drop .refl) ((false : Bool),target.env)) =
      liftedT₂ (Thin.drop (t := .val .bool) .refl) ((false : Bool),target.env)
        (.ok ((⟨targetPost p,by cases p <;> exact List.prefix_refl _⟩ : Out (default : Contract) target.H TgtCtx),
          SVal.prim (integerValue .u8 (doubleDelta p 7 3) (delta_range p)))) := by
  have h := assign_assign_sub_extension p target .u8 .here (.there .here) (.there (.there .here))
    7 3 (by decide) (by decide) rfl rfl (by decide) (delta_range p)
    (Thin.drop (t := .val .bool) .refl) ((false : Bool),target.env)
  cases p <;> exact h

end Solidity.Lowering.V07.DoubleControls
