import Solidity.Frontend.Admission.TypedObservationPolicy

/-! Intrinsic expression-visitor policy closure by the actual mutual
recursor. This does not establish full feature/profile or semantic adequacy.
Statement/items and complete Program closure remain separate obligations. -/
namespace Solidity.Frontend.Admission.TypedObservationPolicy
open Source

theorem expression_allowed : ExpressionPolicy := by
  intro E Γ τ e
  induction e using Solidity.Source.RExpr.rec
    (motive_2 := fun _ es => (Solidity.Frontend.Admission.argsObservations es).all Solidity.Frontend.Admission.ObservationSite.allowed = true)
    (motive_3 := fun _ es => (Solidity.Frontend.Admission.convObservations es).all Solidity.Frontend.Admission.ObservationSite.allowed = true)
    (motive_4 := fun _ l => (Solidity.Frontend.Admission.lvalObservations l).all Solidity.Frontend.Admission.ObservationSite.allowed = true)
  case magic b m h =>
    simpa only [Solidity.Frontend.Admission.observations, List.all_cons, List.all_nil, Bool.and_true] using Solidity.Frontend.Admission.TypedObservationPolicy.magic_allowed b m _ h
  case builtin b args h ih =>
    simp only [Solidity.Frontend.Admission.observations, List.all_cons, ih, Solidity.Frontend.Admission.TypedObservationPolicy.builtin_allowed E.isBase b _ _ h, Bool.and_self]
  case abiEncode k args ih =>
    cases k <;> simp only [Solidity.Frontend.Admission.observations, List.all_cons, ih, Bool.and_true] <;> decide
  all_goals intros
  all_goals first
    | assumption
    | rw [Solidity.Frontend.Admission.observations]
    | rw [Solidity.Frontend.Admission.argsObservations]
    | rw [Solidity.Frontend.Admission.convObservations]
    | rw [Solidity.Frontend.Admission.lvalObservations]
  all_goals simp_all only [List.all_append, List.all_cons, List.all_nil, Bool.and_true]
  all_goals simp only [Solidity.Frontend.Admission.ObservationSite.allowed, Solidity.Frontend.Admission.ObservationSite.status] <;> decide

/-- Open container corollaries; no inhabitants supplied. -/
abbrev ArgumentsPolicy : Prop := ∀ {E : Env} {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs),
  (argsObservations es).all ObservationSite.allowed = true
abbrev ConversionsPolicy : Prop := ∀ {E : Env} {Γ : RCtx} {τs : List STy} (es : RConvArgs E Γ τs),
  (convObservations es).all ObservationSite.allowed = true
abbrev LvaluePolicy : Prop := ∀ {E : Env} {Γ : RCtx} {τ : STy} (l : RLVal E Γ τ),
  (lvalObservations l).all ObservationSite.allowed = true
abbrev OptionalPolicy : Prop :=
  (∀ {E : Env} {Γ : RCtx} (c : ROptBool E Γ), (optBoolObservations c).all ObservationSite.allowed = true) ∧
  (∀ {E : Env} {Γ : RCtx} (e : ROptExpr E Γ), (optExprObservations e).all ObservationSite.allowed = true)

/-- Sol-owned next structural obligation, not an assumed premise/witness. -/
abbrev StatementPolicy : Prop := ∀ {E : Env} {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
  (s : RStmt E R M k Γ Γ'), (stmtObservations s).all ObservationSite.allowed = true

/-- info: 'Solidity.Frontend.Admission.TypedObservationPolicy.expression_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms expression_allowed
end Solidity.Frontend.Admission.TypedObservationPolicy
