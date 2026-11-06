import Solidity.Frontend.Admission.TypedObservationPolicy

/-! Intrinsic expression-visitor policy closure by the actual mutual
recursor. This does not establish full feature/profile or semantic adequacy.
Statement and Program policy closure is supplied in TypedStatementPolicy. -/
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
    simp only [Solidity.Frontend.Admission.observations, List.all_cons, ih, Solidity.Frontend.Admission.TypedObservationPolicy.builtin_allowed E.isBase E.mapFree b _ _ h, Bool.and_self]
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

/-- Container policy propositions, all implemented below. -/
abbrev ArgumentsPolicy : Prop := ∀ {E : Env} {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs),
  (argsObservations es).all ObservationSite.allowed = true
abbrev ConversionsPolicy : Prop := ∀ {E : Env} {Γ : RCtx} {τs : List STy} (es : RConvArgs E Γ τs),
  (convObservations es).all ObservationSite.allowed = true
abbrev LvaluePolicy : Prop := ∀ {E : Env} {Γ : RCtx} {τ : STy} (l : RLVal E Γ τ),
  (lvalObservations l).all ObservationSite.allowed = true
abbrev OptionalPolicy : Prop :=
  (∀ {E : Env} {Γ : RCtx} (c : ROptBool E Γ), (optBoolObservations c).all ObservationSite.allowed = true) ∧
  (∀ {E : Env} {Γ : RCtx} (e : ROptExpr E Γ), (optExprObservations e).all ObservationSite.allowed = true)

theorem conversions_allowed : ConversionsPolicy := by
  intro E Γ ts es
  induction es using Solidity.Source.RConvArgs.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ => True)
    (motive_4 := fun _ _ => True)
  all_goals intros
  all_goals first
    | exact True.intro
    | rfl
    | rw [Solidity.Frontend.Admission.convObservations]
  all_goals simp_all only [List.all_append,
    Solidity.Frontend.Admission.TypedObservationPolicy.expression_allowed, Bool.and_true]

theorem optional_allowed : OptionalPolicy := by
  constructor
  · intro E Γ c
    cases c <;> simp only [Solidity.Frontend.Admission.optBoolObservations,
      Solidity.Frontend.Admission.TypedObservationPolicy.expression_allowed, List.all_nil]
  · intro E Γ e
    cases e <;> simp only [Solidity.Frontend.Admission.optExprObservations,
      Solidity.Frontend.Admission.TypedObservationPolicy.expression_allowed, List.all_nil]

/-- Statement-policy proposition, implemented in TypedStatementPolicy. -/
abbrev StatementPolicy : Prop := ∀ {E : Env} {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
  (s : RStmt E R M k Γ Γ'), (stmtObservations s).all ObservationSite.allowed = true

/-- info: 'Solidity.Frontend.Admission.TypedObservationPolicy.expression_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms expression_allowed
/-- info: 'Solidity.Frontend.Admission.TypedObservationPolicy.conversions_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms conversions_allowed
/-- info: 'Solidity.Frontend.Admission.TypedObservationPolicy.optional_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms optional_allowed
theorem arguments_allowed : Solidity.Frontend.Admission.TypedObservationPolicy.ArgumentsPolicy := by
  intro E Γ ts es
  exact Solidity.Frontend.Admission.TypedObservationPolicy.expression_allowed (Solidity.Source.RExpr.tuple es)

/-- info: 'Solidity.Frontend.Admission.TypedObservationPolicy.arguments_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms arguments_allowed
theorem lvalue_allowed : Solidity.Frontend.Admission.TypedObservationPolicy.LvaluePolicy := by
  intro E Γ t l
  exact Solidity.Frontend.Admission.TypedObservationPolicy.expression_allowed (Solidity.Source.RExpr.delete l)

/-- info: 'Solidity.Frontend.Admission.TypedObservationPolicy.lvalue_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lvalue_allowed
end Solidity.Frontend.Admission.TypedObservationPolicy
