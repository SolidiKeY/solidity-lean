import Solidity.Lowering.P9.DefaultRecognizerCompleteness

/-! Completeness of the existing P9 body checks relative to their unchanged
readiness certificates. This neither admits new syntax nor changes execution. -/
namespace Solidity.Source.Calls.Recognize
open Solidity.Source.Progress
variable {E : Env} {vs : List Decl}

theorem plainB_complete {τ : STy} (plain : PlainResultType τ) : plainB τ = true := by
  rcases plain with value | memory
  · exact Bool.or_eq_true_iff.mpr (.inl value)
  · exact Bool.or_eq_true_iff.mpr (.inr (decide_eq_true memory))

theorem newReadyB_complete {τ : STy} (ready : NewReady E τ) : newReadyB E τ = true := by
  cases ready with
  | bytes => rfl
  | string => rfl
  | array σ word defaults => exact Bool.and_eq_true_iff.mpr ⟨word,defaults⟩

theorem exprB_complete {Γ : RCtx} {τ : STy} {e : RExpr E Γ τ}
    (ready : ReadyExpr (· ∈ vs) e) : exprB vs e = true := by
  induction ready with
  | value fragment operations =>
    exact Bool.or_eq_true_iff.mpr (.inl (decide_eq_true fragment))
  | «local» i => exact Bool.or_eq_true_iff.mpr (.inr rfl)
  | same same child ih =>
    exact Bool.or_eq_true_iff.mpr (.inr (Bool.and_eq_true_iff.mpr ⟨decide_eq_true rfl,ih⟩))
  | branch guard left right ihg ihl ihr =>
    exact Bool.or_eq_true_iff.mpr (.inr (Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨ihg,ihl⟩,ihr⟩))
  | newArray ready indexable child ih =>
    exact Bool.or_eq_true_iff.mpr (.inr (Bool.and_eq_true_iff.mpr ⟨newReadyB_complete ready,ih⟩))

theorem argsB_complete {Γ : RCtx} {types : List STy} {args : RConvArgs E Γ types}
    (ready : ReadyArgs (· ∈ vs) args) : argsB vs args = true := by
  induction ready with
  | nil => rfl
  | cons same plain head tail ih =>
    simp only [argsB,decide_true,Bool.true_and,plainB_complete plain,exprB_complete head,ih]

theorem parentB_complete {Γ : RCtx} {τ : STy} {e : RExpr E Γ τ}
    (ready : AllocationParent (· ∈ vs) e) : parentB vs e = true := by
  cases ready with
  | inline word args => exact argsB_complete args
  | structNew typed args => exact argsB_complete args

theorem stmtAccepted_complete {R : List STy} {M : Bool} {k : SCtx} {Γ Δ : RCtx}
    {s : RStmt E R M k Γ Δ} (ready : ReadyStmt (· ∈ vs) R M s) :
    (decide (s.ValFragC (· ∈ vs)) || stmtB vs s) = true := by
  induction ready using ReadyStmt.rec
    (motive_2 := fun {k Γ Δ} items _ => itemsB vs items = true) with
  | value fragment operations => exact Bool.or_eq_true_iff.mpr (.inl (decide_eq_true fragment))
  | expr expression => exact Bool.or_eq_true_iff.mpr (.inr (exprB_complete expression))
  | declVar τ ready => exact Bool.or_eq_true_iff.mpr (.inr (zeroReadyB_complete ready))
  | declInit same plain expression =>
    exact Bool.or_eq_true_iff.mpr (.inr (Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true rfl,plainB_complete plain⟩,exprB_complete expression⟩))
  | returnValue returns same plain expression =>
    exact Bool.or_eq_true_iff.mpr (.inr (Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true rfl,plainB_complete plain⟩,exprB_complete expression⟩))
  | returns args => exact Bool.or_eq_true_iff.mpr (.inr (argsB_complete args))
  | ifThen condition yes ih =>
    exact Bool.or_eq_true_iff.mpr (.inr (Bool.and_eq_true_iff.mpr
      ⟨exprB_complete condition,ih⟩))
  | ifElse condition yes no ihy ihn =>
    exact Bool.or_eq_true_iff.mpr (.inr (Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨exprB_complete condition,ihy⟩,
        ihn⟩))
  | block items ih => exact Bool.or_eq_true_iff.mpr (.inr ih)
  | nil => rfl
  | stmt head tail ihh iht => exact Bool.and_eq_true_iff.mpr ⟨ihh,iht⟩
  | unchecked inner tail ihi iht => exact Bool.and_eq_true_iff.mpr ⟨ihi,iht⟩

theorem itemsB_complete {R : List STy} {M : Bool} {k : SCtx} {Γ Δ : RCtx}
    {items : RItems E R M k Γ Δ} (ready : ReadyItems (· ∈ vs) R M items) :
    itemsB vs items = true := by
  induction ready using ReadyItems.rec
    (motive_1 := fun {k Γ Δ} s _ => (decide (s.ValFragC (· ∈ vs)) || stmtB vs s) = true) with
  | value fragment operations => exact stmtAccepted_complete (.value fragment operations)
  | expr expression => exact stmtAccepted_complete (.expr expression)
  | declVar τ ready => exact stmtAccepted_complete (.declVar τ ready)
  | declInit same plain expression => exact stmtAccepted_complete (.declInit same plain expression)
  | returnValue returns same plain expression =>
    exact stmtAccepted_complete (.returnValue returns same plain expression)
  | returns args => exact stmtAccepted_complete (.returns args)
  | ifThen condition yes ih => exact stmtAccepted_complete (.ifThen condition yes)
  | ifElse condition yes no ihy ihn => exact stmtAccepted_complete (.ifElse condition yes no)
  | block items ih => exact stmtAccepted_complete (.block items)
  | nil => rfl
  | stmt head tail ihh iht => exact Bool.and_eq_true_iff.mpr ⟨ihh,iht⟩
  | unchecked inner tail ihi iht => exact Bool.and_eq_true_iff.mpr ⟨ihi,iht⟩

theorem boundB_of_itemsB {R : List STy} {M : Bool} {k : SCtx} {Γ Δ : RCtx}
    (items : RItems E R M k Γ Δ) (accepted : itemsB vs items = true) :
    boundB vs items = true := by
  cases items with
  | nil => rfl
  | stmt head rest => exact Bool.or_eq_true_iff.mpr (.inl accepted)
  | unchecked inner rest => exact accepted

theorem boundB_complete {R : List STy} {M : Bool} {k : SCtx} {Γ Δ : RCtx}
    {items : RItems E R M k Γ Δ} (ready : BoundParentItems (· ∈ vs) R M items) :
    boundB vs items = true := by
  induction ready with
  | ready tail => exact boundB_of_itemsB _ (itemsB_complete tail)
  | initialized same plain parent tail ih =>
    apply Bool.or_eq_true_iff.mpr
    exact .inr (Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true rfl,plainB_complete plain⟩,
        parentB_complete parent⟩,ih⟩)

/-- info: 'Solidity.Source.Calls.Recognize.plainB_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms plainB_complete
/-- info: 'Solidity.Source.Calls.Recognize.newReadyB_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms newReadyB_complete
/-- info: 'Solidity.Source.Calls.Recognize.exprB_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exprB_complete
/-- info: 'Solidity.Source.Calls.Recognize.argsB_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms argsB_complete
/-- info: 'Solidity.Source.Calls.Recognize.parentB_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parentB_complete
/-- info: 'Solidity.Source.Calls.Recognize.stmtAccepted_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stmtAccepted_complete
/-- info: 'Solidity.Source.Calls.Recognize.itemsB_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms itemsB_complete
/-- info: 'Solidity.Source.Calls.Recognize.boundB_of_itemsB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boundB_of_itemsB
/-- info: 'Solidity.Source.Calls.Recognize.boundB_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boundB_complete
end Solidity.Source.Calls.Recognize
