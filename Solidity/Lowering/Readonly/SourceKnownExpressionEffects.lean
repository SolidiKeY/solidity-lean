import Solidity.Lowering.Readonly.SourceKnownHistory

/-! Guard-parametric Source expression histories. Regression purpose: an
unavailable delegated calldata read refuses without losing the real journal
history; every other expression keeps the same typed computation. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
variable {E : Env}

private theorem expression_cut_0 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (h : KnownAt G n) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (lower : 0 ≤ e.ctorIdx) (upper : e.ctorIdx < 7) :
    Effect F.static (evalE (calldataKnown := known) G F (n+1) e) := by
  cases e <;> first
  | (exfalso; simp only [RExpr.ctorIdx] at lower upper; omega)
  | (simp only [evalE]; apply withLibraryCalldata_effect; known_history_go h F n)

private theorem expression_cut_1 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (h : KnownAt G n) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (lower : 7 ≤ e.ctorIdx) (upper : e.ctorIdx < 14) :
    Effect F.static (evalE (calldataKnown := known) G F (n+1) e) := by
  cases e <;> first
  | (exfalso; simp only [RExpr.ctorIdx] at lower upper; omega)
  | (simp only [evalE]; apply withLibraryCalldata_effect; known_history_go h F n)

private theorem expression_cut_2 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (h : KnownAt G n) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (lower : 14 ≤ e.ctorIdx) (upper : e.ctorIdx < 21) :
    Effect F.static (evalE (calldataKnown := known) G F (n+1) e) := by
  cases e <;> first
  | (exfalso; simp only [RExpr.ctorIdx] at lower upper; omega)
  | (simp only [evalE]; apply withLibraryCalldata_effect; known_history_go h F n)

private theorem expression_cut_3 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (h : KnownAt G n) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (lower : 21 ≤ e.ctorIdx) (upper : e.ctorIdx < 28) :
    Effect F.static (evalE (calldataKnown := known) G F (n+1) e) := by
  cases e <;> first
  | (exfalso; simp only [RExpr.ctorIdx] at lower upper; omega)
  | (simp only [evalE]; apply withLibraryCalldata_effect; known_history_go h F n)

private theorem expression_cut_4 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (h : KnownAt G n) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (lower : 28 ≤ e.ctorIdx) (upper : e.ctorIdx < 35) :
    Effect F.static (evalE (calldataKnown := known) G F (n+1) e) := by
  cases e <;> first
  | (exfalso; simp only [RExpr.ctorIdx] at lower upper; omega)
  | (simp only [evalE]; apply withLibraryCalldata_effect; known_history_go h F n)

private theorem expression_cut_5 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (h : KnownAt G n) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (lower : 35 ≤ e.ctorIdx) (upper : e.ctorIdx < 41) :
    Effect F.static (evalE (calldataKnown := known) G F (n+1) e) := by
  cases e <;> first
  | (exfalso; simp only [RExpr.ctorIdx] at lower upper; omega)
  | (simp only [evalE]; apply withLibraryCalldata_effect; known_history_go h F n)

/-- Exhaustive expression history, quantified over the real calldata mode. -/
theorem evalE_succ_known {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (h : KnownAt G n) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) :
    Effect F.static (evalE (calldataKnown := known) G F (n+1) e) := by
  by_cases cut0 : e.ctorIdx < 7
  · exact expression_cut_0 G F n known h e (by omega) cut0
  by_cases cut1 : e.ctorIdx < 14
  · exact expression_cut_1 G F n known h e (by omega) cut1
  by_cases cut2 : e.ctorIdx < 21
  · exact expression_cut_2 G F n known h e (by omega) cut2
  by_cases cut3 : e.ctorIdx < 28
  · exact expression_cut_3 G F n known h e (by omega) cut3
  by_cases cut4 : e.ctorIdx < 35
  · exact expression_cut_4 G F n known h e (by omega) cut4
  exact expression_cut_5 G F n known h e (by omega) (by cases e <;> simp only [RExpr.ctorIdx] <;> decide)

end Solidity.Lowering.Readonly.SourceHistory

/-- info: 'Solidity.Lowering.Readonly.SourceHistory.evalE_succ_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.Readonly.SourceHistory.evalE_succ_known
