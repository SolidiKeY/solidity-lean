import Solidity.Calculus.CallResultCapture

/-! # Whole-result capture controls
These use actual updates and inhabited typed states. They do not claim a
bounded representation for the recursively expanded call family.
-/
namespace Solidity.Examples.Tactics.CallResultCapture
open Solidity.CallResultCapture
private abbrev C := StandardExample
private abbrev Γ : Ctx := [.val .uint, .val .uint]
private def start (n : Nat) : State C Γ :=
  ((State.init C).push (t := .val .uint) (uintOfNat n)).push (t := .val .uint) (uintOfNat 99)
private def lit (n : Nat) (h : PrimTy.uint.inRange (Int.ofNat n) = true) : Val C Γ .uint :=
  .simple (.lit n h)
private def result : Tm C Γ (.val .uint) :=
  (Val.binop .add rfl rfl
    (.binop .mul rfl rfl (.simple (.local (.there .here))) (lit 3 rfl)) (lit 1 rfl)).lower
private def name : Var := .fresh "result" 0
private def observed (n : Nat) : Option (PrimTy.uint.Denote × PrimTy.uint.Denote) :=
  ((capture name result).applyV (start n)).bind fun q =>
    ((restore (.there .here : Idx Γ (.val .uint))).applyV
      ((start n).push (t := .val .uint) (q.2 _ .here))).map
        (fun r => (r.2 _ .here, r.2 _ (.there .here)))

/-- The result reads the old target, and a non-head target preserves its neighbor. -/
theorem targetDependent : observed 2 = some (uintOfNat 99, uintOfNat 7) := rfl
/-- Changing the argument changes the result, so capture is not a constant oracle. -/
theorem distinctArgument : observed 3 = some (uintOfNat 99, uintOfNat 10) := rfl
/-- A wrong computed result is rejected on the inhabited execution. -/
theorem wrongResult : observed 2 ≠ some (uintOfNat 99, uintOfNat 6) := by decide

private def failing : Tm C Γ (.val .uint) :=
  (Val.binop .div rfl rfl (lit 1 rfl) (lit 0 rfl)).lower
/-- A selected genuinely partial result is retained. -/
theorem selectedFailure : (capture name failing).applyV (start 2) = none := rfl
/-- Failure establishes every box postcondition, including false. -/
theorem failingBox (φ : Fml C Γ) : holds (start 2) (leaf .box name .here failing φ) := by
  rw [holds_iff]
  change Upd.afterT .box (start 2) _ (holds · φ)
  rw [Upd.afterT_applyV]
  change True ∨ false = true
  exact Or.inl trivial
/-- Failure cannot establish even the true diamond postcondition. -/
theorem failingDiamond : ¬ holds (start 2) (leaf .diamond name .here failing .tt) := by
  rw [holds_iff]
  change ¬ Upd.afterT .diamond (start 2) _ (holds · Fml.tt)
  rw [Upd.afterT_applyV]
  change ¬ (False ∨ false = true)
  simp only [Bool.false_eq_true, or_self, not_false_eq_true]

private def collidingNames : Option (PrimTy.uint.Denote × PrimTy.uint.Denote) :=
  (((capture name result).decl name (.val (lit 13 rfl).lower)).applyV (start 2)).map
    (fun q => (q.2 _ .here, q.2 _ (.there .here)))
/-- Two identical display names still introduce distinct intrinsic result slots. -/
theorem displayNameCollision : collidingNames = some (uintOfNat 13, uintOfNat 7) := rfl

/-- Checked arithmetic still fails at the word bound. -/
theorem overflow : observed (2^256 - 1) = none := rfl

private def funded : State C Γ := { start 2 with selfBalance := uintOfNat 5 }
private def balancePost : Fml C Γ :=
  .eq (.app0 (.env .selfBalance)) (.app0 (.lit (uintOfNat 5)))
/-- A successful capture preserves a nontrivial global postcondition. -/
theorem preservesBalance : holds funded (leaf .diamond name .here result balancePost) := by
  apply complete
  change Upd.afterT .diamond funded _ (holds · balancePost)
  rw [Upd.afterT_applyV]
  change ∀ τ : State C Γ, τ.glob = funded.glob →
    (∀ {u : LTy} (i : Idx Γ u), τ.getV i = (funded.locV.set .here (uintOfNat 7)) u i) →
      holds τ balancePost
  intro τ hg _
  unfold balancePost
  rw [holds_eq]
  have hb : τ.selfBalance = uintOfNat 5 := congrArg State.selfBalance hg
  change some τ.selfBalance = some (uintOfNat 5)
  exact congrArg some hb

/-- Restoration writes the old target and removes only the fresh head. -/
theorem repeatedName (σ : State C Γ) (v : PrimTy.uint.Denote) :
    ((σ.push (t := .val .uint) v).setLocal (.there (.there .here)) v).drop (.push .refl) =
      σ.setLocal (.there .here) v := restore_state σ v (.there .here)

/-- The full result term is present once, with the documented five-node overhead. -/
theorem actualSize : (leaf .box name (.there .here) result (.tt : Fml C Γ)).tmSize = 11 := rfl

end Solidity.Examples.Tactics.CallResultCapture
