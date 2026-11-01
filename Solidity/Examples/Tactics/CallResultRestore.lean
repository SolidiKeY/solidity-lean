import Solidity.Calculus.CallResultRestore
import Solidity.Calculus.CallFunctionGraph

/-! # Generic call-result restoration controls
Actual checked terms, mixed fresh prefixes and observable caller state.
These do not assert a complete source-call family compression theorem.
-/
namespace Solidity.Examples.Tactics.CallResultRestore
open Solidity.CallResultRestore
private abbrev C := StandardExample
private abbrev Γ : Ctx := [.val .uint, .val .uint]
private abbrev Ghosts : Ctx := [.val .bool, .kint, .oldNet, .val .int] ++ Γ
private abbrev Δ : Ctx := .val .uint :: Ghosts
private def original : State C Γ :=
  ((({ State.init C with selfBalance := uintOfNat 5, net := [(uintOfNat 5, 19)] }).push
    (t := .val .uint) (uintOfNat 2)).push (t := .val .uint) (uintOfNat 99))
private def ghosts : State C Ghosts :=
  ((((original.push (t := .val .int) ⟨-2, rfl⟩).push (t := .oldNet) [(uintOfNat 5, -77)]).push
    (t := .kint) 42).push (t := .val .bool) true)
private def extended (v : PrimTy.uint.Denote) : State C Δ :=
  ghosts.push (t := .val .uint) v
private def gh : Ext Γ Ghosts := .push (.push (.push (.push .refl)))
private def frame : Ext Γ Δ := .push gh
private def target : Idx Γ (.val .uint) := .there .here
private abbrev update : Upd C Δ Γ := copyDrop frame target .here
private def lit (n : Nat) (h : PrimTy.uint.inRange (Int.ofNat n) = true) : Val C Γ .uint :=
  .simple (.lit n h)
private def affine (x : Val C Γ .uint) : Val C Γ .uint :=
  .binop .add rfl rfl (.binop .mul rfl rfl x (lit 3 rfl)) (lit 1 rfl)
private def result : Tm C Γ (.val .uint) :=
  (affine (affine (.simple (.local target)))).lower
private def captured : Option PrimTy.uint.Denote :=
  ((CallResultCapture.capture (.fresh "result" 0) (result.wk (Thin.ofExt gh))).applyV ghosts).map
    (fun q => q.2 _ .here)
private def post : Fml C Γ :=
  .and (.eq (.pvV target) (.app0 (.lit (uintOfNat 22))))
    (.and (.eq (.pvV .here) (.app0 (.lit (uintOfNat 99))))
      (.and (.eq (.app0 (.env .selfBalance)) (.app0 (.lit (uintOfNat 5))))
        (CallFunctionGraph.equalZ (.app1 .net (.app0 (.lit (uintOfNat 5)))) (.app0 (.zlit 19)))))

/-- Two actual checked non-offset applications read the old non-head target. -/
theorem evaluatedCapture : captured = some (uintOfNat 22) := rfl

/-- The mixed logical prefix and result head all disappear from the caller. -/
theorem fullState (v : PrimTy.uint.Denote) :
    ((extended v).setLocal (target.ext frame) v).drop frame = original.setLocal target v :=
  state_drop_set frame target v (extended v)

/-- The actual update returns exactly the old frame with the selected result. -/
theorem evaluatedRestore (v : PrimTy.uint.Denote) :
    update.applyV (extended v) = some (original.globG, original.locV.set target v) := by
  rw [copyDrop_applyV]
  rw [← State.locV_drop]
  rfl

/-- Nontrivial target, neighbor, balance and global ledger observations survive. -/
theorem restored (m : Modality) :
    holds (extended (uintOfNat 22)) (.upd m update post) := by
  rw [holds_copyDrop]
  change holds (original.setLocal target (uintOfNat 22)) post
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Changing the actual result changes the caller observation. -/
theorem changedResult :
    holds (extended (uintOfNat 23))
      (.upd .diamond update (.eq (.pvV target) (.app0 (.lit (uintOfNat 23))))) := by
  rw [holds_copyDrop]
  rfl

/-- A false result is refuted in the same inhabited state. -/
theorem wrongResult : ¬ holds (extended (uintOfNat 22))
    (.upd .diamond update (.eq (.pvV target) (.app0 (.lit (uintOfNat 23))))) := by
  rw [holds_copyDrop]
  change ¬ (some (uintOfNat 22) = some (uintOfNat 23))
  decide +kernel

/-- Writing the other old UInt is not a certificate for the intended target. -/
theorem wrongTarget : ¬ holds (extended (uintOfNat 22))
    (.upd .box (copyDrop frame (.here : Idx Γ (.val .uint)) .here)
      (.eq (.pvV target) (.app0 (.lit (uintOfNat 22))))) := by
  rw [holds_copyDrop]
  change ¬ (some (uintOfNat 2) = some (uintOfNat 22))
  decide +kernel

/-- The old target and new result remain distinct despite their equal types. -/
theorem positionalFresh : (target.ext gh).there ≠ (.here : Idx Δ (.val .uint)) :=
  target_fresh gh target

/-- All five actual fresh slots are accounted for. -/
theorem prefixDepth : frame.depth = 5 ∧ Δ.length = Γ.length + 5 := ⟨rfl, rfl⟩

/-- The complete copy/drop update is counted, separately from definitions. -/
theorem actualSize : update.tmSize = 2 := copyDrop_size frame target .here

/-- Capture actually evaluates the checked term and directly feeds restoration,
so this proof does not construct a literal-valued restored input state. -/
theorem endToEnd (m : Modality) : holds ghosts
    (leaf m (.fresh "result" 0) gh target (result.wk (Thin.ofExt gh)) post) := by
  apply (holds_leaf_of_eval m (.fresh "result" 0) gh target (result.wk (Thin.ofExt gh))
    post ghosts (uintOfNat 22) rfl).mpr
  change holds (original.setLocal target (uintOfNat 22)) post
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- This complete term/frame/post fixture has 32 structural nodes. -/
theorem endToEndSize :
    (leaf .box (.fresh "result" 0) gh target (result.wk (Thin.ofExt gh)) post).tmSize = 32 := rfl

private def failing : Tm C Ghosts (.val .uint) :=
  ((Val.binop .div rfl rfl (lit 1 rfl) (lit 0 rfl)).lower).wk (Thin.ofExt gh)

/-- A selected genuine failure still proves a false box postcondition. -/
theorem endFailureBox : holds ghosts
    (leaf .box (.fresh "result" 0) gh target failing (.not .tt)) := by
  apply (holds_leaf_of_none .box (.fresh "result" 0) gh target failing (.not .tt) ghosts rfl).mpr
  exact Or.inl trivial

/-- The same non-exhausting failure cannot prove even true under diamond. -/
theorem endFailureDiamond : ¬ holds ghosts
    (leaf .diamond (.fresh "result" 0) gh target failing .tt) := by
  rw [holds_leaf_of_none .diamond (.fresh "result" 0) gh target failing .tt ghosts rfl]
  change ¬ (False ∨ false = true)
  simp only [Bool.false_eq_true, or_self, not_false_eq_true]

private abbrev Signed : Ctx := [.val .int, .val .uint]
private def signedStart : State C Signed :=
  ((State.init C).push (t := .val .uint) (uintOfNat 99)).push (t := .val .int) ⟨2, rfl⟩
private def signedFrame : Ext Signed (.val .int :: .oldNet :: Signed) := .push (.push .refl)
private def signedState : State C (.val .int :: .oldNet :: Signed) :=
  (signedStart.push (t := .oldNet) []).push (t := .val .int) ⟨-7, rfl⟩

/-- Signed returning values retain their primitive type through the ghost frame. -/
theorem signed (m : Modality) : holds signedState
    (.upd m (copyDrop signedFrame (.here : Idx Signed (.val .int)) .here)
      (.eq (.pvV .here) (.app0 (.lit (p := .int) ⟨-7, rfl⟩)))) := by
  rw [holds_copyDrop]
  rfl

private def boolFrame : Ext [.val .bool] [.val .bool, .oldNet, .val .bool] :=
  .push (.push .refl)
private def boolState : State C [.val .bool, .oldNet, .val .bool] :=
  (((State.init C).push (t := .val .bool) false).push (t := .oldNet) []).push (t := .val .bool) true

/-- Boolean values also pass through the actual oldNet prefix for both modes. -/
theorem boolean (m : Modality) : holds boolState
    (.upd m (copyDrop boolFrame (.here : Idx [.val .bool] (.val .bool)) .here)
      (.eq (.pvV .here) (.app0 (.lit true)))) := by
  rw [holds_copyDrop]
  rfl

end Solidity.Examples.Tactics.CallResultRestore
