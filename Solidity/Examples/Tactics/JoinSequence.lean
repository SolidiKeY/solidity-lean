import Solidity.Calculus.Sound.JoinSequence
import Solidity.Calculus.JoinSequenceSize

/-! # Inhabited joined-assignment execution controls
These check the standalone builder, before walker registration. -/
namespace Solidity.Examples.Tactics.JoinSequence
private abbrev C := StandardExample
private abbrev Γ : Ctx := [.val .bool, .val .uint]
private def uint (n : Nat) (h : PrimTy.uint.inRange (Int.ofNat n) = true) : Val C Γ .uint :=
  .simple (.lit n h)
private def yes : LocalWrites C Γ :=
  [⟨.bool, .here, .simple (.bool false)⟩,
   ⟨.uint, .there .here, uint 1 rfl⟩,
   ⟨.uint, .there .here, .binop .add rfl rfl (.simple (.local (.there .here))) (uint 1 rfl)⟩]
private def no : LocalWrites C Γ :=
  [⟨.uint, .there .here, .binop .div rfl rfl (uint 1 rfl) (uint 0 rfl)⟩]
private def start (b : Bool) : State C Γ :=
  ((State.init C).push (t := .val .uint) (uintOfNat 0)).push (t := .val .bool) b
private def observed (b : Bool) : Option (Bool × PrimTy.uint.Denote) :=
  ((Prog.runSt (start b) (LocalWrites.joined (.fresh "se" 0) (.local .here) yes no)).map
    (fun σ => (σ.env.2.1, σ.env.2.2.1))).toOption

/-- The selected branch changes the original guard, then a later assignment
reads its predecessor. The untaken branch divides by zero. -/
theorem changedGuardDependent : observed true = some (false, uintOfNat 2) := by
  rfl

/-- Selecting the failing branch really fails; it is not erased as dead code. -/
theorem selectedFailure : observed false = none := by
  rfl

/-- A nested Solidity block is deliberately outside the straight-write decoder. -/
theorem refusesNested : (Prog.cons (.block yes.program) .nil).localWrites? = none := rfl

/-- A Solidity requirement is not silently treated as an assignment. -/
theorem refusesRequirement :
    (Prog.cons (.require (.simple (.bool true))) yes.program).localWrites? = none := rfl

/-- Every typed RHS occurs once in emitted syntax: both branches plus guards. -/
theorem emittedSize : (LocalWrites.joined (.fresh "se" 0) (.local .here) yes no).size = 33 := rfl

private def captured : Prog C Γ (.val .bool :: Γ) :=
  .cons (.declLocal .bool (.fresh "se" 0) (some (.simple (.local .here))))
    (.cons (.block (yes.guarded true (no.guarded false))) .nil)
private def capturedObserved (b : Bool) : Option (Bool × PrimTy.uint.Denote) :=
  (((Prog.runSt (start b) captured).map (State.drop (.push .refl))).map
    (fun σ => (σ.env.1, σ.env.2.1))).toOption

/-- The actual capture block keeps the selected dependent writes and skips
an untaken failing RHS even after the source condition changes. -/
theorem capturedChangedGuardDependent :
    capturedObserved true = some (false, uintOfNat 2) := by
  unfold capturedObserved captured
  rw [LocalWrites.captured_drop_runSt (start true) (.fresh "se" 0) (.local .here) yes no]
  rfl

/-- The selected failing branch remains observable through the block. -/
theorem capturedSelectedFailure : capturedObserved false = none := rfl

/-- Actual dispatcher syntax includes the extra block node. -/
theorem capturedEmittedSize : captured.size = 34 := rfl

end Solidity.Examples.Tactics.JoinSequence
