import Solidity.Backend.Passes.ValueCertificate
import Solidity.Backend.Passes.LinkedControls

/-! Mixed memory/core expression and capture controls using existing Instrs. -/
namespace Solidity.Backend.Passes.ExpressionControls

open Solidity.Evm
open Solidity.Evm.Memory
open Solidity.Backend.Passes.Controls.Fixture

def badRead : Val C Γ .uint :=
  .readMem (.index .dyn (.var (.there (.there (.there .here))) rfl) (.simple (.lit 1 rfl)))

def badTest : Val C Γ .bool :=
  .binop .eqB rfl rfl badRead (.simple (.lit 0 rfl))

def conjunction (left : Bool) : Val C Γ .bool :=
  .binop .and rfl rfl (.simple (.bool left)) badTest

def disjunction (left : Bool) : Val C Γ .bool :=
  .binop .or rfl rfl (.simple (.bool left)) badTest

def choice : Val C Γ .uint :=
  .ternary (.simple (.bool true)) (.simple (.lit 7 rfl)) badRead

def checkedAnd (left : Bool) : CompiledVal 0 (Frag.init Γ) (conjunction left) :=
  (Memory.compileVal 0 (Frag.init Γ) (conjunction left)).get (by cases left <;> decide +kernel)

def checkedOr (left : Bool) : CompiledVal 0 (Frag.init Γ) (disjunction left) :=
  (Memory.compileVal 0 (Frag.init Γ) (disjunction left)).get (by cases left <;> decide +kernel)

def checkedChoice : CompiledVal 0 (Frag.init Γ) choice :=
  (Memory.compileVal 0 (Frag.init Γ) choice).get (by decide +kernel)

def checkedBad : CompiledVal 0 (Frag.init Γ) badTest :=
  (Memory.compileVal 0 (Frag.init Γ) badTest).get (by decide +kernel)

/-- Unselected failing operands do not run, with arbitrary nonempty or
empty caller tails. The *entire* initial machine is restored below false. -/
theorem short_circuit_tail (tail : List Word) :
    run (checkedAnd false).code {machine with stack := tail} =
      .ok ({machine with stack := tail}.push (.val (bword false))) 0 := by
  obtain ⟨word, hw, ht⟩ :=
    value_success_tail (checkedAnd false) fixture_repr (value := false) rfl tail
  have he : word = .val (bword false) := hw
  rw [he] at ht
  exact ht

/-- The opposite short-circuit branch similarly preserves true. -/
theorem disjunction_tail (tail : List Word) :
    run (checkedOr true).code {machine with stack := tail} =
      .ok ({machine with stack := tail}.push (.val (bword true))) 0 := by
  obtain ⟨word, hw, ht⟩ :=
    value_success_tail (checkedOr true) fixture_repr (value := true) rfl tail
  have he : word = .val (bword true) := hw
  rw [he] at ht
  exact ht

/-- Both operators really reach the failing RHS on their other branch. -/
theorem selected_failure (tail : List Word) :
    run (checkedAnd true).code {machine with stack := tail} = .revert ∧
    run (checkedOr false).code {machine with stack := tail} = .revert := by
  constructor
  · exact (value_revert_iff (checkedAnd true) fixture_repr tail).mpr (by with_unfolding_all rfl)
  · exact (value_revert_iff (checkedOr false) fixture_repr tail).mpr (by with_unfolding_all rfl)

/-- Eagerly moving the RHS in front of a short-circuit expression is wrong. -/
theorem eager_order_reverts :
    run (checkedBad.code ++ (checkedAnd false).code) machine = .revert :=
  run_append_revert (Evm.Out.eq_revert (by decide +kernel))

private def topValue : Evm.Out → Option Nat
  | .ok m _ => match m.stack with | .val w :: _ => some w.val | _ => none
  | _ => none

/-- The conditional's unselected failing memory read is skipped. -/
theorem conditional_seven : topValue (run checkedChoice.code machine) = some 7 := by
  decide +kernel

/-- A primitive two-result capture uses two fresh intrinsic locals, not
an untyped tuple layer. Their order survives a subsequent memory write. -/
private def captureFirst : Stmt C Γ (.val .uint :: Γ) :=
  .declLocal .uint (.user "first")
    (some (.readMem (.index .dyn (.var (.there (.there .here)) rfl) (.simple (.lit 0 rfl)))))

private def captureSecond : Stmt C (.val .uint :: Γ) (.val .uint :: .val .uint :: Γ) :=
  .declLocal .uint (.user "second")
    (some (.readMem (.index .dyn (.var (.there (.there (.there .here))) rfl)
      (.simple (.lit 1 rfl)))))

private def updateAfter : Stmt C (.val .uint :: .val .uint :: Γ)
    (.val .uint :: .val .uint :: Γ) :=
  .assignMem (.index .dyn (.var (.there (.there (.there (.there .here)))) rfl)
    (.simple (.lit 0 rfl))) (.val (.simple (.lit 12 rfl)))

def capturePair : Prog C Γ (.val .uint :: .val .uint :: Γ) :=
  .cons captureFirst (.cons captureSecond (.cons updateAfter .nil))

def checkedPair : Compiler.Compilation 0 (Frag.init Γ) capturePair :=
  (Compiler.compile 0 (Frag.init Γ) capturePair).get (by decide +kernel)

private def cellValue (a : Nat) : Evm.Out → Option Nat
  | .ok m _ => match m.mem a with | .val w => some w.val | _ => none
  | _ => none

/-- Captures read 7 then 9, and remain 7 and 9 after the aliased element
changes to 12. Wrong recapture after that effect would read 12. -/
theorem captured_pair_values :
    cellValue 4 (run checkedPair.code machine) = some 7 ∧
    cellValue 5 (run checkedPair.code machine) = some 9 ∧
    cellValue 17 (run checkedPair.code machine) = some 12 := by
  constructor
  · decide +kernel
  · constructor <;> decide +kernel

/-- The captured program has a full represented input at the enlarged frame. -/
theorem captured_pair_certificate : checkedPair.Agrees 1 6 base σ machine :=
  checkedPair.correct ((checkedPair.memory_input (by decide +kernel) 1 6 base σ machine).mpr
    ⟨LinkedControls.frame_six, by decide +kernel, .inl (by decide +kernel)⟩)

end Solidity.Backend.Passes.ExpressionControls
