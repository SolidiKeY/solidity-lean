import Solidity.Backend.PrimitivePackets.UnsignedCast.Semantics
import Solidity.Evm.MemoryCompile

/-! Public compiler selection and exact symbolic EVM narrowing instructions.
The constant divisor is nonzero for every legal width; the existing checked
MOD sequence is retained verbatim, including its zero-divisor guard. -/
namespace Solidity.Backend.PrimitivePackets.UnsignedCast
open Solidity.Lowering.V07
open Solidity.Lowering.V07.UnsignedNarrowing
open Evm Evm.Memory

/-- Exactly the emitted symbolic instructions, including the original guard. -/
def instructions {Γ : Ctx} (offset bits : Nat) (j : Idx Γ (.val .uint)) : List Instr :=
  [.mload (cellOf offset j), .push (.val (wmod (toWord ((2 ^ bits : Nat) : Int)))),
    .dup 1, .jumpi 1, .revert, .swap 1, .mod]

def selected {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (bits : Nat) (legal : Legal bits) (j : Idx Γ (.val .uint)) :
    CompiledVal offset F (value (C := C) bits legal j) :=
  ⟨instructions offset bits j,
    .binary .mod rfl rfl _ _ _ _ (.core _ rfl) (.core _ rfl)⟩

theorem compile_selection {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (bits : Nat) (legal : Legal bits) (j : Idx Γ (.val .uint)) :
    Memory.compileVal offset F (value (C := C) bits legal j) =
      some (selected offset F bits legal j) := by
  rfl

theorem generated_code {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (bits : Nat) (legal : Legal bits) (j : Idx Γ (.val .uint)) :
    (Memory.compileVal offset F (value (C := C) bits legal j)).map (·.code) =
      some (instructions offset bits j) := by
  rw [compile_selection]
  rfl

/-- The complete machine result, including every protected field and saved
stack word. Selection is proved above; no supplied CompiledVal is a premise. -/
theorem machine_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (offset L frame : Nat) (F : Frag Γ) (base : Nat → Fin W) (machine : Machine)
    (represented : StateRepr L offset frame F target base machine)
    (bits : Nat) (legal : Legal bits) (j : Idx Γ (.val .uint))
    (n : Int) (range : Source.IntTy.u256.lo ≤ n ∧ n ≤ Source.IntTy.u256.hi)
    (read : TEnv.get j target.env = integerValue Source.IntTy.u256 n range)
    (saved : List Word) :
    let result := integerValue (targetTy bits legal) ((targetTy bits legal).wrap n)
      ((targetTy bits legal).wrap_mem n)
    run (instructions offset bits j) {machine with stack := saved} =
      .ok ({machine with stack := saved}.push (.val result.word)) 0 := by
  have evaluation := value_run target bits legal j n range read
  have execution := (selected offset F bits legal j).cert.correct (represented.stack saved)
  rw [evaluation] at execution
  rcases execution with ⟨v,w,ev,repr,execution⟩ | ⟨ev,_⟩
  · cases Except.ok.inj ev
    obtain ⟨a,rfl,ha⟩ := repr
    have same : a = (integerValue (targetTy bits legal) ((targetTy bits legal).wrap n)
        ((targetTy bits legal).wrap_mem n)).word := by
      apply Fin.ext
      exact Int.ofNat_inj.mp (ha.symm.trans (word_val _).symm)
    rw [same] at execution
    exact execution
  · cases ev

end Solidity.Backend.PrimitivePackets.UnsignedCast
