import Solidity.Backend.PrimitivePackets.UnsignedMul.Execution
import Solidity.Backend.PrimitivePackets.BitNot.Controls

/-! Regression: unchecked unsigned multiplication must clean at every legal
byte width for all operand pairs, including nonzero wrapping products, while
preserving populated caller memory and arbitrary saved stacks. Actual local
family/input witnesses replace no execution or compiler premise. No checked
multiplication, heap/world/session/gas or fetched-EVM adequacy is asserted. -/
namespace H62.PrimitivePackets.UnsignedMulCorrespondence
open Solidity Solidity.Evm Solidity.Evm.Memory Solidity.Lowering.V07
open Solidity.Lowering.V07.UnsignedNarrowing (ty)
open Solidity.Backend.PrimitivePackets.UnsignedMul
open Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture (F target machine represented nat_range)

abbrev Valid (bits : Nat) := bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256

def source {E : Source.Env} {Δ : Source.RCtx} (bits : Nat) (valid : Valid bits)
    (x y : Fin (2^bits)) (tail : Source.Locals E.layout Δ) (state : Source.St E) :
    Source.EMState E (.int (ty bits valid) :: .int (ty bits valid) :: Δ) :=
  (.cons (.int x.val (nat_range bits valid x.val x.isLt))
    (.cons (.int y.val (nat_range bits valid y.val y.isLt)) tail),state)

def si {Δ : Source.RCtx} (bits : Nat) (valid : Valid bits) :
    Bool → Source.Idx (.int (ty bits valid) :: .int (ty bits valid) :: Δ) (.int (ty bits valid))
  | false => .here
  | true => .there .here

def ti : Bool → Idx Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.Γ (.val .uint)
  | false => .here
  | true => .there .here

theorem family {E : Source.Env} {Δ : Source.RCtx} (bits : Nat) (valid : Valid bits)
    (x y : Fin (2^bits)) (tail : Source.Locals E.layout Δ) (state : Source.St E) :
    IntegerLocalFamily (ty bits valid) (si bits valid) ti (source bits valid x y tail state).1
      (target bits valid x.val y.val x.isLt y.isLt).env := by
  constructor
  · intro k; cases k <;> exact integer_related _ _ _
  · intro k l; cases k <;> cases l <;> rfl

abbrev outcome (bits : Nat) (valid : Valid bits) (x y : Fin (2^bits)) :=
  integerValue (ty bits valid) ((ty bits valid).wrap ((x.val : Int) * (y.val : Int)))
    ((ty bits valid).wrap_mem ((x.val : Int) * (y.val : Int)))
def code (bits : Nat) := (selected (C := CompileExamples.C) 0 F bits (ti false) (ti true)).code

theorem joint {E : Source.Env} {Δ : Source.RCtx}
    (bits : Nat) (valid : Valid bits) (x y : Fin (2^bits))
    (G : Source.Glob E) (fr : Source.Fr) (fuel : Nat)
    (tail : Source.Locals E.layout Δ) (state : Source.St E) (saved : List Word) :
    (Source.evalE G {fr with checked := false} (fuel+3)
      (.binary .mul (.local .here) (.local (.there .here)))).run (source bits valid x y tail state) =
      (.ok (.val (Source.intWrap (ty bits valid) ((x.val : Int)*(y.val : Int)))),
        source bits valid x y tail state) ∧
    compileVal 0 F (expression (C := CompileExamples.C) bits (ti false) (ti true)) =
      some (selected 0 F bits (ti false) (ti true)) ∧
    run (code bits) {machine bits valid x.val y.val x.isLt y.isLt with stack := saved} =
      .ok ({machine bits valid x.val y.val x.isLt y.isLt with stack := saved}.push
        (.val (outcome bits valid x y).word)) 0 ∧
    StateRepr 1 0 8 F (target bits valid x.val y.val x.isLt y.isLt) CompileExamples.base
      ({machine bits valid x.val y.val x.isLt y.isLt with stack := saved}.push
        (.val (outcome bits valid x y).word)) := by
  have h := execution G fr fuel (source bits valid x y tail state)
    (target bits valid x.val y.val x.isLt y.isLt) bits valid (si bits valid) ti
    (family bits valid x y tail state) false true x.val y.val
    (nat_range bits valid x.val x.isLt) (nat_range bits valid y.val y.isLt) rfl rfl
    (represented bits valid x.val y.val x.isLt y.isLt)
  obtain ⟨word,repr,runs⟩ := h.2.2.2.2
  rcases repr with ⟨actual,rfl,content⟩
  have same : actual = (outcome bits valid x y).word := by
    apply Fin.ext
    exact Int.ofNat_inj.mp (content.symm.trans (word_val _).symm)
  rw [same] at runs
  exact ⟨h.1,h.2.2.2.1,(runs saved).1,(runs saved).2⟩

theorem reject_all_refuted (bits : Nat) (valid : Valid bits) (x y : Fin (2^bits))
    (saved : List Word) :
    run (code bits) {machine bits valid x.val y.val x.isLt y.isLt with stack := saved} ≠ .revert := by
  have h := (joint bits valid x y (Source.SemanticsExamples.G0 .legacy)
    Source.SemanticsExamples.F0 0 .nil Source.SemanticsExamples.s0 saved).2.2.1
  rw [h]
  intro same
  cases same

#print axioms family
#print axioms joint
#print axioms reject_all_refuted
end H62.PrimitivePackets.UnsignedMulCorrespondence
