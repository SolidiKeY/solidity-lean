import Solidity.Backend.PrimitivePackets.SignedCheckedMul.Agreement
import Solidity.Backend.PrimitivePackets.SignedDiv.Controls

/-! Selected-code controls for checked int256 multiplication. Every joint control
instantiates the arbitrary-state `success`/`overflow` theorems at the populated
six-cell frame of `SignedDiv.Controls` with an arbitrary saved stack `tail`:
both operand orders of `-2^255 * -1`, upper and lower overflow, and regular
products of every sign. `guard_classification` is the existing `Evm.smul_tail`
at the selected guard, not a second arithmetic producer. -/
namespace Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls
open Evm Evm.Memory Solidity.Lowering.V07 Source.SemanticsExamples

def si (k : Bool) : Source.Idx [.int U,.int U] (.int U) := if k then .there .here else .here
def ti (k : Bool) : Idx SignedDiv.Controls.Γ (.val .int) := if k then .there .here else .here

theorem family (a b : PrimTy.int.Denote) :
 IntegerLocalFamily U si ti (SignedDiv.Controls.source a b).1 (SignedDiv.Controls.target a b).env := by
 constructor
 · intro k; cases k <;> exact integer_related _ _ _
 · intro i j; cases i <;> cases j <;> decide

def joint_success (p : Roadmap.Pipeline) (a b : PrimTy.int.Denote)
 (fits : U.lo≤a.val*b.val ∧ a.val*b.val≤U.hi) (tail : List Word) :=
 let result := success (G0 p) F0 0 (SignedDiv.Controls.source a b)
  (SignedDiv.Controls.target a b) si ti (family a b) false true a.val b.val
  (SignedDiv.range a) (SignedDiv.range b) rfl rfl fits (SignedDiv.Controls.initial a b) tail
 And.intro result.2.1 result.2.2

def joint_overflow (p : Roadmap.Pipeline) (a b : PrimTy.int.Denote)
 (outside : ¬ (U.lo≤a.val*b.val ∧ a.val*b.val≤U.hi)) (tail : List Word) :=
 let result := overflow (G0 p) F0 0 (SignedDiv.Controls.source a b)
  (SignedDiv.Controls.target a b) si ti (family a b) false true a.val b.val
  (SignedDiv.range a) (SignedDiv.range b) rfl rfl outside (SignedDiv.Controls.initial a b) tail
 And.intro result.2.1 result.2.2

def maximum : PrimTy.int.Denote := ⟨((2^255:Nat):Int)-1,by decide⟩
def minimum : PrimTy.int.Denote := ⟨-((2^255:Nat):Int),by decide⟩
def one : PrimTy.int.Denote := ⟨1,by decide⟩
def minus : PrimTy.int.Denote := ⟨-1,by decide⟩
def two : PrimTy.int.Denote := ⟨2,by decide⟩
def seven : PrimTy.int.Denote := ⟨7,by decide⟩
def negSeven : PrimTy.int.Denote := ⟨-7,by decide⟩
def nine : PrimTy.int.Denote := ⟨9,by decide⟩
def negNine : PrimTy.int.Denote := ⟨-9,by decide⟩
def zero : PrimTy.int.Denote := ⟨0,by decide⟩

/-- `-2^255 * -1 = 2^255` overflows in both operand orders. -/
def minimum_minus (p : Roadmap.Pipeline) (tail : List Word) := joint_overflow p minimum minus (by decide) tail
def minus_minimum (p : Roadmap.Pipeline) (tail : List Word) := joint_overflow p minus minimum (by decide) tail
/-- Upper overflow other than `-2^255 * -1`: positive and negative operand pairs. -/
def upper (p : Roadmap.Pipeline) (tail : List Word) := joint_overflow p maximum two (by decide) tail
def upper_negative (p : Roadmap.Pipeline) (tail : List Word) := joint_overflow p minimum minimum (by decide) tail
/-- Lower overflow, both operand orders. -/
def lower (p : Roadmap.Pipeline) (tail : List Word) := joint_overflow p minimum two (by decide) tail
def lower_swapped (p : Roadmap.Pipeline) (tail : List Word) := joint_overflow p two minimum (by decide) tail
def lower_maximum (p : Roadmap.Pipeline) (tail : List Word) := joint_overflow p maximum negNine (by decide) tail
/-- Regular products of every sign and the boundary successes. -/
def regular (p : Roadmap.Pipeline) (tail : List Word) := joint_success p negSeven nine (by decide) tail
def regular_positive (p : Roadmap.Pipeline) (tail : List Word) := joint_success p negSeven negNine (by decide) tail
def regular_swapped (p : Roadmap.Pipeline) (tail : List Word) := joint_success p nine negSeven (by decide) tail
def minimum_one (p : Roadmap.Pipeline) (tail : List Word) := joint_success p minimum one (by decide) tail
def one_minimum (p : Roadmap.Pipeline) (tail : List Word) := joint_success p one minimum (by decide) tail
def maximum_minus (p : Roadmap.Pipeline) (tail : List Word) := joint_success p maximum minus (by decide) tail
def minus_maximum (p : Roadmap.Pipeline) (tail : List Word) := joint_success p minus maximum (by decide) tail
def minimum_zero (p : Roadmap.Pipeline) (tail : List Word) := joint_success p minimum zero (by decide) tail
def zero_minimum (p : Roadmap.Pipeline) (tail : List Word) := joint_success p zero minimum (by decide) tail

/-- The selected guard is `Evm.smul_tail` on arbitrary operand words and saved stack. -/
theorem guard_classification (m : Machine) (st : List Word) {a b : Nat} (ha : a < W) (hb : b < W) :
 run (sTail .mul) {m with stack := w[b] :: w[a] :: st} =
  if -(H : Int) ≤ sgn a * sgn b ∧ sgn a * sgn b < H then
   .ok {m with stack := .val (sword (sgn a * sgn b)) :: st} 0
  else .revert := smul_tail m st ha hb

/-- The checked code does not wrap `-2^255 * -1` to `-2^255`, in either order. -/
theorem minimum_minus_not_wrap (p : Roadmap.Pipeline) (tail : List Word) :
 run (selected (C:=SignedDiv.Controls.P) 0 SignedDiv.Controls.F
  (.here : Idx SignedDiv.Controls.Γ (.val .int)) (.there .here)).code
 {SignedDiv.Controls.machine minimum minus with stack:=tail}≠
 .ok ({SignedDiv.Controls.machine minimum minus with stack:=tail}.push (.val (sword minimum.val))) 0 := by
 have actual := (minimum_minus p tail).2
 simp only [ti, Bool.false_eq_true, if_false, if_true] at actual
 rw [actual]
 intro wrong
 cases wrong

theorem minus_minimum_not_wrap (p : Roadmap.Pipeline) (tail : List Word) :
 run (selected (C:=SignedDiv.Controls.P) 0 SignedDiv.Controls.F
  (.here : Idx SignedDiv.Controls.Γ (.val .int)) (.there .here)).code
 {SignedDiv.Controls.machine minus minimum with stack:=tail}≠
 .ok ({SignedDiv.Controls.machine minus minimum with stack:=tail}.push (.val (sword minimum.val))) 0 := by
 have actual := (minus_minimum p tail).2
 simp only [ti, Bool.false_eq_true, if_false, if_true] at actual
 rw [actual]
 intro wrong
 cases wrong

/-- The exact product word is pushed onto the arbitrary saved stack; a wrong word is refused. -/
theorem regular_exact (p : Roadmap.Pipeline) (tail : List Word) :
 run (selected (C:=SignedDiv.Controls.P) 0 SignedDiv.Controls.F
  (.here : Idx SignedDiv.Controls.Γ (.val .int)) (.there .here)).code
 {SignedDiv.Controls.machine negSeven nine with stack:=tail} =
 .ok ({SignedDiv.Controls.machine negSeven nine with stack:=tail}.push (.val (sword (-63)))) 0 := by
 obtain ⟨word,rep,actual⟩ := (regular p tail).2
 simp only [ti, Bool.false_eq_true, if_false, if_true] at actual
 rw [SignedDiv.Controls.word_unique _ word rep] at actual
 exact actual

theorem wrong_result (p : Roadmap.Pipeline) (tail : List Word) :
 run (selected (C:=SignedDiv.Controls.P) 0 SignedDiv.Controls.F
  (.here : Idx SignedDiv.Controls.Γ (.val .int)) (.there .here)).code
 {SignedDiv.Controls.machine negSeven nine with stack:=tail}≠
 .ok ({SignedDiv.Controls.machine negSeven nine with stack:=tail}.push (.val (sword 63))) 0 := by
 rw [regular_exact p tail]
 intro wrong
 have same := (List.cons.inj (congrArg Machine.stack (Evm.Out.ok.inj wrong).1)).1
 exact (by decide : Word.val (sword (-63))≠Word.val (sword 63)) same

theorem low_fuel (p : Roadmap.Pipeline) :
 (Source.evalE (G0 p) {F0 with checked:=true} 0
 (.binary .mul (.local .here) (.local (.there .here)))).run (SignedDiv.Controls.source seven two)=
 (.error .timeout,SignedDiv.Controls.source seven two) := by rfl

theorem exact_panic : Source.panicData .arithmetic=[78,72,123,113]++List.replicate 31 0++[17] := by decide
end Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls
