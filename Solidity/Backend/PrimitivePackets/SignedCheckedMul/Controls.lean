import Solidity.Backend.PrimitivePackets.SignedCheckedMul.Agreement
import Solidity.Backend.PrimitivePackets.SignedDiv.Controls

/-! Selected-code controls for checked int256 multiplication. Every joint control
instantiates the arbitrary-state `success`/`overflow` theorems at the populated
six-cell frame of `SignedDiv.Controls` with an arbitrary saved stack `tail`:
both operand orders of `-2^255 * -1`, upper and lower overflow, and regular
products of all four operand-sign combinations. `guard_classification` is the existing `Evm.smul_tail`
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
/-- Regular products for all four operand-sign combinations, and the boundary successes. -/
def regular (p : Roadmap.Pipeline) (tail : List Word) := joint_success p negSeven nine (by decide) tail
def regular_positive (p : Roadmap.Pipeline) (tail : List Word) := joint_success p negSeven negNine (by decide) tail
def regular_both_positive (p : Roadmap.Pipeline) (tail : List Word) := joint_success p seven nine (by decide) tail
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
 exact fun wrong => nomatch actual.symm.trans wrong

theorem minus_minimum_not_wrap (p : Roadmap.Pipeline) (tail : List Word) :
 run (selected (C:=SignedDiv.Controls.P) 0 SignedDiv.Controls.F
  (.here : Idx SignedDiv.Controls.Γ (.val .int)) (.there .here)).code
 {SignedDiv.Controls.machine minus minimum with stack:=tail}≠
 .ok ({SignedDiv.Controls.machine minus minimum with stack:=tail}.push (.val (sword minimum.val))) 0 := by
 have actual := (minus_minimum p tail).2
 exact fun wrong => nomatch actual.symm.trans wrong

/-- The exact product word is pushed onto the arbitrary saved stack; a wrong word is refused. -/
theorem regular_exact (p : Roadmap.Pipeline) (tail : List Word) :
 run (selected (C:=SignedDiv.Controls.P) 0 SignedDiv.Controls.F
  (.here : Idx SignedDiv.Controls.Γ (.val .int)) (.there .here)).code
 {SignedDiv.Controls.machine negSeven nine with stack:=tail} =
 .ok ({SignedDiv.Controls.machine negSeven nine with stack:=tail}.push (.val (sword (-63)))) 0 := by
 obtain ⟨word,rep,actual⟩ := (regular p tail).2
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
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.source_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.PrimitivePackets.SignedCheckedMul.source_success
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.source_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.PrimitivePackets.SignedCheckedMul.source_overflow
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.public_selection' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.PrimitivePackets.SignedCheckedMul.public_selection
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.original_guard' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.PrimitivePackets.SignedCheckedMul.original_guard
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.guard_is_sTail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.PrimitivePackets.SignedCheckedMul.guard_is_sTail
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.value_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.PrimitivePackets.SignedCheckedMul.value_success
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.value_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.PrimitivePackets.SignedCheckedMul.value_overflow
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.target_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.PrimitivePackets.SignedCheckedMul.target_success
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.target_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.PrimitivePackets.SignedCheckedMul.target_overflow
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.PrimitivePackets.SignedCheckedMul.success
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.PrimitivePackets.SignedCheckedMul.overflow
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.overflow_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.PrimitivePackets.SignedCheckedMul.overflow_iff
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls.family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms family
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls.minimum_minus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms minimum_minus
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls.minus_minimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms minus_minimum
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls.upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms upper
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls.upper_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms upper_negative
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls.lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lower
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls.lower_swapped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lower_swapped
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls.lower_maximum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lower_maximum
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls.regular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms regular
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls.regular_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms regular_positive
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls.regular_both_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms regular_both_positive
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls.regular_swapped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms regular_swapped
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls.minimum_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms minimum_one
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls.one_minimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms one_minimum
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls.maximum_minus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms maximum_minus
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls.minus_maximum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms minus_maximum
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls.minimum_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms minimum_zero
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls.zero_minimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_minimum
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls.guard_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms guard_classification
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls.minimum_minus_not_wrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms minimum_minus_not_wrap
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls.minus_minimum_not_wrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms minus_minimum_not_wrap
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls.regular_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms regular_exact
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls.wrong_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_result
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls.low_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms low_fuel
/-- info: 'Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls.exact_panic' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms exact_panic
end Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls
