import Solidity.Backend.PrimitivePackets.SignedCheckedSub.Agreement
import Solidity.Backend.PrimitivePackets.SignedDiv.Controls
namespace Solidity.Backend.PrimitivePackets.SignedCheckedSub.Controls
open Evm Evm.Memory Solidity.Lowering.V07 Source.SemanticsExamples

def si (k : Bool) : Source.Idx [.int U,.int U] (.int U) := if k then .there .here else .here
def ti (k : Bool) : Idx SignedDiv.Controls.Γ (.val .int) := if k then .there .here else .here

theorem family (a b : PrimTy.int.Denote) :
 IntegerLocalFamily U si ti (SignedDiv.Controls.source a b).1 (SignedDiv.Controls.target a b).env := by
 constructor
 · intro k; cases k <;> exact integer_related _ _ _
 · intro i j; cases i <;> cases j <;> decide

def joint_success (p : Roadmap.Pipeline) (a b : PrimTy.int.Denote)
 (fits : U.lo≤a.val-b.val ∧ a.val-b.val≤U.hi) (tail : List Word) :=
 let result := success (G0 p) F0 0 (SignedDiv.Controls.source a b)
  (SignedDiv.Controls.target a b) si ti (family a b) false true a.val b.val
  (SignedDiv.range a) (SignedDiv.range b) rfl rfl fits (SignedDiv.Controls.initial a b) tail
 And.intro result.2.1 result.2.2

def joint_overflow (p : Roadmap.Pipeline) (a b : PrimTy.int.Denote)
 (outside : ¬ (U.lo≤a.val-b.val ∧ a.val-b.val≤U.hi)) (tail : List Word) :=
 let result := overflow (G0 p) F0 0 (SignedDiv.Controls.source a b)
  (SignedDiv.Controls.target a b) si ti (family a b) false true a.val b.val
  (SignedDiv.range a) (SignedDiv.range b) rfl rfl outside (SignedDiv.Controls.initial a b) tail
 And.intro result.2.1 result.2.2

def maximum : PrimTy.int.Denote := ⟨((2^255:Nat):Int)-1,by decide⟩
def minimum : PrimTy.int.Denote := ⟨-((2^255:Nat):Int),by decide⟩
def one : PrimTy.int.Denote := ⟨1,by decide⟩
def minus : PrimTy.int.Denote := ⟨-1,by decide⟩
def seven : PrimTy.int.Denote := ⟨7,by decide⟩
def two : PrimTy.int.Denote := ⟨2,by decide⟩
def zero : PrimTy.int.Denote := ⟨0,by decide⟩
def upper (p : Roadmap.Pipeline) (tail : List Word) := joint_overflow p maximum minus (by decide) tail
def lower (p : Roadmap.Pipeline) (tail : List Word) := joint_overflow p minimum one (by decide) tail
def regular (p : Roadmap.Pipeline) (tail : List Word) := joint_success p seven two (by decide) tail
def minimum_success (p : Roadmap.Pipeline) (tail : List Word) := joint_success p minimum zero (by decide) tail
def maximum_success (p : Roadmap.Pipeline) (tail : List Word) := joint_success p maximum zero (by decide) tail

theorem upper_not_wrap (p : Roadmap.Pipeline) (tail : List Word) :
 run (selected (C:=SignedDiv.Controls.P) 0 SignedDiv.Controls.F
  (.here : Idx SignedDiv.Controls.Γ (.val .int)) (.there .here)).code
 {SignedDiv.Controls.machine maximum minus with stack:=tail}≠
 .ok ({SignedDiv.Controls.machine maximum minus with stack:=tail}.push (.val (sword minimum.val))) 0 := by
 have actual := (upper p tail).2
 simp [ti] at actual
 rw [actual]
 intro wrong
 cases wrong

theorem wrong_result (p : Roadmap.Pipeline) (tail : List Word) :
 run (selected (C:=SignedDiv.Controls.P) 0 SignedDiv.Controls.F
  (.here : Idx SignedDiv.Controls.Γ (.val .int)) (.there .here)).code
 {SignedDiv.Controls.machine seven two with stack:=tail}≠
 .ok ({SignedDiv.Controls.machine seven two with stack:=tail}.push w[9]) 0 := by
 obtain ⟨word,rep,actual⟩ := (regular p tail).2
 simp [ti] at actual
 rw [SignedDiv.Controls.word_unique _ word rep] at actual
 rw [actual]
 intro wrong
 have same := (List.cons.inj (congrArg Machine.stack (Evm.Out.ok.inj wrong).1)).1
 exact (by decide : Word.val (sword 5)≠w[9]) same

theorem low_fuel (p : Roadmap.Pipeline) :
 (Source.evalE (G0 p) {F0 with checked:=true} 0
 (.binary .sub (.local .here) (.local (.there .here)))).run (SignedDiv.Controls.source seven two)=
 (.error .timeout,SignedDiv.Controls.source seven two) := by rfl

theorem exact_panic : Source.panicData .arithmetic=[78,72,123,113]++List.replicate 31 0++[17] := by decide
#print axioms source_success
#print axioms source_overflow
#print axioms public_selection
#print axioms original_guard
#print axioms value_success
#print axioms value_overflow
#print axioms success
#print axioms overflow
#print axioms overflow_iff
#print axioms upper
#print axioms lower
#print axioms regular
#print axioms minimum_success
#print axioms maximum_success
#print axioms upper_not_wrap
#print axioms wrong_result
#print axioms low_fuel
#print axioms exact_panic
end Solidity.Backend.PrimitivePackets.SignedCheckedSub.Controls
