import Solidity.Backend.Passes.StatefulChecked
import Solidity.Backend.Passes.ValueSequenceControls

namespace Solidity.Backend.Passes.StatefulValueControls
open Evm Evm.Memory
open Backend.Passes.Controls.Fixture
open ValueSequenceControls

def wrapping : Val C Γ .uint := .binop .subW rfl rfl first second
def wrappingCode : CompiledVal 0 (Frag.init Γ) wrapping := (compileVal 0 _ wrapping).get (by decide +kernel)
def comparison : Val C Γ .bool := .binop .gt rfl rfl first second
def comparisonCode : CompiledVal 0 (Frag.init Γ) comparison := (compileVal 0 _ comparison).get (by decide +kernel)
def signedRead : Val C Γ .int := .unop .toInt rfl rfl first
def signedCode : CompiledVal 0 (Frag.init Γ) signedRead := (compileVal 0 _ signedRead).get (by decide +kernel)
def negated : Val C Γ .int := .unop .neg rfl rfl signedRead
def negatedCode : CompiledVal 0 (Frag.init Γ) negated := (compileVal 0 _ negated).get (by decide +kernel)

def signedSeven : PrimTy.int.Denote := ⟨7,rfl⟩
def minusSeven : PrimTy.int.Denote := ⟨-7,rfl⟩
def saved : List (Fin W) := [⟨99,by decide⟩]

theorem wrapping_source : wrapping.evalT σ = .ok three := by with_unfolding_all rfl
theorem comparison_source : comparison.evalT σ = .ok true := by with_unfolding_all rfl
theorem signed_source : signedRead.evalT σ = .ok signedSeven := by with_unfolding_all rfl
theorem negated_source : negated.evalT σ = .ok minusSeven := by with_unfolding_all rfl

def wrappingInvocation : Backend.Scalar.BinaryInvocation Backend.Scalar.wrappingSub seven four
    (saved.map (fun w => BitVec.ofNat 256 w.val)) := ⟨by decide +kernel⟩
def comparisonInvocation : Backend.Scalar.BinaryInvocation Backend.Scalar.uintGt seven four
    (saved.map (fun w => BitVec.ofNat 256 w.val)) := ⟨by decide +kernel⟩

theorem operand_words (tail : List Evm.Word) :
    ∃ (wa wd : Fin W), ReprV .uint seven (.val wa) ∧ ReprV .uint four (.val wd) ∧
      Backend.Scalar.encodeValue .uint seven = BitVec.ofNat 256 wa.val ∧
      Backend.Scalar.encodeValue .uint four = BitVec.ofNat 256 wd.val ∧
      run (d.code ++ a.code) {machine with stack := tail} =
        .ok (({machine with stack := tail}.push (.val wd)).push (.val wa)) 0 :=
  StatefulValues.operands a d fixture_repr first_source second_source tail

theorem wrapping_application :
    ∃ w : Fin W, ReprV .uint three (.val w) ∧
      Backend.Scalar.encodeValue .uint three = BitVec.ofNat 256 w.val ∧
      Backend.Scalar.run Backend.Scalar.wrappingSub.code
        (Backend.Scalar.encodeValue .uint seven :: Backend.Scalar.encodeValue .uint four ::
          saved.map (fun w => BitVec.ofNat 256 w.val)) =
        some (BitVec.ofNat 256 w.val :: saved.map (fun w => BitVec.ofNat 256 w.val)) ∧
      run wrappingCode.code {machine with stack := saved.map Evm.Word.val} =
        .ok ({machine with stack := saved.map Evm.Word.val}.push (.val w)) 0 ∧
      Backend.Scalar.stackBound Backend.Scalar.wrappingSub.code ((saved.length+2 : Nat) : Int) = true :=
  (StatefulValues.binary Backend.Scalar.wrappingSub wrappingCode fixture_repr
    first_source second_source rfl (by decide +kernel) saved wrappingInvocation).2

theorem comparison_application :
    ∃ w : Fin W, ReprV .bool true (.val w) ∧
      Backend.Scalar.encodeValue .bool true = BitVec.ofNat 256 w.val ∧
      Backend.Scalar.run Backend.Scalar.uintGt.code
        (Backend.Scalar.encodeValue .uint seven :: Backend.Scalar.encodeValue .uint four ::
          saved.map (fun w => BitVec.ofNat 256 w.val)) =
        some (BitVec.ofNat 256 w.val :: saved.map (fun w => BitVec.ofNat 256 w.val)) ∧
      run comparisonCode.code {machine with stack := saved.map Evm.Word.val} =
        .ok ({machine with stack := saved.map Evm.Word.val}.push (.val w)) 0 ∧
      Backend.Scalar.stackBound Backend.Scalar.uintGt.code ((saved.length+2 : Nat) : Int) = true :=
  (StatefulValues.binary Backend.Scalar.uintGt comparisonCode fixture_repr
    first_source second_source rfl (by decide +kernel) saved comparisonInvocation).2

theorem cast_application :
    ∃ w : Fin W, ReprV .int signedSeven (.val w) ∧
      Backend.Scalar.encodeValue .int signedSeven = BitVec.ofNat 256 w.val ∧
      Backend.Scalar.run Backend.Scalar.toInt.code
        (Backend.Scalar.encodeValue .uint seven :: saved.map (fun w => BitVec.ofNat 256 w.val)) =
        some (BitVec.ofNat 256 w.val :: saved.map (fun w => BitVec.ofNat 256 w.val)) ∧
      run signedCode.code {machine with stack := saved.map Evm.Word.val} =
        .ok ({machine with stack := saved.map Evm.Word.val}.push (.val w)) 0 ∧
      Backend.Scalar.stackBound Backend.Scalar.toInt.code ((saved.length+1 : Nat) : Int) = true :=
  (StatefulValues.unary Backend.Scalar.toInt signedCode fixture_repr first_source
    (by decide +kernel) saved (by decide +kernel)).2

theorem negation_application :
    ∃ w : Fin W, ReprV .int minusSeven (.val w) ∧
      Backend.Scalar.encodeValue .int minusSeven = BitVec.ofNat 256 w.val ∧
      Backend.Scalar.guarded Backend.Scalar.checkedIntNeg.test Backend.Scalar.checkedIntNeg.body
        Backend.Scalar.overflowFailure
        (Backend.Scalar.encodeValue .int signedSeven :: saved.map (fun w => BitVec.ofNat 256 w.val)) =
        some (.ok (BitVec.ofNat 256 w.val :: saved.map (fun w => BitVec.ofNat 256 w.val))) ∧
      run negatedCode.code {machine with stack := saved.map Evm.Word.val} =
        .ok ({machine with stack := saved.map Evm.Word.val}.push (.val w)) 0 ∧
      Backend.Scalar.stackBound Backend.Scalar.checkedIntNeg.test ((saved.length+1 : Nat) : Int) = true ∧
      Backend.Scalar.stackBound Backend.Scalar.checkedIntNeg.body ((saved.length+1 : Nat) : Int) = true :=
  (StatefulChecked.unary_success Backend.Scalar.checkedIntNeg negatedCode fixture_repr signed_source
    (by decide +kernel) saved (by decide +kernel) (by decide +kernel)).2

theorem actual_bytes :
    Backend.encode Backend.Scalar.wrappingSub.code = [0x03] ∧
    Backend.encode Backend.Scalar.uintGt.code = [0x11] ∧
    Backend.encode Backend.Scalar.checkedIntNeg.body = 0x7f :: List.replicate 32 0 ++ [0x03] := by
  decide +kernel

/-- An empty numeric reinterpretation component is not an empty accepted
state-dependent expression: its actual symbolic memory load remains. -/
theorem empty_cast_component :
    Backend.Scalar.toInt.code = [] ∧ signedCode.code ≠ [] := by
  constructor
  · rfl
  · have h : signedCode.code.length ≠ 0 := by decide +kernel
    exact fun e => h (congrArg List.length e)

private def cell (n : Nat) : Evm.Out → Option Nat
  | .ok m _ => match m.mem n with | .val w => some w.val | _ => none
  | _ => none

/-- ALL locals/aliases, both array headers/elements and independent value. -/
theorem ordered_memory : [3,2,1,0,16,17,18,20,21].mapM
    (fun n => cell n (run wrappingCode.code machine)) =
      some [0,16,16,20,2,7,9,1,4] := by decide +kernel

theorem wrapping_after_capture : wrapping.evalT CaptureControls.afterCapture = .ok four := by
  with_unfolding_all rfl

/-- A uniform closed certificate cannot hide the actual heap-dependent result. -/
theorem not_closed : ¬ Nonempty (Backend.Scalar.ClosedCertificate wrapping) := by
  rintro ⟨closed⟩
  have eq := wrapping_source.symm.trans ((closed.source σ).trans
    ((closed.source CaptureControls.afterCapture).symm.trans wrapping_after_capture))
  have impossible : (3 : Int) = 4 := congrArg Subtype.val (Except.ok.inj eq)
  omega

def checkedInvocation : Backend.Scalar.CheckedInvocation Backend.Scalar.checkedUintSub seven four
    (saved.map (fun w => BitVec.ofNat 256 w.val)) where
  testCapacity := by decide +kernel
  bodyCapacity := by decide +kernel

theorem checked_binary_success :
    ∃ w : Fin W, ReprV .uint three (.val w) ∧
      Backend.Scalar.encodeValue .uint three = BitVec.ofNat 256 w.val ∧
      Backend.Scalar.guarded Backend.Scalar.checkedUintSub.test Backend.Scalar.checkedUintSub.body
        Backend.Scalar.overflowFailure
        (Backend.Scalar.encodeValue .uint seven :: Backend.Scalar.encodeValue .uint four ::
          saved.map (fun w => BitVec.ofNat 256 w.val)) =
        some (.ok (BitVec.ofNat 256 w.val :: saved.map (fun w => BitVec.ofNat 256 w.val))) ∧
      run checkedDifference.code {machine with stack := saved.map Evm.Word.val} =
        .ok ({machine with stack := saved.map Evm.Word.val}.push (.val w)) 0 ∧
      Backend.Scalar.stackBound Backend.Scalar.checkedUintSub.test ((saved.length+2 : Nat) : Int) = true ∧
      Backend.Scalar.stackBound Backend.Scalar.checkedUintSub.body ((saved.length+2 : Nat) : Int) = true :=
  (StatefulChecked.binary_success Backend.Scalar.checkedUintSub checkedDifference fixture_repr
    first_source second_source rfl (by decide +kernel) saved checkedInvocation).2

end Solidity.Backend.Passes.StatefulValueControls
