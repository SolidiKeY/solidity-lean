import Solidity.Backend.Passes.ClosedValues
import Solidity.Backend.Passes.ValueContextControls

/-! Inhabited signed/bool applications and real reference-prefix transport.
Physical capacity is separate from the unbounded local mathematical tail. -/
namespace Solidity.Backend.Passes.ClosedValueControls
open Evm Evm.Memory
open Backend.Passes.Controls.Fixture
open Backend.Passes.ValueSequenceControls

def signed : Val C Γ .int := .simple (.lit (-7) rfl)
def signedCert : Backend.Scalar.ClosedCertificate signed := Backend.Scalar.numericLiteral .int (-7) rfl
def signedCode : CompiledVal 0 (Frag.init Γ) signed :=
  (compileVal 0 _ signed).get (by decide +kernel)
def boolean : Val C Γ .bool := .unop .not rfl rfl (.simple (.bool true))
def boolCert : Backend.Scalar.ClosedCertificate boolean := Backend.Scalar.negatedTrue
def boolCode : CompiledVal 0 (Frag.init Γ) boolean :=
  (compileVal 0 _ boolean).get (by decide +kernel)

theorem signed_application (saved : List (Fin W))
    (capacity : Backend.Scalar.ClosedInvocation signedCert (saved.map (fun a => BitVec.ofNat 256 a.val))) :
    ∃ a : Fin W, ReprV .int signedCert.value (.val a) ∧
      Backend.Scalar.encodeValue .int signedCert.value = BitVec.ofNat 256 a.val ∧
      Backend.Scalar.run signedCert.code (saved.map (fun a => BitVec.ofNat 256 a.val)) =
        some (BitVec.ofNat 256 a.val :: saved.map (fun a => BitVec.ofNat 256 a.val)) ∧
      run signedCode.code {machine with stack := saved.map Word.val} =
        .ok ({machine with stack := saved.map Word.val}.push (.val a)) 0 ∧
      Backend.Scalar.stackBound signedCert.code (saved.length : Int) = true :=
  (ClosedValues.application signedCert signedCode fixture_repr saved capacity).2

theorem boolean_application (saved : List (Fin W))
    (capacity : Backend.Scalar.ClosedInvocation boolCert (saved.map (fun a => BitVec.ofNat 256 a.val))) :
    ∃ a : Fin W, ReprV .bool boolCert.value (.val a) ∧
      Backend.Scalar.encodeValue .bool boolCert.value = BitVec.ofNat 256 a.val ∧
      Backend.Scalar.run boolCert.code (saved.map (fun a => BitVec.ofNat 256 a.val)) =
        some (BitVec.ofNat 256 a.val :: saved.map (fun a => BitVec.ofNat 256 a.val)) ∧
      run boolCode.code {machine with stack := saved.map Word.val} =
        .ok ({machine with stack := saved.map Word.val}.push (.val a)) 0 ∧
      Backend.Scalar.stackBound boolCert.code (saved.length : Int) = true :=
  (ClosedValues.application boolCert boolCode fixture_repr saved capacity).2

def signedInvocation : Backend.Scalar.ClosedInvocation signedCert [BitVec.ofNat 256 99] := ⟨by decide +kernel⟩
def booleanInvocation : Backend.Scalar.ClosedInvocation boolCert [BitVec.ofNat 256 99] := ⟨by decide +kernel⟩

theorem signed_reference_prefix (tail : List Word) :
    ∃ word, ReprV .int signedCert.value word ∧
      run (ValueContextControls.refStage.code ++ signedCode.code) {machine with stack := tail} =
        .ok ((writeMachine {machine with stack := tail} 4 w[20]).push word) 0 := by
  obtain ⟨word, hw, ht⟩ := value_after_fresh_reference signedCode fixture_repr CompileExamples.r1
    (frame' := 6) (by decide) LinkedControls.frame_six.heap.above
    LinkedControls.frame_six.structs.above (signedCert.source σ) tail
  refine ⟨word, hw, ?_⟩
  rw [run_append_ok (ValueContextControls.reference_run tail)]
  exact ht

private def cell (n : Nat) : Evm.Out → Option Nat
  | .ok m _ => match m.mem n with | .val w => some w.val | _ => none
  | _ => none

/-- Every old alias/local/header/element and independent cell is observed. -/
theorem ordered_memory : [4,3,2,1,0,16,17,18,20,21].mapM
    (fun n => cell n (run (ValueContextControls.refStage.code ++ signedCode.code) machine)) =
      some [20,0,16,16,20,2,7,9,1,4] := by
  obtain ⟨word, _, ht⟩ := signed_reference_prefix []
  change run (ValueContextControls.refStage.code ++ signedCode.code) machine = _ at ht
  rw [ht]
  dsimp only [cell, Machine.push, writeMachine]
  decide +kernel

theorem signed_bytes : signedCert.bytes = 0x7f :: List.replicate 31 255 ++ [249] := by decide +kernel
theorem bool_bytes : boolCert.bytes = 0x7f :: List.replicate 31 0 ++ [1,0x15] :=
  Backend.Scalar.negatedTrue_bytes

/-- Scalar canonical bool encoding does not represent arbitrary nonzero words. -/
theorem noncanonical_bool : ¬ ReprV .bool true (.val ⟨2, by decide⟩) := by
  intro h
  have he := congrArg Fin.val (Word.val.inj h)
  change (2 : Nat) = 1 at he
  cases he

theorem capacity_negative : Backend.Scalar.stackBound signedCert.code 1024 = false := by decide +kernel

/-- A successful raw POP removes the saved word; it is not a typed literal
certificate and cannot be substituted for the real emitted PUSH. -/
theorem corrupted_tail : Backend.Scalar.run [.op .POP] [BitVec.ofNat 256 99] = some [] ∧
    Backend.Scalar.run signedCert.code [BitVec.ofNat 256 99] ≠ some [] := by
  constructor
  · rfl
  · rw [signedCert.target]
    intro h
    cases h

end Solidity.Backend.Passes.ClosedValueControls
