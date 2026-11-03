import Solidity.Backend.Passes.StatefulValueNegatives

/-! Actual capture effect followed by a nonclosed scalar expression. Numeric
component and symbolic loader/expression semantics remain separate interfaces. -/
namespace Solidity.Backend.Passes.StatefulCaptureControls
open Evm Evm.Memory Evm.Compiler
open Backend.Passes.Controls.Fixture
open ValueSequenceControls
open StatefulValueControls

def captureProgram : Prog C Γ Γ := .cons CaptureControls.capture .nil
def captureCompiled : Memory.CompiledProg 0 (Frag.init Γ) captureProgram :=
  (Memory.compileProg 0 _ captureProgram).get (by decide +kernel)
def declaration : Prog C Γ (.val .uint :: Γ) :=
  .cons (.declLocal .uint (.user "statefulAfterCapture") (some wrapping)) .nil
def declarationCompiled : Memory.CompiledProg 0 captureCompiled.frag declaration :=
  (Memory.compileProg 0 _ declaration).get (by decide +kernel)

theorem capture_source : captureProgram.run σ = .ok ⟨CaptureControls.afterCapture,List.prefix_refl _⟩ := by
  with_unfolding_all rfl
theorem declaration_source : declaration.run CaptureControls.afterCapture =
    .ok ⟨CaptureControls.afterCapture.push four,List.prefix_refl _⟩ := by with_unfolding_all rfl

theorem initial_input : (Compilation.memory captureCompiled).Input 1 6 base σ machine :=
  ⟨LinkedControls.frame_six,by decide +kernel,.inl (by decide +kernel)⟩

def eight : PrimTy.uint.Denote := ⟨8,rfl⟩
def afterInvocation : Backend.Scalar.BinaryInvocation Backend.Scalar.wrappingSub eight four
    (saved.map (fun w => BitVec.ofNat 256 w.val)) := ⟨by decide +kernel⟩

/-- The scalar adapter is applied to the ACTUAL reached represented state/map
after capture. Both stages, full map relations and both target interfaces are
retained; there is no assumed post-capture preservation equation. -/
theorem reached_application :
    ∃ (mb ob : Nat → Fin W) (mid final : Machine) (word : Fin W),
      run captureCompiled.code machine = .ok mid 0 ∧
      run (captureCompiled.code ++ declarationCompiled.code) machine = .ok final 0 ∧
      final.stack = [] ∧
      MappedOutput (.memory captureCompiled) 1 6 base σ machine CaptureControls.afterCapture mid mb ∧
      MappedOutput (.memory declarationCompiled) 1 6 mb CaptureControls.afterCapture mid
        (CaptureControls.afterCapture.push four) final ob ∧
      ReprV .uint four (.val word) ∧
      Backend.Scalar.encodeValue .uint four = BitVec.ofNat 256 word.val ∧
      Backend.Scalar.run Backend.Scalar.wrappingSub.code
        (Backend.Scalar.encodeValue .uint eight :: Backend.Scalar.encodeValue .uint four ::
          saved.map (fun w => BitVec.ofNat 256 w.val)) =
        some (BitVec.ofNat 256 word.val :: saved.map (fun w => BitVec.ofNat 256 w.val)) ∧
      run wrappingCode.code {mid with stack := saved.map Word.val} =
        .ok ({mid with stack := saved.map Word.val}.push (.val word)) 0 ∧
      Backend.Scalar.stackBound Backend.Scalar.wrappingSub.code ((saved.length+2 : Nat) : Int) = true := by
  obtain ⟨mb,ob,mid,final,_,ha,ht,hs,ma,me⟩ :=
    compilation_mapped_success (.memory captureCompiled) (.memory declarationCompiled) initial_input
      (memory_nonallocating_mapped_link captureCompiled declarationCompiled (by decide +kernel) (by decide +kernel))
      rfl rfl capture_source declaration_source
  have applied := StatefulValues.binary Backend.Scalar.wrappingSub wrappingCode ma.1
    (a := eight) (d := four) (v := four)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl
    (by decide +kernel) saved afterInvocation
  obtain ⟨_,word,hw,he,hn,hv,cap⟩ := applied
  exact ⟨mb,ob,mid,final,word,ha,ht,hs,ma,me,hw,he,hn,hv,cap⟩

private def cell (n : Nat) : Evm.Out → Option Nat
  | .ok m _ => match m.mem n with | .val w => some w.val | _ => none
  | _ => none

/-- All old locals/aliases, both headers/array elements, independent array
and fresh result: exact effect ordering, not selected scalar cells alone. -/
theorem ordered_capture : [4,3,2,1,0,16,17,18,20,21].mapM
    (fun n => cell n (run (captureCompiled.code ++ declarationCompiled.code) machine)) =
      some [4,7,16,16,20,2,8,9,1,4] := by decide +kernel

theorem ordered_without_capture : [4,3,2,1,0,16,17,18,20,21].mapM
    (fun n => cell n (run declarationCompiled.code machine)) =
      some [3,0,16,16,20,2,7,9,1,4] := by decide +kernel

end Solidity.Backend.Passes.StatefulCaptureControls
