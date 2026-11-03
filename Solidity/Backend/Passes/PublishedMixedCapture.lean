import Solidity.Backend.Passes.PublishedValues
import Solidity.Backend.Passes.CoreBoundaryControls

/-! Existing allocation/capture physical links applied to a real environment
and scalar expression. Numeric and symbolic machines remain distinct. -/
namespace Solidity.Backend.Passes.PublishedMixedCapture
open Evm Evm.Compiler Evm.Memory
open Backend.Passes.Controls.Fixture
open Backend.Passes.AllocatingControls
open Backend.Passes.TripleControls

def environment : Backend.Environment.Frame :=
  {self := Backend.Environment.account (lenU 0 (by decide)),
   sender := Backend.Environment.account (lenU 0 (by decide)),
   value := lenU 0 (by decide), time := lenU 0 (by decide), funds := fun _ => lenU 0 (by decide)}

theorem reached_environment : Backend.Environment.Represents environment CaptureControls.afterCapture :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

def rhs : PrimTy.uint.Denote := lenU 3 (by decide)
def expression : Val C Γ .uint := PublishedValues.expression .selfAddress rhs
def program : Prog C Γ (.val .uint :: Γ) :=
  .cons (.declLocal .uint (.user "mixedAfterCapture") (some expression)) .nil

def cert : inFragP captureStage.frag program = some (captureStage.frag.push (.val .uint) .ok) :=
  by decide +kernel

def compiled : Compilation 1 captureStage.frag program := .core _ cert

def answer : PrimTy.uint.Denote := Backend.Environment.wrap (2^256 - 3)

theorem expression_source : expression.evalT CaptureControls.afterCapture = .ok answer := by rfl

theorem program_source : program.run CaptureControls.afterCapture =
    .ok ⟨CaptureControls.afterCapture.push answer, List.prefix_refl _⟩ := by rfl

theorem link (tail : List Evm.Word) :
    ReachedMappedLink (.memory allocationStage) (.memory captureStage) compiled
      1 7 initialBase (State.init C) {initialMachine with stack := tail} := by
  intro o mid mb _ _ _
  exact compilation_core_mapped_link (.memory captureStage) cert (by decide +kernel)

theorem reached_composition (tail : List Evm.Word) :
    ∃ (mb nb ob : Nat → Fin W) (mid next final : Machine),
      run allocationStage.code {initialMachine with stack := tail} = .ok mid 0 ∧
      run captureStage.code mid = .ok next 0 ∧
      run compiled.code next = .ok final 0 ∧
      run ((allocationStage.code ++ captureStage.code) ++ compiled.code)
        {initialMachine with stack := tail} = .ok final 0 ∧
      run (allocationStage.code ++ (captureStage.code ++ compiled.code))
        {initialMachine with stack := tail} = .ok final 0 ∧
      final.stack = tail ∧
      MappedOutput (.memory allocationStage) 1 7 initialBase (State.init C)
        {initialMachine with stack := tail} σ mid mb ∧
      MappedOutput (.memory captureStage) 1 7 mb σ mid CaptureControls.afterCapture next nb ∧
      MappedOutput compiled 1 7 nb CaptureControls.afterCapture next
        (CaptureControls.afterCapture.push answer) final ob :=
  compilation_triple_success (.memory allocationStage) (.memory captureStage) compiled
    (compilation_input_stack (.memory allocationStage) prefix_input7 tail)
    (memory_nonallocating_mapped_link _ _ (by decide +kernel) (by decide +kernel))
    (link tail) rfl rfl rfl ReachabilityControls.fresh_state_reaches_fixture capture_source program_source

/-- The same reached intrinsic expression has a numeric emitted-byte slice
certificate, under the actually derived environment frame. -/
def numeric (m : Backend.Environment.Memory) :
    Backend.Environment.ValueCertificate CaptureControls.afterCapture expression environment
      (PublishedValues.code .selfAddress ⟨3,by decide⟩) m :=
  PublishedValues.certificate CaptureControls.afterCapture environment reached_environment .selfAddress ⟨3,by decide⟩ m

theorem numeric_tail (tail : List Backend.Environment.Word) (m : Backend.Environment.Memory) :
    Backend.Environment.runSlice environment (PublishedValues.code .selfAddress ⟨3,by decide⟩)
      ⟨tail,m⟩ = some ⟨answer::tail,m⟩ := (numeric m).target tail

def code : List Evm.Instr := allocationStage.code ++ (captureStage.code ++ compiled.code)
private def cell (n : Nat) : Evm.Out → Option Nat
  | .ok m _ => match m.mem n with | .val w => some w.val | _ => none
  | _ => none
private theorem c5 : cell 5 (run code initialMachine) = some (2^256 - 3) := by decide +kernel
private theorem c4 : cell 4 (run code initialMachine) = some (7) := by decide +kernel
private theorem c2 : cell 2 (run code initialMachine) = some (16) := by decide +kernel
private theorem c3 : cell 3 (run code initialMachine) = some (16) := by decide +kernel
private theorem c1 : cell 1 (run code initialMachine) = some (19) := by decide +kernel
private theorem c17 : cell 17 (run code initialMachine) = some (8) := by decide +kernel
private theorem c18 : cell 18 (run code initialMachine) = some (9) := by decide +kernel
private theorem c20 : cell 20 (run code initialMachine) = some (4) := by decide +kernel
private theorem c0 : cell 0 (run code initialMachine) = some (21) := by decide +kernel

theorem ordered_observations : [5,4,2,3,1,17,18,20,0].mapM
    (fun n => cell n (run code initialMachine)) = some [2^256-3,7,16,16,19,8,9,4,21] := by
  simp only [List.mapM_cons,List.mapM_nil,c5,c4,c2,c3,c1,c17,c18,c20,c0]
  rfl

end Solidity.Backend.Passes.PublishedMixedCapture
