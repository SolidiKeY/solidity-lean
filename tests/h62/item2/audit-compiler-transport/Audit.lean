import tests.h62.item2.«audit-compiler-transport».JointHypotheses
import Solidity.Backend.Passes.P12MemoryCapture
import Solidity.Backend.Passes.P12StorageCapture
import Solidity.Backend.Passes.CompilerWholeScope

/-! Additive controls for the exact frozen interfaces. Negative controls retain
all joint premises. Success is only for the published allocating scoped-call
fixture and its reassociation, with arbitrary saved stack tails. The abstract
machine has no gas/fork parameters; this does not certify bytecode gas/forks. -/
namespace H62.CompilerTransport
open Solidity Solidity.Evm Solidity.Evm.Compiler

/-- All parameters, including proof parameters, are bound together. -/
theorem memory_joint_impossible :
    ¬ jointHypotheses% Solidity.Backend.Passes.P12MemoryCapture.nonempty_revert_incompatible :=
  jointImpossible% Solidity.Backend.Passes.P12MemoryCapture.nonempty_revert_incompatible

theorem storage_joint_impossible :
    ¬ jointHypotheses% Solidity.Backend.Passes.P12StorageCapture.nonempty_revert_incompatible :=
  jointImpossible% Solidity.Backend.Passes.P12StorageCapture.nonempty_revert_incompatible

open Solidity.Backend.Passes
open MemoryCallControls (C Before initial base machine)

/-- Both associations of the actual allocating scoped-call fixture. -/
def supported (right : Bool) : Prog C [] Before :=
  if right then CompilerWholeScope.rightProgram else CompilerWholeScope.program

def publicCode (right : Bool) : Option (List Instr) :=
  (Compiler.compile 1 (Frag.init []) (supported right)).map (·.code)

/-- Public selection succeeds for every supported member, without an acceptance
premise. Both members select the same actual emitted code. -/
theorem public_total (right : Bool) : publicCode right = some CompilerWholeScope.actual.code := by
  cases right with
  | false =>
    change (Compiler.compile 1 (Frag.init []) CompilerWholeScope.program).map (·.code) = _
    rw [CompilerWholeScope.accepted]
    rfl
  | true => exact CompilerWholeScope.right_selected_code

/-- The public entry returns an actual typed certificate for every supported
program, together with the exact emitted code, without assuming acceptance. -/
theorem public_total_certificate (right : Bool) :
    ∃ (certificate : Compilation 1 (Frag.init []) (supported right)),
      Compiler.compile 1 (Frag.init []) (supported right) = some certificate ∧
      certificate.code = CompilerWholeScope.actual.code := by
  have observed : publicCode right = some CompilerWholeScope.actual.code := public_total right
  change (Compiler.compile 1 (Frag.init []) (supported right)).map (·.code) =
    some CompilerWholeScope.actual.code at observed
  cases chosen : Compiler.compile 1 (Frag.init []) (supported right) with
  | none =>
    rw [chosen] at observed
    cases observed
  | some certificate =>
    rw [chosen] at observed
    exact ⟨certificate,rfl,Option.some.inj observed⟩

/-- Source success holds for the same supported family, including reassociation. -/
theorem supported_source (right : Bool) :
    (supported right).run initial = .ok CompilerWholeScope.result := by
  cases right with
  | false => exact CompilerWholeScope.source_run
  | true =>
    change CompilerWholeScope.rightProgram.run initial = .ok CompilerWholeScope.result
    have same : CompilerWholeScope.program = CompilerWholeScope.rightProgram :=
      typed_sequencing_assoc MemoryCallControls.allocate
        MemoryCallScopeBoundary.Controls.scopeProgram MemoryCallScopeBoundary.Controls.suffix
    rw [← same]
    exact CompilerWholeScope.source_run

/-- A contract that includes success, full mapped output and the actual new
allocator cursor. It is deliberately stronger than conditional preservation. -/
def SupportedSuccess (candidate : Bool → Option (List Instr)) : Prop :=
  ∀ (right : Bool) (tail : List Word),
    (supported right).run initial = .ok CompilerWholeScope.result ∧
    ∃ (code : List Instr) (canonical : Machine) (selected : Nat → Fin W),
      candidate right = some code ∧ canonical.stack = [] ∧
      run code {machine with stack := tail} = .ok {canonical with stack := tail} 0 ∧
      MappedOutput CompilerWholeScope.actual 1 128 base initial {machine with stack := tail}
        CompilerWholeScope.result.st {canonical with stack := tail} selected ∧
      Evm.Memory.StructAllocatorRepr CompilerWholeScope.result.st.heap selected 128 (wmod 264)
        {canonical with stack := tail}

theorem public_success : SupportedSuccess publicCode := by
  intro right tail
  obtain ⟨canonical,selected,empty,runs⟩ := CompilerWholeScope.resources
  exact ⟨supported_source right,CompilerWholeScope.actual.code,canonical,selected,public_total right,empty,
    (runs tail).1,(runs tail).2.1,(runs tail).2.2⟩

def rejectAll : Bool → Option (List Instr) := fun _ => none
def alwaysRevert : Bool → Option (List Instr) := fun _ => some [.revert]

theorem reject_all_fails : ¬ SupportedSuccess rejectAll := by
  intro claimed
  obtain ⟨code,canonical,selected,accepted,rest⟩ := (claimed false []).2
  cases accepted

theorem always_revert_fails : ¬ SupportedSuccess alwaysRevert := by
  intro claimed
  obtain ⟨code,canonical,selected,accepted,empty,success,rest⟩ := (claimed false []).2
  have same : [.revert] = code := Option.some.inj accepted
  subst code
  change Evm.Out.revert = .ok {canonical with stack := []} 0 at success
  cases success

/-- Preserve the actual observable failure boundary: a reverting implementation
is distinguishable for every saved stack, without projecting a failure state. -/
theorem observable_failure (tail : List Word) :
    run [.revert] {machine with stack := tail} = .revert := rfl

/-- A state/frame boundary is real even though successful selection is total. -/
theorem insufficient_frame {selected : Nat → Fin W} {state : State C []} {target : Machine} :
    ¬ CompilerWholeScope.actual.Input 1 (1 + Evm.Memory.frameNeedProg CompilerWholeScope.program)
      selected state target := CompilerWholeScope.source_frame_refused

#print axioms memory_joint_impossible
#print axioms storage_joint_impossible
#print axioms public_total
#print axioms public_total_certificate
#print axioms supported_source
#print axioms public_success
#print axioms reject_all_fails
#print axioms always_revert_fails
#print axioms observable_failure
#print axioms insufficient_frame
end H62.CompilerTransport
