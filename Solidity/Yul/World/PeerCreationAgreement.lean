import Solidity.Yul.World.PeerMemoryAgreement
import Solidity.Yul.World.CreationAddressingChecks
import Solidity.Yul.World.ReturnSize

/-! Actual immutable VY3 target writes consumed by the VY4 address/constructor
adapter. The initcode producer remains explicitly scripted: this proves byte
and address dataflow, not executable initcode/source-view/compiler adequacy. -/
namespace Solidity.Yul.World.PeerCreationAgreement
open Solidity.Source
open Solidity.Source.StateExamples
open Solidity.Backend.Environment (Slice runData read_written)
open Solidity.Roadmap (Fixed Word Outcome)
open Solidity.Yul.World.Checks
open Solidity.Yul.World.AdapterChecks (observed)
open Solidity.Yul.World.CreationFramesChecks (prepared parent actual_preparation)

def target (F : Fixed) (salt : Option Word) :=
  selectCreationAddress F (addr 1) ⟨3,by decide⟩ salt [0xab,0xcd]

def probeAnswer (F : Fixed) (salt : Option Word) (failed : Bool) : FrameAnswer D₀ LW LW :=
  ⟨havoc,[.event (.credit (target F salt) (toWord 5)),
    .log ⟨target F salt,⟨0,by decide⟩,#v[],[0xab,0xcd]⟩] ++ calleeTrace,
    if failed then .revert [253,254] else .success [96,0]⟩

def expected (F : Fixed) (salt : Option Word) (failed : Bool) : CompletedCreation D₀ LW LW :=
  ⟨(probeAnswer F salt failed).outcome,
   finishCreation prepared (constructorFrame prepared.effects.execution parent (target F salt) (toWord 5))
     (probeAnswer F salt failed),rfl⟩

/-- The compiled producer supplies the actual input memory, not a supplied
memory-equality law. Both CREATE2 hashing and the exact port receive its bytes. -/
theorem compiled_initialization (F : Fixed) (salt : Option Word) (failed : Bool) (s : Slice) :
    (runData Solidity.Yul.Compilation.memoryHarness s).bind (fun next =>
      addressedCreation F salt TargetMemory.port (CreationAddressingChecks.producer failed)
        observed next.memory parent (toWord 100000) (toWord 5) (toWord 31) (toWord 2)) =
      some (expected F salt failed) := by
  rw [Solidity.Yul.Compilation.memoryHarness_correct]
  simp only [Option.bind_some]
  have hl : TargetMemory.port.load (Solidity.Backend.Environment.writeBytes s.memory 31 [0xab,0xcd])
      (toWord 31) (toWord 2) = some [0xab,0xcd] := by
    rw [TargetMemory.load_exact _ _ _ (by decide)]
    exact congrArg some (read_written [0xab,0xcd] 31 s.memory)
  have he := addressedCreation_exact F salt TargetMemory.port (CreationAddressingChecks.producer failed)
    observed (Solidity.Backend.Environment.writeBytes s.memory 31 [0xab,0xcd]) parent
    (toWord 100000) (toWord 5) (toWord 31) (toWord 2) [0xab,0xcd] prepared
    (probeAnswer F salt failed) rfl (by decide) hl actual_preparation rfl
  exact he

theorem compiled_success_size (F : Fixed) (salt : Option Word) (s : Slice) :
    ((runData Solidity.Yul.Compilation.memoryHarness s).bind (fun next =>
      addressedCreation F salt TargetMemory.port (CreationAddressingChecks.producer false)
        observed next.memory parent (toWord 100000) (toWord 5) (toWord 31) (toWord 2))).bind
      (fun result => returndataSize result.observed.effects) = some (toWord 0) := by
  rw [compiled_initialization]
  rfl

theorem compiled_revert_size (F : Fixed) (salt : Option Word) (s : Slice) :
    ((runData Solidity.Yul.Compilation.memoryHarness s).bind (fun next =>
      addressedCreation F salt TargetMemory.port (CreationAddressingChecks.producer true)
        observed next.memory parent (toWord 100000) (toWord 5) (toWord 31) (toWord 2))).bind
      (fun result => returndataSize result.observed.effects) = some (toWord 2) := by
  rw [compiled_initialization]
  rfl

end Solidity.Yul.World.PeerCreationAgreement
