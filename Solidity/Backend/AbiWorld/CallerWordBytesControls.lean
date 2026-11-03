import Solidity.Backend.AbiWorld.CallerWordBytes
import Solidity.Evm.MemoryCompileExamples

namespace Solidity.Backend.AbiWorld.CallerWordBytesControls
open Solidity Evm Evm.Memory Backend
namespace P
abbrev C := Evm.Memory.CompileExamples.C
abbrev Γ := Evm.Memory.CompileExamples.Γ
abbrev base := Evm.Memory.CompileExamples.base
abbrev original := Evm.Memory.CompileExamples.σ
abbrev target := Evm.Memory.CompileExamples.machine
abbrev F := Frag.init Γ
end P

def cell : Fin W := ⟨3,by decide⟩
def temporary : Fin W := ⟨17,by decide⟩
def caller (saved : Fin W) := P.original.setLocal (.here : Idx P.Γ (.val .uint)) (indexValue saved)
def machine (saved : Fin W) := writeMachine {P.target with stack := [w[77]]} 3 (.val saved)
def loaded (saved : Fin W) := {machine saved with stack := .val saved :: [w[77]]}
def background : Environment.Memory := fun a => if a=7 then 231 else 19
def initialBytes (saved : Fin W) := Environment.writeBytes background 96 (Semantics.wordBytes saved.val)
def live (a : Nat) : Prop := a=3

theorem represented (saved : Fin W) : StateRepr 1 0 6 P.F (caller saved) P.base (machine saved) :=
 (Evm.Memory.CompileExamples.fixture_six_cells.stack [w[77]]).setVal
  (.here : Idx P.Γ (.val .uint)) (indexValue saved) (.val saved) (ReprV.uint_of rfl)

theorem numeric_load (saved : Fin W) : Evm.run [.mload 3] (machine saved) = .ok (loaded saved) 0 := by rfl

theorem loaded_repr (saved : Fin W) : StateRepr 1 0 6 P.F (caller saved) P.base (loaded saved) :=
 (represented saved).stack _

theorem image (saved : Fin W) : MemoryOps.Physical.WordFrame (loaded saved) (initialBytes saved) live :=
 InternalFlow.RuntimeFrame.Bytes.initial_cell (loaded saved) background cell saved rfl (by decide)

theorem typed_application (saved : Fin W) :
 Evm.run (InternalFlow.RuntimeFrame.Restore.consumeCode 3 (.val temporary)) (loaded saved) = .ok (machine saved) 0 ∧
 StateRepr 1 0 6 P.F (caller saved) P.base (machine saved) ∧
 Environment.runCrypto (InternalFlow.RuntimeFrame.Bytes.code cell (by decide) temporary)
  ⟨lenU saved.val saved.isLt :: [lenU 77 (by decide)],initialBytes saved⟩ =
 some ⟨[lenU 77 (by decide)],InternalFlow.RuntimeFrame.Bytes.afterBytes (initialBytes saved) cell temporary saved⟩ ∧
 MemoryOps.Physical.WordFrame (machine saved)
  (InternalFlow.RuntimeFrame.Bytes.afterBytes (initialBytes saved) cell temporary saved) live ∧
 Environment.readMemory (InternalFlow.RuntimeFrame.Bytes.afterBytes (initialBytes saved) cell temporary saved) 96 32 =
 AbiEntry.encodeArgs (CallerWordBytes.values saved) :=
 CallerWordBytes.typed (loaded_repr saved) .here cell temporary saved rfl (initialBytes saved) live
  (image saved) rfl [w[77]] [lenU 77 (by decide)] rfl (ReprV.uint_of rfl)

theorem loaded_then_restored (saved : Fin W) :
 Evm.run ([.mload 3] ++ InternalFlow.RuntimeFrame.Restore.consumeCode 3 (.val temporary)) (machine saved) =
 .ok (machine saved) 0 := by
 rw [Evm.run_append_ok (numeric_load saved)]
 exact (typed_application saved).1

theorem wrong_symbolic (slot : Slot) (bytes : Environment.Memory) :
 ¬ MemoryOps.Physical.WordFrame {machine (⟨300,by decide⟩) with mem := fun _ => .slot slot} bytes live :=
 InternalFlow.RuntimeFrame.Bytes.symbolic_refusal 3 rfl slot rfl

theorem old_byte (saved : Fin W) :
 InternalFlow.RuntimeFrame.Bytes.afterBytes (initialBytes saved) cell temporary saved 7 = 231 := by
 rw [CallerWordBytes.outside_byte _ _ _ _ _ (Or.inl (by decide))]
 exact Environment.writeBytes_frame (Semantics.wordBytes saved.val) 96 7 background (Or.inl (by decide))

theorem word300 : (CallerWordBytes.word ⟨300,by decide⟩).val=300 := rfl

theorem wrong_low_byte : AbiEntry.encodeArgs (CallerWordBytes.values ⟨300,by decide⟩) ≠
 AbiEntry.encodeArgs (CallerWordBytes.values ⟨44,by decide⟩) := by decide +kernel

def samples : List (Fin W) := [⟨0,by decide⟩,⟨9,by decide⟩,⟨300,by decide⟩,⟨W-1,by unfold W;omega⟩]
def render (bytes : List UInt8) : String := "[" ++ String.intercalate "," (bytes.map (fun b => toString b.toNat)) ++ "]"
def observe (saved : Fin W) : String :=
 match Environment.runCrypto (InternalFlow.RuntimeFrame.Bytes.code cell (by decide) temporary)
  ⟨lenU saved.val saved.isLt :: [lenU 77 (by decide)],initialBytes saved⟩ with
 | none => "NO_STORE"
 | some reached => render (Environment.readMemory reached.memory 96 32)
def observeRevert (saved : Fin W) : String :=
 match Failure.Slice.run [.op .REVERT]
  ⟨(⟨96,by decide⟩ : Roadmap.Word)::(⟨32,by decide⟩ : Roadmap.Word)::[],
   InternalFlow.RuntimeFrame.Bytes.afterBytes (initialBytes saved) cell temporary saved⟩ with
 | some (_,some (.revert bytes)) => render bytes
 | _ => "NO_REVERT"
#eval String.intercalate "\n" (samples.map observe)
#eval String.intercalate "\n" (samples.map observeRevert)
#eval String.intercalate "\n" (samples.map (fun saved => render (AbiEntry.encodeArgs (CallerWordBytes.values saved))))
#print axioms CallerWordBytes.word_encoding
#print axioms CallerWordBytes.recovered
#print axioms CallerWordBytes.typed
#print axioms CallerWordBytes.raw_revert
#print axioms CallerWordBytes.outside_byte
#print axioms represented
#print axioms numeric_load
#print axioms loaded_repr
#print axioms image
#print axioms typed_application
#print axioms loaded_then_restored
#print axioms wrong_symbolic
#print axioms old_byte
#print axioms word300
#print axioms wrong_low_byte
end Solidity.Backend.AbiWorld.CallerWordBytesControls
