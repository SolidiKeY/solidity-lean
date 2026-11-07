import Solidity.Yul.Views.BytePlanHash
import Solidity.Yul.Views.MultiRootByteFramesControls

/-! The real hash expression follows repeated multi-root writes; actual heap
bytes and raw preimage agree. Header/padding negatives compare inputs without
assuming hash injectivity. A late Source error short-circuits the actual hash. -/
namespace Solidity.Yul.Views.BytePlanHash.Controls
open Solidity.Yul.Views.Controls
open MultiRootByteWrites.Controls

def writePrefix := requests.take 3
def value (G : Source.Glob mixedEnv) := Source.mkBytes (D:=mixedLayout) (n:=32) (h:=by decide)
  (Source.wordBytes (G.fixed.hash [0x11,0x22,0x55]))

theorem actual_writePrefix : MultiRootByteWrites.coupled mixedReadFrame 0 mixedPlacement.address writePrefix mixedState mixedPhysical=
    ((.ok (),after),raw) := rfl

theorem source_hash (G : Source.Glob mixedEnv) (n : Nat) :
    (program G mixedReadFrame 0 n writePrefix .here).run mixedState=(.ok (.val (value G)),after) := by rfl

theorem derived_composition (G : Source.Glob mixedEnv) (n : Nat) :
    ∃ bytes,after.2.heap.get 0=some ⟨.bytes .memory,Source.Data.bytes bytes⟩ ∧
      let output := Source.mkBytes (D:=mixedLayout) (n:=32) (h:=by decide) (Source.wordBytes (G.fixed.hash bytes))
      (program G mixedReadFrame 0 n writePrefix .here).run mixedState=(.ok (.val output),after) ∧
      output.word=some (keccak256 G.fixed.evm raw 160 bytes.length) := by
  first | (simp only;done) | decide | omega | rfl | skip
  have result := transport G mixedReadFrame 0 n writePrefix mixedHeap.ty mixedState mixedPlacement mixedPlacement (retainInitial _ _)
    mixed_actual_MemOK StructWordHeap.Controls.support mixedPhysical ByteElementStore.Controls.oldReads mixed_reserved .here 0 mixedChild rfl rfl
  rw [actual_writePrefix] at result
  exact result

theorem exact_preimage : readBytes raw 160 3=[0x11,0x22,0x55] := by decide

theorem physical_word (G : Source.Glob mixedEnv) :
    (value G).word=some (keccak256 G.fixed.evm raw 160 3) :=
  (hashWord_observe mixedLayout (G.fixed.hash [0x11,0x22,0x55])).trans
    (congrArg some (fixedHash_physical G.fixed raw 160 3 [0x11,0x22,0x55] exact_preimage).symm)

theorem failure_short_circuits (G : Source.Glob mixedEnv) (n : Nat) :
    (program G mixedReadFrame 0 n requests .here).run mixedState=(.error (.stuck "not bytes"),after) := by rfl

theorem restored_caller_hash (G : Source.Glob mixedEnv) (n : Nat) :
    ((do let _ ← Source.EM.sub MultiRootByteFrames.Controls.child (MultiRootByteWrites.program mixedReadFrame 0 writePrefix)
         Source.evalE G mixedReadFrame (n+4) (sourceMemoryHashExpr .here)) : Source.EM mixedEnv _ _).run mixedState=
      (.ok (.val (value G)),after) := by rfl

theorem header_padding_old_value_negatives : readBytes raw 128 3≠readBytes raw 160 3 ∧
    readBytes raw 160 4≠readBytes raw 160 3 ∧ readBytes mixedPhysical 160 3≠readBytes raw 160 3 ∧
    raw 163=0xa5 ∧ (mload raw 128).val=3 := by decide
end Solidity.Yul.Views.BytePlanHash.Controls
