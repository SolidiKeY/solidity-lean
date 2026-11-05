import Solidity.Yul.Views.BytePlanHashAlias
import Solidity.Yul.Views.MultiRootByteFramesControls

/-! Two bytes-typed aliases share a string object while writes visit multiple
roots. The universal transport derives the string payload and raw hash input;
late failure, wrong chronology and header/padding inputs remain distinguishable.
These are seeded kernel controls, not external compiler/Keccak observations. -/
namespace Solidity.Yul.Views.BytePlanHashAlias.Controls
open Solidity.Yul.Views.Controls
open MultiRootByteWrites.Controls

def aliases : Source.Locals mixedLayout [.bytes .memory,.bytes .memory] :=
  .cons (.memRef rfl 1) (.cons (.memRef rfl 1) .nil)
def initial : Source.EMState mixedEnv [.bytes .memory,.bytes .memory] := (aliases,mixedState.2)
def finalState : Source.EMState mixedEnv [.bytes .memory,.bytes .memory] := (aliases,after.2)
def writePrefix := requests.take 3

theorem incoming : Source.MemOK mixedEnv mixedHeap.ty initial := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact ⟨⟨mixed_actual_MemOK.1.1,
    ⟨⟨.string .memory,rfl,rfl⟩,⟨⟨.string .memory,rfl,rfl⟩,trivial⟩⟩⟩,
    mixed_actual_MemOK.2⟩

theorem actual_plan : MultiRootByteWrites.coupled mixedReadFrame 0 mixedPlacement.address
    writePrefix initial mixedPhysical=((.ok (),finalState),raw) := by
  first | (simp only;done) | decide | omega | rfl

theorem derived_hash (G : Source.Glob mixedEnv) (n : Nat) :
    ∃ bytes,finalState.2.heap.get 1=some ⟨.string .memory,Source.Data.string bytes⟩ ∧
      let output := Source.mkBytes (D:=mixedLayout) (n:=32) (h:=by decide)
        (Source.wordBytes (G.fixed.hash bytes))
      (BytePlanHash.program G mixedReadFrame 0 n writePrefix .here).run initial=
        (.ok (.val output),finalState) ∧
      output.word=some (keccak256 G.fixed.evm raw 416 bytes.length) := by
  first | (simp only;done) | decide | omega | rfl | skip
  have result := transport G mixedReadFrame 0 n writePrefix mixedHeap.ty initial
    mixedPlacement mixedPlacement (retainInitial _ _) incoming StructWordHeap.Controls.support
    mixedPhysical ByteElementStore.Controls.oldReads mixed_reserved .here 1 true [0xff,0x61] rfl rfl
  rw [actual_plan] at result
  exact result

theorem aliases_read_same (n : Nat) :
    (Source.bytesOfRV mixedReadFrame n (.val (finalState.1.get .here))).run finalState=
      (.ok [0x80,0x61],finalState) ∧
    (Source.bytesOfRV mixedReadFrame n (.val (finalState.1.get (.there .here)))).run finalState=
      (.ok [0x80,0x61],finalState) := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact ⟨rfl,rfl⟩

theorem exact_payload_and_padding : readBytes raw 416 2=[0x80,0x61] ∧ raw 418=0xa5 ∧
    (mload raw 384).val=2 ∧ readBytes raw 384 2≠readBytes raw 416 2 ∧
    readBytes mixedPhysical 416 2≠readBytes raw 416 2 := by
  first | (simp only;done) | decide | omega | rfl

theorem late_failure (G : Source.Glob mixedEnv) (n : Nat) :
    (BytePlanHash.program G mixedReadFrame 0 n requests .here).run initial=
      (.error (.stuck "not bytes"),finalState) := by
  first | (simp only;done) | decide | omega | rfl

/-- Saved caller aliases survive a child with different, nonempty locals. -/
theorem restored_caller (G : Source.Glob mixedEnv) (n : Nat) :
    ((do let _ ← Source.EM.sub MultiRootByteFrames.Controls.child
           (MultiRootByteWrites.program mixedReadFrame 0 writePrefix)
         Source.evalE G mixedReadFrame (n+4) (sourceMemoryHashExpr .here)) :
      Source.EM mixedEnv [.bytes .memory,.bytes .memory] _).run initial=
      (.ok (.val (Source.mkBytes (D:=mixedLayout) (n:=32) (h:=by decide)
        (Source.wordBytes (G.fixed.hash [0x80,0x61])))),finalState) := by
  first | (simp only;done) | decide | omega | rfl
end Solidity.Yul.Views.BytePlanHashAlias.Controls
