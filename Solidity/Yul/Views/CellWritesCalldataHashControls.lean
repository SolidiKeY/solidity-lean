import Solidity.Yul.Views.CellWritesCalldataHash
import Solidity.Yul.Views.FiniteCellWritesControls

/-! Same-run storage/input/hash controls with two calldata aliases and an
oversized reference. Input clips to3 bytes, allocating once after4 writes.
Physical payload copying is separate from allocator-header/FMP realization. -/
namespace Solidity.Yul.Views.Controls
open TransientSlotControls

def cwhFrame : Source.Fr := {frame with cd:=[17,255,0,128]}
def cwhState : Source.EMState rootEnv [.bytes .calldata,.bytes .calldata] :=
  (.cons (.cdRef rfl 1 5) (.cons (.cdRef rfl 1 5) .nil),child.1.2.2)
def cwhMemory : ByteView := fun address => if address=131 then 99 else 42

theorem cwh_run (G : Source.Glob rootEnv) (n : Nat) (first : Bool) :
    let index : Source.Idx [.bytes .calldata,.bytes .calldata] (.bytes .calldata) := if first then .here else .there .here
    (CellWritesCalldataHash.program G cwhFrame (n+4) index fcwRequests).run cwhState=
      (.ok (.val (Source.mkBytes (D:=rootEnv.layout) (n:=32) (h:=by decide) (Source.wordBytes (G.fixed.hash [255,0,128])))),
        objectAllocatedState (CellWritesCalldataHash.afterWrites cwhFrame cwhState fcwRequests)
          (Source.Data.bytes (l:=.memory) [255,0,128])) := by
  apply CellWritesCalldataHash.run G cwhFrame n cwhState _ 1 5 fcwRequests rfl
  cases first <;> rfl

theorem cwh_maps (G : Source.Glob rootEnv) (n : Nat) :
    let reached := (CellWritesCalldataHash.program G cwhFrame (n+4) .here fcwRequests).run cwhState
    finiteEncode mcsPaths (reached.2.2.ex.world.accounts account).storage (packedMask mcsPaths mcsRaw)=some (FiniteCellWrites.raw fcwRequests fcwMaps).1 ∧
    finiteEncode (rootTempRegistry account) (reached.2.2.ex.transient.cells account) (packedMask (rootTempRegistry account) tcuRaw)=
      some (FiniteCellWrites.raw fcwRequests fcwMaps).2 :=
  CellWritesCalldataHash.reencode G cwhFrame n cwhState .here 1 5 fcwRequests mcsPaths _
    (selectedSlotPaths_separated _ _ root_separation) rootTempChecked.separated fcw_registered fcwMaps ⟨mcs_view,tcu_before⟩ rfl rfl

theorem cwh_hash (G : Source.Glob rootEnv) (n : Nat) :
    (Source.mkBytes (D:=rootEnv.layout) (n:=32) (h:=by decide) (Source.wordBytes (G.fixed.hash [255,0,128]))).word=
      some (keccak256 G.fixed.evm (calldatacopy cwhMemory cwhFrame.cd 128 1 3) 128 3) :=
  CellWritesCalldataHash.physical_hash G cwhFrame n cwhState .here 1 5 fcwRequests rfl rfl 128 cwhMemory

theorem cwh_observed (G : Source.Glob rootEnv) (n : Nat) :
    (((CellWritesCalldataHash.program G cwhFrame (n+4) .here fcwRequests >>= Source.getV).run cwhState).1.map Source.Val.word)=
      .ok (some (keccak256 G.fixed.evm (calldatacopy cwhMemory cwhFrame.cd 128 1 3) 128 3)) :=
  CellWritesCalldataHash.observed G cwhFrame n cwhState .here 1 5 fcwRequests rfl rfl 128 cwhMemory

theorem cwh_initial_safe : Source.MemOK rootEnv cwhState.2.heap.ty cwhState :=
  ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,⟨trivial,⟨trivial,trivial⟩⟩⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩

theorem cwh_safe (G : Source.Glob rootEnv) (n : Nat) :
    Source.MemOK rootEnv cwhState.2.heap.ty ((CellWritesCalldataHash.program G cwhFrame (n+4) .here fcwRequests).run cwhState).2 :=
  CellWritesCalldataHash.MemOK G cwhFrame n cwhState .here 1 5 fcwRequests rfl rfl _ cwh_initial_safe

theorem cwh_allocates_once (G : Source.Glob rootEnv) (n : Nat) :
    ((CellWritesCalldataHash.program G cwhFrame (n+4) .here fcwRequests).run cwhState).2.2.heap.next=1 := by
  rw [CellWritesCalldataHash.run G cwhFrame n cwhState .here 1 5 fcwRequests rfl rfl]
  unfold CellWritesCalldataHash.afterWrites
  rw [FiniteCellWrites.run _ _ _ rfl]
  rfl

theorem cwh_low_prefix (G : Source.Glob rootEnv) :
    let reached := (CellWritesCalldataHash.program G cwhFrame 3 .here fcwRequests).run cwhState
    reached.1=.error .timeout ∧ reached.2.2.heap.next=0 ∧
    (Source.readLoc cwhFrame (.stor (τ:=.int rootU8) (rootPath "a"))).run reached.2=(.ok (Source.intWrap rootU8 3),reached.2) := by
  dsimp only
  rw [CellWritesCalldataHash.low_horizon G cwhFrame 3 cwhState .here fcwRequests rfl (by decide)]
  unfold CellWritesCalldataHash.afterWrites
  rw [FiniteCellWrites.run _ _ _ rfl]
  exact ⟨rfl,rfl,rfl⟩

theorem cwh_static (G : Source.Glob rootEnv) (horizon : Nat) :
    (CellWritesCalldataHash.program G {cwhFrame with static:=true} horizon .here fcwRequests).run cwhState=
      (.error (.revert []),cwhState) := CellWritesCalldataHash.static _ _ _ _ _ _ _ rfl

theorem cwh_clip_not_pad :
    readBytes (calldatacopy cwhMemory cwhFrame.cd 128 1 3) 128 3=[255,0,128] ∧
    readBytes (calldatacopy cwhMemory cwhFrame.cd 128 1 5) 128 5=[255,0,128,0,0] ∧
    calldatacopy cwhMemory cwhFrame.cd 128 1 3 131=99 := ⟨rfl,rfl,rfl⟩
end Solidity.Yul.Views.Controls
