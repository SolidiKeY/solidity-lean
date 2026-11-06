import Solidity.Lowering.StorageOps.SourceFixedStorageCopy
import Solidity.Backend.StorageOps.TargetFixedSnapshot

/-! Independent actual Source fixed copy and actual snapshot target execution.
Only OLD captured payload/outside word agreements are cross-model premises.
No Source path/address compiler or new representation relation is introduced.
Compiled Source producers are pinned PUBLIC2fe plus checked owned C120; newer
public ABI/calldata/frame deltas are NOT silently imported or claimed checked. -/
namespace Solidity.Backend.StorageOps.SourceFixedStorageCopyTarget
open SourceStorageCopy SourceArrayDeleteTarget

/-- Actual fixed Source storRef copy, actual load-all/store-reverse instructions,
and selected payload/older-word correspondence. Source fixed roots have no
word header contract; no None-to-zero or live Source alias claim is made. -/
theorem complete {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (writable : frame.static=false) (t : Source.IntTy)
 (sourcePath dstPath : Source.SPath) (different : sourcePath≠dstPath)
 (size : TypeGraph.FixedSize) (padding : Nat) (indices : List Nat)
 (payload : Nat → Source.Val E.layout (.int t))
 (typed : E.pathTy dstPath=some (.array .storage (.int t) (some size.val)))
 (ordinary : E.transientRoot dstPath=false)
 (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (reads : ∀ j<size.val,(Source.readAt (E:=E) (Γ:=Γ) frame (sourcePath.go (.index j)) (.int t)).run (locals,state)=(.ok (payload j),(locals,state)))
 (target : Evm.Machine) (src dst : Evm.Slot)
 (sourceWords : ∀ j<size.val,(payload j).word.map Fin.val=some (target.store (src.add j)))
 (olderWords : ∀ j ∈ indices,size.val≤j → wordAt frame state.ex (dstPath.go (.index j))=some (target.store (dst.add j))) :
 let sourceResult := (Source.storeVal (E:=E) (Γ:=Γ) frame (size.val+padding+4)
  (.array .storage (.int t) (some size.val)) dstPath
  (Source.Val.storRef (τ:=.array .storage (.int t) (some size.val)) rfl sourcePath)).run (locals,state)
 let targetResult := TargetFixedSnapshot.afterCopy .uint size target src dst
 sourceResult=(.ok (),(locals,{state with ex:=state.ex.run (writes frame t dstPath payload (fun j => (SourceFixedStorageCopy.element_type t dstPath size.val typed j).symm) 0 size.val)})) ∧
 Evm.run (TargetFixedSnapshot.code .uint size src dst) target=.ok targetResult 0 ∧
 (∀ j ∈ indices,wordAt frame sourceResult.2.2.ex (dstPath.go (.index j))=some (targetResult.store (dst.add j))) := by
 dsimp only
 refine ⟨SourceFixedStorageCopy.complete frame writable t sourcePath dstPath different size.val padding payload typed locals state reads,
  TargetFixedSnapshot.run_code _ _ _ _ _,?_⟩
 intro j member
 have observed := SourceFixedStorageCopy.data_word frame writable t sourcePath dstPath different size.val padding j payload typed ordinary locals state reads
 rw [observed]
 by_cases copied : j<size.val
 · rw [if_pos copied,TargetFixedSnapshot.after_data .uint size target src dst j copied]
   exact sourceWords j copied
 · rw [if_neg copied,TargetFixedSnapshot.after_outside .uint size target src dst (dst.add j) (by
    intro o inside equal
    have same := Evm.Slot.add_inj equal
    omega)]
   exact olderWords j member (by omega)

/-- info: 'Solidity.Backend.StorageOps.SourceFixedStorageCopyTarget.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete
end Solidity.Backend.StorageOps.SourceFixedStorageCopyTarget
