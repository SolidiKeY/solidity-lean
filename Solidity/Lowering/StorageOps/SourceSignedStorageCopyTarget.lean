import Solidity.Lowering.StorageOps.SourceIntCopyReadbacks
import Solidity.Backend.StorageOps.TargetCopyRepresentation

/-! Actual independent Source storRef runtime-copy to actual EXISTING target
copy observations. OLD Source/target header/payload/retained agreements are
explicit captured-operation premises, not desired preservation or a compiler
simulation. Numeric/representation composition reuses published owner facts. -/
namespace Solidity.Backend.StorageOps.SourceSignedStorageCopyTarget
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open SourceStorageCopy SourceCopyReadbacks SourceArrayDeleteTarget
open SourceIntCopyReadbacks (int256)

/-- Copied/stale/older Source cells match actual target runtime reads/writes.
Only OLD observation agreements and the actual independent Source execution
are used. Missing/unmatched older observations are NOT silently turned zero. -/
theorem complete {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (writable : frame.static=false) (sourcePath dstPath : Source.SPath) (different : sourcePath≠dstPath)
 (count oldLength : Nat) (fits : count<2^256) (indices : List Nat)
 (payload : Nat → Source.Val E.layout (.int int256))
 (typed : E.pathTy dstPath=some (.array .storage (.int int256) none))
 (ordinary : E.transientRoot dstPath=false)
 (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (sourceHeader : (Source.readLen (E:=E) (Γ:=Γ) frame sourcePath).run (locals,state)=(.ok count,(locals,state)))
 (reads : ∀ j<count,(Source.readAt (E:=E) (Γ:=Γ) frame (sourcePath.go (.index j)) (.int int256)).run (locals,state)=(.ok (payload j),(locals,state)))
 (dstHeader : (Source.readLen (E:=E) (Γ:=Γ) frame dstPath).run (locals,state)=(.ok oldLength,(locals,state)))
 (target : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
 (srcLength : target.store src=count) (dstLength : target.store dst=oldLength)
 (sourceWords : ∀ j<count,(payload j).word.map Fin.val=some (target.store (.data src j)))
 (olderWords : ∀ j ∈ indices,max count oldLength≤j → wordAt frame state.ex (dstPath.go (.index j))=some (target.store (.data dst j))) :
 let sourceResult := (Source.storeVal (E:=E) (Γ:=Γ) frame (count+(oldLength-count)+4) (.array .storage (.int int256) none) dstPath
  (Source.Val.storRef (τ:=.array .storage (.int int256) none) rfl sourcePath)).run (locals,state)
 let targetResult := TargetArrayCopyTail.afterCopy target tail src dst
 sourceResult=(.ok (),(locals,{state with ex:=state.ex.run (copyLog frame int256 dstPath count oldLength payload typed)})) ∧
 Evm.run TargetArrayCopy.code {target with stack:=.slot src :: .slot dst :: tail}=.ok targetResult 0 ∧
 wordAt frame sourceResult.2.2.ex dstPath=some (targetResult.store dst) ∧
 (∀ j ∈ indices,wordAt frame sourceResult.2.2.ex (dstPath.go (.index j))=some (targetResult.store (.data dst j))) := by
 rw [SourceStorageCopy.complete frame writable int256 sourcePath dstPath different count oldLength payload typed locals state sourceHeader reads dstHeader]
 refine ⟨rfl,TargetArrayCopyTail.run_current target tail src dst,?_,?_⟩
 · rw [copy_header frame int256 dstPath count oldLength payload typed state.ex ordinary,header_word count fits,TargetArrayCopyTail.after_header,srcLength]
 · intro j member
   rw [SourceIntCopyReadbacks.copy_data frame int256 dstPath count oldLength j payload typed state.ex ordinary,TargetArrayCopyTail.after_data,srcLength,dstLength]
   by_cases copied : j<count
   · rw [if_pos copied,if_pos copied,sourceWords j copied]
   · rw [if_neg copied,if_neg copied]
     by_cases stale : j<oldLength
     · rw [if_pos stale,if_pos stale]
     · rw [if_neg stale,if_neg stale]
       exact olderWords j member (by omega)

/-- Compose the ACTUAL independent Source operation with PUBLIC old owners,
original finite-run numeric transport and the existing actual target program.
Only OLD source/header/payload/retained agreements are premises. -/
theorem complete_numeric {n N L R : Nat} {G : Schema n}
 {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 {E : Source.Env} {Γ : Source.RCtx}
 (run : FiniteRun N L R hash P locations)
 (frame : Source.Fr) (writable : frame.static=false) (sourcePath dstPath : Source.SPath) (different : sourcePath≠dstPath)
 (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (typed : E.pathTy dstPath=some (.array .storage (.int int256) none))
 (ordinary : E.transientRoot dstPath=false)
 (old source : Value G (.array (.prim .int))) (indices : List Index)
 (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
 (store : Store) (numeric : WordStore) (target : Evm.Machine) (tail : List Evm.Word)
 (payload : Nat → Source.Val E.layout (.int int256))
 (sourceHeader : (Source.readLen (E:=E) (Γ:=Γ) frame sourcePath).run (locals,state)=(.ok source.length.val,(locals,state)))
 (reads : ∀ j<source.length.val,(Source.readAt (E:=E) (Γ:=Γ) frame (sourcePath.go (.index j)) (.int int256)).run (locals,state)=(.ok (payload j),(locals,state)))
 (dstHeader : (Source.readLen (E:=E) (Γ:=Γ) frame dstPath).run (locals,state)=(.ok old.length.val,(locals,state)))
 (beforeDst : Represented old (PrimitivePop.queries indices) dst store)
 (beforeSrc : Represented source (PrimitivePop.queries indices) src store)
 (initial : Transport N hash locations store numeric)
 (dstCoveredHeader : dst ∈ locations) (srcCoveredHeader : src ∈ locations)
 (dstCovered : ∀ i ∈ indices,Solidity.Storage.Loc.data dst i.val ∈ locations)
 (srcCovered : ∀ i ∈ indices,Solidity.Storage.Loc.data src i.val ∈ locations)
 (sourceCovered : ∀ j<source.length.val,Solidity.Storage.Loc.data src j ∈ locations)
 (visitedCovered : ∀ j<max old.length.val source.length.val,Solidity.Storage.Loc.data dst j ∈ locations)
 (fitting : ∀ l ∈ locations,TargetOperations.KeysFit l)
 (targetInitial : ∀ l (member : l ∈ locations),target.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (store l))
 (sourceWords : ∀ j<source.length.val,(payload j).word.map Fin.val=some (TargetOperations.encodeWord (store (.data src j))).val)
 (olderWords : ∀ i ∈ indices,max source.length.val old.length.val≤i.val →
  wordAt frame state.ex (dstPath.go (.index i.val))=some (TargetOperations.encodeWord (store (.data dst i.val))).val) :
 let sourceResult := (Source.storeVal (E:=E) (Γ:=Γ) frame (source.length.val+(old.length.val-source.length.val)+4) (.array .storage (.int int256) none) dstPath
  (Source.Val.storRef (τ:=.array .storage (.int int256) none) rfl sourcePath)).run (locals,state)
 let targetResult := TargetArrayCopyTail.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)
 let resultNumeric := NumericTraversal.copy N hash dst src numeric
 sourceResult=(.ok (),(locals,{state with ex:=state.ex.run (copyLog frame int256 dstPath source.length.val old.length.val payload typed)})) ∧
 Evm.run TargetArrayCopy.code {target with stack:=.slot (TargetOperations.toSlot src srcFits) :: .slot (TargetOperations.toSlot dst dstFits) :: tail}=.ok targetResult 0 ∧
 Represented (old.overlay source) (PrimitivePop.queries indices) dst (CopyTransport.symbolicCopy dst src store) ∧
 Transport N hash locations (CopyTransport.symbolicCopy dst src store) resultNumeric ∧
 (∀ l (member : l ∈ locations),targetResult.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (resultNumeric (l.word N hash))) ∧
 wordAt frame sourceResult.2.2.ex dstPath=some (TargetOperations.encodeWord (resultNumeric (dst.word N hash))).val ∧
 (∀ i ∈ indices,wordAt frame sourceResult.2.2.ex (dstPath.go (.index i.val))=some (TargetOperations.encodeWord (resultNumeric ((Solidity.Storage.Loc.data dst i.val).word N hash))).val) ∧
 (∀ q ∈ PrimitivePop.queries (G:=G) (p:=.int) indices,∀ word,q.read (old.overlay source)=some word → resultNumeric ((q.location dst).word N hash)=word) := by
 dsimp only
 have dstOwner : Represented old [.length .nil] dst store := by
  intro q member; have same:=List.mem_singleton.mp member; subst q; exact beforeDst _ List.mem_cons_self
 have srcOwner : Represented source [.length .nil] src store := by
  intro q member; have same:=List.mem_singleton.mp member; subst q; exact beforeSrc _ List.mem_cons_self
 have sourceLength := TargetHeaderPush.source_header source src srcFits store target srcOwner (targetInitial src srcCoveredHeader)
 have oldLength := TargetHeaderPush.source_header old dst dstFits store target dstOwner (targetInitial dst dstCoveredHeader)
 have certificate := TargetCopyRepresentation.complete run old source indices dst src dstFits srcFits store numeric target tail beforeDst beforeSrc initial
  dstCoveredHeader srcCoveredHeader dstCovered srcCovered sourceCovered visitedCovered fitting targetInitial
 have originalSource : ∀ j<source.length.val,(payload j).word.map Fin.val=some (target.store (.data (TargetOperations.toSlot src srcFits) j)) := by
  intro j live
  have observed := congrArg Fin.val (targetInitial (.data src j) (sourceCovered j live))
  change target.store (.data (TargetOperations.toSlot src srcFits) j)=(TargetOperations.encodeWord (store (.data src j))).val at observed
  rw [observed]
  exact sourceWords j live
 have originalOlder : ∀ j ∈ indices.map Fin.val,max source.length.val old.length.val≤j → wordAt frame state.ex (dstPath.go (.index j))=some (target.store (.data (TargetOperations.toSlot dst dstFits) j)) := by
  intro j member unvisited
  obtain ⟨i,inside,rfl⟩ := List.mem_map.mp member
  have observed := congrArg Fin.val (targetInitial (.data dst i.val) (dstCovered i inside))
  change target.store (.data (TargetOperations.toSlot dst dstFits) i.val)=(TargetOperations.encodeWord (store (.data dst i.val))).val at observed
  rw [observed]
  exact olderWords i inside unvisited
 have sourceCertificate := complete frame writable sourcePath dstPath different source.length.val old.length.val source.length.isLt (indices.map Fin.val)
  payload typed ordinary locals state sourceHeader reads dstHeader target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)
  sourceLength oldLength originalSource originalOlder
 refine ⟨sourceCertificate.1,certificate.1,certificate.2.1,certificate.2.2.1,certificate.2.2.2.1,?_,?_,certificate.2.2.2.2⟩
 · have output := congrArg Fin.val (certificate.2.2.2.1 dst dstCoveredHeader)
   change (TargetArrayCopyTail.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)).store (TargetOperations.toSlot dst dstFits)=_ at output
   rw [← output]
   exact sourceCertificate.2.2.1
 · intro i member
   have output := congrArg Fin.val (certificate.2.2.2.1 (.data dst i.val) (dstCovered i member))
   change (TargetArrayCopyTail.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)).store (.data (TargetOperations.toSlot dst dstFits) i.val)=_ at output
   rw [← output]
   exact sourceCertificate.2.2.2 i.val (List.mem_map.mpr ⟨i,member,rfl⟩)

/-- info: 'Solidity.Backend.StorageOps.SourceSignedStorageCopyTarget.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete
/-- info: 'Solidity.Backend.StorageOps.SourceSignedStorageCopyTarget.complete_numeric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_numeric
end Solidity.Backend.StorageOps.SourceSignedStorageCopyTarget
