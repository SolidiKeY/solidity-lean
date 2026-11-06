import Solidity.Backend.StorageOps.FreshDefaultPush
import Solidity.Backend.StorageOps.PathRepresentation
import Solidity.Backend.StorageOps.LifecyclePaths

/-! ROOT composition of actual fresh allocation and existing default code.
PUBLIC recursive represented/path/frame laws are consumed read-only. Prefixes
have arbitrary finite typed length; no recursive representation is recreated.
The original FiniteRun is an explicit typed per-run premise. Connecting the
source-determined hashed trace to it remains the SS-CP5-HASHED producer's job. -/
namespace Solidity.Backend.StorageOps.FreshDefaultRoot
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- The actual root save and the actual generated initialization footprint
frame disjoint ROOT observations, including exact failures and compatibility.
No physical-cell contract is inferred from a failed logical read. -/
theorem outside_owner {n : Nat} {G : Schema n} {A E : TypeGraph.Ty n}
 (root result : Value G A) (pre : TypeGraph.Path G A (.array E)) (next : Value G (.array E))
 (saved : root.save pre next=some result) (queries : List (Query G A))
 (base child arrayBase : Solidity.Storage.Loc) (captured : Store) (word : Semantics.Word)
 (before : Represented root queries base captured)
 (apart : ∀ q ∈ queries,q.apart pre)
 (headerApart : ∀ q ∈ queries,q.location base≠arrayBase)
 (initApart : ∀ q ∈ queries,∀ demand ∈ CopyDefaults.demands G E,q.location base≠demand.location child) :
 Represented result queries base
  ((CopyDefaults.updates G E child).foldl (fun store op => Representation.write store op.1 op.2)
    (Representation.write captured arrayBase word)) := by
 intro q member
 obtain ⟨supported,compatible,represented⟩ := before q member
 refine ⟨supported,?_,?_⟩
 · rw [Query.compatible_frame root result pre next saved q (apart q member)]
   exact compatible
 · intro value observed
   have frame : ((CopyDefaults.updates G E child).foldl (fun store op => Representation.write store op.1 op.2)
      (Representation.write captured arrayBase word)) (q.location base)=captured (q.location base) := by
    simp only [CopyDefaults.updates,List.foldl_map]
    exact (ClearDemands.fold_outside (CopyDefaults.demands G E) child (q.location base)
      (Representation.write captured arrayBase word) (initApart q member)).trans
      (Representation.write_other captured arrayBase (q.location base) word (headerApart q member))
   rw [frame]
   apply represented value
   rwa [Query.read_frame root result pre next saved q (apart q member)] at observed

/-- Existing fresh current-header push/default code now transports actual
ROOT queries through any successful recursive typed prefix. OLD observations,
run/coverage/addresses and symbolic query separation remain explicit. -/
theorem complete {n N L R : Nat} {G : Schema n} {A E : TypeGraph.Ty n}
 (root result : Value G A) (pre : TypeGraph.Path G A (.array E)) (old : Value G (.array E))
 (found : root.find pre=some old) (pushed : pushAt root pre=some result)
 (fresh : old.extent.val=old.length.val) (permit : CopyPermit G E)
 (queries : List (Query G E)) (supported : ∀ q ∈ queries,q.supported)
 (outside : List (Query G A)) (base : Solidity.Storage.Loc) (fits : TargetOperations.KeysFit base)
 {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations) (captured : Store) (numeric : WordStore) (machine : Evm.Machine)
 (before : Represented root (([.length .nil] : List (Query G (.array E))).map (Query.prefix pre)) base captured)
 (beforeOutside : Represented root outside base captured)
 (apart : ∀ q ∈ outside,q.apart pre)
 (headerApart : ∀ q ∈ outside,q.location base≠pathLoc pre base)
 (initApart : ∀ q ∈ outside,∀ demand ∈ CopyDefaults.demands G E,
   q.location base≠demand.location (pathLoc (AggregatePopFrames.indexPath (G:=G) (E:=E) old.length) (pathLoc pre base)))
 (initial : Transport N hash locations captured numeric) (rootCovered : pathLoc pre base ∈ locations)
 (covered : ∀ q ∈ CopyDefaults.demands G E ++ queries,
   q.location (pathLoc (AggregatePopFrames.indexPath (G:=G) (E:=E) old.length) (pathLoc pre base)) ∈ locations)
 (coverage : old.length.val+1≤lmax)
 (fitting : ∀ l ∈ locations,TargetOperations.KeysFit l)
 (agreement : ∀ l (member : l ∈ locations),machine.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (captured l)) :
 ∃ next : Value G (.array E),
 operationPush old=some next ∧ root.save pre next=some result ∧
 let arrayBase := pathLoc pre base
 let arrayFits := TargetOperations.path_keysFit pre base fits
 let childPre := AggregatePopFrames.indexPath (G:=G) (E:=E) old.length
 let child := pathLoc childPre arrayBase
 let childFits := TargetOperations.path_keysFit childPre arrayBase arrayFits
 let word := lengthWord next.length.val next.length.isLt
 let middleStore := Representation.write captured arrayBase word
 let middleNumeric := writeWord numeric (arrayBase.word N hash) word
 let middleTarget := {machine with store:=Evm.WordStore.write machine.store (TargetOperations.toSlot arrayBase arrayFits) (TargetOperations.encodeWord word).val}
 let afterStore := (CopyDefaults.updates G E child).foldl (fun store op => Representation.write store op.1 op.2) middleStore
 let afterNumeric := CopyDefaults.numericInit (N:=N) G E child hash middleNumeric
 let afterTarget := TargetDefaultInit.afterInit G E child childFits middleTarget
 FreshDefaultPush.execute G E N hash arrayBase numeric=some afterNumeric ∧
 Evm.run (TargetHeaderPush.code (TargetOperations.toSlot arrayBase arrayFits) ++ TargetDefaultInit.code G E permit child childFits) machine=.ok afterTarget 0 ∧
 result.find (pre.append childPre)=some (Value.dflt E) ∧
 Represented result (((.length .nil::queries.map (Query.prefix childPre)).map (Query.prefix pre))++outside) base afterStore ∧
 Transport N hash locations afterStore afterNumeric ∧
 (∀ l (member : l ∈ locations),afterTarget.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (afterNumeric (l.word N hash))) := by
 obtain ⟨actual,next,read,changed,saved⟩ := modifyAt_success root result pre operationPush (by simpa only [pushAt] using pushed)
 rw [found] at read
 cases read
 have readBack : result.find pre=some next := Value.find_save root result pre next saved
 have prefixSupported : PathSupported pre := by
  have atHeader := before ((Query.length (G:=G) (.nil : TypeGraph.Path G (.array E) (.array E))).prefix pre)
    (List.mem_map.mpr ⟨_,List.mem_singleton_self _,rfl⟩)
  exact ((Query.supported_prefix pre _).mp atHeader.1).1
 have childOwner := PathRepresentation.focus root old pre found [.length .nil] base captured before
 have localCertificate := FreshDefaultPush.complete old next fresh changed permit queries supported (pathLoc pre base)
  (TargetOperations.path_keysFit pre base fits) run captured numeric machine childOwner initial rootCovered covered coverage fitting agreement
 have rootOwner := Represented.prefix pre readBack prefixSupported localCertificate.2.2.1
 have outsideOwner := outside_owner root result pre next saved outside base
  (pathLoc (AggregatePopFrames.indexPath (G:=G) (E:=E) old.length) (pathLoc pre base))
  (pathLoc pre base) captured (lengthWord next.length.val next.length.isLt) beforeOutside apart headerApart initApart
 have childRead := FreshDefaultPush.fresh_find old next fresh changed
 have rootChild : result.find (pre.append (AggregatePopFrames.indexPath (G:=G) (E:=E) old.length))=some (Value.dflt E) := by
  change (pre.append _).read Value.dflt result=_
  rw [TypeGraph.Path.read_append]
  change (result.find pre).bind (fun child => child.find (AggregatePopFrames.indexPath (G:=G) (E:=E) old.length))=_
  rw [readBack]
  exact childRead
 refine ⟨next,changed,saved,localCertificate.1,localCertificate.2.1,rootChild,?_,localCertificate.2.2.2.1,localCertificate.2.2.2.2⟩
 intro q member
 rcases List.mem_append.mp member with inside|outside
 · exact rootOwner q inside
 · exact outsideOwner q outside

/-- info: 'Solidity.Backend.StorageOps.FreshDefaultRoot.outside_owner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms outside_owner
/-- info: 'Solidity.Backend.StorageOps.FreshDefaultRoot.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete
end Solidity.Backend.StorageOps.FreshDefaultRoot
