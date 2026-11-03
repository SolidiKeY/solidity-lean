import Solidity.Backend.StorageOps.RuntimeCopyComposition
import Solidity.Backend.StorageOps.RecursiveRepeatCopy

/-! OLD typed owners, actual current-input symbolic/numeric copies and complete
ordered observations. Logical failures do not imply reachable-world rollback. -/
namespace Solidity.Backend.StorageOps.RuntimeCopyCompositionControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph NumericCopyCommutation
private def graph : Schema 0 where
 origin := "v10-runtime-copy-composition"
 declId := fun i => nomatch i
 declId_injective := by intro i; exact Fin.elim0 i
 name := fun i => nomatch i
 fields := fun i => nomatch i
 rank := fun i => nomatch i
 nonempty := by intro i; exact Fin.elim0 i
 distinct := by intro i; exact Fin.elim0 i
 guarded := by intro i; exact Fin.elim0 i
private def w (n : Fin 256) : Semantics.Word := lengthWord n.val (by have h:=n.isLt; omega)
private def dst : Solidity.Storage.Loc := .root 0
private def src : Solidity.Storage.Loc := .root 1
private def d (i : Nat) : Solidity.Storage.Loc := .data dst i
private def s (i : Nat) : Solidity.Storage.Loc := .data src i
private def hash (p : Solidity.Storage.Pre) : Nat := if p=.data 0 then 16 else 48
private def locations : List Solidity.Storage.Loc := [dst,src,d 0,d 1,d 2,d 3,d 4,d 5,d 6,s 0,s 1,s 2,s 3,s 4,s 5,s 6]
private def captured : Store := fun l => if l=dst then w 4 else if l=src then w 2 else
 if l=d 0 then w 31 else if l=d 1 then w 37 else if l=d 2 then w 41 else if l=d 3 then w 43 else
 if l=d 4 then w 99 else if l=d 5 then w 151 else if l=d 6 then w 157 else
 if l=s 0 then w 7 else if l=s 1 then w 0 else if l=s 2 then w 23 else if l=s 3 then w 53 else
 if l=s 4 then w 71 else if l=s 5 then w 113 else if l=s 6 then w 127 else w 0
private def initial : WordStore := fun a => if a<16 then captured (.root a) else if a<48 then captured (d (a-16)) else captured (s (a-48))
private def sym1 := CopyTransport.symbolicCopy dst src captured
private def sym2 := CopyTransport.symbolicCopy dst src sym1
private def num1 := NumericTraversal.copy 128 hash dst src initial
private def num2 := NumericTraversal.copy 128 hash dst src num1
private def symView (store : Store) := locations.map (fun l => (store l).val.toNat)
private def numView (store : WordStore) := [0,1,16,17,18,19,20,21,22,48,49,50,51,52,53,54].map (fun a => (store a).val.toNat)
private def old : Value graph (.array (.prim .uint)) := .array ⟨5,by decide⟩ ⟨4,by decide⟩ (by decide) fun i =>
 .present (.prim (if i.val=0 then w 31 else if i.val=1 then w 37 else if i.val=2 then w 41 else if i.val=3 then w 43 else w 99))
private def source : Value graph (.array (.prim .uint)) := .array ⟨5,by decide⟩ ⟨2,by decide⟩ (by decide) fun i =>
 if i.val=1 then .absent else .present (.prim (if i.val=0 then w 7 else if i.val=2 then w 23 else if i.val=3 then w 53 else w 71))
private def onceGraph := recursiveCopy old source
private def twiceGraph := recursiveCopy onceGraph source
private def ix (i : Fin 6) : Index := ⟨i.val,by have h:=i.isLt; omega⟩
private def indices : List Index := [ix 4,ix 1,ix 3,ix 0,ix 2,ix 5,ix 4]
private def element (i : Index) : TypeGraph.Path graph (.array (.prim .uint)) (.prim .uint) := .cons (.index i) .nil
private def graphView (v : Value graph (.array (.prim .uint))) :=
 (v.length.val,v.extent.val,
 indices.map (fun i => (v.observe (element i)).map (fun word => word.val.toNat)),
 indices.map (fun i => ((element i).readLive Value.dflt v).map (fun leaf => leaf.head.val.toNat)))
private theorem run : FiniteRun 128 16 2 hash [.data 0,.data 1] locations := by
 constructor
 · intro p; simp only [hash]; split <;> decide
 · decide
 · decide
 · decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [dst,src,d,s,Solidity.Storage.Loc.Bounded] <;> decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
private theorem before : Transport 128 hash locations captured initial := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
private theorem covered : ∀ l ∈ writeSet 128 hash dst src initial ++ (readSet 128 hash dst src initial).tail,l∈locations := by
 intro l member
 change l∈[dst,d 0,d 1,d 2,d 3]++[src,s 0,s 1] at member
 simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with (rfl|rfl|rfl|rfl|rfl)|(rfl|rfl|rfl) <;> decide
private theorem safe : dst=src ∨ ∀ w∈writeSet 128 hash dst src initial,∀ r∈(readSet 128 hash dst src initial).tail,w≠r := Or.inr (by decide)
private theorem oldOwner : Represented old (PrimitivePop.queries indices) dst captured := by
 intro q member
 simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
   intro word observed
   change some (w 4 )=some word at observed
   cases observed
   rfl
 · refine ⟨⟨by change 4<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed
   change some (w 99)=some word at observed
   cases observed
   rfl
 · refine ⟨⟨by change 1<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed
   change some (w 37)=some word at observed
   cases observed
   rfl
 · refine ⟨⟨by change 3<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed
   change some (w 43)=some word at observed
   cases observed
   rfl
 · refine ⟨⟨by change 0<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed
   change some (w 31)=some word at observed
   cases observed
   rfl
 · refine ⟨⟨by change 2<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed
   change some (w 41)=some word at observed
   cases observed
   rfl
 · refine ⟨⟨by change 5<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed
   change (none : Option Semantics.Word)=some word at observed
   cases observed
 · refine ⟨⟨by change 4<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed
   change some (w 99)=some word at observed
   cases observed
   rfl
private theorem sourceOwner : Represented source (PrimitivePop.queries indices) src captured := by
 intro q member
 simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
   intro word observed
   change some (w 2 )=some word at observed
   cases observed
   rfl
 · refine ⟨⟨by change 4<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed
   change some (w 71)=some word at observed
   cases observed
   rfl
 · refine ⟨⟨by change 1<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed
   change some (w 0)=some word at observed
   cases observed
   rfl
 · refine ⟨⟨by change 3<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed
   change some (w 53)=some word at observed
   cases observed
   rfl
 · refine ⟨⟨by change 0<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed
   change some (w 7)=some word at observed
   cases observed
   rfl
 · refine ⟨⟨by change 2<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed
   change some (w 23)=some word at observed
   cases observed
   rfl
 · refine ⟨⟨by change 5<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed
   change (none : Option Semantics.Word)=some word at observed
   cases observed
 · refine ⟨⟨by change 4<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word observed
   change some (w 71)=some word at observed
   cases observed
   rfl
private theorem selected : ∀ i∈indices,d i.val∈locations ∧ s i.val∈locations := by
 intro i member
 simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
private theorem visited : ∀ i<max old.length.val source.length.val,d i∈locations := by
 intro i inside
 have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by change i<max 4 2 at inside; omega
 rcases cases with rfl|rfl|rfl|rfl <;> decide
private theorem sourceCovered : ∀ i<source.length.val,s i∈locations := by
 intro i inside
 have cases : i=0 ∨ i=1 := by change i<2 at inside; omega
 rcases cases with rfl|rfl <;> decide

/-- OLD inputs inhabit every premise; BOTH current-input transports and whole
Store equalities are conclusions, not assumed middle certificates. -/
theorem certificate : Transport 128 hash locations sym1 num1 ∧ Transport 128 hash locations sym2 num2 ∧ sym2=sym1 ∧ num2=num1 :=
 RuntimeCopyComposition.complete run dst src captured initial before covered safe

/-- PUBLIC owner relation after the independent graph copy repeated twice.
The operation adapter used here is OWNED CopyTransport.complete, not an owner
representation implementation or independent Source/compiler theorem. -/
theorem represented_client : Represented twiceGraph (PrimitivePop.queries indices) dst sym2 := by
 have owner := (CopyTransport.complete run old source indices dst src captured initial oldOwner sourceOwner before
  (by decide) (by decide) (fun i inside => (selected i inside).1) (fun i inside => (selected i inside).2) sourceCovered visited).2
 change Represented (recursiveCopy (recursiveCopy old source) source) _ _ _
 rw [RecursiveRepeatCopy.value_repeat]
 rw [certificate.2.2.1]
 exact owner

/-- COMPLETE symbolic/numeric OLD/once/twice vectors, including older shadows. -/
theorem ordered_stores :
 (symView captured,numView initial,symView sym1,numView num1,symView sym2,numView num2)=
 ([4,2,31,37,41,43,99,151,157,7,0,23,53,71,113,127],
  [4,2,31,37,41,43,99,151,157,7,0,23,53,71,113,127],
  [2,2,7,0,0,0,99,151,157,7,0,23,53,71,113,127],
  [2,2,7,0,0,0,99,151,157,7,0,23,53,71,113,127],
  [2,2,7,0,0,0,99,151,157,7,0,23,53,71,113,127],
  [2,2,7,0,0,0,99,151,157,7,0,23,53,71,113,127]) := by rfl

/-- COMPLETE source/OLD destination/once/twice retained-versus-live reads in
selected order4,1,3,0,2,5,4; malformed5 stays None despite physical word151. -/
theorem ordered_graph : (graphView source,graphView old,graphView onceGraph,graphView twiceGraph)=
 ((2,5,[some 71,some 0,some 53,some 7,some 23,none,some 71],[none,some 0,none,some 7,none,none,none]),
  (4,5,[some 99,some 37,some 43,some 31,some 41,none,some 99],[none,some 37,some 43,some 31,some 41,none,none]),
  (2,5,[some 99,some 0,some 0,some 7,some 0,none,some 99],[none,some 0,none,some 7,none,none,none]),
  (2,5,[some 99,some 0,some 0,some 7,some 0,none,some 99],[none,some 0,none,some 7,none,none,none])) := by rfl

private def rawSlot (v : Value graph (.array (.prim .uint))) (i : Nat) : Slot graph (.prim .uint) :=
 match v with
 | .array extent _ _ slots => oldSlot extent slots i

/-- Source default remains absent; copied live default is materialized. -/
theorem absent_and_older : rawSlot source 1=.absent ∧ rawSlot twiceGraph 1=.present (.prim (w 0)) ∧
 source.find (element (ix 1))=some (.prim (w 0)) ∧
 twiceGraph.find (element (ix 5))=none ∧ sym2 (d 5)=w 151 ∧ sym2 (d 4)=w 99 := by repeat' constructor

/-- Exact aliases retain the OLD relation and the ENTIRE symbolic/numeric stores. -/
theorem self_certificate :
 let self1 := CopyTransport.symbolicCopy dst dst captured
 let selfNum1 := NumericTraversal.copy 128 hash dst dst initial
 Transport 128 hash locations self1 selfNum1 ∧
 Transport 128 hash locations (CopyTransport.symbolicCopy dst dst self1) (NumericTraversal.copy 128 hash dst dst selfNum1) ∧
 CopyTransport.symbolicCopy dst dst self1=self1 ∧ NumericTraversal.copy 128 hash dst dst selfNum1=selfNum1 := by
 apply RuntimeCopyComposition.complete run dst dst captured initial before
 · intro l member
   change l∈[dst,d 0,d 1,d 2,d 3]++[dst,d 0,d 1,d 2,d 3] at member
   simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with (rfl|rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl|rfl) <;> decide
 · exact Or.inl rfl


private def nestedSrc := d 0
private def badLocations : List Solidity.Storage.Loc := [dst,nestedSrc,d 1,d 2,.data nestedSrc 0,.data nestedSrc 1]
private def badStore : Store := fun l => if l=dst then w 1 else if l=nestedSrc then w 2 else
 if l=d 1 then w 31 else if l=d 2 then w 99 else if l=.data nestedSrc 0 then w 7 else if l=.data nestedSrc 1 then w 17 else w 0
private def badInitial : WordStore := fun a => if a=0 then w 1 else if a=16 then w 2 else
 if a=17 then w 31 else if a=18 then w 99 else if a=48 then w 7 else if a=49 then w 17 else w 0
private def badSym1 := CopyTransport.symbolicCopy dst nestedSrc badStore
private def badSym2 := CopyTransport.symbolicCopy dst nestedSrc badSym1
private def badNum1 := NumericTraversal.copy 128 hash dst nestedSrc badInitial
private def badNum2 := NumericTraversal.copy 128 hash dst nestedSrc badNum1
private def badSymView (store : Store) := badLocations.map (fun l => (store l).val.toNat)
private def badNumView (store : WordStore) := [0,16,17,18,48,49].map (fun a => (store a).val.toNat)

/-- Genuine OLD transport and GOOD regions coexist with unsafe current source
interference. This numeric-location client is not asserted typed Source. -/
theorem bad_old_evidence : FiniteRun 128 16 2 hash [.data 0,.data 16] badLocations ∧
 Transport 128 hash badLocations badStore badInitial := by
 constructor
 · constructor
   · intro p; simp only [hash]; split <;> decide
   · decide
   · decide
   · decide
   · intro l member
     simp only [badLocations,List.mem_cons,List.not_mem_nil,or_false] at member
     rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [dst,d,nestedSrc,Solidity.Storage.Loc.Bounded] <;> decide
   · intro l member
     simp only [badLocations,List.mem_cons,List.not_mem_nil,or_false] at member
     rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
 · intro l member
   simp only [badLocations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

/-- COMPLETE ordered fixture observations for BOTH actual executions. -/
theorem bad_ordered :
 (badSymView badStore,badNumView badInitial,badSymView badSym1,badNumView badNum1,badSymView badSym2,badNumView badNum2)=
 ([1,2,31,99,7,17],[1,2,31,99,7,17],
  [2,7,17,99,7,17],[2,7,17,99,7,17],
  [7,7,17,0,7,17],[7,7,17,0,7,17]) := by rfl

/-- Refutes BOTH unrestricted repeat laws, not just an input check. -/
theorem bad_rejected :
 ¬ (dst=nestedSrc ∨ ∀ w∈writeSet 128 hash dst nestedSrc badInitial,∀ r∈(readSet 128 hash dst nestedSrc badInitial).tail,w≠r) ∧
 badSym2≠badSym1 ∧ badNum2≠badNum1 := by
 refine ⟨by decide,?_,?_⟩
 · intro same
   have headers : w 7=w 2 := congrFun same dst
   exact (by decide : w 7≠w 2) headers
 · intro same
   have headers : w 7=w 2 := congrFun same 0
   exact (by decide : w 7≠w 2) headers

/-- info: 'Solidity.Backend.StorageOps.RuntimeCopyCompositionControls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
/-- info: 'Solidity.Backend.StorageOps.RuntimeCopyCompositionControls.represented_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_client
/-- info: 'Solidity.Backend.StorageOps.RuntimeCopyCompositionControls.ordered_stores' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered_stores
/-- info: 'Solidity.Backend.StorageOps.RuntimeCopyCompositionControls.ordered_graph' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered_graph
/-- info: 'Solidity.Backend.StorageOps.RuntimeCopyCompositionControls.absent_and_older' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms absent_and_older
/-- info: 'Solidity.Backend.StorageOps.RuntimeCopyCompositionControls.self_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms self_certificate
/-- info: 'Solidity.Backend.StorageOps.RuntimeCopyCompositionControls.bad_old_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms bad_old_evidence
/-- info: 'Solidity.Backend.StorageOps.RuntimeCopyCompositionControls.bad_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms bad_ordered
/-- info: 'Solidity.Backend.StorageOps.RuntimeCopyCompositionControls.bad_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms bad_rejected
end Solidity.Backend.StorageOps.RuntimeCopyCompositionControls
