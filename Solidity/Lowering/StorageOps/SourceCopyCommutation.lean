import Solidity.Lowering.StorageOps.SourceCopyReadbacks

/-! Operation-side finite touched paths for CURRENT Source copy logs.
No Source state/journal equality, compiler simulation or implicit rollback. -/
namespace Solidity.Backend.StorageOps.SourceCopyCommutation
open SourceStorageCopy SourceCopyFrames SourceCopyReadbacks SourceArrayDeleteTarget

/-- Exact header plus runtime copied/cleared prefix; older shadows excluded. -/
def Touched (dst : Source.SPath) (count oldLength : Nat) (query : Source.SPath) : Prop :=
 query=dst ∨ ∃ j<max count oldLength,query=dst.go (.index j)

theorem frame {E : Source.Env} (fr : Source.Fr) (dst query : Source.SPath)
 (count oldLength : Nat) (payload : Nat → Source.Val E.layout (.int Source.IntTy.u256))
 (typed : E.pathTy dst=some (.array .storage (.int Source.IntTy.u256) none))
 (state : Source.ExecState E.layout E.lay E.lay) (outside : ¬Touched dst count oldLength query) :
 wordAt fr (state.run (copyLog fr Source.IntTy.u256 dst count oldLength payload typed)) query=wordAt fr state query := by
 have h := SourceCopyFrames.copy_other fr Source.IntTy.u256 dst query count oldLength payload typed state
  (fun same => outside (Or.inl same))
  (fun j member same => outside (Or.inr ⟨j,by omega,same⟩))
  (by
   intro j member same
   have bound := List.mem_range'.mp member
   exact outside (Or.inr ⟨j,by omega,same⟩))
 unfold wordAt
 rw [h.1]

/-- Touched words have a source-captured result independent of OLD storage.
Present-zero versus missing outside the footprint remains observable. -/
theorem overwritten {E : Source.Env} (fr : Source.Fr) (dst query : Source.SPath)
 (count oldLength : Nat) (payload : Nat → Source.Val E.layout (.int Source.IntTy.u256))
 (typed : E.pathTy dst=some (.array .storage (.int Source.IntTy.u256) none))
 (ordinary : E.transientRoot dst=false)
 (a b : Source.ExecState E.layout E.lay E.lay) (inside : Touched dst count oldLength query) :
 wordAt fr (a.run (copyLog fr Source.IntTy.u256 dst count oldLength payload typed)) query=
 wordAt fr (b.run (copyLog fr Source.IntTy.u256 dst count oldLength payload typed)) query := by
 rcases inside with header | ⟨j,bound,child⟩
 · rw [header,copy_header fr Source.IntTy.u256 dst count oldLength payload typed a ordinary,
    copy_header fr Source.IntTy.u256 dst count oldLength payload typed b ordinary]
 · rw [child,copy_data fr dst count oldLength j payload typed a ordinary,
    copy_data fr dst count oldLength j payload typed b ordinary]
   by_cases copied : j<count
   · rw [if_pos copied,if_pos copied]
   · have stale : j<oldLength := by omega
     rw [if_neg copied,if_neg copied,if_pos stale,if_pos stale]

/-- A copy transports equality at one OLD word, including missing values. -/
theorem word_congr {E : Source.Env} (fr : Source.Fr) (dst query : Source.SPath)
 (count oldLength : Nat) (payload : Nat → Source.Val E.layout (.int Source.IntTy.u256))
 (typed : E.pathTy dst=some (.array .storage (.int Source.IntTy.u256) none))
 (ordinary : E.transientRoot dst=false)
 (a b : Source.ExecState E.layout E.lay E.lay) (same : wordAt fr a query=wordAt fr b query) :
 wordAt fr (a.run (copyLog fr Source.IntTy.u256 dst count oldLength payload typed)) query=
 wordAt fr (b.run (copyLog fr Source.IntTy.u256 dst count oldLength payload typed)) query := by
 by_cases inside : Touched dst count oldLength query
 · exact overwritten fr dst query count oldLength payload typed ordinary a b inside
 · rw [frame fr dst query count oldLength payload typed a inside,
    frame fr dst query count oldLength payload typed b inside]
   exact same

/-- Actual Source.Op logs commute ONLY in word observations under disjoint
runtime footprints. Payloads are fixed captures; journals remain ordered. -/
theorem commute {E : Source.Env} (fr : Source.Fr) (d1 d2 : Source.SPath)
 (n1 old1 n2 old2 : Nat)
 (p1 p2 : Nat → Source.Val E.layout (.int Source.IntTy.u256))
 (t1 : E.pathTy d1=some (.array .storage (.int Source.IntTy.u256) none))
 (t2 : E.pathTy d2=some (.array .storage (.int Source.IntTy.u256) none))
 (o1 : E.transientRoot d1=false) (o2 : E.transientRoot d2=false)
 (state : Source.ExecState E.layout E.lay E.lay)
 (apart : ∀ query,Touched d1 n1 old1 query → ¬Touched d2 n2 old2 query) :
 let l1 := copyLog fr Source.IntTy.u256 d1 n1 old1 p1 t1
 let l2 := copyLog fr Source.IntTy.u256 d2 n2 old2 p2 t2
 ∀ query,wordAt fr ((state.run l1).run l2) query=wordAt fr ((state.run l2).run l1) query := by
 dsimp only
 intro query
 by_cases inside : Touched d1 n1 old1 query
 · rw [frame fr d2 query n2 old2 p2 t2 _ (apart query inside)]
   exact overwritten fr d1 query n1 old1 p1 t1 o1 state _ inside
 · rw [frame fr d1 query n1 old1 p1 t1 _ inside]
   exact word_congr fr d2 query n2 old2 p2 t2 o2 _ state
    (frame fr d1 query n1 old1 p1 t1 state inside)

/-- info: 'Solidity.Backend.StorageOps.SourceCopyCommutation.frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms frame

/-- info: 'Solidity.Backend.StorageOps.SourceCopyCommutation.overwritten' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms overwritten

/-- info: 'Solidity.Backend.StorageOps.SourceCopyCommutation.word_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms word_congr

/-- info: 'Solidity.Backend.StorageOps.SourceCopyCommutation.commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms commute

end Solidity.Backend.StorageOps.SourceCopyCommutation
