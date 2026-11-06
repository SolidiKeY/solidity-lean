import Solidity.Backend.StorageOps.NestedPopCommutation

/-! Actual nested-pop operations with unequal runtime lengths, GOOD finite
regions, complete ordered words and ancestor-overlap negative. Numeric model
only; no Source/representation/target/world execution is silently inferred. -/
namespace Solidity.Backend.StorageOps.NestedPopCommutation.Controls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
private def word (i : Fin 256) : Semantics.Word := ⟨i.val,by have h:=i.isLt; simp only [PrimTy.inRange,decide_eq_true_eq]; omega⟩
private def left : Solidity.Storage.Loc := .root 0
private def right : Solidity.Storage.Loc := .root 1
private def lc (i : Nat) : Solidity.Storage.Loc := .data left i
private def rc (i : Nat) : Solidity.Storage.Loc := .data right i
private def le (j : Nat) : Solidity.Storage.Loc := .data (lc 1) j
private def re (j : Nat) : Solidity.Storage.Loc := .data (rc 0) j
private def mappingCell : Solidity.Storage.Loc := .hash 1 (lc 1) 0
private def deep : Solidity.Storage.Loc := .data (le 2) 0
private def hash (p : Solidity.Storage.Pre) : Nat :=
 if p=.data 0 then 16 else if p=.data 1 then 32 else if p=.data 17 then 64 else
 if p=.data 32 then 80 else if p=.entry 1 17 then 128 else if p=.data 66 then 144 else 0
private def preimages : List Solidity.Storage.Pre := [.data 0,.data 1,.data 17,.data 32,.entry 1 17,.data 66]
private def locations : List Solidity.Storage.Loc :=
 [left,right,lc 0,lc 1,lc 2,rc 0,rc 1,le 0,le 1,le 2,le 3,re 0,re 1,re 2,mappingCell,deep]
private def initial : WordStore := fun a =>
 if a=0 then word 2 else if a=1 then word 1 else if a=16 then word 2 else if a=17 then word 3 else
 if a=18 then word 1 else if a=32 then word 2 else if a=33 then word 1 else if a=64 then word 7 else
 if a=65 then word 17 else if a=66 then word 23 else if a=67 then word 71 else if a=80 then word 53 else
 if a=81 then word 59 else if a=82 then word 89 else if a=128 then word 77 else if a=144 then word 31 else word 99
private def leftResult := (NestedPopTransport.execute 256 hash left initial).getD initial
private def rightResult := (NestedPopTransport.execute 256 hash right initial).getD initial
private def final := (NestedPopTransport.execute 256 hash right leftResult).getD initial
private def captured : Store := fun l =>
 if l=left then word 2 else if l=right then word 1 else if l=lc 0 then word 2 else if l=lc 1 then word 3 else
 if l=lc 2 then word 1 else if l=rc 0 then word 2 else if l=rc 1 then word 1 else if l=le 0 then word 7 else
 if l=le 1 then word 17 else if l=le 2 then word 23 else if l=le 3 then word 71 else if l=re 0 then word 53 else
 if l=re 1 then word 59 else if l=re 2 then word 89 else if l=mappingCell then word 77 else if l=deep then word 31 else word 99
private theorem run : FiniteRun 256 8 2 hash preimages locations := by
 constructor
 · intro p
   simp only [hash]
   split <;> first | decide | (split <;> first | decide | (split <;> first | decide | (split <;> first | decide | (split <;> first | decide | (split <;> decide)))))
 · decide
 · decide
 · decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [left,right,lc,rc,le,re,mappingCell,deep,Solidity.Storage.Loc.Bounded] <;> decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem leftTouches : touches 256 hash left initial=[left,lc 1,le 0,le 1,le 2] := rfl
private theorem rightTouches : touches 256 hash right initial=[right,rc 0,re 0,re 1] := rfl
private theorem covered : ∀ l ∈ touches 256 hash left initial ++ touches 256 hash right initial, l ∈ locations := by
 rw [leftTouches,rightTouches]
 intro l member
 simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) <;> decide
private theorem separate : ∀ a ∈ touches 256 hash left initial, ∀ b ∈ touches 256 hash right initial, a ≠ b := by
 rw [leftTouches,rightTouches]
 intro a ha b hb
 simp only [List.mem_cons,List.not_mem_nil,or_false] at ha hb
 rcases ha with rfl | rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;> decide
private def lr (s : WordStore) := (NestedPopTransport.execute 256 hash left s).bind (NestedPopTransport.execute 256 hash right)
private def rl (s : WordStore) := (NestedPopTransport.execute 256 hash right s).bind (NestedPopTransport.execute 256 hash left)

/-- Genuine application of the general commutation theorem, unequal outer2/1
and inner3/2 live lengths; both success branches are inhabited. -/
theorem certificate : FiniteRun 256 8 2 hash preimages locations ∧ lr initial=some final ∧ rl initial=some final := by
 refine ⟨run,rfl,?_⟩
 exact (pop_pop run left right initial covered separate).symm.trans (by rfl)
private def view (s : WordStore) := [0,1,16,17,18,32,33,64,65,66,67,80,81,82,128,144,255].map s

/-- COMPLETE ordered ACTUAL old/left/right/both-order vectors and generated
runtime accesses. Retained tails, other children, opaque mapping cell77, deeper
raw31 and outside99 survive; only selected LIVE grandchildren clear. -/
theorem ordered :
 (view initial,view leftResult,view rightResult,(lr initial).map view,(rl initial).map view,
  (touches 256 hash left initial).map (fun l => l.word 256 hash),
  (touches 256 hash right initial).map (fun l => l.word 256 hash)) =
 ([word 2,word 1,word 2,word 3,word 1,word 2,word 1,word 7,word 17,word 23,word 71,word 53,word 59,word 89,word 77,word 31,word 99],
  [word 1,word 1,word 2,word 0,word 1,word 2,word 1,word 0,word 0,word 0,word 71,word 53,word 59,word 89,word 77,word 31,word 99],
  [word 2,word 0,word 2,word 3,word 1,word 0,word 1,word 7,word 17,word 23,word 71,word 0,word 0,word 89,word 77,word 31,word 99],
  some [word 1,word 0,word 2,word 0,word 1,word 0,word 1,word 0,word 0,word 0,word 71,word 0,word 0,word 89,word 77,word 31,word 99],
  some [word 1,word 0,word 2,word 0,word 1,word 0,word 1,word 0,word 0,word 0,word 71,word 0,word 0,word 89,word 77,word 31,word 99],
  [0,17,64,65,66],[1,32,80,81]) := rfl

private def observers : List Solidity.Storage.Loc := [lc 0,lc 2,rc 1,le 3,re 2,mappingCell,deep]
/-- ALL covered outside observations framed from actual generated sets and
original GOOD finite regions, including older/deeper/mapping-like cells. -/
theorem frames :
 (∀ l ∈ observers, leftResult (l.word 256 hash)=initial (l.word 256 hash)) ∧
 (∀ l ∈ observers, rightResult (l.word 256 hash)=initial (l.word 256 hash)) := by
 constructor
 · apply execute_frames run left initial leftResult rfl observers
   · rw [leftTouches]
     intro l member
     simp only [observers,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
     rcases member with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide
   · rw [leftTouches]
     intro a ha b hb
     simp only [observers,List.mem_cons,List.not_mem_nil,or_false] at ha hb
     rcases ha with rfl | rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
 · apply execute_frames run right initial rightResult rfl observers
   · rw [rightTouches]
     intro l member
     simp only [observers,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
     rcases member with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide
   · rw [rightTouches]
     intro a ha b hb
     simp only [observers,List.mem_cons,List.not_mem_nil,or_false] at ha hb
     rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Post-Transport follows from original initialized stores and generated logs,
not an asserted output relation. Both actual nested pop families are exercised. -/
theorem transported :
 Transport 256 hash locations ((writeLog 256 hash left initial).foldl (fun s op => Representation.write s op.1 op.2) captured) leftResult ∧
 Transport 256 hash locations ((writeLog 256 hash right initial).foldl (fun s op => Representation.write s op.1 op.2) captured) rightResult := by
 have before : Transport 256 hash locations captured initial := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
 exact ⟨execute_transport run left captured initial leftResult before rfl
   (fun l member => covered l (List.mem_append.mpr (Or.inl member))),
  execute_transport run right captured initial rightResult before rfl
   (fun l member => covered l (List.mem_append.mpr (Or.inr member)))⟩

private def emptyLeft := writeWord initial 0 (word 0)
private def emptyRight := writeWord initial 1 (word 0)
private def emptyBoth := writeWord emptyLeft 1 (word 0)
/-- Both empty failure arrangements and both-empty are exact Option outcomes.
The opposite first pop can succeed/change storage before the second fails;
this is NOT a world rollback theorem. -/
theorem failures : (lr emptyLeft,rl emptyLeft,lr emptyRight,rl emptyRight,lr emptyBoth,rl emptyBoth)=
 (none,none,none,none,none,none) ∧
 (NestedPopTransport.execute 256 hash right emptyLeft).isSome=true ∧
 (NestedPopTransport.execute 256 hash left emptyRight).isSome=true := ⟨rfl,rfl,rfl⟩

private def overlapInitial := writeWord initial 66 (word 1)
/-- GOOD original regions still permit SYMBOLIC ancestor overlap. Left pop
zeros the other root, making second pop fail; reverse succeeds and changes it.
The original cross-set disjointness premise cannot be dropped. No typed Source
alias admission or world observation is inferred from this numeric control. -/
theorem overlap_negative : FiniteRun 256 8 2 hash preimages locations ∧
 ((NestedPopTransport.execute 256 hash left overlapInitial).bind (NestedPopTransport.execute 256 hash (lc 1)))=none ∧
 ((NestedPopTransport.execute 256 hash (lc 1) overlapInitial).bind (NestedPopTransport.execute 256 hash left)).isSome=true ∧
 ¬ (∀ a ∈ touches 256 hash left overlapInitial, ∀ b ∈ touches 256 hash (lc 1) overlapInitial, a ≠ b) := by
 refine ⟨run,rfl,rfl,?_⟩
 intro alleged
 have bad:=alleged (lc 1) (by decide) (lc 1) (by decide)
 exact bad rfl

/-- info: 'Solidity.Backend.StorageOps.NestedPopCommutation.Controls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
/-- info: 'Solidity.Backend.StorageOps.NestedPopCommutation.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.NestedPopCommutation.Controls.frames' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms frames
/-- info: 'Solidity.Backend.StorageOps.NestedPopCommutation.Controls.transported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms transported
/-- info: 'Solidity.Backend.StorageOps.NestedPopCommutation.Controls.failures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms failures
/-- info: 'Solidity.Backend.StorageOps.NestedPopCommutation.Controls.overlap_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms overlap_negative
end Solidity.Backend.StorageOps.NestedPopCommutation.Controls
