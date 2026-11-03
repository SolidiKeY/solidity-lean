import Solidity.Backend.StorageOps.PrimitiveCycleNumeric

/-! Actual whole numeric-store cycle controls distinguish raw algebra from
finite physical separation and from a whole compiler/Source/world bridge. -/
namespace Solidity.Backend.StorageOps.PrimitiveCycleNumeric.Controls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
private def base : Solidity.Storage.Loc := .root 0
private def hash (key : Solidity.Storage.Pre) : Nat := if key=.data 0 then 4 else 0
private def w0 : Semantics.Word := ⟨0,by decide⟩
private def w1 : Semantics.Word := ⟨1,by decide⟩
private def w2 : Semantics.Word := ⟨2,by decide⟩
private def w53 : Semantics.Word := ⟨53,by decide⟩
private def w99 : Semantics.Word := ⟨99,by decide⟩
private def small (i : Fin 4) : Index := ⟨i.val,by have h:=i.isLt; omega⟩
private def numeric (length : Index) : WordStore := fun a =>
 if a=0 then lengthWord length.val length.isLt else if a=7 then w99 else w53
private theorem header (length : Index) : LifecycleNumeric.headerLength 16 hash base (numeric length)=length.val := by
 apply LifecycleNumeric.headerLength_known hash base _ length
 rfl
private def addresses : List Nat := [0,4,5,6,7,9,5]
private def view (s : WordStore) := addresses.map s

/-- ALL intrinsic word lengths with BOTH actual Option outcomes. No legacy
metadata or finite-query cap, and every raw numeric word is covered by equality. -/
theorem arbitrary_headers (length : Index) :
 PrimitiveCycleProgram.execute 16 hash base (numeric length)=
 if 0<length.val then some (afterPop 16 hash base (numeric length)) else none := by
 rw [cycle,pop_outcome,header]

/-- Complete ordered actual numeric triple outcomes, including failure, older
shadow99, outside53 and repeated-address observations. -/
theorem ordered :
 ([small 0,small 1,small 2,small 3].map (fun h => (PrimitiveCycleProgram.execute 16 hash base (numeric h)).map view)) =
 [none,some [w0,w0,w53,w53,w99,w53,w53],some [w1,w53,w0,w53,w99,w53,w0],
 some [w2,w53,w53,w0,w99,w53,w53]] := by
 simp only [List.map_cons,List.map_nil,arbitrary_headers]
 rfl

private def locations : List Solidity.Storage.Loc := [base,.data base 1]
private def preimages : List Solidity.Storage.Pre := [.data 0]
private theorem run : FiniteRun 16 4 1 hash preimages locations := by
 constructor
 · intro p; simp only [hash]; split <;> decide
 · decide
 · decide
 · decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl <;> simp only [base,Solidity.Storage.Loc.Bounded] <;> decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl <;> decide

/-- Genuine finite-run application: selected-zero is derived with exact original
coverage, while raw outside words are preserved directly by operation writes. -/
theorem finite_selected : ∃ result,
 PrimitiveCycleProgram.execute 16 hash base (numeric (small 2))=some result ∧
 result 0=w1 ∧ result 5=w0 ∧
 ∀ a, a ≠ 0 → a ≠ 5 → result a=numeric (small 2) a := by
 refine ⟨afterPop 16 hash base (numeric (small 2)),?_,rfl,?_,?_⟩
 · rw [arbitrary_headers]; rfl
 · exact selected_zero run base (numeric (small 2)) (by decide) (by change .data base 1 ∈ locations; decide)
 · intro a root child
   change writeWord (writeWord (numeric (small 2)) 5 w0) 0 w1 a=numeric (small 2) a
   simp only [writeWord,if_neg root,if_neg child]

private def collideHash (_ : Solidity.Storage.Pre) : Nat := 0
private def collisionOld : WordStore := fun a => if a=0 then w2 else w53
/-- Omitting separation from selected_zero is FALSE: child/root collide at0.
Actual whole-cycle equality STILL holds because numeric header writes are LAST.
Thus an intermediate zero claim cannot be smuggled into the raw identity. -/
theorem collision_negative :
 (Solidity.Storage.Loc.data base 1).word 1 collideHash=base.word 1 collideHash ∧
 (afterPop 1 collideHash base collisionOld) ((Solidity.Storage.Loc.data base 1).word 1 collideHash)=w1 ∧
 (afterPop 1 collideHash base collisionOld) ((Solidity.Storage.Loc.data base 1).word 1 collideHash) ≠ ClearDemands.zero ∧
 PrimitivePop.execute 1 collideHash base collisionOld=some (afterPop 1 collideHash base collisionOld) ∧
 PrimitiveCycleProgram.execute 1 collideHash base collisionOld=PrimitivePop.execute 1 collideHash base collisionOld := by
 refine ⟨rfl,rfl,?_,rfl,cycle 1 collideHash base collisionOld⟩
 decide

private def wrong : WordStore := writeWord (writeWord (numeric (small 2)) 6 w0) 0 w2
/-- Actual push/pop on OLD input clears a different retained slot and keeps
header2. This is not the first pop result observed by the triple. -/
theorem wrong_order :
 ((LifecycleNumeric.pushPrimitive 16 hash base (numeric (small 2))).bind (PrimitivePop.execute 16 hash base)).map view =
 some [w2,w53,w53,w0,w99,w53,w53] ∧
 wrong ≠ afterPop 16 hash base (numeric (small 2)) := by
 refine ⟨rfl,?_⟩
 intro same
 have bad := congrArg (fun store : WordStore => (store 0).val) same
 change (2:Int)=1 at bad
 omega

private def high : Index := ⟨2^256-1,by decide⟩
/-- Full word-range execution beyond legacy owner metadata. No selected-zero
claim is inferred without the corresponding finite physical region premises. -/
theorem fullword :
 PrimitiveCycleProgram.execute 16 hash base (numeric high)=some (afterPop 16 hash base (numeric high)) ∧
 LifecycleNumeric.headerLength 16 hash base (afterPop 16 hash base (numeric high))=2^256-2 := by
 constructor
 · rw [arbitrary_headers,if_pos (by change 0<2^256-1; decide)]
 · rw [pop_header,header]
   change 2^256-1-1=2^256-2
   omega

/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleNumeric.Controls.arbitrary_headers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms arbitrary_headers
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleNumeric.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleNumeric.Controls.finite_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms finite_selected
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleNumeric.Controls.collision_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms collision_negative
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleNumeric.Controls.wrong_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_order
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleNumeric.Controls.fullword' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fullword
end Solidity.Backend.StorageOps.PrimitiveCycleNumeric.Controls
