import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocationInventory

/-! Extensionality of the existing intrinsic object product and uniqueness of
heaps from their old initialHeap plus exact new-object contents. No erased heap or
new execution relation is introduced. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.TypedHeapExtensionality
open Evm Evm.Memory

theorem objects_ext {H : HTy} (Rs : List RefTy) (left right : Objs H Rs)
 (same : ∀ i R (typed : Rs[i]?=some R), Objs.get Rs left i typed=Objs.get Rs right i typed) : left=right := by
 induction Rs with
 | nil => cases left;cases right;rfl
 | cons R Rs ih =>
   have head : left.1=right.1 := same 0 R rfl
   have tail : left.2=right.2 := ih left.2 right.2 (fun i S typed =>
     same (i+1) S (by simpa only [List.getElem?_cons_succ] using typed))
   exact Prod.ext head tail

theorem heap_ext {H : HTy} (left right : Heap H)
 (same : ∀ {R : RefTy} (r : HRef H R), left.get r=right.get r) : left=right := by
 exact objects_ext H left right (fun i R typed => same ⟨i,typed⟩)

/-- Each newly typed reference denotes the exact allocated bool[3] object. -/
def Defaults (initial : Nat) {H : HTy} (heap : Heap H) : Prop :=
 ∀ {R : RefTy} (r : HRef H R), initial≤r.id →
 R=.array (.prim .bool) ∧
 HEq (heap.get r) (defaultArray .bool AllocatingScalarSource.size : MObj H (.array (.prim .bool)))

theorem of_inventory {C : Contract} {Γ : Ctx} {initial count cursor : Nat}
 {σ : State C Γ} {base : Nat → Fin W}
 (inventory : ScalarAllocationInventory.Holds initial count cursor σ base)
 (size : σ.H.length=initial+count) : Defaults initial σ.heap := by
 intro R r fresh
 obtain ⟨j,small,identity,kind,contents,address⟩ := ScalarAllocationInventory.covers inventory size r fresh
 exact ⟨kind,contents⟩

theorem prefix_unique {H H' : HTy} (initialHeap : Heap H) (e : H <+: H') (left right : Heap H')
 (leftKeeps : Heap.Keeps e initialHeap left) (rightKeeps : Heap.Keeps e initialHeap right)
 (newSame : ∀ {R : RefTy} (r : HRef H' R), H.length≤r.id → left.get r=right.get r) : left=right := by
 apply heap_ext
 intro R r
 by_cases old : r.id<H.length
 · have typed : H[r.id]?=some R := by
     have actual := r.get?
     obtain ⟨suffix,rfl⟩ := e
     simpa only [List.getElem?_append_left old] using actual
   let prior : HRef H R := ⟨r.id,typed⟩
   have same : prior.wk e=r := by cases r;rfl
   rw [←same,leftKeeps prior,rightKeeps prior]
 · exact newSame r (by omega)

theorem default_unique {H H' : HTy} (initialHeap : Heap H) (e : H <+: H') (left right : Heap H')
 (leftKeeps : Heap.Keeps e initialHeap left) (rightKeeps : Heap.Keeps e initialHeap right)
 (leftDefaults : Defaults H.length left) (rightDefaults : Defaults H.length right) : left=right := by
 apply prefix_unique initialHeap e left right leftKeeps rightKeeps
 intro R r fresh
 obtain ⟨kind,first⟩ := leftDefaults r fresh
 obtain ⟨otherKind,second⟩ := rightDefaults r fresh
 cases kind
 exact (eq_of_heq first).trans (eq_of_heq second).symm

/-- Exact extension typing follows from the actual prefix, length and types of
all newly typed references. -/
theorem typing_shape {H H' : HTy} (e : H <+: H') (heap : Heap H') (count : Nat)
 (size : H'.length=H.length+count) (defaults : Defaults H.length heap) :
 H'=H++List.replicate count (.array (.prim .bool)) := by
 obtain ⟨suffix,rfl⟩ := e
 have length : suffix.length=count := by
   simp only [List.length_append] at size
   omega
 have same : suffix=List.replicate count (.array (.prim .bool)) := by
   apply List.ext_getElem?
   intro i
   by_cases small : i<suffix.length
   · have lookup : suffix[i]?=some suffix[i] := List.getElem?_eq_some_iff.mpr ⟨small,rfl⟩
     let r : HRef (H++suffix) suffix[i] := ⟨H.length+i,by
       rw [List.getElem?_append_right (by omega)]
       simpa only [Nat.add_sub_cancel_left] using lookup⟩
     have kind := (defaults r (by change H.length≤H.length+i;omega)).1
     rw [List.getElem?_replicate_of_lt (show i<count by omega),lookup]
     exact congrArg some kind
   · rw [List.getElem?_eq_none (by omega),List.getElem?_replicate,if_neg (show ¬i<count by omega)]
 exact congrArg (H++·) same

/-- Full dependent heap identity, without assuming equal output typings. -/
theorem profiles_heq {H H₁ H₂ : HTy} (initialHeap : Heap H) (e₁ : H <+: H₁) (e₂ : H <+: H₂)
 (left : Heap H₁) (right : Heap H₂) (count : Nat)
 (leftSize : H₁.length=H.length+count) (rightSize : H₂.length=H.length+count)
 (leftKeeps : Heap.Keeps e₁ initialHeap left) (rightKeeps : Heap.Keeps e₂ initialHeap right)
 (leftDefaults : Defaults H.length left) (rightDefaults : Defaults H.length right) :
 H₁=H₂ ∧ HEq left right := by
 have same := (typing_shape e₁ left count leftSize leftDefaults).trans
   (typing_shape e₂ right count rightSize rightDefaults).symm
 cases same
 exact ⟨rfl,heq_of_eq (default_unique initialHeap e₁ left right leftKeeps rightKeeps leftDefaults rightDefaults)⟩

/-- A real default allocation, followed by a preserving extension whose later
objects have the required contents, supplies the complete new-object profile. -/
theorem prepend_defaults {H H' : HTy} (heap : Heap H)
 (e : H++[.array (.prim .bool)] <+: H') (after : Heap H')
 (kept : Heap.Keeps e (heap.alloc (defaultArray .bool AllocatingScalarSource.size)).1 after)
 (tail : Defaults (H.length+1) after) : Defaults H.length after := by
 intro R r fresh
 by_cases first : r.id=H.length
 · let allocated := heap.alloc (defaultArray .bool AllocatingScalarSource.size)
   let ref := allocated.2.wk e
   have sameId : r.id=ref.id := first
   obtain ⟨kind,sameRef⟩ := HRef.heq_of_id r ref sameId
   cases kind
   have same : r=ref := eq_of_heq sameRef
   subst r
   refine ⟨rfl,?_⟩
   apply heq_of_eq
   change after.get (allocated.2.wk e)=_
   rw [kept allocated.2]
   change MObj.wk e (.array (.prim .bool)) ((heap.alloc (defaultArray .bool AllocatingScalarSource.size)).1.get
     (heap.alloc (defaultArray .bool AllocatingScalarSource.size)).2)=_
   rw [Heap.get_alloc_self]
   simp only [MObj.wk,defaultArray,List.map_replicate,MVal.wk]
 · exact tail r (by omega)

end Solidity.Backend.InternalFlow.RuntimeFrame.TypedHeapExtensionality
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.TypedHeapExtensionality.default_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.TypedHeapExtensionality.default_unique
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.TypedHeapExtensionality.prepend_defaults' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.TypedHeapExtensionality.prepend_defaults

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.TypedHeapExtensionality.profiles_heq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.TypedHeapExtensionality.profiles_heq

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.TypedHeapExtensionality.objects_ext' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.TypedHeapExtensionality.objects_ext

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.TypedHeapExtensionality.heap_ext' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.TypedHeapExtensionality.heap_ext

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.TypedHeapExtensionality.of_inventory' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.TypedHeapExtensionality.of_inventory

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.TypedHeapExtensionality.prefix_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.TypedHeapExtensionality.prefix_unique

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.TypedHeapExtensionality.typing_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.TypedHeapExtensionality.typing_shape
