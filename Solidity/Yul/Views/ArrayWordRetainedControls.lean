import Solidity.Yul.Views.ArrayWordRetained
import Solidity.Source.Semantics

/-! A real two-element allocation is shrunk by an actual typed heapPut, then a
member write retains the ORIGINAL allocation/capacity lineage. Dormant tail word
9 and an unknown byte survive; these helpers do not prove high-level reachability. -/
namespace Solidity.Yul.Views.ArrayWordRetained.Controls
open ArrayWordStore

def E : Source.Env := ⟨[]⟩
def F : Source.Fr := {this:=1,sender:=2,value:=0,static:=true,contract:="RetainedWord",cd:=[]}
def empty : Source.EMState E [] := (.nil,Source.St.init E)
def originalWords (i : Fin 2) : Roadmap.Word := if i.val=0 then 7 else 9
def originalData := dynamicUintData E.layout 2 originalWords
def origin := objectAllocatedState empty originalData
def allocated : Placement origin.2.heap := ComputedPlacement.build _ rfl (by decide)
def words : Fin 1 → Roadmap.Word := fun _ => 7
def old : Fin 1 → Source.Val E.layout (.int Source.IntTy.u256) := fun i => uintValueOfWord E.layout (words i)
def shortData := dynamicUintData E.layout 1 words
def current := withSourceHeap origin (origin.2.heap.write 0 shortData (by rfl))
def p : Placement current.2.heap := retainedWritePlacement allocated allocated (retainInitial _ _) 0 shortData
  (by rfl) (.array true 1) (.array _ _ _) (by decide)
def prior : RetainedAllocation allocated p := retainWritten allocated allocated (retainInitial _ _) 0 shortData
  (by rfl) (.array true 1) (.array _ _ _) (by decide)

theorem actual_shrink : (Source.heapPut (E:=E) (Γ:=[]) 0 ⟨_,shortData⟩).run origin=(.ok (),current) := rfl

def seed : ByteView := mstore (mstore (fun i=>if i=319 then 170 else 0) 192 9) 64 allocated.free
def memory := encodeMixedHeap p (generatedHeapEntries p) seed
def patch := mstore memory 160 42
def values := replace old ⟨0,by decide⟩ (uintValueOfWord E.layout 42)
def after := withSourceHeap current (current.2.heap.write 0
  (memberArrayData E.layout (.int Source.IntTy.u256) none 1 (fun _ e=>nomatch e) values) (by rfl))
def q := memberArrayWrittenPlacement current.2.heap p 0 (.int Source.IntTy.u256) none 1
  (fun _ e=>nomatch e) old values rfl
def nextHistory : RetainedAllocation allocated q :=
  history current.2.heap allocated p prior 0 _ none 1 (fun _ e=>nomatch e) old values rfl

theorem current_safe : Source.MemOK E current.2.heap.ty current := by
  have start : Source.MemOK E empty.2.heap.ty empty :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have original := (objectAllocRef_MemOK empty.2.heap.ty empty originalData rfl trivial
    (fun _ => ⟨_,rfl⟩) (.array (fun _ => .val trivial)) start).1
  have smaller := memberArrayHeapPut_MemOK E empty.2.heap.ty origin allocated 0 (.int Source.IntTy.u256) none 1
    (fun _ e=>nomatch e) old words (fun i => .scalar _ _ (uintValueOfWord_word _ _)) original
  change Source.MemOK E empty.2.heap.ty ((Source.heapPut (E:=E) (Γ:=[]) 0 ⟨_,shortData⟩).run origin).2 at smaller
  rw [actual_shrink] at smaller
  exact smaller.self

theorem retained_whole :
    (Source.writeLoc F 0 (.mem 0 0) (uintValueOfWord E.layout 42)).run current=(.ok (),after) ∧
    RetainedAllocation allocated q ∧ encodeMixedHeap q (generatedHeapEntries q) patch=patch ∧
    enumeratedMemoryWriteback after allocated q nextHistory patch=.ok (some (.ok (),after)) := by
  have support : ∀ a τ d,current.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ := by
    intro a τ d found
    by_cases same : a=0
    · subst a
      cases found
      exact Or.inl (Or.inr (Or.inl rfl))
    · have missing := current.2.heap.bounded a (by change 1≤a;omega)
      change current.2.heap.cells a=some ⟨τ,d⟩ at found
      rw [missing] at found
      cases found
  have reads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id) :=
    encodeMixedHeap_reads p _ (prepareHeapInventory_ok p _ rfl).2.2 seed
  have reserved : ReservedOK seed p.free := by
    constructor
    · exact congrArg Fin.val (mload_mstore _ 64 allocated.free)
    · intro i
      rw [seed,mstore_outside _ _ _ _ (by have small:=i.isLt;omega),
        mstore_outside _ _ _ _ (by have small:=i.isLt;omega)]
      have small:=i.isLt
      rw [if_neg (by omega)]
  exact whole current.2.heap.ty current allocated p prior current_safe support F 0 0 (.int Source.IntTy.u256) none 1
    (fun _ e=>nomatch e) old words (fun i => .scalar _ _ (uintValueOfWord_word _ _)) rfl ⟨0,by decide⟩
    (uintValueOfWord E.layout 42) 42 (.scalar _ _ (uintValueOfWord_word _ _)) memory reads
    (encodeMixedHeap_reserved p _ seed reserved)

theorem capacity_retained : (allocated.shape 0).size=96 ∧ (p.shape 0).size=64 ∧
    (q.shape 0).size=64 ∧ q.free.val=224 ∧ q.address=allocated.address :=
  ⟨rfl,rfl,rfl,rfl,nextHistory.addresses⟩
theorem beyond_current (address : Nat) (outside : 192≤address) : memory address=seed address := by
  rw [memory,encodeMixedHeap_residual p _ seed address]
  intro e member
  have indices : (generatedHeapEntries p).map MixedHeapEntry.id=[0] := rfl
  have selected : e.id=0 := List.mem_singleton.mp (indices ▸ (List.mem_map.mpr ⟨e,member,rfl⟩))
  have fit := e.image.fits p e.id e.found
  have addressEq : p.address e.id=128 := by rw [selected];rfl
  have shape : p.shape e.id=.array true 1 := by rw [selected];rfl
  rw [shape] at fit
  change e.image.span≤64 at fit
  exact Or.inr (by rw [addressEq];omega)

theorem dormant_tail : mload patch 192=9 ∧ patch 319=170 := by
  have old : mload patch 192=mload seed 192 := mload_congr patch seed 192 (fun byte => by
    rw [patch,mstore_outside _ _ _ _ (by have small:=byte.isLt;omega)]
    exact beyond_current _ (by omega))
  constructor
  · rw [old]
    change mload (mstore (mstore (fun i=>if i=319 then 170 else 0) 192 9) 64 allocated.free) 192=9
    rw [mload_congr _ (mstore (fun i=>if i=319 then 170 else 0) 192 9) 192
      (fun byte => mstore_outside _ _ _ _ (by have small:=byte.isLt;omega)),mload_mstore]
  · rw [patch,mstore_outside _ _ _ _ (by decide),beyond_current 319 (by decide),seed,
      mstore_outside _ _ _ _ (by decide),mstore_outside _ _ _ _ (by decide)]
    rfl

theorem cannot_repack_current : ComputedPlacement.position current.2.heap current.2.heap.next≠p.free.val := by decide
theorem actual_reads :
    (Source.readLoc (E:=E) F (.mem (τ:=.int Source.IntTy.u256) 0 0)).run after=
      (.ok (uintValueOfWord E.layout 42),after) ∧
    (Source.readLoc (E:=E) F (.mem (τ:=.int Source.IntTy.u256) 0 1)).run after=
      (.error (.revert (Source.panicData .index)),after) := ⟨rfl,rfl⟩
end Solidity.Yul.Views.ArrayWordRetained.Controls
