import Solidity.Yul.Views.AllocationPointer

/-! A real raw word store corresponds to one actual typed array-member write.
Canonical scalar/pointer interpretation is the existing MemoryElement codec.
Array reconstruction is whole-map equality with the same complementary bytes,
not a new whole-heap or arbitrary dirty-owned representation theorem. -/
namespace Solidity.Yul.Views.ArrayWordStore

def replace {α : Type} {n : Nat} (old : Fin n → α) (index : Fin n) (value : α) : Fin n → α :=
  fun j => if j.val=index.val then value else old j

theorem word_read (memory : ByteView) (base : Nat) {n : Nat} (index j : Fin n) (word : Roadmap.Word) :
    mload (mstore memory (base+index.val*32) word) (base+j.val*32)=
      if j.val=index.val then word else mload memory (base+j.val*32) := by
  first | (simp only;done) | decide | omega | rfl | skip
  by_cases same : j.val=index.val
  · rw [if_pos same,same,mload_mstore]
  · rw [if_neg same]
    exact mload_congr _ memory _ (fun byte => mstore_outside _ _ _ _ (by have small:=byte.isLt;omega))

theorem header (k : Option Nat) (n : Nat) (memory : ByteView) (base : Nat)
    (index : Fin n) (word : Roadmap.Word) (old : arrayLengthChoice k memory base=n) :
    arrayLengthChoice k (mstore memory (base+arrayPayloadOffset k+index.val*32) word) base=n := by
  first | (simp only;done) | decide | omega | rfl | skip
  cases k with
  | some fixed => exact old
  | none =>
    change (mload _ base).val=n
    rw [mload_congr _ memory base (fun byte => mstore_outside _ _ _ _ (by
      change ¬(base+32+index.val*32≤base+byte.val ∧ base+byte.val<base+32+index.val*32+32)
      have small:=byte.isLt
      omega))]
    exact old

theorem source {E Γ} (s : Source.EMState E Γ) (F : Source.Fr) (horizon root : Nat)
    (τ : Source.STy) (k : Option Nat) (n : Nat) (hl : ∀ x,k=some x → x=n)
    (old : Fin n → Source.Val E.layout τ)
    (found : s.2.heap.get root=some ⟨_,memberArrayData E.layout τ k n hl old⟩)
    (index : Fin n) (value : Source.Val E.layout τ) :
    (Source.writeLoc F horizon (.mem root index.val) value).run s=
      (Source.heapPut root ⟨_,memberArrayData E.layout τ k n hl (replace old index value)⟩).run s := by
  first | (simp only;done) | decide | omega | rfl | skip
  change (Source.memSet root index.val value).run s=_
  rw [Source.memSet,Source.Hoare.run_bind,heapObj_known s root _ found]
  dsimp only [memberArrayData]
  rw [dif_pos index.isLt,dif_pos rfl]
  have dataEq : (Source.Data.array (l:=.memory) n hl
      (fun j => if j.val=index.val then Source.Data.val value else Source.Data.val (old j)))=
      memberArrayData E.layout τ k n hl (replace old index value) := by
    apply congrArg (fun elements : Fin n → Source.Data E.layout τ => Source.Data.array (l:=.memory) n hl elements)
    funext j
    dsimp only [replace]
    split <;> rfl
  rw [dataEq]
  rfl

theorem writeback {E Γ} (s : Source.EMState E Γ) (p : Placement s.2.heap) (es : List (MixedHeapEntry p))
    (coverage : CoversMixedHeap es) (F : Source.Fr) (horizon root : Nat) (τ : Source.STy)
    (supported : OrdinaryMemberType τ) (k : Option Nat) (n : Nat) (hl : ∀ x,k=some x → x=n)
    (old : Fin n → Source.Val E.layout τ) (words : Fin n → Roadmap.Word)
    (encoded : ∀ j,MemoryElement p (old j) (words j))
    (found : s.2.heap.get root=some ⟨_,memberArrayData E.layout τ k n hl old⟩)
    (memory : ByteView) (length : arrayLengthChoice k memory (p.address root)=n)
    (reads : ∀ j,mload memory (p.address root+arrayPayloadOffset k+j.val*32)=words j)
    (index : Fin n) (value : Source.Val E.layout τ) (word : Roadmap.Word) (newEncoded : MemoryElement p value word) :
    memberArrayStateWriteback s p es root τ k n hl
      (mstore memory (p.address root+arrayPayloadOffset k+index.val*32) word)=
      some ((Source.writeLoc F horizon (.mem root index.val) value).run s) := by
  first | (simp only;done) | decide | omega | rfl | skip
  have nextEncoded : ∀ j,MemoryElement p (replace old index value j) (replace words index word j) := by
    intro j
    unfold replace
    split
    · exact newEncoded
    · exact encoded j
  have nextReads : ∀ j,mload (mstore memory (p.address root+arrayPayloadOffset k+index.val*32) word)
      (p.address root+arrayPayloadOffset k+j.val*32)=replace words index word j := by
    intro j
    rw [word_read,reads j]
    rfl
  unfold memberArrayStateWriteback
  rw [if_pos (header k n memory (p.address root) index word length),
    decodeArrayMembers_reads p es coverage τ supported n (replace old index value) (replace words index word)
      nextEncoded _ _ nextReads]
  simp only [Option.map_some]
  rw [source s F horizon root τ k n hl old found index value]

theorem reencode (k : Option Nat) (n : Nat) (bound : n<2^256)
    (memory : ByteView) (base : Nat) (words : Fin n → Roadmap.Word)
    (length : arrayLengthChoice k memory base=n)
    (reads : ∀ j,mload memory (base+arrayPayloadOffset k+j.val*32)=words j)
    (index : Fin n) (word : Roadmap.Word) :
    let patched := mstore memory (base+arrayPayloadOffset k+index.val*32) word
    memberArrayView k n bound (replace words index word) patched base=patched := by
  first | (simp only;done) | decide | omega | rfl | skip
  have observed : (fun j => mload (mstore memory (base+arrayPayloadOffset k+index.val*32) word)
      (base+arrayPayloadOffset k+j.val*32))=replace words index word := by
    funext j
    rw [word_read,reads j]
    rfl
  rw [←observed]
  exact memberArrayView_reencode k n bound _ base (header k n memory base index word length)
end Solidity.Yul.Views.ArrayWordStore
