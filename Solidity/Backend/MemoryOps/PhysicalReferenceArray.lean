import Solidity.Backend.MemoryOps.PhysicalPointerFrame
import Solidity.Evm.MemoryRefArray

/-! G32 local typed reference-array layout. Existing RefArrayRepr fixes the
logical child pointers; PointerFrame fixes their scaled physical byte images.
This is a single dynamic parent, not a recursively closed heap graph. Shared
children are allowed. Physical descendant liveness requires separate ownership.
No Source/EVM producer is replaced or edited. -/
namespace Solidity.Backend.MemoryOps.Physical

/-- The actual live pointer slots of this typed dynamic parent. -/
def ReferenceSlots {H : HTy} {R : RefTy} (hp : Heap H)
    (root : HRef H (.array (.ref R))) (base : Nat → Fin Evm.W) (cell : Nat) : Prop :=
  ∃ i, i<hp.len root .dyn ∧ cell=(base root.id).val+1+i

/-- INITIAL typed parent contents are connected to both memory models. Header
and element encodings remain different. No global address injectivity, unique
child ownership or recursively represented-child postcondition is assumed. -/
structure ReferenceArrayAt {H : HTy} {R : RefTy} (hp : Heap H)
    (root : HRef H (.array (.ref R))) (base : Nat → Fin Evm.W)
    (m : Evm.Machine) (bytes : Environment.Memory) : Prop where
  word : Evm.Memory.RefArrayRepr hp root base m
  headerFits : 32*(base root.id).val+32≤2^256
  header : CellAt m bytes (base root.id).val
  pointers : PointerFrame m bytes (ReferenceSlots hp root base)

/-- Exact byte observation for an actually selected INITIAL typed child.
The pointer value is identified from the published word relation, rather than
assuming agreement between the existential physical pointer and this child. -/
theorem ReferenceArrayAt.child_bytes {H : HTy} {R : RefTy} {hp : Heap H}
    {root : HRef H (.array (.ref R))} {base : Nat → Fin Evm.W}
    {m : Evm.Machine} {bytes : Environment.Memory}
    (h : ReferenceArrayAt hp root base m bytes) (i : Nat) (child : HRef H R)
    (hchild : (MObj.elems .dyn (hp.get root))[i]?=some child) :
    32*(base child.id).val<2^256 ∧
      Environment.readMemory bytes (32*((base root.id).val+1+i)) 32=
        Semantics.wordBytes (32*(base child.id).val) := by
  have hi : i<hp.len root .dyn := (List.getElem?_eq_some_iff.mp hchild).1
  obtain ⟨b,hw,hfit,hbytes⟩ := h.pointers.cells _ ⟨i,hi,rfl⟩
  have he : b=base child.id := Evm.Word.val.inj (hw.symm.trans (h.word.elements i child hchild))
  subst b
  exact ⟨hfit,hbytes⟩

/-- Updating the real typed parent and its actual memory cell retains the
header and all unaffected pointer bytes. Repeated child identities are allowed;
no physical descendant ownership is inferred from typed-object framing. -/
theorem ReferenceArrayAt.set {H : HTy} {R : RefTy} {hp : Heap H}
    {root : HRef H (.array (.ref R))} {base : Nat → Fin Evm.W}
    {m : Evm.Machine} {bytes : Environment.Memory}
    (h : ReferenceArrayAt hp root base m bytes) (i : Nat)
    (hi : i<hp.len root .dyn) (child : HRef H R)
    (childFits : 32*(base child.id).val<2^256) :
    ReferenceArrayAt (hp.set root (MObj.setElem .dyn (hp.get root) i child)) root base
      (Evm.Memory.writeMachine m ((base root.id).val+1+i) (.val (base child.id)))
      (Environment.writeBytes bytes (32*((base root.id).val+1+i))
        (Semantics.wordBytes (32*(base child.id).val))) := by
  have cellFits : 32*((base root.id).val+1+i)+32≤2^256 :=
    h.pointers.fits _ ⟨i,hi,rfl⟩
  have hlen : (hp.set root (MObj.setElem .dyn (hp.get root) i child)).len root .dyn=
      hp.len root .dyn := by
    simp only [Heap.len,Heap.get_set_same,MObj.elems_setElem,List.length_set]
  have pointers := h.pointers.write ((base root.id).val+1+i) (base child.id) cellFits childFits
  refine ⟨h.word.set i hi child,h.headerFits,?_,?_⟩
  · obtain ⟨value,hw,hb⟩ := h.header
    refine ⟨value,(Evm.upd_other _ _ (by omega)).trans hw,?_⟩
    rw [readMemory_write_frame]
    · exact hb
    · rw [word_bytes_length]
      omega
  · constructor
    · intro cell hc
      obtain ⟨j,hj,he⟩ := hc
      rw [hlen] at hj
      exact pointers.fits cell (.inl ⟨j,hj,he⟩)
    · intro cell hc
      obtain ⟨j,hj,he⟩ := hc
      rw [hlen] at hj
      exact pointers.cells cell (.inl ⟨j,hj,he⟩)

/-- Complete existing typed/word/byte store execution with the reached typed
parent relation. There is no assumed successful suffix or postrelation. -/
theorem ReferenceArrayAt.store {H : HTy} {R : RefTy} {hp : Heap H}
    {root : HRef H (.array (.ref R))} {base : Nat → Fin Evm.W}
    {m : Evm.Machine} {bytes : Environment.Memory}
    (h : ReferenceArrayAt hp root base m bytes) (i : Fin Evm.W)
    (hi : i.val<hp.len root .dyn) (child : HRef H R)
    (childFits : 32*(base child.id).val<2^256) :
    let cell := (base root.id).val+1+i.val
    let next := Evm.Memory.writeMachine m cell (.val (base child.id))
    let byteNext := Environment.writeBytes bytes (32*cell)
      (Semantics.wordBytes (32*(base child.id).val))
    ∃ out : Heap H,
      hp.writeAddr (.index root .dyn (Evm.Memory.indexValue i)) child=some out ∧
      Evm.run (Evm.Memory.writeArrayCode (base root.id))
        ((m.push (.val (base child.id))).push (.val i))=.ok next 0 ∧
      (∃ offset : Fin Evm.W,offset.val=32*cell ∧ ∀ tail : List Environment.Word,
        Environment.cryptoStep (.op .MSTORE)
          ⟨lenU offset.val offset.isLt::lenU (32*(base child.id).val) childFits::tail,bytes⟩=
            some ⟨tail,byteNext⟩) ∧
      ReferenceArrayAt out root base next byteNext ∧
      (∀ {Q : RefTy} (q : HRef H Q),root.id≠q.id → out.get q=hp.get q) := by
  have cellFits : 32*((base root.id).val+1+i.val)+32≤2^256 :=
    h.pointers.fits _ ⟨i.val,hi,rfl⟩
  obtain ⟨out,ht,hw,hb,_read,_exterior,hframe⟩ :=
    reference_store hp root child base m bytes i hi h.word.length cellFits childFits
  have ht' : hp.writeAddr (.index root .dyn (Evm.Memory.indexValue i)) child=
      some (hp.set root (MObj.setElem .dyn (hp.get root) i.val child)) := by
    change (if i.val<hp.len root .dyn then some _ else none)=_
    simp only [hi,↓reduceIte,Evm.Memory.indexValue,Int.toNat_natCast]
  have hout : out=hp.set root (MObj.setElem .dyn (hp.get root) i.val child) :=
    Option.some.inj (ht.symm.trans ht')
  subst out
  exact ⟨_,ht,hw,hb,h.set i.val hi child childFits,hframe⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceArrayAt.child_bytes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms ReferenceArrayAt.child_bytes
/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceArrayAt.set' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ReferenceArrayAt.set
/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceArrayAt.store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ReferenceArrayAt.store
end Solidity.Backend.MemoryOps.Physical

