import Solidity.Backend.MemoryOps.PhysicalReferenceArray

/-! G32/G34 a primitive child mutation frames an existing reference parent.
Intrinsic parent/child object separation follows from their actual types;
physical slot separation is a separate explicit local requirement. No global
address injection, constructor, byte-load evaluator or Source graph is added. -/
namespace Solidity.Backend.MemoryOps.Physical

/-- The INITIAL parent relation survives actual primitive set/write functions.
This is an ownership/frame producer, not a claim that an arbitrary input index
passes the primitive child's bounds check. The checked execution is composed
separately from the existing primitive write certificate. -/
theorem ReferenceArrayAt.set_primitive {H : HTy} {R : RefTy} {p : PrimTy}
    {hp : Heap H} {root : HRef H (.array (.ref R))}
    {base : Nat → Fin Evm.W} {m : Evm.Machine} {bytes : Environment.Memory}
    (h : ReferenceArrayAt hp root base m bytes)
    (child : HRef H (.array (.prim p))) (i : Nat) (v : p.Denote)
    (w : Fin Evm.W)
    (headerNe : (base root.id).val≠(base child.id).val+1+i)
    (slotsNe : ∀ c, ReferenceSlots hp root base c → c≠(base child.id).val+1+i) :
    ReferenceArrayAt (hp.set child (MObj.setElem .dyn (hp.get child) i v)) root base
      (Evm.Memory.writeMachine m ((base child.id).val+1+i) (.val w))
      (Environment.writeBytes bytes (32*((base child.id).val+1+i))
        (Semantics.wordBytes w.val)) := by
  have objectNe : child.id≠root.id := by
    intro he
    cases (HRef.heq_of_id child root he).1
  have getRoot : (hp.set child (MObj.setElem .dyn (hp.get child) i v)).get root=hp.get root :=
    Heap.get_set_ne hp child root objectNe _
  have lenRoot : (hp.set child (MObj.setElem .dyn (hp.get child) i v)).len root .dyn=
      hp.len root .dyn := by
    simp only [Heap.len,getRoot]
  refine ⟨?_,h.headerFits,cell_write_other m bytes _ _ w headerNe h.header,?_⟩
  · constructor
    · simpa only [lenRoot] using h.word.space
    · change Evm.upd m.mem _ _ _= _
      rw [Evm.upd_other _ _ headerNe,lenRoot]
      exact h.word.length
    · intro j q hq
      rw [getRoot] at hq
      have hj : j<hp.len root .dyn := (List.getElem?_eq_some_iff.mp hq).1
      change Evm.upd m.mem _ _ _= _
      rw [Evm.upd_other _ _ (slotsNe _ ⟨j,hj,rfl⟩)]
      exact h.word.elements j q hq
  · constructor
    · intro c hc
      obtain ⟨j,hj,he⟩ := hc
      rw [lenRoot] at hj
      exact h.pointers.fits c ⟨j,hj,he⟩
    · intro c hc
      obtain ⟨j,hj,he⟩ := hc
      rw [lenRoot] at hj
      have hc : ReferenceSlots hp root base c := ⟨j,hj,he⟩
      have hne : c≠(base child.id).val+1+i := slotsNe c hc
      obtain ⟨b,hw,hfit,hbytes⟩ := h.pointers.cells c hc
      refine ⟨b,(Evm.upd_other _ _ hne).trans hw,hfit,?_⟩
      rw [readMemory_write_frame]
      · exact hbytes
      · rw [word_bytes_length]
        omega

/-- A concrete unsafe overlap: storing numeric8 into a logical-pointer cell
encodes8, whereas that cell's pointer value8 requires physical address256.
This refutes unconditional parent preservation, not universal necessity of the
sufficient separation premise (for example zero encodings may coincide). -/
theorem numeric_eight_breaks_pointer (m : Evm.Machine) (bytes : Environment.Memory)
    (cell : Nat) :
    ¬ PointerCellAt (Evm.Memory.writeMachine m cell (.val (Evm.wmod 8)))
      (Environment.writeBytes bytes (32*cell) (Semantics.wordBytes 8)) cell := by
  intro h
  obtain ⟨b,hw,_fit,hbytes⟩ := h
  have he : b=Evm.wmod 8 := Evm.Word.val.inj (hw.symm.trans (Evm.upd_same _ _ _))
  subst b
  have hread : Environment.readMemory
      (Environment.writeBytes bytes (32*cell) (Semantics.wordBytes 8)) (32*cell) 32=
      Semantics.wordBytes 8 := by
    simpa only [word_bytes_length] using Environment.read_written (Semantics.wordBytes 8) (32*cell) bytes
  apply pointer_eight_not_numeric
  exact hread.symm.trans hbytes

/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceArrayAt.set_primitive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ReferenceArrayAt.set_primitive
/-- info: 'Solidity.Backend.MemoryOps.Physical.numeric_eight_breaks_pointer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms numeric_eight_breaks_pointer
end Solidity.Backend.MemoryOps.Physical
