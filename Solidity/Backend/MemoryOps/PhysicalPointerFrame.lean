import Solidity.Backend.MemoryOps.PhysicalReferenceStore

/-! G32 pointer cells use logical word addresses and scaled physical byte
addresses. This local initial/post footprint does not represent a recursive
heap graph, prove physical child liveness, or assert address injectivity.
Numeric headers/data continue to use the separate existing WordFrame. -/
namespace Solidity.Backend.MemoryOps.Physical

/-- An existing logical pointer and its complete byte-address serialization. -/
def PointerCellAt (m : Evm.Machine) (bytes : Environment.Memory) (cell : Nat) : Prop :=
  ∃ base : Fin Evm.W, m.mem cell=.val base ∧ 32*base.val<2^256 ∧
    Environment.readMemory bytes (32*cell) 32=Semantics.wordBytes (32*base.val)

/-- A footprint of pointer cells, allowing repeated pointers and arbitrary
unrepresented bytes. Nonwrapping addresses and pointer values are explicit. -/
structure PointerFrame (m : Evm.Machine) (bytes : Environment.Memory)
    (live : Nat → Prop) : Prop where
  fits : ∀ cell, live cell → 32*cell+32≤2^256
  cells : ∀ cell, live cell → PointerCellAt m bytes cell

/-- Preservation derives the reached footprint from the INITIAL pointer
relation. The stored physical value is scaled, unlike a numeric word. -/
theorem PointerFrame.write {m : Evm.Machine} {bytes : Environment.Memory}
    {live : Nat → Prop} (h : PointerFrame m bytes live) (dst : Nat)
    (base : Fin Evm.W) (fits : 32*dst+32≤2^256)
    (pointerFits : 32*base.val<2^256) :
    PointerFrame (Evm.Memory.writeMachine m dst (.val base))
      (Environment.writeBytes bytes (32*dst) (Semantics.wordBytes (32*base.val)))
      (fun cell => live cell ∨ cell=dst) := by
  constructor
  · intro cell hc
    rcases hc with hc | rfl
    · exact h.fits cell hc
    · exact fits
  · intro cell hc
    by_cases he : cell=dst
    · subst cell
      refine ⟨base,Evm.upd_same _ _ _,pointerFits,?_⟩
      simpa only [word_bytes_length] using Environment.read_written
        (Semantics.wordBytes (32*base.val)) (32*dst) bytes
    · rcases hc with hc | hc
      · obtain ⟨old,hw,hfit,hb⟩ := h.cells cell hc
        refine ⟨old,(Evm.upd_other _ _ he).trans hw,hfit,?_⟩
        rw [readMemory_write_frame]
        · exact hb
        · rw [word_bytes_length]
          omega
      · exact (he hc).elim

/-- Numeric cells remain numeric when the selected pointer slot is outside
their footprint. No same-cell numeric/pointer encoding is silently equated. -/
theorem WordFrame.pointer_write {m : Evm.Machine} {bytes : Environment.Memory}
    {live : Nat → Prop} (h : WordFrame m bytes live) (dst : Nat)
    (base : Fin Evm.W) (separate : ∀ cell, live cell → cell≠dst) :
    WordFrame (Evm.Memory.writeMachine m dst (.val base))
      (Environment.writeBytes bytes (32*dst) (Semantics.wordBytes (32*base.val))) live := by
  refine ⟨h.fits,?_⟩
  intro cell hc
  obtain ⟨value,hw,hb⟩ := h.cells cell hc
  have he : cell≠dst := separate cell hc
  refine ⟨value,(Evm.upd_other _ _ he).trans hw,?_⟩
  rw [readMemory_write_frame]
  · exact hb
  · rw [word_bytes_length]
    omega

/-- The real typed/word/byte redirection preserves both INITIAL local
footprints. The two footprints may share children/pointer values; only numeric
cell locations must exclude the actually changed reference slot. This does not
establish a recursively closed graph or physical child liveness. -/
theorem reference_store_frames {H : HTy} {R : RefTy}
    (hp : Heap H) (root : HRef H (.array (.ref R))) (child : HRef H R)
    (base : Nat → Fin Evm.W) (m : Evm.Machine) (bytes : Environment.Memory)
    (i : Fin Evm.W) (hi : i.val<hp.len root .dyn)
    (header : m.mem (base root.id).val=.val (Evm.wmod (hp.len root .dyn)))
    (cellFits : 32*((base root.id).val+1+i.val)+32≤2^256)
    (childFits : 32*(base child.id).val<2^256)
    (pointerLive numericLive : Nat → Prop)
    (pointers : PointerFrame m bytes pointerLive)
    (numbers : WordFrame m bytes numericLive)
    (separate : ∀ cell, numericLive cell → cell≠(base root.id).val+1+i.val) :
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
      PointerFrame next byteNext (fun c => pointerLive c ∨ c=cell) ∧
      WordFrame next byteNext numericLive ∧
      (∀ {Q : RefTy} (q : HRef H Q),root.id≠q.id → out.get q=hp.get q) := by
  obtain ⟨out,ht,hw,hb,_read,_exterior,hframe⟩ :=
    reference_store hp root child base m bytes i hi header cellFits childFits
  exact ⟨out,ht,hw,hb,pointers.write _ _ cellFits childFits,
    numbers.pointer_write _ _ separate,hframe⟩

/-- Concrete regression: an unscaled word pointer cannot substitute for its
physical address even though the selected logical child is the same. -/
theorem pointer_eight_not_numeric : Semantics.wordBytes 8≠Semantics.wordBytes (32*8) := by
  decide

/-- Statement only; unproved target: establish a repeated-pointer footprint
at slots17/18, then redirect17 from logical1 to8. Every selected/retained word
and byte span is explicit; initial arbitrary exterior memory is not zeroed. -/
def PointerFrameAliasClientGoal : Prop :=
  ∀ (m : Evm.Machine) (bytes : Environment.Memory),
  let old := Evm.Memory.writeMachine
    (Evm.Memory.writeMachine m 18 (.val (Evm.wmod 1))) 17 (.val (Evm.wmod 1))
  let oldBytes := Environment.writeBytes
    (Environment.writeBytes bytes 576 (Semantics.wordBytes 32))
    544 (Semantics.wordBytes 32)
  let next := Evm.Memory.writeMachine old 17 (.val (Evm.wmod 8))
  let nextBytes := Environment.writeBytes oldBytes 544 (Semantics.wordBytes 256)
  PointerFrame old oldBytes (fun c => c=17 ∨ c=18) ∧
  PointerFrame next nextBytes (fun c => c=17 ∨ c=18) ∧
  [old.mem 17,old.mem 18,next.mem 17,next.mem 18]=
    [.val (Evm.wmod 1),.val (Evm.wmod 1),.val (Evm.wmod 8),.val (Evm.wmod 1)] ∧
  [Environment.readMemory oldBytes 544 32,Environment.readMemory oldBytes 576 32,
    Environment.readMemory nextBytes 544 32,Environment.readMemory nextBytes 576 32]=
    [Semantics.wordBytes 32,Semantics.wordBytes 32,
      Semantics.wordBytes 256,Semantics.wordBytes 32]

/-- info: 'Solidity.Backend.MemoryOps.Physical.pointer_eight_not_numeric' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms pointer_eight_not_numeric
/-- info: 'Solidity.Backend.MemoryOps.Physical.PointerFrame.write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PointerFrame.write
/-- info: 'Solidity.Backend.MemoryOps.Physical.WordFrame.pointer_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms WordFrame.pointer_write
/-- info: 'Solidity.Backend.MemoryOps.Physical.reference_store_frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reference_store_frames
end Solidity.Backend.MemoryOps.Physical

