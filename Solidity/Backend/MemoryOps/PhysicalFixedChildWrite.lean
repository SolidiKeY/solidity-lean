import Solidity.Backend.MemoryOps.PhysicalReferenceChild
import Solidity.Backend.MemoryOps.SourceUintFixedWrite

/-! Headerless fixed uint child writes with an existing represented reference
parent. Source typed cells, intrinsic updates and terminal word/byte stores
are paired, not silently identified as a compiled pointer/index byte program.
No constructor, byte-load interpreter, global address injection or Source
transaction/allocator certificate is introduced. -/
namespace Solidity.Backend.MemoryOps.Physical

theorem ReferenceArrayAt.write_fixed_uint {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy} {n : Nat}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H}
    {root : HRef H (.array (.ref R))} {child : HRef H (.fixed (.prim .uint) n)}
    {base : Nat → Fin Evm.W} {m : Evm.Machine} {bytes : Environment.Memory}
    (parent : ReferenceArrayAt hp root base m bytes)
    (source : SourceUintFixedAt y address hp child) (F : Source.Fr) (fuel : Nat)
    (i w : Fin Evm.W) (hi : i.val<n)
    (fits : 32*((base child.id).val+i.val)+32≤2^256)
    (headerNe : (base root.id).val≠(base child.id).val+i.val)
    (slotsNe : ∀ c,ReferenceSlots hp root base c → c≠(base child.id).val+i.val) :
    let cell := (base child.id).val+i.val
    let next := Evm.Memory.writeMachine m cell (.val w)
    let byteNext := Environment.writeBytes bytes (32*cell) (Semantics.wordBytes w.val)
    ∃ (out : Heap H) (z : Source.EMState E Γ) (logical offset : Fin Evm.W),
      logical.val=cell ∧ offset.val=32*cell ∧
      hp.writeAddr (.index child .fixed (Evm.Memory.indexValue i)) (Evm.Memory.indexValue w)=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) F fuel (.mem address i.val)
        (sourceUint (Evm.Memory.indexValue w))).run y=(.ok (),z) ∧
      Evm.run [.mstoreAt] ((m.push (.val w)).push (.val logical))=.ok next 0 ∧
      (∀ tail : List Environment.Word,Environment.cryptoStep (.op .MSTORE)
        ⟨lenU offset.val offset.isLt::lenU w.val w.isLt::tail,bytes⟩=
          some ⟨tail,byteNext⟩) ∧
      ReferenceArrayAt out root base next byteNext ∧ SourceUintFixedAt z address out child ∧
      z.1=y.1 ∧ (∀ {Q : RefTy} (q : HRef H Q),child.id≠q.id → out.get q=hp.get q) ∧
      (∀ a,a≠address → z.2.heap.get a=y.2.heap.get a) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals ∧
      (∀ a,a<32*cell ∨ 32*cell+32≤a → byteNext a=bytes a) := by
  first
  | solve | simp only [] | omega
  | dsimp only
    obtain ⟨out,z,typed,run,reached⟩ := source.write_addr F fuel (Evm.Memory.indexValue i) (Evm.Memory.indexValue w) hi
    have canonical : hp.writeAddr (.index child .fixed (Evm.Memory.indexValue i)) (Evm.Memory.indexValue w)=
        some (hp.set child (MObj.setElem .fixed (hp.get child) i.val (Evm.Memory.indexValue w))) := by
      have length : (MObj.elems .fixed (hp.get child)).length=n := by
        rw [MObj.elems_fixed];exact (hp.get child).2
      simp only [Heap.writeAddr,Heap.setIndex,Evm.Memory.indexValue,Int.toNat_natCast,length,hi,↓reduceIte]
    have outEq := Option.some.inj (typed.symm.trans canonical)
    have framed := parent.set_fixed_primitive child i.val (Evm.Memory.indexValue w) w headerNe slotsNe
    rw [←outEq] at framed
    obtain ⟨locals,objects,addresses,world,events,logs,fnLocals⟩ :=
      source.write_frames F fuel (Evm.Memory.indexValue i) (Evm.Memory.indexValue w) hi typed run
    have bound : (base child.id).val+i.val<Evm.W := by change (base child.id).val+i.val<2^256;omega
    refine ⟨out,z,⟨(base child.id).val+i.val,bound⟩,⟨32*((base child.id).val+i.val),by change 32*((base child.id).val+i.val)<2^256;omega⟩,rfl,rfl,typed,run,word_mstore m _ w,?_,
      framed,reached,locals,objects,addresses,world,events,logs,fnLocals,?_⟩
    · intro tail
      exact byte_mstore bytes tail ⟨(base child.id).val+i.val,bound⟩ w fits
    · intro a ha
      apply Environment.writeBytes_frame
      simpa only [Environment.wordBytes_length] using ha

/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceArrayAt.write_fixed_uint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ReferenceArrayAt.write_fixed_uint
end Solidity.Backend.MemoryOps.Physical
