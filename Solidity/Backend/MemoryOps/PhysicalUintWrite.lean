import Solidity.Backend.MemoryOps.PhysicalSourceUint
import Solidity.Backend.MemoryOps.SourceUintWrite

/-! Actual reached Source/intrinsic/word updates derive the physical postrelation.
Address scaling stays explicit; this is not emitted bytecode address relocation. -/
namespace Solidity.Backend.MemoryOps.Physical

theorem UintArrayAt.write_cell {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H}
    {r : HRef H (.array (.prim .uint))} {base : Fin Evm.W}
    {m : Evm.Machine} {bytes : Environment.Memory}
    (h : UintArrayAt y address hp r base m bytes) (F : Source.Fr) (fuel : Nat)
    (i w : Fin Evm.W) (hi : i.val<hp.len r .dyn) :
    let cell := base.val+1+i.val
    let next := Evm.Memory.writeMachine m cell (.val w)
    let byteNext := Environment.writeBytes bytes (32*cell) (Semantics.wordBytes w.val)
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      hp.writeAddr (.index r .dyn (Evm.Memory.indexValue i)) (Evm.Memory.indexValue w)=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) F fuel (.mem address i.val)
        (sourceUint (Evm.Memory.indexValue w))).run y=(.ok (),z) ∧
      Evm.run (Evm.Memory.writeArrayCode base) ((m.push (.val w)).push (.val i))=.ok next 0 ∧
      (∃ offset : Fin Evm.W,offset.val=32*cell ∧ ∀ tail : List Environment.Word,
        Environment.cryptoStep (.op .MSTORE)
          ⟨lenU offset.val offset.isLt::lenU w.val w.isLt::tail,bytes⟩=some ⟨tail,byteNext⟩) ∧
      UintArrayAt z address out r base next byteNext ∧
      z.1=y.1 ∧ z.2={y.2 with heap := z.2.heap} ∧
      (∀ b,b≠address → z.2.heap.get b=y.2.heap.get b) ∧
      (∀ {Q : RefTy} (q : HRef H Q),r.id≠q.id → out.get q=hp.get q) ∧
      (∀ k,k<32*cell ∨ 32*cell+32≤k → byteNext k=bytes k) := by
  dsimp only
  obtain ⟨out,z,ht,hs,hrep⟩ := h.source.write_addr F fuel
    (Evm.Memory.indexValue i) (Evm.Memory.indexValue w) hi
  have hout : out=hp.set r (MObj.setElem .dyn (hp.get r) i.val (Evm.Memory.indexValue w)) := by
    have hk : hp.writeAddr (.index r .dyn (Evm.Memory.indexValue i)) (Evm.Memory.indexValue w)=
        some (hp.set r (MObj.setElem .dyn (hp.get r) i.val (Evm.Memory.indexValue w))) := by
      have hi' : i.val<(MObj.elems .dyn (hp.get r)).length := hi
      simp only [Heap.writeAddr,Heap.setIndex,Evm.Memory.indexValue,Int.toNat_natCast,hi',↓reduceIte]
    exact Option.some.inj (ht.symm.trans hk)
  have hlen : out.len r .dyn=hp.len r .dyn := by
    rw [hout]
    simp only [Heap.len,Heap.get_set_same,MObj.elems_setElem,List.length_set]
  have hw : Evm.run (Evm.Memory.writeArrayCode base) ((m.push (.val w)).push (.val i))=
      .ok (Evm.Memory.writeMachine m (base.val+1+i.val) (.val w)) 0 ∧
      Evm.Memory.ArrayRepr out r base (Evm.Memory.writeMachine m (base.val+1+i.val) (.val w)) := by
    rcases Evm.Memory.writeArray_correct h.words i (Evm.Memory.indexValue w) (.val w)
      (Evm.ReprV.uint_of rfl) with ⟨out',ht',hw',ha'⟩ | ⟨ht',_⟩
    · have heq : out'=out := Option.some.inj (ht'.symm.trans ht)
      subst out'
      exact ⟨hw',ha'⟩
    · rw [ht] at ht'
      cases ht'
  have hfit : 32*(base.val+1+i.val)+32≤2^256 :=
    h.physical.fits _ ⟨by omega,by omega⟩
  have logicalFits : base.val+1+i.val<Evm.W := by
    change base.val+1+i.val<2^256
    omega
  have byteRun : ∃ offset : Fin Evm.W,offset.val=32*(base.val+1+i.val) ∧ ∀ tail : List Environment.Word,
      Environment.cryptoStep (.op .MSTORE)
        ⟨lenU offset.val offset.isLt::lenU w.val w.isLt::tail,bytes⟩=
        some ⟨tail,Environment.writeBytes bytes (32*(base.val+1+i.val)) (Semantics.wordBytes w.val)⟩ := by
    refine ⟨⟨32*(base.val+1+i.val),by change 32*(base.val+1+i.val)<2^256;omega⟩,rfl,?_⟩
    intro tail
    exact byte_mstore bytes tail ⟨base.val+1+i.val,logicalFits⟩ w hfit
  have physical : WordFrame (Evm.Memory.writeMachine m (base.val+1+i.val) (.val w))
      (Environment.writeBytes bytes (32*(base.val+1+i.val)) (Semantics.wordBytes w.val))
      (fun c => (base.val≤c ∧ c<base.val+1+hp.len r .dyn) ∨ c=base.val+1+i.val) :=
    h.physical.write (base.val+1+i.val) w hfit
  have newrep : UintArrayAt z address out r base
      (Evm.Memory.writeMachine m (base.val+1+i.val) (.val w))
      (Environment.writeBytes bytes (32*(base.val+1+i.val)) (Semantics.wordBytes w.val)) := by
    refine ⟨hrep,hw.2,?_⟩
    constructor
    · intro c hc
      apply physical.fits
      exact Or.inl (by simpa only [hlen] using hc)
    · intro c hc
      apply physical.cells
      exact Or.inl (by simpa only [hlen] using hc)
  obtain ⟨knownType,known⟩ := source_uint_write y address (MObj.elems .dyn (hp.get r))
    h.source i.val hi (Evm.Memory.indexValue w)
  have hz : z=(y.1,{y.2 with heap := y.2.heap.write address (sourceUintMemory ((MObj.elems .dyn (hp.get r)).set i.val (Evm.Memory.indexValue w))) knownType}) :=
    congrArg Prod.snd (hs.symm.trans known)
  refine ⟨out,z,ht,hs,hw.1,byteRun,newrep,?_,?_,?_,?_,?_⟩
  · rw [hz]
  · rw [hz]
  · intro b hn
    rw [hz]
    exact Source.Heap.write_other y.2.heap hn _ knownType
  · intro Q q hne
    exact indexedWrite_frame hp out r .dyn (Evm.Memory.indexValue i) (Evm.Memory.indexValue w) ht q hne
  · intro k hk
    apply Environment.writeBytes_frame
    simpa only [word_bytes_length] using hk

/-- info: 'Solidity.Backend.MemoryOps.Physical.UintArrayAt.write_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UintArrayAt.write_cell
end Solidity.Backend.MemoryOps.Physical
