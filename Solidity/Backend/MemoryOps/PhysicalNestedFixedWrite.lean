import Solidity.Backend.MemoryOps.SourceUintFixedRefsExact
import Solidity.Backend.MemoryOps.PhysicalPointerFrame
import Solidity.Backend.MemoryOps.PhysicalByteJournal

/-! Nested whole WORD execution and actual terminal byte MSTORE. Numeric and
scaled-pointer footprints stay distinct. No byte pointer-load/emitter theorem. -/
namespace Solidity.Backend.MemoryOps.Physical

theorem PointerFrame.numeric_write {m : Evm.Machine} {bytes : Environment.Memory} {live : Nat → Prop}
    (h : PointerFrame m bytes live) (dst : Nat) (value : Fin Evm.W)
    (separate : ∀ c,live c → c≠dst) :
    PointerFrame (Evm.Memory.writeMachine m dst (.val value))
      (Environment.writeBytes bytes (32*dst) (Semantics.wordBytes value.val)) live := by
  first
  | solve | simp only [] | omega
  | refine ⟨h.fits,?_⟩
    intro c hc
    obtain ⟨base,word,fit,image⟩ := h.cells c hc
    refine ⟨base,(Evm.upd_other _ _ (separate c hc)).trans word,fit,?_⟩
    rw [readMemory_write_frame]
    · exact image
    · rw [Environment.wordBytes_length]
      have ne := separate c hc
      omega

theorem nested_fixed_word_byte_store {C : Contract} {Δ : Ctx} {n L b frame : Nat}
    {F : Evm.Frag Δ} {σ : State C Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m)
    (root : Idx Δ (.mem (UintFixedRefsRef n))) (i j : Idx Δ (.val .uint))
    (value : Val C Δ .uint) (inside : Evm.valIn F value=true)
    (r : HRef σ.H (UintFixedRefsRef n)) (q : HRef σ.H (.fixed (.prim .uint) n)) (k l v : Fin Evm.W)
    (hroot : TEnv.get root σ.env=some r)
    (hi : TEnv.get i σ.env=Evm.Memory.indexValue k) (hj : TEnv.get j σ.env=Evm.Memory.indexValue l)
    (hv : value.evalT σ=.ok (Evm.Memory.indexValue v))
    (selected : σ.heap.index r .dyn (Evm.Memory.indexValue k)=some q) (valid : l.val<n)
    (bytes : Environment.Memory) (numericLive pointerLive : Nat → Prop)
    (numbers : WordFrame m bytes numericLive) (pointers : PointerFrame m bytes pointerLive)
    (fits : 32*((base q.id).val+l.val)+32≤2^256)
    (separate : ∀ c,pointerLive c → c≠(base q.id).val+l.val)
    (tail : List Environment.Word) (faultTail : List Roadmap.Word) (suffix : Backend.Program) :
    let cell := (base q.id).val+l.val
    let next := Evm.Memory.writeMachine m cell (.val v)
    let byteNext := Environment.writeBytes bytes (32*cell) (Semantics.wordBytes v.val)
    ∃ (logical offset : Fin Evm.W),logical.val=cell ∧ offset.val=32*cell ∧
      Evm.run (Evm.compileVal b value ++
        ([.mload (Evm.cellOf b root)] ++ Evm.compileVal b (.simple (.local i) : Val C Δ .uint) ++
          Evm.Memory.Objects.readCode (.dyn : ArrTy (UintFixedRefsRef n) (.ref (.fixed (.prim .uint) n)))) ++
        Evm.compileVal b (.simple (.local j) : Val C Δ .uint) ++
        Evm.Memory.Objects.writeCode (.fixed : ArrTy (.fixed (.prim .uint) n) (.prim .uint))) m=.ok next 0 ∧
      Environment.cryptoStep (.op .MSTORE) ⟨lenU offset.val offset.isLt::lenU v.val v.isLt::tail,bytes⟩=
        some ⟨tail,byteNext⟩ ∧
      WordFrame next byteNext (fun c => numericLive c ∨ c=cell) ∧ PointerFrame next byteNext pointerLive ∧
      (∀ a,a<32*cell ∨ 32*cell+32≤a → byteNext a=bytes a) ∧
      Failure.Slice.run (.op .REVERT::suffix)
        ⟨(⟨offset.val,offset.isLt⟩ : Roadmap.Word)::(⟨32,by decide⟩ : Roadmap.Word)::faultTail,byteNext⟩=
        some (⟨faultTail,byteNext⟩,some (.revert (Semantics.wordBytes v.val))) := by
  first
  | solve | simp only [] | omega
  | dsimp only
    have logicalFits : (base q.id).val+l.val<Evm.W := by change (base q.id).val+l.val<2^256;omega
    have offsetFits : 32*((base q.id).val+l.val)<Evm.W := by change 32*((base q.id).val+l.val)<2^256;omega
    let logical : Fin Evm.W := ⟨(base q.id).val+l.val,logicalFits⟩
    let offset : Fin Evm.W := ⟨32*((base q.id).val+l.val),offsetFits⟩
    refine ⟨logical,offset,rfl,rfl,nested_fixed_store_exact hm root i j value inside r q k l v hroot hi hj hv selected valid,
      byte_mstore bytes tail logical v fits,numbers.write _ v fits,pointers.numeric_write _ v separate,?_,
      revert_written_word bytes logical v fits faultTail suffix⟩
    intro a ha
    apply Environment.writeBytes_frame
    rw [Environment.wordBytes_length]
    exact ha

/-- info: 'Solidity.Backend.MemoryOps.Physical.PointerFrame.numeric_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PointerFrame.numeric_write
/-- info: 'Solidity.Backend.MemoryOps.Physical.nested_fixed_word_byte_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nested_fixed_word_byte_store
end Solidity.Backend.MemoryOps.Physical
