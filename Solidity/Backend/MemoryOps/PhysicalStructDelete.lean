import Solidity.Backend.MemoryOps.PhysicalStructChild
import Solidity.Backend.MemoryOps.SourceStructDelete

/-! Actual named-member child deletion and its local physical frame. Component
MSTORE evidence does not execute the whole pointer prefix in bytes. -/
namespace Solidity.Backend.MemoryOps.Physical

/-- INITIAL named-struct correspondence and aligned live-cell inputs derive
actual default deletion and the reached physical child frame. No final heap or
byte observation is assumed; the whole word path and component byte store
remain distinct executions. -/
theorem delete_struct_child_physical
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {a : Nat} (layout : SourceBoolStructLayout E dn s tag child)
    (G : Source.Glob E) (Fsrc : Source.Fr) (n nps : Nat)
    (σ : State C Δ) (r : HRef σ.H (.struct s)) (address : Nat → Nat)
    (hr : SourceBoolStructAt y a σ.heap r address layout)
    (sroot : Source.Idx Γ (.struct .memory dn)) (si : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.struct s))) (i : Val C Δ .uint)
    (k : PrimTy.uint.Denote)
    (hsroot : y.1.get sroot=.memRef rfl a) (hsi : y.1.get si=sourceUint k)
    (htroot : TEnv.get root σ.env=some r) (hti : i.evalT σ=.ok k)
    (hmf : (Ty.ref (.struct s)).mapFree=true)
    (hk : k.1.toNat<σ.heap.len (σ.heap.field r layout.child_type) .dyn)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m)
    (hif : Evm.valIn F i=true)
    (bytes : Environment.Memory)
    (physical : WordFrame m bytes (fun c => (base (σ.heap.field r layout.child_type).id).val≤c ∧
      c<(base (σ.heap.field r layout.child_type).id).val+1+σ.heap.len (σ.heap.field r layout.child_type) .dyn)) :
    let q := σ.heap.field r layout.child_type
    let cell := (base q.id).val+1+k.1.toNat
    let byteNext := Environment.writeBytes bytes (32*cell) (Semantics.wordBytes (Evm.bword false).val)
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ) (target : Evm.Machine) (offset : Fin Evm.W),
      σ.heap.writeAddr (.index q .dyn k) false=some out ∧
      (Source.deleteLoc (E := E) (Γ := Γ) Fsrc (n+3) (τ := .bool) (.mem (address q.id) k.1.toNat)).run y=(.ok (),z) ∧
      (Source.evalE G Fsrc (n+4) (sourceStructChildDelete layout sroot si)).run y=(.ok Source.RVal.unit,z) ∧
      (Source.execS G Fsrc (n+5) nps none
        (.expr (sourceStructChildDelete layout sroot si) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      Stmt.run σ (.deleteMem (.loc (.index .dyn (.loc (.field (.var root hmf) child layout.child_type)) i)) rfl)=
        .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (structChildDeleteCode b root child i) m=.ok target 0 ∧
      SourceBoolStructAt z a out r address layout ∧ Source.MemOK E SH z ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap out) base target ∧
      WordFrame target byteNext (fun c => (base q.id).val≤c ∧ c<(base q.id).val+1+out.len q .dyn) ∧
      offset.val=32*cell ∧
      (∀ tail : List Environment.Word,Environment.cryptoStep (.op .MSTORE)
        ⟨lenU offset.val offset.isLt::lenU (Evm.bword false).val (Evm.bword false).isLt::tail,bytes⟩=some ⟨tail,byteNext⟩) ∧
      Environment.readMemory byteNext (32*cell) 32=Semantics.wordBytes (Evm.bword false).val ∧
      (∀ j,j<32*cell ∨ 32*cell+32≤j → byteNext j=bytes j) ∧
      out.get r=σ.heap.get r ∧ out.field r layout.child_type=q ∧
      out.field r layout.tag_type=σ.heap.field r layout.tag_type ∧
      z.2.heap.get a=y.2.heap.get a ∧ z.1=y.1 ∧ target.stack=m.stack ∧
      Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out) target ∧
      (∀ {R : RefTy} (t : HRef σ.H R),q.id≠t.id → out.get t=σ.heap.get t) ∧
      (∀ d,d≠address q.id → z.2.heap.get d=y.2.heap.get d) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  dsimp only
  let q := σ.heap.field r layout.child_type
  let cell := (base q.id).val+1+k.1.toNat
  let next := Evm.Memory.writeMachine m cell (.val (Evm.bword false))
  let byteNext := Environment.writeBytes bytes (32*cell) (Semantics.wordBytes (Evm.bword false).val)
  obtain ⟨out,z,target,hw,hs,he,_oldStmt,ht,hcode,hsource,hmem',hwords,hloc,hstack,halloc,
      hparent,hother,hsourceOther,hex,hevents,hlogs,hfn⟩ :=
    hr.delete_child_word layout G Fsrc n σ r address sroot si root i k
      hsroot hsi htroot hti hmf hk SH hmem hm hif
  have statement := source_expr_statement_run G Fsrc (n+4) nps _ y z _ he
  have hout : out=σ.heap.set q (MObj.setElem .dyn (σ.heap.get q) k.1.toNat false) := by
    have known : σ.heap.writeAddr (.index q .dyn k) false=
        some (σ.heap.set q (MObj.setElem .dyn (σ.heap.get q) k.1.toNat false)) := by
      change (if k.1.toNat<σ.heap.len q .dyn then some _ else none)=_
      rw [if_pos hk]
    exact Option.some.inj (hw.symm.trans known)
  have hlen : out.len q .dyn=σ.heap.len q .dyn := by
    rw [hout]
    simp only [Heap.len,Heap.get_set_same,MObj.elems_setElem,List.length_set]
  have expectedWords : Evm.Memory.ArrayRepr out q (base q.id) next := by
    rw [hout]
    exact (hm.heap.arrays q).set k.1.toNat hk false (.val (Evm.bword false)) rfl
  have fits : 32*cell+32≤2^256 := physical.fits cell ⟨by dsimp only [cell,q];omega,by dsimp only [cell,q];omega⟩
  have updated := physical.write cell (Evm.bword false) fits
  have physicalOut : WordFrame target byteNext
      (fun c => (base q.id).val≤c ∧ c<(base q.id).val+1+out.len q .dyn) := by
    constructor
    · intro c hc
      exact updated.fits c (.inl (by simpa only [hlen] using hc))
    · intro c hc
      obtain ⟨w,hwc,hbc⟩ := updated.cells c (.inl (by simpa only [hlen] using hc))
      have same := bool_array_cells_eq expectedWords (hwords.heap.arrays q) c hc
      exact ⟨w,same.symm.trans hwc,hbc⟩
  have logicalFits : cell<Evm.W := by change cell<2^256;omega
  let offset : Fin Evm.W := ⟨32*cell,by change 32*cell<2^256;omega⟩
  have byteRun : ∀ tail : List Environment.Word,Environment.cryptoStep (.op .MSTORE)
      ⟨lenU offset.val offset.isLt::lenU (Evm.bword false).val (Evm.bword false).isLt::tail,bytes⟩=some ⟨tail,byteNext⟩ := by
    intro tail
    exact byte_mstore bytes tail ⟨cell,logicalFits⟩ (Evm.bword false) fits
  have childSame : out.field r layout.child_type=q := by unfold Heap.field;rw [hparent];rfl
  have tagSame : out.field r layout.tag_type=σ.heap.field r layout.tag_type := by unfold Heap.field;rw [hparent]
  refine ⟨out,z,target,offset,hw,hs,he,statement,ht,hcode,hsource,hmem',hwords,physicalOut,rfl,byteRun,?_,?_,
    hparent,childSame,tagSame,hsourceOther a hr.parent_ne_leaf,hloc,hstack,halloc,hother,hsourceOther,hex,hevents,hlogs,hfn⟩
  · simpa only [Environment.wordBytes_length] using Environment.read_written (Semantics.wordBytes (Evm.bword false).val) (32*cell) bytes
  · intro j outside
    exact Environment.writeBytes_frame _ _ j _ (by simp only [Environment.wordBytes_length];exact outside)


/-- info: 'Solidity.Backend.MemoryOps.Physical.delete_struct_child_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms delete_struct_child_physical
end Solidity.Backend.MemoryOps.Physical
