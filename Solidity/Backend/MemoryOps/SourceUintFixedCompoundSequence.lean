import Solidity.Backend.MemoryOps.SourceUintFixedCompound
import Solidity.Backend.MemoryOps.SourceUintFixedAlias

/-! Reached fixed compound composition using ordinary existing Source Items,
Prog and word append. The second arithmetic case is derived from the first write. -/
namespace Solidity.Backend.MemoryOps

def sourceUintFixedAddTwice {E : Source.Env} {Γ : Source.RCtx} {N : Nat}
    (root : Source.Idx Γ (.array .memory (.int .u256) (some N))) (index rhs : Source.Idx Γ (.int .u256)) :
    Source.RItems E [] false .body Γ Γ :=
  .stmt (.expr (sourceUintFixedIndexedAdd root index rhs)) (.stmt (.expr (sourceUintFixedIndexedAdd root index rhs)) .nil)
def intrinsicUintFixedAddTwice {C : Contract} {Δ : Ctx} {N : Nat}
    (root : Idx Δ (.mem (.fixed (.prim .uint) N))) (index rhs : Idx Δ (.val .uint)) : Prog C Δ Δ :=
  .cons (.opAssign .add rfl rfl (.mindex .fixed (.var root rfl) (.local index)) (.simple (.local rhs)))
    (.cons (.opAssign .add rfl rfl (.mindex .fixed (.var root rfl) (.local index)) (.simple (.local rhs))) .nil)

theorem resolved_uint_fixed_add_twice_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx} {N : Nat}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (fuel nps : Nat) (σ : State C Δ) (r : HRef σ.H (.fixed (.prim .uint) N))
    (hr : SourceUintFixedAt y address σ.heap r)
    (sroot : Source.Idx Γ (.array .memory (.int .u256) (some N))) (si srhs : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.fixed (.prim .uint) N))) (index rhs : Idx Δ (.val .uint))
    (k value : PrimTy.uint.Denote) (hsroot : y.1.get sroot=.memRef rfl address)
    (hsi : y.1.get si=sourceUint k) (hsrhs : y.1.get srhs=sourceUint value)
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get index σ.env=k) (htrhs : TEnv.get rhs σ.env=value)
    (hk : k.1.toNat<σ.heap.len r .fixed)
    (hadd : PrimTy.uint.inRange ((MObj.elems .fixed (σ.heap.get r))[k.1.toNat].1+value.1)=true)
    (htwice : PrimTy.uint.inRange (((MObj.elems .fixed (σ.heap.get r))[k.1.toNat].1+value.1)+value.1)=true)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m)
    (ha : Evm.Memory.Objects.AllocatorRepr σ.heap base frame cursor m) (hb : 0<b) :
    let old := (MObj.elems .fixed (σ.heap.get r))[k.1.toNat]
    let one : PrimTy.uint.Denote := ⟨old.1+value.1,hadd⟩
    let two : PrimTy.uint.Denote := ⟨(old.1+value.1)+value.1,htwice⟩
    ∃ (out1 out2 : Heap σ.H) (z1 z2 : Source.EMState E Γ) (m1 m2 : Evm.Machine),
      (Source.evalE G Fsrc (fuel+4) (sourceUintFixedIndexedAdd sroot si srhs)).run y=(.ok (.val (sourceUint one)),z1) ∧
      (Source.evalE G Fsrc (fuel+3) (sourceUintFixedIndexedAdd sroot si srhs)).run z1=(.ok (.val (sourceUint two)),z2) ∧
      (Source.execItems G Fsrc (fuel+6) nps none (sourceUintFixedAddTwice sroot si srhs) y.1).run (.nil,y.2)=
        (.ok (.normal z2.1),(.nil,z2.2)) ∧
      Prog.run σ (intrinsicUintFixedAddTwice root index rhs)=.ok ⟨σ.withHeap out2,List.prefix_refl _⟩ ∧
      σ.heap.writeAddr (.index r .fixed k) one=some out1 ∧ out1.writeAddr (.index r .fixed k) two=some out2 ∧
      Evm.run (fixedUintAddCode (C := C) b root index rhs) m=.ok m1 0 ∧
      Evm.run (fixedUintAddCode (C := C) b root index rhs) m1=.ok m2 0 ∧
      Evm.run (fixedUintAddCode (C := C) b root index rhs ++ fixedUintAddCode (C := C) b root index rhs) m=.ok m2 0 ∧
      SourceUintFixedAt z1 address out1 r ∧ SourceUintFixedAt z2 address out2 r ∧
      Evm.Memory.Objects.StateRepr L b frame F (σ.withHeap out2) base m2 ∧
      Evm.Memory.Objects.AllocatorRepr out2 base frame cursor m2 ∧
      Source.MemOK E SH z1 ∧ Source.MemOK E SH z2 ∧ z1.1=y.1 ∧ z2.1=y.1 ∧
      m2.stack=m.stack ∧ m2.mem 0=m.mem 0 ∧
      (∀ {Q : RefTy} (q : HRef σ.H Q),r.id≠q.id → out2.get q=σ.heap.get q) ∧
      (∀ a,a≠address → z2.2.heap.get a=y.2.heap.get a) ∧
      z2.2.ex=y.2.ex ∧ z2.2.events=y.2.events ∧ z2.2.logs=y.2.logs ∧ z2.2.fnLocals=y.2.fnLocals ∧
      (∀ a,a≠address → z1.2.heap.get a=y.2.heap.get a) := by
  dsimp only
  let old := (MObj.elems .fixed (σ.heap.get r))[k.1.toNat]
  let one : PrimTy.uint.Denote := ⟨old.1+value.1,hadd⟩
  obtain ⟨o1,z1,m1,hw1,hsw1,he1,hstmt1,hi1,hc1,hr1,hm1,hmok1,hl1,hstack1,keep1,hobj1,haddr1,hex1,hev1,hlog1,hfn1⟩ :=
    resolved_uint_fixed_add_word G Fsrc (fuel+1) σ r hr sroot si srhs root index rhs k value hsroot hsi hsrhs htroot hti htrhs hk hadd hm SH hmem
  have hlen : o1.len r .fixed=σ.heap.len r .fixed := by simp only [Heap.len,MObj.elems_fixed,(o1.get r).2,(σ.heap.get r).2]
  have hk1 : k.1.toNat<o1.len r .fixed := by rw [hlen];exact hk
  have hel := indexedWrite_elems σ.heap o1 r .fixed k one hw1
  have hget : (MObj.elems .fixed (o1.get r))[k.1.toNat]?=some one := by rw [hel];exact List.getElem?_set_self hk
  have hold : (MObj.elems .fixed (o1.get r))[k.1.toNat]=one :=
    Option.some.inj ((List.getElem?_eq_getElem hk1).symm.trans hget)
  have hadd1 : PrimTy.uint.inRange ((MObj.elems .fixed (o1.get r))[k.1.toNat].1+value.1)=true := by rw [hold];exact htwice
  obtain ⟨o2,z2,m2,hw2,hsw2,he2,hstmt2,hi2,hc2,hr2,hm2,hmok2,hl2,hstack2,keep2,hobj2,haddr2,hex2,hev2,hlog2,hfn2⟩ :=
    resolved_uint_fixed_add_word G Fsrc fuel (σ.withHeap o1) r hr1 sroot si srhs root index rhs k value
      (by rw [hl1];exact hsroot) (by rw [hl1];exact hsi) (by rw [hl1];exact hsrhs)
      htroot hti htrhs hk1 hadd1 hm1 SH hmok1
  have htwo : (⟨(MObj.elems .fixed (o1.get r))[k.1.toNat].1+value.1,hadd1⟩ : PrimTy.uint.Denote)=
      ⟨(old.1+value.1)+value.1,htwice⟩ := by
    apply Subtype.ext
    change (MObj.elems .fixed (o1.get r))[k.1.toNat].1+value.1=(old.1+value.1)+value.1
    rw [hold]
  dsimp only [State.withHeap] at hw2 he2
  rw [htwo] at hw2 he2
  have hs1 := source_expr_statement_run G Fsrc (fuel+4) nps _ y z1 (.val (sourceUint one)) he1
  have hs2 := source_expr_statement_run G Fsrc (fuel+3) nps _ z1 z2 _ he2
  have hitems := source_items_pair_run G Fsrc fuel nps _ _ y z1 z2
    (by simpa only [hl1] using hs1) (by simpa only [hl2] using hs2)
  have ha2 := keep2 cursor hb (keep1 cursor hb ha)
  refine ⟨o1,o2,z1,z2,m1,m2,he1,he2,hitems,intrinsic_heap_pair_run σ _ _ o1 o2 hi1 hi2,hw1,hw2,hc1,hc2,?_,hr1,hr2,hm2,ha2,hmok1,hmok2,hl1,hl2.trans hl1,hstack2.trans hstack1,ha2.free.cell.trans ha.free.cell.symm,?_,?_,hex2.trans hex1,hev2.trans hev1,hlog2.trans hlog1,hfn2.trans hfn1,haddr1⟩
  · rw [Evm.run_append_ok hc1,hc2]
  · intro Q q hn;exact (hobj2 q hn).trans (hobj1 q hn)
  · intro a hn;rw [haddr2 a hn,haddr1 a hn]

theorem resolved_uint_fixed_add_late_overflow_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx} {N : Nat}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (fuel nps : Nat) (checked : Fsrc.checked=true) (σ : State C Δ) (r : HRef σ.H (.fixed (.prim .uint) N))
    (hr : SourceUintFixedAt y address σ.heap r)
    (sroot : Source.Idx Γ (.array .memory (.int .u256) (some N))) (si srhs : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.fixed (.prim .uint) N))) (index rhs : Idx Δ (.val .uint))
    (k value : PrimTy.uint.Denote) (hsroot : y.1.get sroot=.memRef rfl address)
    (hsi : y.1.get si=sourceUint k) (hsrhs : y.1.get srhs=sourceUint value)
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get index σ.env=k) (htrhs : TEnv.get rhs σ.env=value)
    (hk : k.1.toNat<σ.heap.len r .fixed)
    (hadd : PrimTy.uint.inRange ((MObj.elems .fixed (σ.heap.get r))[k.1.toNat].1+value.1)=true)
    (htwice : PrimTy.uint.inRange (((MObj.elems .fixed (σ.heap.get r))[k.1.toNat].1+value.1)+value.1)≠true)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m)
    (ha : Evm.Memory.Objects.AllocatorRepr σ.heap base frame cursor m) (hb : 0<b) :
    let old := (MObj.elems .fixed (σ.heap.get r))[k.1.toNat]
    let one : PrimTy.uint.Denote := ⟨old.1+value.1,hadd⟩
    ∃ (out1 : Heap σ.H) (z1 : Source.EMState E Γ) (m1 : Evm.Machine),
      (Source.evalE G Fsrc (fuel+4) (sourceUintFixedIndexedAdd sroot si srhs)).run y=(.ok (.val (sourceUint one)),z1) ∧
      (Source.evalE G Fsrc (fuel+3) (sourceUintFixedIndexedAdd sroot si srhs)).run z1=
        (.error (.revert (Source.panicData .arithmetic)),z1) ∧
      (Source.execItems G Fsrc (fuel+6) nps none (sourceUintFixedAddTwice sroot si srhs) y.1).run (.nil,y.2)=
        (.error (.revert (Source.panicData .arithmetic)),(.nil,z1.2)) ∧
      Prog.run σ (intrinsicUintFixedAddTwice root index rhs)=.error .revert ∧
      σ.heap.writeAddr (.index r .fixed k) one=some out1 ∧
      Evm.run (fixedUintAddCode (C := C) b root index rhs) m=.ok m1 0 ∧
      Evm.run (fixedUintAddCode (C := C) b root index rhs) m1=.revert ∧
      Evm.run (fixedUintAddCode (C := C) b root index rhs ++ fixedUintAddCode (C := C) b root index rhs) m=.revert ∧
      SourceUintFixedAt z1 address out1 r ∧ Evm.Memory.Objects.StateRepr L b frame F (σ.withHeap out1) base m1 ∧
      Evm.Memory.Objects.AllocatorRepr out1 base frame cursor m1 ∧ Source.MemOK E SH z1 ∧ z1.1=y.1 ∧
      m1.stack=m.stack ∧ m1.mem 0=m.mem 0 ∧
      (∀ {Q : RefTy} (q : HRef σ.H Q),r.id≠q.id → out1.get q=σ.heap.get q) ∧
      (∀ a,a≠address → z1.2.heap.get a=y.2.heap.get a) ∧
      z1.2.ex=y.2.ex ∧ z1.2.events=y.2.events ∧ z1.2.logs=y.2.logs ∧ z1.2.fnLocals=y.2.fnLocals := by
  dsimp only
  let old := (MObj.elems .fixed (σ.heap.get r))[k.1.toNat]
  let one : PrimTy.uint.Denote := ⟨old.1+value.1,hadd⟩
  obtain ⟨o1,z1,m1,hw1,hsw1,he1,hstmt1,hi1,hc1,hr1,hm1,hmok1,hl1,hstack1,keep1,hobj1,haddr1,hex1,hev1,hlog1,hfn1⟩ :=
    resolved_uint_fixed_add_word G Fsrc (fuel+1) σ r hr sroot si srhs root index rhs k value hsroot hsi hsrhs htroot hti htrhs hk hadd hm SH hmem
  have hlen : o1.len r .fixed=σ.heap.len r .fixed := by simp only [Heap.len,MObj.elems_fixed,(o1.get r).2,(σ.heap.get r).2]
  have hk1 : k.1.toNat<o1.len r .fixed := by rw [hlen];exact hk
  have hel := indexedWrite_elems σ.heap o1 r .fixed k one hw1
  have hget : (MObj.elems .fixed (o1.get r))[k.1.toNat]?=some one := by rw [hel];exact List.getElem?_set_self hk
  have hold : (MObj.elems .fixed (o1.get r))[k.1.toNat]=one :=
    Option.some.inj ((List.getElem?_eq_getElem hk1).symm.trans hget)
  have hadd1 : PrimTy.uint.inRange ((MObj.elems .fixed (o1.get r))[k.1.toNat].1+value.1)≠true := by rw [hold];exact htwice
  have hf := resolved_uint_fixed_add_overflow_word G Fsrc fuel checked (σ.withHeap o1) r hr1 sroot si srhs root index rhs k value
    (by rw [hl1];exact hsroot) (by rw [hl1];exact hsi) (by rw [hl1];exact hsrhs)
    htroot hti htrhs hk1 hadd1 hm1
  have hs1 := source_expr_statement_run G Fsrc (fuel+4) nps _ y z1 (.val (sourceUint one)) he1
  have hs2 := source_expr_statement_error G Fsrc (fuel+3) nps _ z1 z1 _ hf.1
  have hitems := source_items_pair_error G Fsrc fuel nps _ _ y z1 z1 _
    (by simpa only [hl1] using hs1) hs2
  refine ⟨o1,z1,m1,he1,hf.1,hitems,intrinsic_heap_pair_error σ _ _ o1 .revert hi1 hf.2.2.1,hw1,hc1,hf.2.2.2,?_,hr1,hm1,keep1 cursor hb ha,hmok1,hl1,hstack1,
    (keep1 cursor hb ha).free.cell.trans ha.free.cell.symm,hobj1,haddr1,hex1,hev1,hlog1,hfn1⟩
  rw [Evm.run_append_ok hc1];exact hf.2.2.2

/-- info: 'Solidity.Backend.MemoryOps.resolved_uint_fixed_add_twice_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_uint_fixed_add_twice_word
/-- info: 'Solidity.Backend.MemoryOps.resolved_uint_fixed_add_late_overflow_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_uint_fixed_add_late_overflow_word
end Solidity.Backend.MemoryOps
