import Solidity.Backend.MemoryOps.SourceUintFixedDecrement
import Solidity.Backend.MemoryOps.IntervalOverwrite

/-! A genuine two-statement Source Items and intrinsic Prog application, not
merely two target runs: increment then reached decrement restores initial heap. -/
namespace Solidity.Backend.MemoryOps

def sourceUintFixedBumpPair {E : Source.Env} {Γ : Source.RCtx} {N : Nat}
    (pinc pdec : Bool) (root : Source.Idx Γ (.array .memory (.int .u256) (some N))) (index : Source.Idx Γ (.int .u256)) :
    Source.RItems E [] false .body Γ Γ :=
  .stmt (.expr (sourceUintFixedIncrement pinc root index)) (.stmt (.expr (sourceUintFixedDecrement pdec root index)) .nil)
def intrinsicUintFixedBumpPair {C : Contract} {Δ : Ctx} {N : Nat}
    (pinc pdec : Bool) (root : Idx Δ (.mem (.fixed (.prim .uint) N))) (index : Idx Δ (.val .uint)) : Prog C Δ Δ :=
  .cons (.incDec (fixedUintIncrementOp pinc) rfl (.mindex .fixed (.var root rfl) (.local index)))
    (.cons (.incDec (fixedUintDecrementOp pdec) rfl (.mindex .fixed (.var root rfl) (.local index))) .nil)

/-- Only INITIAL increment range, actual bounds/alignment and existing full
ownership are premises. The second OLD, range, execution and restoration are
derived from the first real write. Original caller nps is never recomputed. -/
theorem resolved_uint_fixed_bump_pair_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx} {N : Nat}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (fuel nps : Nat) (pinc pdec : Bool) (σ : State C Δ) (r : HRef σ.H (.fixed (.prim .uint) N))
    (hr : SourceUintFixedAt y address σ.heap r)
    (sroot : Source.Idx Γ (.array .memory (.int .u256) (some N))) (si : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.fixed (.prim .uint) N))) (index : Idx Δ (.val .uint))
    (k : PrimTy.uint.Denote) (hsroot : y.1.get sroot=.memRef rfl address) (hsi : y.1.get si=sourceUint k)
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get index σ.env=k)
    (hk : k.1.toNat<σ.heap.len r .fixed)
    (hadd : PrimTy.uint.inRange ((MObj.elems .fixed (σ.heap.get r))[k.1.toNat].1+1)=true)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m)
    (ha : Evm.Memory.Objects.AllocatorRepr σ.heap base frame cursor m) (hb : 0<b) :
    let old := (MObj.elems .fixed (σ.heap.get r))[k.1.toNat]
    let one : PrimTy.uint.Denote := ⟨old.1+1,hadd⟩
    ∃ (out1 out2 : Heap σ.H) (z1 z2 : Source.EMState E Γ) (m1 m2 : Evm.Machine),
      (Source.evalE G Fsrc (fuel+4) (sourceUintFixedIncrement pinc sroot si)).run y=
        (.ok (.val (sourceUint (if pinc then one else old))),z1) ∧
      (Source.evalE G Fsrc (fuel+3) (sourceUintFixedDecrement pdec sroot si)).run z1=
        (.ok (.val (sourceUint (if pdec then old else one))),z2) ∧
      (Source.execItems G Fsrc (fuel+6) nps none (sourceUintFixedBumpPair pinc pdec sroot si) y.1).run (.nil,y.2)=
        (.ok (.normal z2.1),(.nil,z2.2)) ∧
      Prog.run σ (intrinsicUintFixedBumpPair pinc pdec root index)=.ok ⟨σ.withHeap out2,List.prefix_refl _⟩ ∧
      σ.heap.writeAddr (.index r .fixed k) one=some out1 ∧ out1.writeAddr (.index r .fixed k) old=some out2 ∧ out2=σ.heap ∧
      Evm.run (fixedUintIncrementCode (C := C) b root index) m=.ok m1 0 ∧
      Evm.run (fixedUintDecrementCode (C := C) b root index) m1=.ok m2 0 ∧
      Evm.run (fixedUintIncrementCode (C := C) b root index ++ fixedUintDecrementCode (C := C) b root index) m=.ok m2 0 ∧
      SourceUintFixedAt z1 address out1 r ∧ SourceUintFixedAt z2 address out2 r ∧
      Evm.Memory.Objects.StateRepr L b frame F (σ.withHeap out2) base m2 ∧
      Evm.Memory.Objects.AllocatorRepr out2 base frame cursor m2 ∧
      Source.MemOK E SH z1 ∧ Source.MemOK E SH z2 ∧ z1.1=y.1 ∧ z2.1=y.1 ∧
      m2.stack=m.stack ∧ m2.mem 0=m.mem 0 ∧
      (∀ a,a≠address → z1.2.heap.get a=y.2.heap.get a) ∧
      (∀ a,z2.2.heap.get a=y.2.heap.get a) ∧
      z2.2.ex=y.2.ex ∧ z2.2.events=y.2.events ∧ z2.2.logs=y.2.logs ∧ z2.2.fnLocals=y.2.fnLocals := by
  dsimp only
  let old := (MObj.elems .fixed (σ.heap.get r))[k.1.toNat]
  let one : PrimTy.uint.Denote := ⟨old.1+1,hadd⟩
  obtain ⟨o1,z1,m1,hw1,hsw1,he1,hstmt1,hi1,hc1,hr1,hm1,hmok1,hl1,hstack1,keep1,hobj1,haddr1,hex1,hev1,hlog1,hfn1⟩ :=
    resolved_uint_fixed_increment_word G Fsrc (fuel+1) pinc σ r hr sroot si root index k hsroot hsi htroot hti hk hadd SH hmem hm
  have hlen : o1.len r .fixed=σ.heap.len r .fixed := by simp only [Heap.len,MObj.elems_fixed,(o1.get r).2,(σ.heap.get r).2]
  have hk1 : k.1.toNat<o1.len r .fixed := by rw [hlen];exact hk
  have hel := indexedWrite_elems σ.heap o1 r .fixed k one hw1
  have hget : (MObj.elems .fixed (o1.get r))[k.1.toNat]?=some one := by rw [hel];exact List.getElem?_set_self hk
  have hold : (MObj.elems .fixed (o1.get r))[k.1.toNat]=one :=
    Option.some.inj ((List.getElem?_eq_getElem hk1).symm.trans hget)
  have hsub : PrimTy.uint.inRange ((MObj.elems .fixed (o1.get r))[k.1.toNat].1-1)=true := by
    rw [hold]
    have hcancel : one.1-1=old.1 := by change old.1+1-1=old.1;omega
    rw [hcancel];exact old.2
  obtain ⟨o2,z2,m2,hw2,hsw2,he2,hstmt2,hi2,hc2,hr2,hm2,hmok2,hl2,hstack2,keep2,hobj2,haddr2,hex2,hev2,hlog2,hfn2⟩ :=
    resolved_uint_fixed_decrement_word G Fsrc fuel pdec (σ.withHeap o1) r hr1 sroot si root index k
      (by rw [hl1];exact hsroot) (by rw [hl1];exact hsi) htroot hti hk1 hsub SH hmok1 hm1
  have hnew : (⟨(MObj.elems .fixed (o1.get r))[k.1.toNat].1-1,hsub⟩ : PrimTy.uint.Denote)=old := by
    apply Subtype.ext
    change (MObj.elems .fixed (o1.get r))[k.1.toNat].1-1=old.1
    rw [hold];change old.1+1-1=old.1;omega
  dsimp only [State.withHeap] at hw2 he2
  rw [hnew] at hw2 he2
  rw [hold] at he2
  have hs1 := source_expr_statement_run G Fsrc (fuel+4) nps _ y z1 _ he1
  have hs2 := source_expr_statement_run G Fsrc (fuel+3) nps _ z1 z2 _ he2
  have hitems := source_items_pair_run G Fsrc fuel nps _ _ y z1 z2
    (by simpa only [hl1] using hs1) (by simpa only [hl2] using hs2)
  have hv2 := indexedWrite_elems o1 o2 r .fixed k old hw2
  have hsame : o2.get r=σ.heap.get r := by
    apply Subtype.ext
    simp only [MObj.elems_fixed] at hel hv2
    rw [hv2,hel,List.set_set]
    simpa only [MObj.elems_fixed,old] using List.set_getElem_self hk
  have hrestore : o2=σ.heap := by
    apply memoryOps_heap_ext
    intro Q q
    by_cases hn : r.id=q.id
    · obtain ⟨hQ,hq⟩ := HRef.heq_of_id r q hn
      cases hQ;cases hq;exact hsame
    · exact (hobj2 q hn).trans (hobj1 q hn)
  have hsource : ∀ a,z2.2.heap.get a=y.2.heap.get a := by
    intro a
    by_cases hn : a=address
    · subst a
      rw [hr2,hr,hrestore]
    · rw [haddr2 a hn,haddr1 a hn]
  have ha2 := keep2 cursor hb (keep1 cursor hb ha)
  have hword : Evm.run (fixedUintIncrementCode (C := C) b root index ++ fixedUintDecrementCode (C := C) b root index) m=.ok m2 0 := by
    rw [Evm.run_append_ok hc1];exact hc2
  exact ⟨o1,o2,z1,z2,m1,m2,he1,he2,hitems,intrinsic_heap_pair_run σ (.incDec (fixedUintIncrementOp pinc) rfl (.mindex .fixed (.var root rfl) (.local index))) (.incDec (fixedUintDecrementOp pdec) rfl (.mindex .fixed (.var root rfl) (.local index))) o1 o2 hi1 hi2,hw1,hw2,hrestore,hc1,hc2,hword,hr1,hr2,hm2,ha2,hmok1,hmok2,hl1,hl2.trans hl1,hstack2.trans hstack1,ha2.free.cell.trans ha.free.cell.symm,haddr1,hsource,hex2.trans hex1,hev2.trans hev1,hlog2.trans hlog1,hfn2.trans hfn1⟩

/-- info: 'Solidity.Backend.MemoryOps.resolved_uint_fixed_bump_pair_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_uint_fixed_bump_pair_word
end Solidity.Backend.MemoryOps
