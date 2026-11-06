import Solidity.Backend.MemoryOps.SourceUintFixedBumpSequence

/-! Reached-state fixed-array decrement and checked failure.
Two actual decrements, not two runs from the initial heap. Source failure
retains the first reached EM state; target revert exposes no suffix machine.
The original evaluator fuel, caller nps and positive fixed-type premises stay.
-/
namespace Solidity.Backend.MemoryOps

def sourceUintFixedDecrementTwice {E : Source.Env} {Γ : Source.RCtx} {N : Nat}
    (first second : Bool) (root : Source.Idx Γ (.array .memory (.int .u256) (some N)))
    (index : Source.Idx Γ (.int .u256)) : Source.RItems E [] false .body Γ Γ :=
  .stmt (.expr (sourceUintFixedDecrement first root index))
    (.stmt (.expr (sourceUintFixedDecrement second root index)) .nil)

def intrinsicUintFixedDecrementTwice {C : Contract} {Δ : Ctx} {N : Nat}
    (first second : Bool) (root : Idx Δ (.mem (.fixed (.prim .uint) N)))
    (index : Idx Δ (.val .uint)) : Prog C Δ Δ :=
  .cons (.incDec (fixedUintDecrementOp first) rfl (.mindex .fixed (.var root rfl) (.local index)))
    (.cons (.incDec (fixedUintDecrementOp second) rfl (.mindex .fixed (.var root rfl) (.local index))) .nil)

/-- INITIAL represented cell is one. The first actual write derives zero and
all reached premises. The second checked decrement fails before another write.
No final-state representation, successful prefix or suffix result is assumed. -/
theorem resolved_uint_fixed_decrement_late_underflow_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx} {N : Nat}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (fuel nps : Nat) (first second : Bool) (checked : Fsrc.checked=true)
    (σ : State C Δ) (r : HRef σ.H (.fixed (.prim .uint) N))
    (hr : SourceUintFixedAt y address σ.heap r)
    (sroot : Source.Idx Γ (.array .memory (.int .u256) (some N))) (si : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.fixed (.prim .uint) N))) (index : Idx Δ (.val .uint))
    (k : PrimTy.uint.Denote) (hsroot : y.1.get sroot=.memRef rfl address) (hsi : y.1.get si=sourceUint k)
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get index σ.env=k)
    (hk : k.1.toNat<σ.heap.len r .fixed)
    (hstart : (MObj.elems .fixed (σ.heap.get r))[k.1.toNat].1=1)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m)
    (ha : Evm.Memory.Objects.AllocatorRepr σ.heap base frame cursor m) (hb : 0<b) :
    let old := (MObj.elems .fixed (σ.heap.get r))[k.1.toNat]
    let zero : PrimTy.uint.Denote := ⟨0,by decide⟩
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ) (target : Evm.Machine),
      (Source.evalE G Fsrc (fuel+4) (sourceUintFixedDecrement first sroot si)).run y=
        (.ok (.val (sourceUint (if first then zero else old))),z) ∧
      (Source.evalE G Fsrc (fuel+3) (sourceUintFixedDecrement second sroot si)).run z=
        (.error (.revert (Source.panicData .arithmetic)),z) ∧
      (Source.execItems G Fsrc (fuel+6) nps none (sourceUintFixedDecrementTwice first second sroot si) y.1).run (.nil,y.2)=
        (.error (.revert (Source.panicData .arithmetic)),(.nil,z.2)) ∧
      Prog.run σ (intrinsicUintFixedDecrementTwice first second root index)=.error .revert ∧
      σ.heap.writeAddr (.index r .fixed k) zero=some out ∧
      Evm.run (fixedUintDecrementCode (C := C) b root index) m=.ok target 0 ∧
      Evm.run (fixedUintDecrementCode (C := C) b root index) target=.revert ∧
      Evm.run (fixedUintDecrementCode (C := C) b root index ++ fixedUintDecrementCode (C := C) b root index) m=.revert ∧
      (MObj.elems .fixed (out.get r))[k.1.toNat]'(by
        simpa only [Heap.len,MObj.elems_fixed,(out.get r).2,(σ.heap.get r).2] using hk)=zero ∧
      SourceUintFixedAt z address out r ∧
      Evm.Memory.Objects.StateRepr L b frame F (σ.withHeap out) base target ∧
      Evm.Memory.Objects.AllocatorRepr out base frame cursor target ∧
      Source.MemOK E SH z ∧ z.1=y.1 ∧ target.stack=m.stack ∧ target.mem 0=m.mem 0 ∧
      (∀ {Q : RefTy} (q : HRef σ.H Q),r.id≠q.id → out.get q=σ.heap.get q) ∧
      (∀ a,a≠address → z.2.heap.get a=y.2.heap.get a) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  dsimp only
  let old := (MObj.elems .fixed (σ.heap.get r))[k.1.toNat]
  let zero : PrimTy.uint.Denote := ⟨0,by decide⟩
  have hsub : PrimTy.uint.inRange ((MObj.elems .fixed (σ.heap.get r))[k.1.toNat].1-1)=true := by
    rw [hstart];decide
  let new : PrimTy.uint.Denote := ⟨old.1-1,hsub⟩
  obtain ⟨out,z,target,hw,hsw,he,hstmt,hi,hc,hr1,hm1,hmok1,hl1,hstack,keep,hobj,haddr,hex,hev,hlog,hfn⟩ :=
    resolved_uint_fixed_decrement_word G Fsrc (fuel+1) first σ r hr sroot si root index k
      hsroot hsi htroot hti hk hsub SH hmem hm
  have hnew : new=zero := by
    apply Subtype.ext
    change old.1-1=0
    change (MObj.elems .fixed (σ.heap.get r))[k.1.toNat].1-1=0
    rw [hstart];rfl
  change σ.heap.writeAddr (.index r .fixed k) new=some out at hw
  change (Source.evalE G Fsrc (fuel+4) (sourceUintFixedDecrement first sroot si)).run y=
    (.ok (.val (sourceUint (if first then new else old))),z) at he
  rw [hnew] at hw he
  have hlen : out.len r .fixed=σ.heap.len r .fixed := by
    simp only [Heap.len,MObj.elems_fixed,(out.get r).2,(σ.heap.get r).2]
  have hk1 : k.1.toNat<out.len r .fixed := by rw [hlen];exact hk
  have hel : MObj.elems .fixed (out.get r)=
      (MObj.elems .fixed (σ.heap.get r)).set k.val.toNat zero := indexedWrite_elems σ.heap out r .fixed k zero hw
  have hget : (MObj.elems .fixed (out.get r))[k.1.toNat]?=some zero := by
    rw [hel];exact List.getElem?_set_self hk
  have hold : (MObj.elems .fixed (out.get r))[k.1.toNat]=zero :=
    Option.some.inj ((List.getElem?_eq_getElem hk1).symm.trans hget)
  have hbad : PrimTy.uint.inRange ((MObj.elems .fixed (out.get r))[k.1.toNat].1-1)≠true := by
    rw [hold];change PrimTy.uint.inRange ((0 : Int)-1)≠true;decide
  have hf :
      (Source.evalE G Fsrc (fuel+3) (sourceUintFixedDecrement second sroot si)).run z=
        (.error (.revert (Source.panicData .arithmetic)),z) ∧
      (Source.execS G Fsrc (fuel+4) Γ.length none
        (.expr (sourceUintFixedDecrement second sroot si) : Source.RStmt E [] false .body Γ Γ) z.1).run (.nil,z.2)=
        (.error (.revert (Source.panicData .arithmetic)),(.nil,z.2)) ∧
      TRun.incDec (fixedUintDecrementOp second) (.mindex .fixed (.var root rfl) (.local index))
        (σ.withHeap out)=.error .revert ∧
      Evm.run (fixedUintDecrementCode b root index) target=.revert :=  resolved_uint_fixed_decrement_underflow_word G Fsrc fuel second checked
    (σ.withHeap out) r hr1 sroot si root index k
    (by rw [hl1];exact hsroot) (by rw [hl1];exact hsi) htroot hti hk1 hbad hm1
  have hs1 : (Source.execS G Fsrc (fuel+4+1) nps none
      (.expr (sourceUintFixedDecrement first sroot si) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal z.1),(.nil,z.2)) :=  source_expr_statement_run G Fsrc (fuel+4) nps _ y z _ he
  have hs2 : (Source.execS G Fsrc (fuel+3+1) nps none
      (.expr (sourceUintFixedDecrement second sroot si) : Source.RStmt E [] false .body Γ Γ) z.1).run (.nil,z.2)=
        (.error (.revert (Source.panicData .arithmetic)),(.nil,z.2)) :=  source_expr_statement_error G Fsrc (fuel+3) nps _ z z _ hf.1
  have hitems :
      (Source.execItems G Fsrc (fuel+6) nps none (sourceUintFixedDecrementTwice first second sroot si) y.1).run (.nil,y.2)=
        (.error (.revert (Source.panicData .arithmetic)),(.nil,z.2)) :=  source_items_pair_error G Fsrc fuel nps _ _ y z z _
    (by simpa only [hl1] using hs1) hs2
  refine ⟨out,z,target,he,hf.1,hitems,
    intrinsic_heap_pair_error σ _ _ out .revert hi hf.2.2.1,hw,hc,hf.2.2.2,?_,hold,
    hr1,hm1,keep cursor hb ha,hmok1,hl1,hstack,
    (keep cursor hb ha).free.cell.trans ha.free.cell.symm,hobj,haddr,hex,hev,hlog,hfn⟩
  rw [Evm.run_append_ok hc];exact hf.2.2.2

/-- Insufficient expression horizon is timeout at the original state, not an
arithmetic panic or a transaction rollback theorem. -/
theorem source_uint_fixed_decrement_horizon_two
    {E : Source.Env} {Γ : Source.RCtx} {N : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (y : Source.EMState E Γ) (pre : Bool)
    (root : Source.Idx Γ (.array .memory (.int .u256) (some N))) (index : Source.Idx Γ (.int .u256)) :
    (Source.evalE G Fsrc 2 (sourceUintFixedDecrement pre root index)).run y=(.error .timeout,y) := by
  rfl

/- Expected standard-only axiom set; NOT checked in this RAM draft. -/
/-- info: 'Solidity.Backend.MemoryOps.resolved_uint_fixed_decrement_late_underflow_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_uint_fixed_decrement_late_underflow_word
/-- info: 'Solidity.Backend.MemoryOps.source_uint_fixed_decrement_horizon_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_fixed_decrement_horizon_two
end Solidity.Backend.MemoryOps
