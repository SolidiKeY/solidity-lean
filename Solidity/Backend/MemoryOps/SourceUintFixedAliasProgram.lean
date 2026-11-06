import Solidity.Backend.MemoryOps.SourceUintFixedAlias

/-! Rebinding selects the SAME represented fixed reference, then actual reached
writes/deletes consume it. Existing Source RItems, Prog and word code only. -/
namespace Solidity.Backend.MemoryOps

def sourceUintFixedAliasProgram {E : Source.Env} {Γ : Source.RCtx} {n : Nat}
    (dst src : Source.Idx Γ (.array .memory (.int .u256) (some n)))
    (si sv : Source.Idx Γ (.int .u256)) : Source.RItems E [] false .body Γ Γ :=
  .stmt (.expr (sourceLocalAlias dst src))
    (.stmt (.expr (sourceUintFixedIndexedAssign dst si sv))
      (.stmt (.expr (sourceUintFixedIndexedDelete dst si)) .nil))

def intrinsicUintFixedAliasProgram {C : Contract} {Δ : Ctx} {n : Nat}
    (dst src : Idx Δ (.mem (.fixed (.prim .uint) n))) (i v : Idx Δ (.val .uint)) : Prog C Δ Δ :=
  .cons (.rebindMem dst (.alias (.var src rfl)))
    (.cons (.assignMem (.index .fixed (.var dst rfl) (.simple (.local i))) (.val (.simple (.local v))))
      (.cons (.deleteMem (.loc (.index .fixed (.var dst rfl) (.simple (.local i)))) rfl) .nil))

theorem source_uint_fixed_alias_program_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx} {n : Nat}
    (G : Source.Glob E) (Fsrc : Source.Fr) (horizon : Nat) (y : Source.EMState E Γ)
    (sdst ssrc : Source.Idx Γ (.array .memory (.int .u256) (some n)))
    (si sv : Source.Idx Γ (.int .u256)) (address : Nat) (σ : State C Δ)
    (dst src : Idx Δ (.mem (.fixed (.prim .uint) n))) (i v : Idx Δ (.val .uint))
    (r : HRef σ.H (.fixed (.prim .uint) n)) (k value : PrimTy.uint.Denote)
    (hsrc : y.1.get ssrc=.memRef rfl address) (hsi : y.1.get si=sourceUint k) (hsv : y.1.get sv=sourceUint value)
    (htsrc : TEnv.get src σ.env=some r) (hti : TEnv.get i σ.env=k) (htv : TEnv.get v σ.env=value)
    (hr : SourceUintFixedAt y address σ.heap r) (hk : k.1.toNat<n) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m)
    (ha : Evm.Memory.Objects.AllocatorRepr σ.heap base frame cursor m) (hb : 0<b) :
    let ym : Source.EMState E Γ := (y.1.set sdst (.memRef rfl address),y.2)
    let σm := σ.setLocal dst (some r)
    let mm := Evm.Memory.writeMachine m (Evm.cellOf b dst) (.val (base r.id))
    let wc := Evm.compileVal b (.simple (.local v) : Val C Δ .uint) ++ [.mload (Evm.cellOf b dst)] ++
      Evm.compileVal b (.simple (.local i) : Val C Δ .uint) ++ Evm.Memory.Objects.writeCode (.fixed : ArrTy (.fixed (.prim .uint) n) (.prim .uint))
    let dc := Evm.compileVal b (Evm.Memory.deleteDefaultValue .uint : Val C Δ .uint) ++ [.mload (Evm.cellOf b dst)] ++
      Evm.compileVal b (.simple (.local i) : Val C Δ .uint) ++ Evm.Memory.Objects.writeCode (.fixed : ArrTy (.fixed (.prim .uint) n) (.prim .uint))
    ∃ (out1 out2 : Heap σ.H) (z1 z2 : Source.EMState E Γ) (target1 target2 : Evm.Machine),
      (Source.execS G Fsrc (horizon+6) Γ.length none (.expr (sourceLocalAlias sdst ssrc) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execS G Fsrc (horizon+5) Γ.length none (.expr (sourceUintFixedIndexedAssign sdst si sv) : Source.RStmt E [] false .body Γ Γ) ym.1).run (.nil,ym.2)=
        (.ok (.normal z1.1),(.nil,z1.2)) ∧
      (Source.execS G Fsrc (horizon+4) Γ.length none (.expr (sourceUintFixedIndexedDelete sdst si) : Source.RStmt E [] false .body Γ Γ) z1.1).run (.nil,z1.2)=
        (.ok (.normal z2.1),(.nil,z2.2)) ∧
      (Source.execItems G Fsrc (horizon+7) Γ.length none (sourceUintFixedAliasProgram sdst ssrc si sv) y.1).run (.nil,y.2)=
        (.ok (.normal z2.1),(.nil,z2.2)) ∧
      Prog.run σ (intrinsicUintFixedAliasProgram dst src i v)=.ok ⟨σm.withHeap out2,List.prefix_refl _⟩ ∧
      σ.heap.writeAddr (.index r .fixed k) value=some out1 ∧ out1.writeAddr (.index r .fixed k) (PrimTy.dflt .uint)=some out2 ∧
      SourceUintFixedAt ym address σm.heap r ∧ SourceUintFixedAt z1 address out1 r ∧ SourceUintFixedAt z2 address out2 r ∧
      Evm.run (Evm.Memory.aliasLocalCode b dst src) m=.ok mm 0 ∧ Evm.run wc mm=.ok target1 0 ∧ Evm.run dc target1=.ok target2 0 ∧
      Evm.run (Evm.Memory.aliasLocalCode b dst src ++ wc ++ dc) m=.ok target2 0 ∧
      Evm.Memory.Objects.StateRepr L b frame F (σm.withHeap out2) base target2 ∧
      Evm.Memory.Objects.AllocatorRepr out2 base frame cursor target2 ∧
      Source.MemOK E SH z1 ∧ Source.MemOK E SH z2 ∧ z1.1=ym.1 ∧ z2.1=ym.1 ∧
      z2.1.get sdst=.memRef rfl address ∧ TEnv.get dst (σm.withHeap out2).env=some r ∧
      (∀ {τ : Source.STy} (q : Source.Idx Γ τ),sdst.toNat≠q.toNat → z2.1.get q=y.1.get q) ∧
      (∀ {t : LTy} (q : Idx Δ t),dst.toNat≠q.toNat → TEnv.get q (σm.withHeap out2).env=TEnv.get q σ.env) ∧
      target2.stack=m.stack ∧ target2.mem 0=m.mem 0 ∧
      (∀ {Q : RefTy} (q : HRef σ.H Q),r.id≠q.id → out2.get q=σ.heap.get q) ∧
      (∀ a,a≠address → z2.2.heap.get a=y.2.heap.get a) ∧
      z2.2.ex=y.2.ex ∧ z2.2.events=y.2.events ∧ z2.2.logs=y.2.logs ∧ z2.2.fnLocals=y.2.fnLocals ∧
      (∀ {N : Nat} (q : HRef σ.H (.fixed (.prim .uint) N)) (a : Nat),r.id≠q.id → a≠address →
        SourceUintFixedAt y a σ.heap q → SourceUintFixedAt z2 a out2 q) ∧
      (Source.evalE G Fsrc (horizon+4) (sourceUintFixedIndexedAssign sdst si sv)).run ym=(.ok (.val (sourceUint value)),z1) ∧
      (Source.evalE G Fsrc (horizon+3) (sourceUintFixedIndexedDelete sdst si)).run z1=(.ok Source.RVal.unit,z2) ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (horizon+3) (.mem address k.1.toNat) (sourceUint value)).run ym=(.ok (),z1) ∧
      (Source.deleteLoc (E := E) (Γ := Γ) Fsrc (horizon+2) (τ := .int .u256) (.mem address k.1.toNat)).run z1=(.ok (),z2) ∧
      (∀ a,a≠address → z1.2.heap.get a=y.2.heap.get a) ∧
      (∀ {Q : RefTy} (q : HRef σ.H Q),r.id≠q.id → out1.get q=σ.heap.get q) := by
  dsimp only
  let ym : Source.EMState E Γ := (y.1.set sdst (.memRef rfl address),y.2)
  let σm := σ.setLocal dst (some r)
  obtain ⟨heA,hsA,hiA,hcA,hrA,hmokA,hmA,haA,keepA,hrootS,hrootT,hglob,hheap,hstackA,hfree,hsloc,htloc,hhp,hhS⟩ :=
    source_uint_fixed_alias_word G Fsrc (horizon+3) y sdst ssrc address hsrc SH hmem σ dst src r htsrc hr hm ha hb
  have hsi' : ym.1.get si=sourceUint k := (fixed_alias_scalar_frames y sdst si address σ dst i r).1.trans hsi
  have hsv' : ym.1.get sv=sourceUint value := (fixed_alias_scalar_frames y sdst sv address σ dst v r).1.trans hsv
  have hti' : TEnv.get i σm.env=k := (fixed_alias_scalar_frames y sdst si address σ dst i r).2.trans hti
  have htv' : TEnv.get v σm.env=value := (fixed_alias_scalar_frames y sdst sv address σ dst v r).2.trans htv
  obtain ⟨out1,z1,target1,hw1,hs1,he1,hstmt1,hi1,hc1,hr1,hm1,hmok1,hl1,hstack1,keep1⟩ :=
    resolved_uint_fixed_assign_word G Fsrc (horizon+1) σm r hrA sdst si sv dst i v k value hrootS hsi' hsv' hrootT hti' htv' hk hmA SH hmokA
  obtain ⟨out2,z2,target2,hw2,hs2,he2,hstmt2,hi2,hc2,hr2,hm2,hmok2,hl2,hstack2,keep2⟩ :=
    resolved_uint_fixed_delete_word G Fsrc horizon (σm.withHeap out1) r hr1 sdst si dst i k
      (by rw [hl1];exact hrootS) (by rw [hl1];exact hsi') hrootT hti' hk hm1 SH hmok1
  have hs1' : (Source.execS G Fsrc (horizon+5) Γ.length none (.expr (sourceUintFixedIndexedAssign sdst si sv) : Source.RStmt E [] false .body Γ Γ) ym.1).run (.nil,ym.2)=
      (.ok (.normal z1.1),(.nil,z1.2)) := by simpa only [hl1] using hstmt1
  have hs2' : (Source.execS G Fsrc (horizon+4) Γ.length none (.expr (sourceUintFixedIndexedDelete sdst si) : Source.RStmt E [] false .body Γ Γ) z1.1).run (.nil,z1.2)=
      (.ok (.normal z2.1),(.nil,z2.2)) := by simpa only [hl2] using hstmt2
  have htail := source_items_pair_run G Fsrc horizon Γ.length _ _ ym z1 z2 hs1' hs2'
  have hitems := source_items_cons_run G Fsrc (horizon+6) Γ.length _ _ y ym z2 hsA htail
  have hpair := intrinsic_heap_pair_run σm _ _ out1 out2 hi1 hi2
  have hp : Prog.run σ (intrinsicUintFixedAliasProgram dst src i v)=.ok ⟨σm.withHeap out2,List.prefix_refl _⟩ := by
    rw [intrinsicUintFixedAliasProgram,Prog.run_cons_ok hiA,hpair]
    rfl
  have ha2 := keep2 cursor hb (keep1 cursor hb haA)
  have hf1 := hrA.write_frames Fsrc (horizon+3) k value hk hw1 hs1
  have hf2 := hr1.write_frames Fsrc (horizon+2) k (PrimTy.dflt .uint) hk hw2 hs2
  have hobj : ∀ {Q : RefTy} (q : HRef σ.H Q),r.id≠q.id → out2.get q=σ.heap.get q := by
    intro Q q hn
    rw [hf2.2.1 q hn,hf1.2.1 q hn]
    rfl
  have haddr : ∀ a,a≠address → z2.2.heap.get a=y.2.heap.get a := by
    intro a hn
    rw [hf2.2.2.1 a hn,hf1.2.2.1 a hn]
  refine ⟨out1,out2,z1,z2,target1,target2,hsA,hs1',hs2',hitems,hp,hw1,hw2,hrA,hr1,hr2,hcA,hc1,hc2,?_,hm2,ha2,
    hmok1,hmok2,hl1,hl2.trans hl1,?_,hrootT,?_,htloc,hstack2.trans (hstack1.trans hstackA),ha2.free.cell.trans ha.free.cell.symm,
    hobj,haddr,hf2.2.2.2.1.trans hf1.2.2.2.1,hf2.2.2.2.2.1.trans hf1.2.2.2.2.1,
    hf2.2.2.2.2.2.1.trans hf1.2.2.2.2.2.1,hf2.2.2.2.2.2.2.trans hf1.2.2.2.2.2.2,?_,he1,he2,hs1,hs2,hf1.2.2.1,?_⟩
  · rw [List.append_assoc,Evm.run_append_ok hcA,Evm.run_append_ok hc1,hc2]
  · rw [hl2,hl1];exact hrootS
  · intro τ q hn
    rw [hl2,hl1];exact hsloc q hn
  · intro N q a hq ha hrep
    unfold SourceUintFixedAt at hrep ⊢
    rw [haddr a ha,hobj q hq]
    exact hrep
  · intro Q q hn
    exact hf1.2.1 q hn

/-- info: 'Solidity.Backend.MemoryOps.source_uint_fixed_alias_program_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_fixed_alias_program_word
end Solidity.Backend.MemoryOps
