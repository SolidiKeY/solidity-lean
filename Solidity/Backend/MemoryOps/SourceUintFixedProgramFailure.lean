import Solidity.Backend.MemoryOps.SourceUintFixedProgram

/-! Exact late rejection after real fixed allocation and a successful changed
write. Only the Source outcome retains globals; no suffix heap/rollback claim. -/
namespace Solidity.Backend.MemoryOps

def sourceUintFixedRejectProgram {E : Source.Env} {Γ : Source.RCtx} (n : Nat)
    (si sv sj : Source.Idx Γ (.int .u256)) :
    Source.RItems E [] false .body Γ ((.array .memory (.int .u256) (some n))::Γ) :=
  .stmt (.declVar (.array .memory (.int .u256) (some n)))
    (.stmt (.expr (sourceUintFixedIndexedAssign .here (.there si) (.there sv)))
      (.stmt (.expr (sourceUintFixedIndexedDelete .here (.there sj))) .nil))

def intrinsicUintFixedRejectProgram {C : Contract} {Δ : Ctx} (n : Nat) (i v j : Idx Δ (.val .uint)) :
    Prog C Δ (.mem (.fixed (.prim .uint) n)::Δ) :=
  .cons (.declMem (.fixed (.prim .uint) n) (.user "fixedFresh") none rfl rfl)
    (.cons (.assignMem (.index .fixed (.var .here rfl) (.simple (.local (.there i))))
      (.val (.simple (.local (.there v)))))
      (.cons (.deleteMem (.loc (.index .fixed (.var .here rfl) (.simple (.local (.there j))))) rfl) .nil))

theorem source_uint_fixed_program_reject
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fsrc : Source.Fr) (y : Source.EMState E Γ) (σ : State C Δ)
    (n : Nat) (hn : 0<n) (si sv sj : Source.Idx Γ (.int .u256)) (i v j : Idx Δ (.val .uint))
    (k value l : PrimTy.uint.Denote) (hsi : y.1.get si=sourceUint k) (hsv : y.1.get sv=sourceUint value)
    (hsl : y.1.get sj=sourceUint l) (htj : TEnv.get j σ.env=l) (hl : n≤l.1.toNat)
    (hti : TEnv.get i σ.env=k) (htv : TEnv.get v σ.env=value) (hk : k.1.toNat<n)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m)
    (ha : Evm.Memory.Objects.AllocatorRepr σ.heap base frame cursor m)
    (hb : 0<b) (hs : cursor.val+max 1 n<Evm.W) (hcap : b+(Δ.length+1)≤frame) :
    let A := RefTy.fixed (.prim .uint) n
    let SA := Source.STy.array .memory (.int .u256) (some n)
    let g := σ.heap.allocDefault A rfl
    let σ' := (σ.adopt g).1.push (t := .mem A) (some g.val)
    let mid : Source.EMState E (SA::Γ) := (.cons (.memRef rfl y.2.heap.next) y.1,
      {y.2 with heap := (y.2.heap.alloc ⟨SA,sourceUintFixedZero n⟩).1})
    let writeCode := Evm.compileVal b (.simple (.local (.there v)) : Val C (.mem A::Δ) .uint) ++
      [.mload (Evm.cellOf b (.here : Idx (.mem A::Δ) (.mem A)))] ++
      Evm.compileVal b (.simple (.local (.there i)) : Val C (.mem A::Δ) .uint) ++
      Evm.Memory.Objects.writeCode (.fixed : ArrTy A (.prim .uint))
    let deleteCode := Evm.compileVal b (Evm.Memory.deleteDefaultValue .uint : Val C (.mem A::Δ) .uint) ++
      [.mload (Evm.cellOf b (.here : Idx (.mem A::Δ) (.mem A)))] ++
      Evm.compileVal b (.simple (.local (.there j)) : Val C (.mem A::Δ) .uint) ++
      Evm.Memory.Objects.writeCode (.fixed : ArrTy A (.prim .uint))
    ∃ (base' : Nat → Fin Evm.W) (target0 target1 : Evm.Machine) (out1 : Heap g.H') (z1 : Source.EMState E (SA::Γ)),
      (Source.execS G Fsrc (n+6) Γ.length none (.declVar SA : Source.RStmt E [] false .body Γ (SA::Γ)) y.1).run (.nil,y.2)=
        (.ok (.normal mid.1),(.nil,mid.2)) ∧
      (Source.execS G Fsrc (n+5) Γ.length none (.expr (sourceUintFixedIndexedAssign .here (.there si) (.there sv)) : Source.RStmt E [] false .body (SA::Γ) (SA::Γ)) mid.1).run (.nil,mid.2)=
        (.ok (.normal z1.1),(.nil,z1.2)) ∧
      (Source.evalE G Fsrc (n+3) (sourceUintFixedIndexedDelete .here (.there sj))).run z1=
        (.error (.revert (Source.panicData .index)),z1) ∧
      (Source.execItems G Fsrc (n+7) Γ.length none (sourceUintFixedRejectProgram n si sv sj) y.1).run (.nil,y.2)=
        (.error (.revert (Source.panicData .index)),(.nil,z1.2)) ∧
      Prog.run σ (intrinsicUintFixedRejectProgram n i v j)=.error .revert ∧
      g.heap.writeAddr (.index g.val .fixed k) value=some out1 ∧
      out1.writeAddr (.index g.val .fixed l) (PrimTy.dflt .uint)=none ∧
      SourceUintFixedAt mid y.2.heap.next g.heap g.val ∧ SourceUintFixedAt z1 y.2.heap.next out1 g.val ∧
      Evm.run (Evm.Memory.Objects.defaultDeclareCode (Γ := Δ)
        (Evm.Memory.Objects.DefaultBuilder.fixedPrimitive .uint n).code b) m=.ok target0 0 ∧
      Evm.run writeCode target0=.ok target1 0 ∧ Evm.run deleteCode target1=.revert ∧
      Evm.run (Evm.Memory.Objects.defaultDeclareCode (Γ := Δ)
        (Evm.Memory.Objects.DefaultBuilder.fixedPrimitive .uint n).code b ++ writeCode ++ deleteCode) m=.revert ∧
      Evm.Memory.Objects.StateRepr L b frame (F.push (.mem A) .ok) (σ'.withHeap out1) base' target1 ∧
      Evm.Memory.Objects.AllocatorRepr out1 base' frame ⟨cursor.val+max 1 n,hs⟩ target1 ∧
      Source.MemOK E SH z1 ∧ z1.1=mid.1 ∧ target1.stack=m.stack ∧
      (∀ {Q : RefTy} (q : HRef σ.H Q),out1.get (q.wk g.ext)=g.heap.get (q.wk g.ext)) ∧
      (∀ address,address≠y.2.heap.next → z1.2.heap.get address=mid.2.heap.get address) ∧
      z1.2.ex=y.2.ex ∧ z1.2.events=y.2.events ∧ z1.2.logs=y.2.logs ∧ z1.2.fnLocals=y.2.fnLocals := by
  dsimp only
  let A := RefTy.fixed (.prim .uint) n
  let SA := Source.STy.array .memory (.int .u256) (some n)
  let g := σ.heap.allocDefault A rfl
  let σ' := (σ.adopt g).1.push (t := .mem A) (some g.val)
  let mid : Source.EMState E (SA::Γ) := (.cons (.memRef rfl y.2.heap.next) y.1,
    {y.2 with heap := (y.2.heap.alloc ⟨SA,sourceUintFixedZero n⟩).1})
  obtain ⟨base',target0,hdMinimal,hti0,hcode0,hr,hmok,hm0,ha0,hbase,hstack0,hid,hne,hsource⟩ :=
    source_uint_fixed_declaration_word G Fsrc y σ n hn SH hmem hm ha hb hs hcap
  let z0 : Source.EMState E Γ := (y.1,{y.2 with heap := (y.2.heap.alloc ⟨SA,sourceUintFixedZero n⟩).1})
  have hzero : (Source.zeroVal (E := E) (Γ := Γ) (n+5) SA).run y=(.ok (.memRef rfl y.2.heap.next),z0) :=
    source_uint_fixed_zeroVal_slack y n 2
  have hd := source_decl_statement_run G Fsrc (n+5) Γ.length y z0 (.memRef rfl y.2.heap.next) hzero
  have hj : TEnv.get (.there j) σ'.env=l := by
    change TEnv.get j (TEnv.wk g.ext Δ σ.env)=_
    rw [TEnv.get_wk];exact htj
  have hi : TEnv.get (.there i) σ'.env=k := by
    change TEnv.get i (TEnv.wk g.ext Δ σ.env)=_
    rw [TEnv.get_wk];exact hti
  have hv : TEnv.get (.there v) σ'.env=value := by
    change TEnv.get v (TEnv.wk g.ext Δ σ.env)=_
    rw [TEnv.get_wk];exact htv
  obtain ⟨out1,z1,target1,hw1,hs1,he1,hstmt1,ht1,hc1,hr1,hm1,hmok1,hl1,hstack1,ha1⟩ :=
    resolved_uint_fixed_assign_word G Fsrc (n+1) σ' g.val hr .here (.there si) (.there sv) .here (.there i) (.there v)
      k value rfl hsi hsv rfl hi hv hk hm0 SH hmok
  have hsroot1 : z1.1.get .here=.memRef rfl y.2.heap.next := by rw [hl1];rfl
  have hsl1 : z1.1.get (.there sj)=sourceUint l := by rw [hl1];exact hsl
  have hbnd := resolved_uint_fixed_delete_word_bounds G Fsrc n (σ'.withHeap out1) g.val hr1
    .here (.there sj) .here (.there j) l hsroot1 hsl1 rfl hj hl hm1
  have hnone := (hr1.delete_bounds Fsrc (n+1) l hl).2
  have hj' : TEnv.get (.there j) (σ'.withHeap out1).env=l := hj
  have hnone' : (σ'.withHeap out1).heap.writeAddr (.index g.val .fixed l) (PrimTy.dflt .uint)=none := hnone
  have hlast : Stmt.run (σ'.withHeap out1)
      (.deleteMem (.loc (.index .fixed (.var .here rfl) (.simple (.local (.there j))))) rfl)=.error .revert := by
    change TRun.deleteMem (.loc (.index .fixed (.var .here rfl) (.simple (.local (.there j))))) (σ'.withHeap out1)=_
    simp only [TRun.deleteMem,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,
      show TEnv.get (.here : Idx (.mem A::Δ) (.mem A)) (σ'.withHeap out1).env=some g.val from rfl,
      hj',TRun.clearT,hnone',bind,Except.bind,pure,Except.pure,TRes.ofOpt]
  have hs1' := source_expr_statement_run G Fsrc (n+4) Γ.length _ mid z1 (.val (sourceUint value)) he1
  have hs2' := source_expr_statement_error G Fsrc (n+3) Γ.length
    (sourceUintFixedIndexedDelete .here (.there sj)) z1 z1 _ hbnd.1
  have htail := source_items_pair_error G Fsrc n Γ.length
    (.expr (sourceUintFixedIndexedAssign .here (.there si) (.there sv)))
    (.expr (sourceUintFixedIndexedDelete .here (.there sj))) mid z1 z1 _ hs1' hs2'
  have hitems : (Source.execItems G Fsrc (n+7) Γ.length none (sourceUintFixedRejectProgram n si sv sj) y.1).run (.nil,y.2)=
      (.error (.revert (Source.panicData .index)),(.nil,z1.2)) := by
    rw [sourceUintFixedRejectProgram,Source.execItems,Source.Hoare.run_bind,hd]
    change (Source.execItems G Fsrc (n+6) Γ.length none
      (.stmt (.expr (sourceUintFixedIndexedAssign .here (.there si) (.there sv)))
        (.stmt (.expr (sourceUintFixedIndexedDelete .here (.there sj))) .nil)) mid.1 >>=
      fun o => Source.EM.lift (o.up Γ)).run (.nil,mid.2)=_
    rw [Source.Hoare.run_bind,htail]
  have hp : Prog.run σ (intrinsicUintFixedRejectProgram n i v j)=.error .revert := by
    have hd' : Stmt.run σ (.declMem A (.user "fixedFresh") none rfl rfl)=.ok ⟨σ',g.ext⟩ := hti0
    have hpair := intrinsic_heap_pair_error σ' _ _ out1 .revert ht1 hlast
    rw [intrinsicUintFixedRejectProgram,Prog.run_cons_ok hd',hpair]
    rfl
  have hf1 := hr.write_frames Fsrc (n+3) k value hk hw1 hs1
  refine ⟨base',target0,target1,out1,z1,hd,hs1',hbnd.1,hitems,hp,hw1,hnone,hr,hr1,hcode0,hc1,hbnd.2,?_,
    hm1,ha1 _ hb ha0,hmok1,hl1,hstack1.trans hstack0,?_,hf1.2.2.1,hf1.2.2.2.1,hf1.2.2.2.2.1,hf1.2.2.2.2.2.1,hf1.2.2.2.2.2.2⟩
  · rw [List.append_assoc,Evm.run_append_ok hcode0,Evm.run_append_ok hc1,hbnd.2]
  · intro Q q
    exact hf1.2.1 (q.wk g.ext) (hne q)

/-- info: 'Solidity.Backend.MemoryOps.source_uint_fixed_program_reject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_fixed_program_reject
end Solidity.Backend.MemoryOps
