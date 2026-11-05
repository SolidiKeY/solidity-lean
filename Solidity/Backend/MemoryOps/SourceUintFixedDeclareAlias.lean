import Solidity.Backend.MemoryOps.SourceUintFixedAliasProgram
import Solidity.Backend.MemoryOps.SourceUintFixedFuel
import Solidity.Backend.MemoryOps.SourceStructDeclaration

/-! Actual fixed declaration then OLD-local rebinding to the NEW root and reached
mutation/deletion, using existing Source RItems, Prog and published word code. -/
namespace Solidity.Backend.MemoryOps

def sourceUintFixedDeclareAlias {E : Source.Env} {Γ : Source.RCtx} {n : Nat}
    (dst : Source.Idx Γ (.array .memory (.int .u256) (some n))) (si sv : Source.Idx Γ (.int .u256)) :
    Source.RItems E [] false .body Γ ((.array .memory (.int .u256) (some n))::Γ) :=
  .stmt (.declVar (.array .memory (.int .u256) (some n)))
    (sourceUintFixedAliasProgram (.there dst) .here (.there si) (.there sv))
def intrinsicUintFixedDeclareAlias {C : Contract} {Δ : Ctx} {n : Nat}
    (dst : Idx Δ (.mem (.fixed (.prim .uint) n))) (i v : Idx Δ (.val .uint)) :
    Prog C Δ (.mem (.fixed (.prim .uint) n)::Δ) :=
  .cons (.declMem (.fixed (.prim .uint) n) (.user "fixedAliasFresh") none rfl rfl)
    (intrinsicUintFixedAliasProgram (.there dst) .here (.there i) (.there v))

theorem source_uint_fixed_declare_alias_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fsrc : Source.Fr) (y : Source.EMState E Γ) (σ : State C Δ)
    (n : Nat) (hn : 0<n) (sdst : Source.Idx Γ (.array .memory (.int .u256) (some n)))
    (dst : Idx Δ (.mem (.fixed (.prim .uint) n))) (si sv : Source.Idx Γ (.int .u256))
    (i v : Idx Δ (.val .uint)) (k value : PrimTy.uint.Denote)
    (hsi : y.1.get si=sourceUint k) (hsv : y.1.get sv=sourceUint value)
    (hti : TEnv.get i σ.env=k) (htv : TEnv.get v σ.env=value) (hk : k.1.toNat<n)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m)
    (ha : Evm.Memory.Objects.AllocatorRepr σ.heap base frame cursor m)
    (hb : 0<b) (hs : cursor.val+max 1 n<Evm.W) (hcap : b+(Δ.length+1)≤frame) :
    let A := RefTy.fixed (.prim .uint) n
    let SA := Source.STy.array .memory (.int .u256) (some n)
    let g := σ.heap.allocDefault A rfl
    let σd := (σ.adopt g).1.push (t := .mem A) (some g.val)
    let mid : Source.EMState E (SA::Γ) := (.cons (.memRef rfl y.2.heap.next) y.1,
      {y.2 with heap := (y.2.heap.alloc ⟨SA,sourceUintFixedZero n⟩).1})
    let ym : Source.EMState E (SA::Γ) := (mid.1.set (.there sdst) (.memRef rfl y.2.heap.next),mid.2)
    let σa := σd.setLocal (.there dst) (some g.val)
    let ac := Evm.Memory.aliasLocalCode b (.there dst) (.here : Idx (.mem A::Δ) (.mem A))
    let wc := Evm.compileVal b (.simple (.local (.there v)) : Val C (.mem A::Δ) .uint) ++ [.mload (Evm.cellOf b (.there dst : Idx (.mem A::Δ) (.mem A)))] ++
      Evm.compileVal b (.simple (.local (.there i)) : Val C (.mem A::Δ) .uint) ++ Evm.Memory.Objects.writeCode (.fixed : ArrTy A (.prim .uint))
    let dc := Evm.compileVal b (Evm.Memory.deleteDefaultValue .uint : Val C (.mem A::Δ) .uint) ++ [.mload (Evm.cellOf b (.there dst : Idx (.mem A::Δ) (.mem A)))] ++
      Evm.compileVal b (.simple (.local (.there i)) : Val C (.mem A::Δ) .uint) ++ Evm.Memory.Objects.writeCode (.fixed : ArrTy A (.prim .uint))
    let cc := Evm.Memory.Objects.defaultDeclareCode (Γ := Δ) (Evm.Memory.Objects.DefaultBuilder.fixedPrimitive .uint n).code b
    ∃ (base' : Nat → Fin Evm.W) (m0 m1 m2 : Evm.Machine) (out1 out2 : Heap g.H') (z1 z2 : Source.EMState E (SA::Γ)),
      (Source.execS G Fsrc (n+7) Γ.length none (.declVar SA : Source.RStmt E [] false .body Γ (SA::Γ)) y.1).run (.nil,y.2)=
        (.ok (.normal mid.1),(.nil,mid.2)) ∧
      (Source.execItems G Fsrc (n+8) Γ.length none (sourceUintFixedDeclareAlias sdst si sv) y.1).run (.nil,y.2)=
        (.ok (.normal z2.1),(.nil,z2.2)) ∧
      Prog.run σ (intrinsicUintFixedDeclareAlias dst i v)=.ok ⟨σa.withHeap out2,g.ext⟩ ∧
      g.heap.writeAddr (.index g.val .fixed k) value=some out1 ∧ out1.writeAddr (.index g.val .fixed k) (PrimTy.dflt .uint)=some out2 ∧
      SourceUintFixedAt mid y.2.heap.next g.heap g.val ∧ SourceUintFixedAt z1 y.2.heap.next out1 g.val ∧ SourceUintFixedAt z2 y.2.heap.next out2 g.val ∧
      Evm.run cc m=.ok m0 0 ∧ Evm.run (ac ++ wc) m0=.ok m1 0 ∧ Evm.run dc m1=.ok m2 0 ∧
      Evm.run (cc ++ ac ++ wc ++ dc) m=.ok m2 0 ∧
      Evm.Memory.Objects.StateRepr L b frame (F.push (.mem A) .ok) (σa.withHeap out2) base' m2 ∧
      Evm.Memory.Objects.AllocatorRepr out2 base' frame ⟨cursor.val+max 1 n,hs⟩ m2 ∧
      Source.MemOK E SH mid ∧ Source.MemOK E SH z1 ∧ Source.MemOK E SH z2 ∧
      z1.1=ym.1 ∧ z2.1=ym.1 ∧
      z2.1.get (.there sdst)=.memRef rfl y.2.heap.next ∧ z2.1.get .here=.memRef rfl y.2.heap.next ∧
      TEnv.get (.there dst) (σa.withHeap out2).env=some g.val ∧ TEnv.get .here (σa.withHeap out2).env=some g.val ∧
      (∀ {Q : RefTy} (q : HRef σ.H Q),out2.get (q.wk g.ext)=MObj.wk g.ext Q (σ.heap.get q)) ∧
      (∀ address,y.2.heap.get address≠none → z2.2.heap.get address=y.2.heap.get address) ∧
      g.val.id=σ.H.length ∧ (∀ {Q : RefTy} (q : HRef σ.H Q),g.val.id≠(q.wk g.ext).id) ∧
      m2.stack=m.stack ∧ m2.mem 0=Evm.Word.val ⟨cursor.val+max 1 n,hs⟩ ∧
      (∀ address,y.2.heap.get address≠none → z1.2.heap.get address=y.2.heap.get address) ∧
      z2.2.ex=y.2.ex ∧ z2.2.events=y.2.events ∧ z2.2.logs=y.2.logs ∧ z2.2.fnLocals=y.2.fnLocals := by
  dsimp only
  let A := RefTy.fixed (.prim .uint) n
  let SA := Source.STy.array .memory (.int .u256) (some n)
  let g := σ.heap.allocDefault A rfl
  let σd := (σ.adopt g).1.push (t := .mem A) (some g.val)
  let mid : Source.EMState E (SA::Γ) := (.cons (.memRef rfl y.2.heap.next) y.1,
    {y.2 with heap := (y.2.heap.alloc ⟨SA,sourceUintFixedZero n⟩).1})
  let ym : Source.EMState E (SA::Γ) := (mid.1.set (.there sdst) (.memRef rfl y.2.heap.next),mid.2)
  obtain ⟨base',m0,hd0,ht0,hc0,hr0,hmok0,hm0,ha0,hbase,hstack0,hid,hne,hsource⟩ :=
    source_uint_fixed_declaration_word G Fsrc y σ n hn SH hmem hm ha hb hs hcap
  have hi' : TEnv.get (.there i) σd.env=k := by
    change TEnv.get i (TEnv.wk g.ext Δ σ.env)=_
    rw [TEnv.get_wk];exact hti
  have hv' : TEnv.get (.there v) σd.env=value := by
    change TEnv.get v (TEnv.wk g.ext Δ σ.env)=_
    rw [TEnv.get_wk];exact htv
  obtain ⟨out1,out2,z1,z2,m1,m2,hsA,hs1,hs2,hitems,hprog,hw1,hw2,hrA,hr1,hr2,hcA,hc1,hc2,hwhole,hm2,ha2,hmok1,hmok2,hl1,hl2,hrootS,hrootT,hsloc,htloc,hstack,hfree,hobj,haddr,hex,hev,hlog,hfn,hviews,he1,he2,hwrite,hdelete,haddr1,hobj1⟩ :=
    source_uint_fixed_alias_program_word G Fsrc n mid (.there sdst) .here (.there si) (.there sv) y.2.heap.next σd
      (.there dst) .here (.there i) (.there v) g.val k value rfl hsi hsv rfl hi' hv' hr0 hk SH hmok0 hm0 ha0 hb
  have heA := source_local_alias_run G Fsrc (n+3) mid (.there sdst) .here (.memRef rfl y.2.heap.next) rfl
  have hsa := source_expr_statement_run G Fsrc (n+5) Γ.length _ mid ym (.val (.memRef rfl y.2.heap.next)) heA
  have hsw := source_expr_statement_run G Fsrc (n+4) Γ.length _ ym z1 (.val (sourceUint value)) he1
  have hsd := source_expr_statement_run G Fsrc (n+3) Γ.length _ z1 z2 Source.RVal.unit he2
  have hpair := source_items_pair_run G Fsrc n Γ.length _ _ ym z1 z2
    (by simpa only [hl1] using hsw) (by simpa only [hl2,hl1] using hsd)
  have htail := source_items_cons_run G Fsrc (n+6) Γ.length _ _ mid ym z2 hsa hpair
  change (Source.execItems G Fsrc (n+7) Γ.length none (sourceUintFixedAliasProgram (.there sdst) .here (.there si) (.there sv)) mid.1).run (.nil,mid.2)=
    (.ok (.normal z2.1),(.nil,z2.2)) at htail
  let zd : Source.EMState E Γ := (y.1,{y.2 with heap := (y.2.heap.alloc ⟨SA,sourceUintFixedZero n⟩).1})
  have hd := source_decl_statement_run G Fsrc (n+6) Γ.length y zd (.memRef rfl y.2.heap.next)
    (source_uint_fixed_zeroVal_slack y n 3)
  have hitems' : (Source.execItems G Fsrc (n+8) Γ.length none (sourceUintFixedDeclareAlias sdst si sv) y.1).run (.nil,y.2)=
      (.ok (.normal z2.1),(.nil,z2.2)) := by
    rw [sourceUintFixedDeclareAlias,Source.execItems,Source.Hoare.run_bind,hd]
    change (Source.execItems G Fsrc (n+7) Γ.length none (sourceUintFixedAliasProgram (.there sdst) .here (.there si) (.there sv)) mid.1 >>=
      fun o => Source.EM.lift (o.up Γ)).run (.nil,mid.2)=_
    rw [Source.Hoare.run_bind,htail]
    rfl
  have hp : Prog.run σ (intrinsicUintFixedDeclareAlias dst i v)=.ok ⟨(σd.setLocal (.there dst) (some g.val)).withHeap out2,g.ext⟩ := by
    have hd' : Stmt.run σ (.declMem A (.user "fixedAliasFresh") none rfl rfl)=.ok ⟨σd,g.ext⟩ := ht0
    rw [intrinsicUintFixedDeclareAlias,Prog.run_cons_ok hd',hprog]
    rfl
  have hg : Heap.Keeps g.ext σ.heap g.heap := (source_uint_fixed_intrinsic y σ.heap n hn).2.2.1
  refine ⟨base',m0,m1,m2,out1,out2,z1,z2,hd,hitems',hp,hw1,hw2,hr0,hr1,hr2,hc0,?_,hc2,?_,hm2,ha2,hmok0,hmok1,hmok2,hl1,hl2,hrootS,?_,hrootT,?_,?_,?_,hid,hne,hstack.trans hstack0,ha2.free.cell,?_,hex,hev,hlog,hfn⟩
  · rw [Evm.run_append_ok hcA];exact hc1
  · rw [List.append_assoc,List.append_assoc,Evm.run_append_ok hc0]
    exact hwhole
  · rw [hl2];rfl
  · exact TEnv.get_set_ne _ _ _ _ (by simp only [Idx.toNat];omega)
  · intro Q q
    rw [hobj (q.wk g.ext) (hne q)]
    exact hg q
  · intro a ha
    rw [haddr a (Ne.symm (hsource a ha).1),(hsource a ha).2]
  · intro a ha
    rw [haddr1 a (Ne.symm (hsource a ha).1),(hsource a ha).2]

/-- info: 'Solidity.Backend.MemoryOps.source_uint_fixed_declare_alias_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_fixed_declare_alias_word
end Solidity.Backend.MemoryOps
