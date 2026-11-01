import Solidity.Backend.MemoryOps.SourceUintFixedCompoundSequence
import Solidity.Backend.MemoryOps.SourceUintFixedFuel
import Solidity.Backend.MemoryOps.SourceStructDeclaration

/-! Real fixed declaration, OLD-local rebinding to the NEW root, then two
reached compound writes. Ordinary Source Items, intrinsic Prog and word append;
no new evaluator. Positive Source admission and constructor space stay explicit. -/
namespace Solidity.Backend.MemoryOps

def sourceUintFixedDeclareCompound {E : Source.Env} {Γ : Source.RCtx} {n : Nat}
    (dst : Source.Idx Γ (.array .memory (.int .u256) (some n))) (si sv : Source.Idx Γ (.int .u256)) :
    Source.RItems E [] false .body Γ ((.array .memory (.int .u256) (some n))::Γ) :=
  .stmt (.declVar (.array .memory (.int .u256) (some n)))
    (.stmt (.expr (sourceLocalAlias (.there dst) .here))
      (sourceUintFixedAddTwice (.there dst) (.there si) (.there sv)))
def intrinsicUintFixedDeclareCompound {C : Contract} {Δ : Ctx} {n : Nat}
    (dst : Idx Δ (.mem (.fixed (.prim .uint) n))) (i v : Idx Δ (.val .uint)) :
    Prog C Δ (.mem (.fixed (.prim .uint) n)::Δ) :=
  .cons (.declMem (.fixed (.prim .uint) n) (.user "fixedCompoundAliasFresh") none rfl rfl)
    (.cons (.rebindMem (.there dst) (.alias (.var .here rfl)))
      (intrinsicUintFixedAddTwice (.there dst) (.there i) (.there v)))

/-- INITIAL scalar/range/allocator facts derive the actual declaration, alias and
both reached writes. No initial pointer alignment is needed for the overwritten
OLD local. Its other aliases retain their old identities and contents. -/
theorem source_uint_fixed_declare_compound_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fsrc : Source.Fr) (y : Source.EMState E Γ) (σ : State C Δ)
    (n : Nat) (hn : 0<n) (sdst : Source.Idx Γ (.array .memory (.int .u256) (some n)))
    (dst : Idx Δ (.mem (.fixed (.prim .uint) n))) (si sv : Source.Idx Γ (.int .u256))
    (i v : Idx Δ (.val .uint)) (k value : PrimTy.uint.Denote)
    (hsi : y.1.get si=sourceUint k) (hsv : y.1.get sv=sourceUint value)
    (hti : TEnv.get i σ.env=k) (htv : TEnv.get v σ.env=value) (hk : k.1.toNat<n)
    (hdouble : PrimTy.uint.inRange (value.1+value.1)=true)
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
    let wc := fixedUintAddCode (C := C) (Γ := .mem A::Δ) b (.there dst) (.there i) (.there v)
    let cc := Evm.Memory.Objects.defaultDeclareCode (Γ := Δ) (Evm.Memory.Objects.DefaultBuilder.fixedPrimitive .uint n).code b
    let twice : PrimTy.uint.Denote := ⟨value.1+value.1,hdouble⟩
    ∃ (base' : Nat → Fin Evm.W) (m0 ma m1 m2 : Evm.Machine) (out1 out2 : Heap g.H') (z1 z2 : Source.EMState E (SA::Γ)),
      (Source.execS G Fsrc (n+7) Γ.length none (.declVar SA : Source.RStmt E [] false .body Γ (SA::Γ)) y.1).run (.nil,y.2)=
        (.ok (.normal mid.1),(.nil,mid.2)) ∧
      (Source.execS G Fsrc (n+6) Γ.length none (.expr (sourceLocalAlias (.there sdst) .here) : Source.RStmt E [] false .body (SA::Γ) (SA::Γ)) mid.1).run (.nil,mid.2)=
        (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execItems G Fsrc (n+8) Γ.length none (sourceUintFixedDeclareCompound sdst si sv) y.1).run (.nil,y.2)=
        (.ok (.normal z2.1),(.nil,z2.2)) ∧
      Prog.run σ (intrinsicUintFixedDeclareCompound dst i v)=.ok ⟨σa.withHeap out2,g.ext⟩ ∧
      g.heap.writeAddr (.index g.val .fixed k) value=some out1 ∧ out1.writeAddr (.index g.val .fixed k) twice=some out2 ∧
      (Source.evalE G Fsrc (n+4) (sourceUintFixedIndexedAdd (.there sdst) (.there si) (.there sv))).run ym=(.ok (.val (sourceUint value)),z1) ∧
      (Source.evalE G Fsrc (n+3) (sourceUintFixedIndexedAdd (.there sdst) (.there si) (.there sv))).run z1=(.ok (.val (sourceUint twice)),z2) ∧
      SourceUintFixedAt mid y.2.heap.next g.heap g.val ∧ SourceUintFixedAt z1 y.2.heap.next out1 g.val ∧ SourceUintFixedAt z2 y.2.heap.next out2 g.val ∧
      Evm.run cc m=.ok m0 0 ∧ Evm.run ac m0=.ok ma 0 ∧ Evm.run wc ma=.ok m1 0 ∧ Evm.run wc m1=.ok m2 0 ∧
      Evm.run (cc ++ ac ++ wc ++ wc) m=.ok m2 0 ∧
      Evm.Memory.Objects.StateRepr L b frame (F.push (.mem A) .ok) (σa.withHeap out2) base' m2 ∧
      Evm.Memory.Objects.AllocatorRepr out2 base' frame ⟨cursor.val+max 1 n,hs⟩ m2 ∧
      Source.MemOK E SH mid ∧ Source.MemOK E SH z1 ∧ Source.MemOK E SH z2 ∧
      z1.1=ym.1 ∧ z2.1=ym.1 ∧ z2.1.get (.there sdst)=.memRef rfl y.2.heap.next ∧ z2.1.get .here=.memRef rfl y.2.heap.next ∧
      TEnv.get (.there dst) (σa.withHeap out2).env=some g.val ∧ TEnv.get .here (σa.withHeap out2).env=some g.val ∧
      (∀ {τ : Source.STy} (q : Source.Idx Γ τ),sdst.toNat≠q.toNat → z2.1.get (.there q)=y.1.get q) ∧
      (∀ {t : LTy} (q : Idx Δ t),dst.toNat≠q.toNat → TEnv.get (.there q) (σa.withHeap out2).env=TEnv.get q (TEnv.wk g.ext Δ σ.env)) ∧
      (∀ {Q : RefTy} (q : HRef σ.H Q),out2.get (q.wk g.ext)=MObj.wk g.ext Q (σ.heap.get q)) ∧
      (∀ a,y.2.heap.get a≠none → z2.2.heap.get a=y.2.heap.get a) ∧
      g.val.id=σ.H.length ∧ (∀ {Q : RefTy} (q : HRef σ.H Q),g.val.id≠(q.wk g.ext).id) ∧
      m2.stack=m.stack ∧ m2.mem 0=Evm.Word.val ⟨cursor.val+max 1 n,hs⟩ ∧
      (∀ a,y.2.heap.get a≠none → z1.2.heap.get a=y.2.heap.get a) ∧
      z2.2.ex=y.2.ex ∧ z2.2.events=y.2.events ∧ z2.2.logs=y.2.logs ∧ z2.2.fnLocals=y.2.fnLocals := by
  dsimp only
  let A := RefTy.fixed (.prim .uint) n
  let SA := Source.STy.array .memory (.int .u256) (some n)
  let g := σ.heap.allocDefault A rfl
  let σd := (σ.adopt g).1.push (t := .mem A) (some g.val)
  let mid : Source.EMState E (SA::Γ) := (.cons (.memRef rfl y.2.heap.next) y.1,
    {y.2 with heap := (y.2.heap.alloc ⟨SA,sourceUintFixedZero n⟩).1})
  let ym : Source.EMState E (SA::Γ) := (mid.1.set (.there sdst) (.memRef rfl y.2.heap.next),mid.2)
  let σa := σd.setLocal (.there dst) (some g.val)
  obtain ⟨base',m0,hd0,ht0,hc0,hr0,hmok0,hm0,ha0,hbase,hstack0,hid,hne,hsource⟩ :=
    source_uint_fixed_declaration_word G Fsrc y σ n hn SH hmem hm ha hb hs hcap
  have hi' : TEnv.get (.there i) σd.env=k := by
    change TEnv.get i (TEnv.wk g.ext Δ σ.env)=_
    rw [TEnv.get_wk];exact hti
  have hv' : TEnv.get (.there v) σd.env=value := by
    change TEnv.get v (TEnv.wk g.ext Δ σ.env)=_
    rw [TEnv.get_wk];exact htv
  obtain ⟨heA,hsA,hiA,hcA,hrA,hmokA,hmA,haA,keepA,hrootS,hrootT,hglob,hheap,hstackA,hfree,hsloc,htloc,hhp,hhS⟩ :=
    source_uint_fixed_alias_word G Fsrc (n+3) mid (.there sdst) .here y.2.heap.next rfl SH hmok0 σd (.there dst) .here g.val rfl hr0 hm0 ha0 hb
  have his : ym.1.get (.there si)=sourceUint k := (fixed_alias_scalar_frames mid (.there sdst) (.there si) y.2.heap.next σd (.there dst) (.there i) g.val).1.trans hsi
  have hvs : ym.1.get (.there sv)=sourceUint value := (fixed_alias_scalar_frames mid (.there sdst) (.there sv) y.2.heap.next σd (.there dst) (.there v) g.val).1.trans hsv
  have hit : TEnv.get (.there i) σa.env=k := (fixed_alias_scalar_frames mid (.there sdst) (.there si) y.2.heap.next σd (.there dst) (.there i) g.val).2.trans hi'
  have hvt : TEnv.get (.there v) σa.env=value := (fixed_alias_scalar_frames mid (.there sdst) (.there sv) y.2.heap.next σd (.there dst) (.there v) g.val).2.trans hv'
  have hz := (source_uint_fixed_intrinsic y σ.heap n hn).2.1
  change MObj.elems .fixed (g.heap.get g.val)=List.replicate n (PrimTy.dflt .uint) at hz
  have hbound : k.1.toNat<g.heap.len g.val .fixed := by
    change k.1.toNat<(MObj.elems .fixed (g.heap.get g.val)).length
    rw [hz,List.length_replicate];exact hk
  have hold : (MObj.elems .fixed (g.heap.get g.val))[k.1.toNat]=PrimTy.dflt .uint :=
    Option.some.inj ((List.getElem?_eq_getElem hbound).symm.trans (by rw [hz];exact List.getElem?_replicate_of_lt hk))
  have hadd : PrimTy.uint.inRange ((MObj.elems .fixed (σa.heap.get g.val))[k.1.toNat].1+value.1)=true := by
    change PrimTy.uint.inRange ((MObj.elems .fixed (g.heap.get g.val))[k.1.toNat].1+value.1)=true
    rw [hold];simpa only [PrimTy.dflt,Int.zero_add] using value.2
  have htwo : PrimTy.uint.inRange (((MObj.elems .fixed (σa.heap.get g.val))[k.1.toNat].1+value.1)+value.1)=true := by
    change PrimTy.uint.inRange (((MObj.elems .fixed (g.heap.get g.val))[k.1.toNat].1+value.1)+value.1)=true
    rw [hold];simpa only [PrimTy.dflt,Int.zero_add] using hdouble
  obtain ⟨out1,out2,z1,z2,m1,m2,he1,he2,hitems,hprog,hw1,hw2,hc1,hc2,hwhole,hr1,hr2,hm2,ha2,hmok1,hmok2,hl1,hl2,hstack,hfree2,hobj,haddr,hex,hev,hlog,hfn,haddr1⟩ :=
    resolved_uint_fixed_add_twice_word G Fsrc n Γ.length σa g.val hrA (.there sdst) (.there si) (.there sv)
      (.there dst) (.there i) (.there v) k value hrootS his hvs hrootT hit hvt hbound hadd htwo SH hmokA hmA haA hb
  have hone : (⟨(MObj.elems .fixed (σa.heap.get g.val))[k.1.toNat].1+value.1,hadd⟩ : PrimTy.uint.Denote)=value := by
    apply Subtype.ext
    change (MObj.elems .fixed (g.heap.get g.val))[k.1.toNat].1+value.1=value.1
    rw [hold];simp only [PrimTy.dflt,Int.zero_add]
  have hsecond : (⟨((MObj.elems .fixed (σa.heap.get g.val))[k.1.toNat].1+value.1)+value.1,htwo⟩ : PrimTy.uint.Denote)=⟨value.1+value.1,hdouble⟩ := by
    apply Subtype.ext
    change ((MObj.elems .fixed (g.heap.get g.val))[k.1.toNat].1+value.1)+value.1=value.1+value.1
    rw [hold];simp only [PrimTy.dflt,Int.zero_add]
  rw [hone] at hw1 he1
  rw [hsecond] at hw2 he2
  have hsa := source_expr_statement_run G Fsrc (n+5) Γ.length _ mid ym (.val (.memRef rfl y.2.heap.next)) heA
  have htail := source_items_cons_run G Fsrc (n+6) Γ.length _ _ mid ym z2 hsa hitems
  let zd : Source.EMState E Γ := (y.1,{y.2 with heap := (y.2.heap.alloc ⟨SA,sourceUintFixedZero n⟩).1})
  have hd := source_decl_statement_run G Fsrc (n+6) Γ.length y zd (.memRef rfl y.2.heap.next) (source_uint_fixed_zeroVal_slack y n 3)
  have hsrc : (Source.execItems G Fsrc (n+8) Γ.length none (sourceUintFixedDeclareCompound sdst si sv) y.1).run (.nil,y.2)=
      (.ok (.normal z2.1),(.nil,z2.2)) := by
    rw [sourceUintFixedDeclareCompound,Source.execItems,Source.Hoare.run_bind,hd]
    change (Source.execItems G Fsrc (n+7) Γ.length none (.stmt (.expr (sourceLocalAlias (.there sdst) .here)) (sourceUintFixedAddTwice (.there sdst) (.there si) (.there sv))) mid.1 >>= fun o => Source.EM.lift (o.up Γ)).run (.nil,mid.2)=_
    rw [Source.Hoare.run_bind,htail];rfl
  have hp : Prog.run σ (intrinsicUintFixedDeclareCompound dst i v)=.ok ⟨σa.withHeap out2,g.ext⟩ := by
    have hd' : Stmt.run σ (.declMem A (.user "fixedCompoundAliasFresh") none rfl rfl)=.ok ⟨σd,g.ext⟩ := ht0
    rw [intrinsicUintFixedDeclareCompound,Prog.run_cons_ok hd']
    change Except.map _ (Prog.run σd (.cons (.rebindMem (.there dst) (.alias (.var .here rfl))) (intrinsicUintFixedAddTwice (.there dst) (.there i) (.there v))))=_
    rw [Prog.run_cons_ok hiA,hprog];rfl
  have hg : Heap.Keeps g.ext σ.heap g.heap := (source_uint_fixed_intrinsic y σ.heap n hn).2.2.1
  have hword : Evm.run (Evm.Memory.Objects.defaultDeclareCode (Γ := Δ) (Evm.Memory.Objects.DefaultBuilder.fixedPrimitive .uint n).code b ++ Evm.Memory.aliasLocalCode b (.there dst) (.here : Idx (.mem A::Δ) (.mem A)) ++ fixedUintAddCode (C := C) (Γ := .mem A::Δ) b (.there dst) (.there i) (.there v) ++ fixedUintAddCode (C := C) (Γ := .mem A::Δ) b (.there dst) (.there i) (.there v)) m=.ok m2 0 := by
    rw [List.append_assoc,List.append_assoc,Evm.run_append_ok hc0,Evm.run_append_ok hcA];exact hwhole
  have hnewS : z2.1.get .here=.memRef rfl y.2.heap.next := by rw [hl2];rfl
  have hdstS : z2.1.get (.there sdst)=.memRef rfl y.2.heap.next := by rw [hl2];exact hrootS
  have hnewT : TEnv.get .here (σa.withHeap out2).env=some g.val :=
    TEnv.get_set_ne _ _ _ _ (by simp only [Idx.toNat];omega)
  have hlocalS : ∀ {τ : Source.STy} (q : Source.Idx Γ τ),sdst.toNat≠q.toNat → z2.1.get (.there q)=y.1.get q := by
    intro τ q hnq
    rw [hl2];exact hsloc (.there q) (fun he => hnq (Nat.add_right_cancel he))
  have hlocalT : ∀ {t : LTy} (q : Idx Δ t),dst.toNat≠q.toNat → TEnv.get (.there q) (σa.withHeap out2).env=TEnv.get q (TEnv.wk g.ext Δ σ.env) := by
    intro t q hnq
    exact htloc (.there q) (fun he => hnq (Nat.add_right_cancel he))
  have hobjects : ∀ {Q : RefTy} (q : HRef σ.H Q),out2.get (q.wk g.ext)=MObj.wk g.ext Q (σ.heap.get q) := by
    intro Q q
    rw [hobj (q.wk g.ext) (hne q)];exact hg q
  have hsource2 : ∀ a,y.2.heap.get a≠none → z2.2.heap.get a=y.2.heap.get a := by
    intro a ha;rw [haddr a (Ne.symm (hsource a ha).1),(hsource a ha).2]
  have hsource1 : ∀ a,y.2.heap.get a≠none → z1.2.heap.get a=y.2.heap.get a := by
    intro a ha;rw [haddr1 a (Ne.symm (hsource a ha).1),(hsource a ha).2]
  exact ⟨base',m0,_,m1,m2,out1,out2,z1,z2,hd,hsa,hsrc,hp,hw1,hw2,he1,he2,hr0,hr1,hr2,hc0,hcA,hc1,hc2,hword,hm2,ha2,hmok0,hmok1,hmok2,hl1,hl2,hdstS,hnewS,hrootT,hnewT,hlocalS,hlocalT,hobjects,hsource2,hid,hne,hstack.trans (hstackA.trans hstack0),ha2.free.cell,hsource1,hex,hev,hlog,hfn⟩

/-- info: 'Solidity.Backend.MemoryOps.source_uint_fixed_declare_compound_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_fixed_declare_compound_word

/-- Insufficient constructor horizon short-circuits the entire actual program,
before any alias or update. No suffix heap or rollback is inferred. -/
theorem source_uint_fixed_declare_compound_timeout {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (y : Source.EMState E Γ) (n fuel : Nat)
    (dst : Source.Idx Γ (.array .memory (.int .u256) (some n))) (si sv : Source.Idx Γ (.int .u256))
    (hf : fuel≤n+4) :
    (Source.execItems G F fuel Γ.length none (sourceUintFixedDeclareCompound dst si sv) y.1).run (.nil,y.2)=
      (.error .timeout,(.nil,y.2)) := by
  cases fuel with
  | zero => rfl
  | succ f =>
    have hd := source_uint_fixed_declaration_timeout G F y n f (by omega)
    rw [sourceUintFixedDeclareCompound,Source.execItems,Source.Hoare.run_bind,hd]

/-- info: 'Solidity.Backend.MemoryOps.source_uint_fixed_declare_compound_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_fixed_declare_compound_timeout
end Solidity.Backend.MemoryOps
