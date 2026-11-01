import Solidity.Backend.MemoryOps.SourceUintFixedFuel
import Solidity.Backend.MemoryOps.SourceStructDeclaration
import Solidity.Backend.MemoryOps.SourceUintFixedDelete

/-! Actual context-changing fixed declaration, reached write and delete in ONE
existing Source RItems and intrinsic Prog, with whole existing word append. -/
namespace Solidity.Backend.MemoryOps

def sourceUintFixedProgram {E : Source.Env} {Γ : Source.RCtx} (n : Nat)
    (si sv : Source.Idx Γ (.int .u256)) :
    Source.RItems E [] false .body Γ ((.array .memory (.int .u256) (some n))::Γ) :=
  .stmt (.declVar (.array .memory (.int .u256) (some n)))
    (.stmt (.expr (sourceUintFixedIndexedAssign .here (.there si) (.there sv)))
      (.stmt (.expr (sourceUintFixedIndexedDelete .here (.there si))) .nil))

def intrinsicUintFixedProgram {C : Contract} {Δ : Ctx} (n : Nat) (i v : Idx Δ (.val .uint)) :
    Prog C Δ (.mem (.fixed (.prim .uint) n)::Δ) :=
  .cons (.declMem (.fixed (.prim .uint) n) (.user "fixedFresh") none rfl rfl)
    (.cons (.assignMem (.index .fixed (.var .here rfl) (.simple (.local (.there i))))
      (.val (.simple (.local (.there v)))))
      (.cons (.deleteMem (.loc (.index .fixed (.var .here rfl) (.simple (.local (.there i))))) rfl) .nil))

theorem source_uint_fixed_program_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fsrc : Source.Fr) (y : Source.EMState E Γ) (σ : State C Δ)
    (n : Nat) (hn : 0<n) (si sv : Source.Idx Γ (.int .u256)) (i v : Idx Δ (.val .uint))
    (k value : PrimTy.uint.Denote) (hsi : y.1.get si=sourceUint k) (hsv : y.1.get sv=sourceUint value)
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
      Evm.compileVal b (.simple (.local (.there i)) : Val C (.mem A::Δ) .uint) ++
      Evm.Memory.Objects.writeCode (.fixed : ArrTy A (.prim .uint))
    ∃ (base' : Nat → Fin Evm.W) (target0 target1 target2 : Evm.Machine) (out1 out2 : Heap g.H') (z1 z2 : Source.EMState E (SA::Γ)),
      (Source.execS G Fsrc (n+6) Γ.length none (.declVar SA : Source.RStmt E [] false .body Γ (SA::Γ)) y.1).run (.nil,y.2)=
        (.ok (.normal mid.1),(.nil,mid.2)) ∧
      (Source.execS G Fsrc (n+5) Γ.length none (.expr (sourceUintFixedIndexedAssign .here (.there si) (.there sv)) : Source.RStmt E [] false .body (SA::Γ) (SA::Γ)) mid.1).run (.nil,mid.2)=
        (.ok (.normal mid.1),(.nil,z1.2)) ∧
      (Source.execS G Fsrc (n+4) Γ.length none (.expr (sourceUintFixedIndexedDelete .here (.there si)) : Source.RStmt E [] false .body (SA::Γ) (SA::Γ)) z1.1).run (.nil,z1.2)=
        (.ok (.normal z1.1),(.nil,z2.2)) ∧
      (Source.execItems G Fsrc (n+7) Γ.length none (sourceUintFixedProgram n si sv) y.1).run (.nil,y.2)=
        (.ok (.normal z2.1),(.nil,z2.2)) ∧
      Prog.run σ (intrinsicUintFixedProgram n i v)=.ok ⟨σ'.withHeap out2,g.ext⟩ ∧
      g.heap.writeAddr (.index g.val .fixed k) value=some out1 ∧
      out1.writeAddr (.index g.val .fixed k) (PrimTy.dflt .uint)=some out2 ∧
      SourceUintFixedAt mid y.2.heap.next g.heap g.val ∧
      SourceUintFixedAt z1 y.2.heap.next out1 g.val ∧ SourceUintFixedAt z2 y.2.heap.next out2 g.val ∧
      Evm.run (Evm.Memory.Objects.defaultDeclareCode (Γ := Δ)
        (Evm.Memory.Objects.DefaultBuilder.fixedPrimitive .uint n).code b) m=.ok target0 0 ∧
      Evm.run writeCode target0=.ok target1 0 ∧ Evm.run deleteCode target1=.ok target2 0 ∧
      Evm.run (Evm.Memory.Objects.defaultDeclareCode (Γ := Δ)
        (Evm.Memory.Objects.DefaultBuilder.fixedPrimitive .uint n).code b ++ writeCode ++ deleteCode) m=.ok target2 0 ∧
      Evm.Memory.Objects.StateRepr L b frame (F.push (.mem A) .ok) (σ'.withHeap out2) base' target2 ∧
      Evm.Memory.Objects.AllocatorRepr out2 base' frame ⟨cursor.val+max 1 n,hs⟩ target2 ∧
      Source.MemOK E SH z1 ∧ Source.MemOK E SH z2 ∧ z1.1=mid.1 ∧ z2.1=mid.1 ∧ target2.stack=m.stack ∧
      (Source.writeLoc (E := E) (Γ := SA::Γ) Fsrc (n+3) (.mem y.2.heap.next k.1.toNat) (sourceUint value)).run mid=(.ok (),z1) ∧
      (Source.deleteLoc (E := E) (Γ := SA::Γ) Fsrc (n+2) (τ := .int .u256) (.mem y.2.heap.next k.1.toNat)).run z1=(.ok (),z2) ∧
      (Source.evalE G Fsrc (n+4) (sourceUintFixedIndexedAssign .here (.there si) (.there sv))).run mid=(.ok (.val (sourceUint value)),z1) ∧
      (Source.evalE G Fsrc (n+3) (sourceUintFixedIndexedDelete .here (.there si))).run z1=(.ok Source.RVal.unit,z2) ∧
      target0.stack=m.stack ∧ target1.stack=m.stack ∧
      (∀ {Q : RefTy} (q : HRef σ.H Q),out2.get (q.wk g.ext)=g.heap.get (q.wk g.ext)) ∧
      (∀ address,address≠y.2.heap.next → z2.2.heap.get address=mid.2.heap.get address) ∧
      z2.2.ex=y.2.ex ∧ z2.2.events=y.2.events ∧ z2.2.logs=y.2.logs ∧ z2.2.fnLocals=y.2.fnLocals := by
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
  have hsi1 : z1.1.get (.there si)=sourceUint k := by rw [hl1];exact hsi
  obtain ⟨out2,z2,target2,hw2,hs2,he2,hstmt2,ht2,hc2,hr2,hm2,hmok2,hl2,hstack2,ha2⟩ :=
    resolved_uint_fixed_delete_word G Fsrc n (σ'.withHeap out1) g.val hr1 .here (.there si) .here (.there i)
      k hsroot1 hsi1 rfl hi hk hm1 SH hmok1
  have hf1 := hr.write_frames Fsrc (n+3) k value hk hw1 hs1
  have hf2 := hr1.write_frames Fsrc (n+2) k (PrimTy.dflt .uint) hk hw2 hs2
  have hs1' := source_expr_statement_run G Fsrc (n+4) Γ.length _ mid z1 (.val (sourceUint value)) he1
  have hs2' := source_expr_statement_run G Fsrc (n+3) Γ.length _ z1 z2 Source.RVal.unit he2
  have htail := source_items_pair_run G Fsrc n Γ.length
    (.expr (sourceUintFixedIndexedAssign .here (.there si) (.there sv)))
    (.expr (sourceUintFixedIndexedDelete .here (.there si))) mid z1 z2
    (by simpa only [hl1] using hs1') (by simpa only [hl2] using hs2')
  have hitems : (Source.execItems G Fsrc (n+7) Γ.length none (sourceUintFixedProgram n si sv) y.1).run (.nil,y.2)=
      (.ok (.normal z2.1),(.nil,z2.2)) := by
    rw [sourceUintFixedProgram,Source.execItems,Source.Hoare.run_bind,hd]
    change (Source.execItems G Fsrc (n+6) Γ.length none
      (.stmt (.expr (sourceUintFixedIndexedAssign .here (.there si) (.there sv)))
        (.stmt (.expr (sourceUintFixedIndexedDelete .here (.there si))) .nil)) mid.1 >>=
      fun o => Source.EM.lift (o.up Γ)).run (.nil,mid.2)=_
    rw [Source.Hoare.run_bind,htail]
    rfl
  have hp : Prog.run σ (intrinsicUintFixedProgram n i v)=.ok ⟨σ'.withHeap out2,g.ext⟩ := by
    have hd' : Stmt.run σ (.declMem A (.user "fixedFresh") none rfl rfl)=.ok ⟨σ',g.ext⟩ := hti0
    rw [intrinsicUintFixedProgram,Prog.run_cons_ok hd',Prog.run_cons_ok ht1,Prog.run_cons_ok ht2,Prog.run_nil]
    rfl
  refine ⟨base',target0,target1,target2,out1,out2,z1,z2,hd,(by simpa only [hl1] using hs1'),(by simpa only [hl2] using hs2'),hitems,hp,hw1,hw2,hr,hr1,hr2,hcode0,hc1,hc2,?_,hm2,
    ha2 _ hb (ha1 _ hb ha0),hmok1,hmok2,hl1,hl2.trans hl1,hstack2.trans (hstack1.trans hstack0),hs1,hs2,he1,he2,hstack0,hstack1.trans hstack0,?_,?_,
    hf2.2.2.2.1.trans hf1.2.2.2.1,hf2.2.2.2.2.1.trans hf1.2.2.2.2.1,
    hf2.2.2.2.2.2.1.trans hf1.2.2.2.2.2.1,hf2.2.2.2.2.2.2.trans hf1.2.2.2.2.2.2⟩
  · rw [List.append_assoc,Evm.run_append_ok hcode0,Evm.run_append_ok hc1,hc2]
  · intro Q q
    rw [hf2.2.1 (q.wk g.ext) (hne q),hf1.2.1 (q.wk g.ext) (hne q)]
  · intro address hnaddr
    rw [hf2.2.2.1 address hnaddr,hf1.2.2.1 address hnaddr]

/-- info: 'Solidity.Backend.MemoryOps.source_uint_fixed_program_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_fixed_program_word
end Solidity.Backend.MemoryOps
