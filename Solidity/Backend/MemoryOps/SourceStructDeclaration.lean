import Solidity.Backend.MemoryOps.SourceStructGrowth
import Solidity.Backend.MemoryOps.SourceDeclaration

/-! Real context-changing Source default declaration followed by reached named
reference assignment. Source cons and intrinsic indices are transported separately;
no new syntax/evaluator/allocator or generic construction claim is introduced. -/
namespace Solidity.Backend.MemoryOps
open Semantics

/-- This existing observer concerns heap contents, not the shape of local context. -/
theorem SourceBoolMemoryAt.recontext {E : Source.Env} {Γ Δ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {z : Source.EMState E Δ} {addr : Nat} {hp : Heap H}
    {r : HRef H R} {a : ArrTy R (.prim .bool)}
    (hr : SourceBoolMemoryAt y addr hp r a) (hh : z.2.heap=y.2.heap) :
    SourceBoolMemoryAt z addr hp r a := by
  unfold SourceBoolMemoryAt
  rw [hh]
  exact hr

/-- Actual local-context change needs equal heaps, not equal locals. -/
theorem SourceBoolStructAt.recontext {E : Source.Env} {Γ Δ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {z : Source.EMState E Δ} {addr : Nat} {hp : Heap H}
    {r : HRef H (.struct s)} {address : Nat → Nat} {layout : SourceBoolStructLayout E dn s tag child}
    (hr : SourceBoolStructAt y addr hp r address layout) (hh : z.2.heap=y.2.heap) :
    SourceBoolStructAt z addr hp r address layout := by
  exact ⟨by rw [hh];exact hr.parent,hr.leaf.recontext hh⟩

/-- Existing RItems sequencing with a real first context extension. -/
theorem source_items_context_pair_run {E : Source.Env} {Γ Δ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (n nps : Nat)
    (s : Source.RStmt E [] false .body Γ Δ) (t : Source.RStmt E [] false .body Δ Δ)
    (y : Source.EMState E Γ) (mid out : Source.EMState E Δ)
    (hs : (Source.execS G F (n+5) nps none s y.1).run (.nil,y.2)=(.ok (.normal mid.1),(.nil,mid.2)))
    (ht : (Source.execS G F (n+4) nps none t mid.1).run (.nil,mid.2)=(.ok (.normal out.1),(.nil,out.2))) :
    (Source.execItems G F (n+6) nps none (.stmt s (.stmt t .nil)) y.1).run (.nil,y.2)=
      (.ok (.normal out.1),(.nil,out.2)) := by
  have hn : (Source.execItems G F (n+4) nps none (.nil : Source.RItems E [] false .body Δ Δ) out.1).run (.nil,out.2)=
      (.ok (.normal out.1),(.nil,out.2)) := rfl
  have htail := source_items_cons_run G F (n+4) nps t .nil mid out out ht hn
  rw [Source.execItems,Source.Hoare.run_bind,hs]
  change (Source.execItems G F (n+5) nps none (.stmt t .nil) mid.1 >>= fun o => Source.EM.lift (o.up Γ)).run (.nil,mid.2)=_
  rw [Source.Hoare.run_bind,htail]
  rfl

/-- Rejection after a REAL context-changing prefix retains that reached global
state; it supplies no successful suffix or rollback observation. -/
theorem source_items_context_pair_error {E : Source.Env} {Γ Δ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (n nps : Nat)
    (s : Source.RStmt E [] false .body Γ Δ) (t : Source.RStmt E [] false .body Δ Δ)
    (y : Source.EMState E Γ) (mid out : Source.EMState E Δ) (halt : Source.Halt)
    (hs : (Source.execS G F (n+2) nps none s y.1).run (.nil,y.2)=(.ok (.normal mid.1),(.nil,mid.2)))
    (ht : (Source.execS G F (n+1) nps none t mid.1).run (.nil,mid.2)=(.error halt,(.nil,out.2))) :
    (Source.execItems G F (n+3) nps none (.stmt s (.stmt t .nil)) y.1).run (.nil,y.2)=
      (.error halt,(.nil,out.2)) := by
  have htail : (Source.execItems G F (n+2) nps none (.stmt t .nil : Source.RItems E [] false .body Δ Δ) mid.1).run (.nil,mid.2)=
      (.error halt,(.nil,out.2)) := by
    rw [Source.execItems,Source.Hoare.run_bind,ht]
  rw [Source.execItems,Source.Hoare.run_bind,hs]
  change (Source.execItems G F (n+2) nps none (.stmt t .nil) mid.1 >>= fun o => Source.EM.lift (o.up Γ)).run (.nil,mid.2)=_
  rw [Source.Hoare.run_bind,htail]

def sourceStructDeclareAssign {E : Source.Env} {Γ : Source.RCtx}
    (layout : SourceBoolStructLayout E dn s tag child) (root : Source.Idx Γ (.struct .memory dn)) :
    Source.RItems E [] false .body Γ (SourceBoolArrayTy::Γ) :=
  .stmt (.declVar SourceBoolArrayTy)
    (.stmt (.expr (sourceStructAssign layout (.there root) .here)) .nil)

/-- Initial alignment and allocator premises derive declaration, then the actual
reached assignment in both extended contexts and the whole word append. -/
theorem SourceBoolStructAt.declare_assign_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {addr : Nat} (layout : SourceBoolStructLayout E dn s tag child)
    (G : Source.Glob E) (Fsrc : Source.Fr) (n : Nat)
    (σ : State C Δ) (r : HRef σ.H (.struct s)) (address : Nat → Nat)
    (hr : SourceBoolStructAt y addr σ.heap r address layout)
    (sroot : Source.Idx Γ (.struct .memory dn)) (root : Idx Δ (.mem (.struct s)))
    (hsroot : y.1.get sroot=.memRef rfl addr) (htroot : TEnv.get root σ.env=some r)
    (hmf : (Ty.ref (.struct s)).mapFree=true) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m)
    (ha : Evm.Memory.StructAllocatorRepr σ.heap base frame cursor m) (hb : 0<b)
    (hspace : cursor.val+1<Evm.W) (hcap : b+(Δ.length+1)≤frame) :
    let o := Evm.Memory.defaultArray (H := σ.H) .bool ⟨0,Evm.W_pos⟩
    let σ' := σ.allocPush o
    let fresh := (σ.alloc o).2
    let e := List.prefix_append σ.H [RefTy.array (.prim .bool)]
    let rr := r.wk e
    let address' := allocatedSourceAddress address σ.H.length y.2.heap.next
    let base' := Evm.upd base σ.H.length cursor
    let mm := Evm.Memory.writeMachine (Evm.Memory.allocateMachine m cursor ⟨0,Evm.W_pos⟩) (Evm.cell (b+Δ.length)) (.val cursor)
    let out := σ'.heap.setField rr layout.child_type fresh
    ∃ (mid z : Source.EMState E (SourceBoolArrayTy::Γ)) (target : Evm.Machine),
      (Source.execS G Fsrc (n+5) Γ.length none (.declVar SourceBoolArrayTy : Source.RStmt E [] false .body Γ (SourceBoolArrayTy::Γ)) y.1).run (.nil,y.2)=
        (.ok (.normal mid.1),(.nil,mid.2)) ∧
      (Source.writeLoc (E := E) (Γ := SourceBoolArrayTy::Γ) Fsrc (n+2) (.mem (τ := SourceBoolArrayTy) addr 1)
        (.memRef rfl y.2.heap.next)).run mid=(.ok (),z) ∧
      (Source.evalE G Fsrc (n+3) (sourceStructAssign layout (.there sroot) .here)).run mid=
        (.ok (.val (.memRef rfl y.2.heap.next)),z) ∧
      (Source.execS G Fsrc (n+4) Γ.length none (.expr (sourceStructAssign layout (.there sroot) .here) : Source.RStmt E [] false .body (SourceBoolArrayTy::Γ) (SourceBoolArrayTy::Γ)) mid.1).run (.nil,mid.2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
      (Source.execItems G Fsrc (n+6) Γ.length none (sourceStructDeclareAssign layout sroot) y.1).run (.nil,y.2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
      TRun.declMem (.array (.prim .bool)) none rfl σ=.ok ⟨σ',e⟩ ∧
      Prog.run σ (.cons (.declMem (.array (.prim .bool)) (.user "freshBool") none rfl rfl)
        (.cons (.assignMem (.field (.var (.there root) hmf) child layout.child_type) (.ref (.var .here rfl))) .nil))=
        .ok ⟨σ'.withHeap out,e⟩ ∧
      Evm.run (Evm.Memory.declareNewCode b (.lit 0 rfl : Simple C Δ .uint)) m=.ok mm 0 ∧
      Evm.run (structReferenceWriteCode b (.there root) .here child) mm=.ok target 0 ∧
      Evm.run (Evm.Memory.declareNewCode b (.lit 0 rfl : Simple C Δ .uint)++structReferenceWriteCode b (.there root) .here child) m=.ok target 0 ∧
      SourceBoolStructAt mid addr σ'.heap rr address' layout ∧ SourceBoolStructAt z addr out rr address' layout ∧
      Source.MemOK E SH mid ∧ Source.MemOK E SH z ∧
      Evm.Memory.StateRepr L b frame (F.push (.mem (.array (.prim .bool))) .ok) (σ'.withHeap out) base' target ∧
      Evm.Memory.StructAllocatorRepr out base' frame ⟨cursor.val+1,hspace⟩ target ∧
      mid.1.get .here=.memRef rfl y.2.heap.next ∧ mid.1.get (.there sroot)=.memRef rfl addr ∧ z.1=mid.1 ∧
      TEnv.get (.there root) σ'.env=some rr ∧ TEnv.get .here σ'.env=some fresh ∧
      out.field rr layout.tag_type=σ.heap.field r layout.tag_type ∧ out.field rr layout.child_type=fresh ∧ out.len fresh .dyn=0 ∧
      (∀ q : HRef σ.H (.array (.prim .bool)), SourceBoolMemoryAt y (address q.id) σ.heap q .dyn →
        SourceBoolMemoryAt z (address' (q.wk e).id) out (q.wk e) .dyn) ∧
      target.stack=m.stack ∧
      target=Evm.Memory.writeMachine mm ((base' rr.id).val+Evm.Memory.fieldOffset (structDef s) child) (.val (base' fresh.id)) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  dsimp only
  let o := Evm.Memory.defaultArray (H := σ.H) .bool ⟨0,Evm.W_pos⟩
  let σ' := σ.allocPush o
  let e := List.prefix_append σ.H [RefTy.array (.prim .bool)]
  let address' := allocatedSourceAddress address σ.H.length y.2.heap.next
  obtain ⟨z0,hzero,hdecl,hd,hcode,hfresh,hmem',hm',ha',hstack,hid⟩ :=
    source_bool_declaration_word G Fsrc y (n+2) SH hmem σ hm ha hb hspace hcap
  obtain ⟨halloc,hkeep,hstruct,hnew,hmem0,hfid,haddr,hold,hne,hpa,hca,halias,hlocal,heff⟩ := hr.alloc_bool o SH hmem
  simp only [o,MObj.elems_dyn,Evm.Memory.defaultArray,List.replicate_zero] at halloc hstruct halias
  have hzid := congrArg Prod.snd (hzero.symm.trans (source_bool_default_run y (n+2)))
  change z0=(y.1,{y.2 with heap := (y.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory []⟩).1}) at hzid
  rw [←hzid] at hstruct halias
  let mid : Source.EMState E (SourceBoolArrayTy::Γ) := (.cons (.memRef rfl y.2.heap.next) z0.1,z0.2)
  have hrmid : SourceBoolStructAt mid addr σ'.heap (r.wk e) address' layout := hstruct.recontext rfl
  have hzlocals : z0.1=y.1 := by rw [hzid]
  have hsr : mid.1.get (.there sroot)=.memRef rfl addr := by change z0.1.get sroot=_;rw [hzlocals];exact hsroot
  have hsf : mid.1.get (.here : Source.Idx (SourceBoolArrayTy::Γ) SourceBoolArrayTy)=.memRef rfl (address' (σ.alloc o).2.id) := by
    change Source.Val.memRef rfl y.2.heap.next=Source.Val.memRef rfl (address' (σ.alloc o).2.id)
    rw [hid]
    simp only [address',allocatedSourceAddress,↓reduceIte]
  have htr : TEnv.get (.there root) σ'.env=some (r.wk e) := by
    change TEnv.get root (TEnv.wk e Δ σ.env)=_
    rw [TEnv.get_wk]
    change (TEnv.get root σ.env).map (HRef.wk e)=_
    rw [htroot]
    rfl
  have htf : TEnv.get (.here : Idx (.mem (RefTy.array (.prim .bool))::Δ) (.mem (.array (.prim .bool)))) σ'.env=some (σ.alloc o).2 := rfl
  have hfmid : SourceBoolMemoryAt mid (address' (σ.alloc o).2.id) σ'.heap (σ.alloc o).2 .dyn := by
    rw [hid]
    simp only [address',allocatedSourceAddress,↓reduceIte]
    exact hfresh
  obtain ⟨z,target,hw,he,hs,hi,hc,hrz,hmz,hmword,hl,hsword,htarget,halloc2,htag,hsel,hchildren,hsource,heffects⟩ :=
    SourceBoolStructAt.resolved_assign_word layout G Fsrc n σ' (r.wk e) (σ.alloc o).2 address' hrmid hfmid
      (.there sroot) .here (.there root) .here hsr hsf htr htf hmf SH hmem' hm'
  have hw' : (Source.writeLoc (E := E) (Γ := SourceBoolArrayTy::Γ) Fsrc (n+2) (.mem (τ := SourceBoolArrayTy) addr 1)
      (.memRef rfl y.2.heap.next)).run mid=(.ok (),z) := by
    rw [hid] at hw
    simp only [address',allocatedSourceAddress,↓reduceIte] at hw
    exact hw
  have he' : (Source.evalE G Fsrc (n+3) (sourceStructAssign layout (.there sroot) .here)).run mid=(.ok (.val (.memRef rfl y.2.heap.next)),z) := by
    rw [hid] at he
    simp only [address',allocatedSourceAddress,↓reduceIte] at he
    exact he
  have hs' := source_expr_statement_run G Fsrc (n+3) Γ.length _ mid z _ he'
  have htag0 := hkeep.field r layout.tag_type
  change σ'.heap.field (r.wk e) layout.tag_type=σ.heap.field r layout.tag_type at htag0
  have hlen : (σ'.heap.setField (r.wk e) layout.child_type (σ.alloc o).2).len (σ.alloc o).2 .dyn=0 := by
    unfold Heap.len
    rw [hchildren,State.allocPush_get,MObj.elems_wk,MObj.elems_dyn]
    simp only [o,Evm.Memory.defaultArray,List.replicate_zero,List.map_nil,List.length_nil]
  refine ⟨mid,z,target,hdecl,hw',he',hs',?_,hd,?_,hcode,hc,?_,hrmid,hrz,hmem',hmz,hmword,halloc2 ⟨cursor.val+1,hspace⟩ hb ha',rfl,hsr,hl,htr,htf,htag.trans htag0,hsel,hlen,?_,hsword.trans hstack,htarget,?_,?_,?_,?_⟩
  · exact source_items_context_pair_run G Fsrc n Γ.length _ _ y mid z hdecl hs'
  · have hd' : Stmt.run σ (.declMem (.array (.prim .bool)) (.user "freshBool") none rfl rfl)=.ok ⟨σ',e⟩ := hd
    rw [Prog.run_cons_ok hd',Prog.run_cons_ok hi,Prog.run_nil]
    rfl
  · rw [Evm.run_append_ok hcode]
    exact hc
  · intro q hq
    exact hsource _ ((halias q hq).1.recontext rfl)
  · exact heffects.1.trans (by change z0.2.ex=_;rw [hzid])
  · exact heffects.2.1.trans (by change z0.2.events=_;rw [hzid])
  · exact heffects.2.2.1.trans (by change z0.2.logs=_;rw [hzid])
  · exact heffects.2.2.2.trans (by change z0.2.fnLocals=_;rw [hzid])


/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.recontext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolMemoryAt.recontext

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.recontext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolStructAt.recontext

/-- info: 'Solidity.Backend.MemoryOps.source_items_context_pair_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_items_context_pair_run

/-- info: 'Solidity.Backend.MemoryOps.source_items_context_pair_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_items_context_pair_error

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.declare_assign_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolStructAt.declare_assign_word

end Solidity.Backend.MemoryOps
