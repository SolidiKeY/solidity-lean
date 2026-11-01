import Solidity.Backend.MemoryOps.SourceStructDeclaration

/-! Existing named uint256 member assignment, framing its reference-valued
Boolean child. Actual Source setNth/evaluation and published primitive word
write certificates only; no new value/state layer or primitive compiler. -/
namespace Solidity.Backend.MemoryOps
open Semantics

/-- Exact actual DataList.setNth tag update for the independently represented struct. -/
theorem source_struct_tag_write {E : Source.Env} {Γ : Source.RCtx}
    (y : Source.EMState E Γ) (a : Nat) (dn : Source.DeclName)
    (h : E.layout.fields dn=[.int .u256,SourceBoolArrayTy])
    (old value : PrimTy.uint.Denote) (childAddress : Nat)
    (hr : y.2.heap.get a=some ⟨.struct .memory dn,sourceBoolStructData dn h old childAddress⟩) :
    ∃ ht : y.2.heap.ty a=some (.struct .memory dn),
      (Source.memSet (E := E) (Γ := Γ) a 0 (sourceUint value)).run y=
        (.ok (), (y.1,{y.2 with heap := y.2.heap.write a (sourceBoolStructData dn h value childAddress) ht})) := by
  have hs : ∀ (ts : List Source.STy) (ht : ts=[.int .u256,SourceBoolArrayTy]),
      (ht.symm ▸ (Source.DataList.cons (.val (sourceUint old)) (.cons (.val (.memRef rfl childAddress)) .nil)) : Source.DataList E.layout ts).setNth 0 (.val (sourceUint value))=
      .ok (ht.symm ▸ (Source.DataList.cons (.val (sourceUint value)) (.cons (.val (.memRef rfl childAddress)) .nil))) := by
    intro ts ht
    subst ts
    rfl
  have ht : y.2.heap.ty a=some (.struct .memory dn) := by
    change (y.2.heap.get a).map Sigma.fst=some _
    rw [hr]
    rfl
  refine ⟨ht,?_⟩
  rw [Source.memSet,Source.Hoare.run_bind,source_heapObj_run y a _ hr]
  change ((Source.EM.lift (((h.symm ▸ (Source.DataList.cons (.val (sourceUint old)) (.cons (.val (.memRef rfl childAddress)) .nil))) : Source.DataList E.layout (E.layout.fields dn)).setNth 0 (.val (sourceUint value)))) >>=
    fun fs => Source.heapPut a ⟨.struct .memory dn,Source.Data.struct fs⟩).run y=_
  rw [hs _ h]
  change (Source.heapPut a ⟨.struct .memory dn,sourceBoolStructData dn h value childAddress⟩).run y=_
  simp only [Source.heapPut,Source.Hoare.run_bind]
  rw [show (Source.EM.st (E := E) (Γ := Γ)).run y=(.ok y.2,y) from rfl]
  simp only [ht,↓reduceDIte]
  rfl

/-- Primitive field update preserves the selected reference and all old Boolean
contents. Source-array separation follows actual occupied types, not injection. -/
theorem SourceBoolStructAt.write_tag {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (.struct s)}
    {address : Nat → Nat} {layout : SourceBoolStructLayout E dn s tag child}
    (hr : SourceBoolStructAt y a hp r address layout) (value : PrimTy.uint.Denote)
    (F : Source.Fr) (fuel : Nat) (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    let out := hp.setField r layout.tag_type value
    ∃ z : Source.EMState E Γ,
      (Source.writeLoc (E := E) (Γ := Γ) F fuel (.mem (τ := .int .u256) a 0) (sourceUint value)).run y=(.ok (),z) ∧
      SourceBoolStructAt z a out r address layout ∧ Source.MemOK E SH z ∧ z.1=y.1 ∧
      out.field r layout.tag_type=value ∧ out.field r layout.child_type=hp.field r layout.child_type ∧
      (∀ q : HRef H (.array (.prim .bool)),out.get q=hp.get q) ∧
      (∀ q,SourceBoolMemoryAt y (address q.id) hp q .dyn → SourceBoolMemoryAt z (address q.id) out q .dyn) ∧
      (∀ b,b≠a → z.2.heap.get b=y.2.heap.get b) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  dsimp only
  let out := hp.setField r layout.tag_type value
  have htag : out.field r layout.tag_type=value := by
    simp only [out,Heap.field,Heap.setField,Heap.get_set_same,MFields.get_set_same]
  have hchild : out.field r layout.child_type=hp.field r layout.child_type := by
    simp only [out,Heap.field,Heap.setField,Heap.get_set_same,MFields.get_set_ne _ _ _ _ layout.distinct]
  have hchildren : ∀ q : HRef H (.array (.prim .bool)),out.get q=hp.get q := by
    intro q
    apply Heap.get_set_ne
    intro he
    cases (HRef.heq_of_id r q he).1
  obtain ⟨ht,hw⟩ := source_struct_tag_write y a dn layout.source_types (hp.field r layout.tag_type) value
    (address (hp.field r layout.child_type).id) hr.parent
  let z : Source.EMState E Γ := (y.1,{y.2 with heap := y.2.heap.write a (sourceBoolStructData dn layout.source_types value (address (hp.field r layout.child_type).id)) ht})
  have hs : (Source.writeLoc (E := E) (Γ := Γ) F fuel (.mem (τ := .int .u256) a 0) (sourceUint value)).run y=(.ok (),z) := hw
  have hmk := Source.writeLoc_memOK (E := E) (Γ := Γ) (H := SH) F fuel (.mem (τ := .int .u256) a 0) (sourceUint value) y ⟨hm,trivial⟩
  rw [hs] at hmk
  have hsource : ∀ q,SourceBoolMemoryAt y (address q.id) hp q .dyn → SourceBoolMemoryAt z (address q.id) out q .dyn := by
    intro q hq
    have hne : address q.id≠a := by
      intro he
      rw [he] at hq
      have heq := congrArg Sigma.fst (Option.some.inj (hr.parent.symm.trans hq))
      cases heq
    unfold SourceBoolMemoryAt
    change (y.2.heap.write _ _ ht).get (address q.id)=some _
    rw [Source.Heap.write_other y.2.heap hne,hchildren]
    exact hq
  refine ⟨z,hs,⟨?_,?_⟩,hmk,rfl,htag,hchild,hchildren,hsource,?_,rfl,rfl,rfl,rfl⟩
  · change (y.2.heap.write _ _ ht).get a=some _
    rw [Source.Heap.write_get,htag,hchild]
  · rw [hchild]
    exact hsource _ hr.leaf
  · intro b hb
    exact Source.Heap.write_other y.2.heap hb _ ht

def sourceStructTagAssign {E : Source.Env} {Γ : Source.RCtx}
    (layout : SourceBoolStructLayout E dn s tag child)
    (root : Source.Idx Γ (.struct .memory dn)) (rhs : Source.Idx Γ (.int .u256)) : Source.RExpr E Γ (.int .u256) :=
  .assign (.member (.local root) (by decide) 0 layout.source_tag_type) (.local rhs)

def structTagWriteCode {C : Contract} {Δ : Ctx} (b : Nat)
    (root : Idx Δ (.mem (.struct s))) (tag : Name) (v : Val C Δ .uint) : List Evm.Instr :=
  Evm.compileVal b v ++ [.mload (Evm.cellOf b root)] ++ Evm.Memory.writeFieldCode (Evm.Memory.fieldOffset (structDef s) tag)

/-- INITIAL independent named observer and aligned pure operands derive actual
Source RHS-first assignment/statement, intrinsic field assignment and whole word
program. Reference child/aliases, allocator, locals and Source world are framed. -/
theorem SourceBoolStructAt.assign_tag_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {a : Nat} (layout : SourceBoolStructLayout E dn s tag child)
    (G : Source.Glob E) (Fsrc : Source.Fr) (n : Nat)
    (σ : State C Δ) (r : HRef σ.H (.struct s)) (address : Nat → Nat)
    (hr : SourceBoolStructAt y a σ.heap r address layout)
    (sroot : Source.Idx Γ (.struct .memory dn)) (srhs : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.struct s))) (v : Val C Δ .uint) (value : PrimTy.uint.Denote)
    (hsroot : y.1.get sroot=.memRef rfl a) (hsrhs : y.1.get srhs=sourceUint value)
    (htroot : TEnv.get root σ.env=some r) (htv : v.evalT σ=.ok value)
    (hmf : (Ty.ref (.struct s)).mapFree=true) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) (hvf : Evm.valIn F v=true) :
    let out := σ.heap.setField r layout.tag_type value
    ∃ (z : Source.EMState E Γ) (target : Evm.Machine),
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (n+2) (.mem (τ := .int .u256) a 0) (sourceUint value)).run y=(.ok (),z) ∧
      (Source.evalE G Fsrc (n+3) (sourceStructTagAssign layout sroot srhs)).run y=(.ok (.val (sourceUint value)),z) ∧
      (Source.execS G Fsrc (n+4) Γ.length none (.expr (sourceStructTagAssign layout sroot srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
      Stmt.run σ (.assignMem (.field (.var root hmf) tag layout.tag_type) (.val v))=.ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (structTagWriteCode b root tag v) m=.ok target 0 ∧
      SourceBoolStructAt z a out r address layout ∧ Source.MemOK E SH z ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap out) base target ∧
      z.1=y.1 ∧ target.stack=m.stack ∧ Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out) target ∧
      out.field r layout.tag_type=value ∧ out.field r layout.child_type=σ.heap.field r layout.child_type ∧
      (∀ q,SourceBoolMemoryAt y (address q.id) σ.heap q .dyn → SourceBoolMemoryAt z (address q.id) out q .dyn) ∧
      (∀ b,b≠a → z.2.heap.get b=y.2.heap.get b) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  dsimp only
  obtain ⟨z,hw,hr',hmk,hl,htag,hchild,hchildren,hsource,hframe,hex,hev,hlog,hfn⟩ := hr.write_tag value Fsrc (n+2) SH hmem
  have he : (Source.evalE G Fsrc (n+3) (sourceStructTagAssign layout sroot srhs)).run y=(.ok (.val (sourceUint value)),z) := by
    rw [sourceStructTagAssign,Source.evalE,Source.Hoare.run_bind,source_local_value_run G Fsrc (n+1) y srhs (sourceUint value) hsrhs]
    change ((Source.evalLoc G Fsrc (n+2) (.member (.local sroot) (by decide) 0 layout.source_tag_type)) >>= fun loc =>
      Source.writeLoc Fsrc (n+2) loc (sourceUint value) >>= fun _ => pure (Source.RVal.val (sourceUint value))).run y=_
    have hloc : (Source.evalLoc G Fsrc (n+2) (.member (.local sroot) (by decide) 0 layout.source_tag_type)).run y=(.ok (.mem a 0),y) := by
      rw [Source.evalLoc,Source.Hoare.run_bind,source_local_value_run G Fsrc n y sroot (.memRef rfl a) hsroot]
      rfl
    rw [Source.Hoare.run_bind,hloc]
    change (Source.writeLoc Fsrc (n+2) (.mem (τ := .int .u256) a 0) (sourceUint value) >>= fun _ => pure (Source.RVal.val (sourceUint value))).run y=_
    rw [Source.Hoare.run_bind,hw]
    rfl
  have hi : TRun.assignMem (.field (.var root hmf) tag layout.tag_type) (.val v) σ=.ok ⟨σ.withHeap (σ.heap.setField r layout.tag_type value),List.prefix_refl _⟩ := by
    simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,MPath.mvalT,htroot,htv,Heap.writeAddr,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  have cert := Evm.Memory.PtrFrag.writePrimitive hm (Evm.Memory.PtrFrag.local root hmf) layout.tag_type v (Evm.compileVal b v) (Evm.val_sim v hm.core hvf)
  rw [hi] at cert
  rcases cert with ⟨o,target,ho,hcode,hstate,hstack,halloc⟩ | ⟨hbad,_⟩
  · cases Except.ok.inj ho
    exact ⟨z,target,hw,he,source_expr_statement_run G Fsrc (n+3) Γ.length _ y z _ he,hi,hcode,hr',hmk,hstate,hl,hstack,halloc,htag,hchild,hsource,hframe,hex,hev,hlog,hfn⟩
  · cases hbad

/-- Actual low Source horizons timeout before a field update, without claiming
word-machine timeout or rollback. -/
theorem source_struct_tag_low_horizon {E : Source.Env} {Γ : Source.RCtx}
    (layout : SourceBoolStructLayout E dn s tag child)
    (G : Source.Glob E) (F : Source.Fr) (y : Source.EMState E Γ)
    (root : Source.Idx Γ (.struct .memory dn)) (rhs : Source.Idx Γ (.int .u256)) :
    ∀ n,n≤2 → (Source.evalE G F n (sourceStructTagAssign layout root rhs)).run y=(.error .timeout,y) := by
  intro n hn
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | n+3 => omega


/-- info: 'Solidity.Backend.MemoryOps.source_struct_tag_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_struct_tag_write

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.write_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolStructAt.write_tag

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.assign_tag_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolStructAt.assign_tag_word

/-- info: 'Solidity.Backend.MemoryOps.source_struct_tag_low_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_struct_tag_low_horizon

end Solidity.Backend.MemoryOps
