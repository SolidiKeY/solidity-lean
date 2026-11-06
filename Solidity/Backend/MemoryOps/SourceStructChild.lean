import Solidity.Backend.MemoryOps.SourceStructAlias

/-! Actual named-member-selected Boolean child indexing and mutation.
Only existing Source syntax, intrinsic paths and published word certificates
are composed. The finite initial observer is not a general Source graph. -/
namespace Solidity.Backend.MemoryOps
open Semantics

def sourceStructChildLoc {E : Source.Env} {Γ : Source.RCtx}
    (layout : SourceBoolStructLayout E dn s tag child)
    (root : Source.Idx Γ (.struct .memory dn)) (i : Source.Idx Γ (.int .u256)) : Source.RLVal E Γ .bool :=
  .indexArray (.member (.local root) 1 layout.source_child_type) (by decide) (.local i) rfl

def sourceStructChildRead {E : Source.Env} {Γ : Source.RCtx}
    (layout : SourceBoolStructLayout E dn s tag child)
    (root : Source.Idx Γ (.struct .memory dn)) (i : Source.Idx Γ (.int .u256)) : Source.RExpr E Γ .bool :=
  .indexArray (.member (.local root) 1 layout.source_child_type) (.local i) rfl

def sourceStructChildAssign {E : Source.Env} {Γ : Source.RCtx}
    (layout : SourceBoolStructLayout E dn s tag child)
    (root : Source.Idx Γ (.struct .memory dn)) (i : Source.Idx Γ (.int .u256)) (v : Source.Idx Γ .bool) : Source.RExpr E Γ .bool :=
  .assign (sourceStructChildLoc layout root i) (.local v)

theorem SourceBoolStructAt.eval_child_loc {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (.struct s)}
    {address : Nat → Nat} {layout : SourceBoolStructLayout E dn s tag child}
    (hr : SourceBoolStructAt y a hp r address layout) (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (root : Source.Idx Γ (.struct .memory dn)) (i : Source.Idx Γ (.int .u256)) (k : PrimTy.uint.Denote)
    (hroot : y.1.get root=.memRef rfl a) (hi : y.1.get i=sourceUint k)
    (hk : k.1.toNat<hp.len (hp.field r layout.child_type) .dyn) :
    (Source.evalLoc G F (n+3) (sourceStructChildLoc layout root i)).run y=
      (.ok (.mem (address (hp.field r layout.child_type).id) k.1.toNat),y) := by
  rw [sourceStructChildLoc,Source.evalLoc,Source.Hoare.run_bind,hr.eval_member_child G F n root hroot]
  change ((Source.evalE G F (n+2) (.local i)) >>= fun v => Source.indexNat v >>= fun k =>
    Source.indexLoc F (.memRef rfl (address (hp.field r layout.child_type).id) : Source.Val E.layout SourceBoolArrayTy) k).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F (n+1) y i _ hi]
  exact hr.leaf.indexLoc_run F _ hk

theorem SourceBoolStructAt.eval_child_read {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (.struct s)}
    {address : Nat → Nat} {layout : SourceBoolStructLayout E dn s tag child}
    (hr : SourceBoolStructAt y a hp r address layout) (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (root : Source.Idx Γ (.struct .memory dn)) (i : Source.Idx Γ (.int .u256)) (k : PrimTy.uint.Denote) (v : Bool)
    (hroot : y.1.get root=.memRef rfl a) (hi : y.1.get i=sourceUint k)
    (hv : hp.index (hp.field r layout.child_type) .dyn k=some v) :
    (Source.evalE G F (n+3) (sourceStructChildRead layout root i)).run y=(.ok (.val (.bool v)),y) := by
  have hk : k.1.toNat<hp.len (hp.field r layout.child_type) .dyn := (List.getElem?_eq_some_iff.mp hv).1
  rw [sourceStructChildRead,Source.evalE,Source.Hoare.run_bind,hr.eval_member_child G F n root hroot]
  change ((Source.evalE G F (n+2) (.local i)) >>= fun v => Source.indexNat v >>= fun k =>
    Source.indexLoc F (.memRef rfl (address (hp.field r layout.child_type).id) : Source.Val E.layout SourceBoolArrayTy) k >>= fun loc =>
    Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F (n+1) y i _ hi]
  change (Source.indexLoc F (.memRef rfl (address (hp.field r layout.child_type).id) : Source.Val E.layout SourceBoolArrayTy) k.1.toNat >>= fun loc =>
    Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,hr.leaf.indexLoc_run F _ hk]
  change (Source.readLoc F (τ := .bool) (.mem (address (hp.field r layout.child_type).id) k.1.toNat) >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,(hr.leaf.read_iff F k v).mpr hv]
  rfl

theorem SourceBoolStructAt.parent_ne_leaf {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (.struct s)}
    {address : Nat → Nat} {layout : SourceBoolStructLayout E dn s tag child}
    (hr : SourceBoolStructAt y a hp r address layout) : a≠address (hp.field r layout.child_type).id := by
  intro he
  have hc := hr.leaf
  rw [←he] at hc
  have ht := congrArg Sigma.fst (Option.some.inj (hr.parent.symm.trans hc))
  cases ht

/-- The selected child's actual write frames the existing named parent and
ALL other intrinsic objects. Source aliases at different addresses are framed;
no global address injection is required. -/
theorem SourceBoolStructAt.write_child {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (.struct s)}
    {address : Nat → Nat} {layout : SourceBoolStructLayout E dn s tag child}
    (hr : SourceBoolStructAt y a hp r address layout) (F : Source.Fr) (fuel : Nat)
    (k : PrimTy.uint.Denote) (v : Bool) (hk : k.1.toNat<hp.len (hp.field r layout.child_type) .dyn)
    (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    let q := hp.field r layout.child_type
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      hp.writeAddr (.index q .dyn k) v=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) F fuel (.mem (address q.id) k.1.toNat) (.bool v)).run y=(.ok (),z) ∧
      SourceBoolStructAt z a out r address layout ∧ Source.MemOK E SH z ∧ z.1=y.1 ∧
      out.get r=hp.get r ∧
      (∀ {R : RefTy} (t : HRef H R),q.id≠t.id → out.get t=hp.get t) ∧
      (∀ b,b≠address q.id → z.2.heap.get b=y.2.heap.get b) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  dsimp only
  let q := hp.field r layout.child_type
  let values := MObj.elems .dyn (hp.get q)
  obtain ⟨ht,hw⟩ := source_bool_write y (address q.id) values hr.leaf k.1.toNat hk v
  let out := hp.set q (MObj.setElem .dyn (hp.get q) k.1.toNat v)
  let z : Source.EMState E Γ := (y.1,{y.2 with heap := y.2.heap.write (address q.id) (sourceBoolMemory (values.set k.1.toNat v)) ht})
  have hqr : q.id≠r.id := by
    intro he
    cases (HRef.heq_of_id q r he).1
  have hparent : out.get r=hp.get r := Heap.get_set_ne hp q r hqr _
  have hfield : out.field r layout.child_type=q := by unfold Heap.field;rw [hparent];rfl
  have htag : out.field r layout.tag_type=hp.field r layout.tag_type := by unfold Heap.field;rw [hparent]
  have hs : (Source.writeLoc (E := E) (Γ := Γ) F fuel (.mem (address q.id) k.1.toNat) (.bool v)).run y=(.ok (),z) := hw
  have hmem := Source.writeLoc_memOK (E := E) (Γ := Γ) (H := SH) F fuel
    (.mem (τ := .bool) (address q.id) k.1.toNat) (.bool v) y ⟨hm,trivial⟩
  rw [hs] at hmem
  refine ⟨out,z,?_,hs,⟨?_,?_⟩,hmem,rfl,hparent,?_,?_,rfl,rfl,rfl,rfl⟩
  · simp only [Heap.len] at hk
    simp only [Heap.writeAddr,Heap.setIndex,hk,↓reduceIte];rfl
  · rw [hfield,htag]
    exact (Source.Heap.write_other y.2.heap hr.parent_ne_leaf _ ht).trans hr.parent
  · unfold SourceBoolMemoryAt
    rw [hfield]
    change (y.2.heap.write _ _ ht).get (address q.id)=some _
    rw [Source.Heap.write_get,Heap.get_set_same,MObj.elems_setElem]
  · intro R t hne;exact Heap.get_set_ne hp q t hne _
  · intro b hb;exact Source.Heap.write_other y.2.heap hb _ ht

def structChildWriteCode {C : Contract} {Δ : Ctx} (b : Nat)
    (root : Idx Δ (.mem (.struct s))) (child : Name) (i : Val C Δ .uint) (v : Val C Δ .bool) : List Evm.Instr :=
  Evm.compileVal b v ++ ([.mload (Evm.cellOf b root)] ++ Evm.Memory.readFieldCode (Evm.Memory.fieldOffset (structDef s) child)) ++
    Evm.compileVal b i ++ Evm.Memory.writeArrayStackCode

theorem SourceBoolStructAt.assign_child_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {a : Nat} (layout : SourceBoolStructLayout E dn s tag child)
    (G : Source.Glob E) (Fsrc : Source.Fr) (n : Nat)
    (σ : State C Δ) (r : HRef σ.H (.struct s)) (address : Nat → Nat)
    (hr : SourceBoolStructAt y a σ.heap r address layout)
    (sroot : Source.Idx Γ (.struct .memory dn)) (si : Source.Idx Γ (.int .u256)) (sv : Source.Idx Γ .bool)
    (root : Idx Δ (.mem (.struct s))) (i : Val C Δ .uint) (v : Val C Δ .bool)
    (k : PrimTy.uint.Denote) (value : Bool)
    (hsroot : y.1.get sroot=.memRef rfl a) (hsi : y.1.get si=sourceUint k) (hsv : y.1.get sv=.bool value)
    (htroot : TEnv.get root σ.env=some r) (hti : i.evalT σ=.ok k) (htv : v.evalT σ=.ok value)
    (hmf : (Ty.ref (.struct s)).mapFree=true)
    (hk : k.1.toNat<σ.heap.len (σ.heap.field r layout.child_type) .dyn)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m)
    (hif : Evm.valIn F i=true) (hvf : Evm.valIn F v=true) :
    let q := σ.heap.field r layout.child_type
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ) (target : Evm.Machine),
      σ.heap.writeAddr (.index q .dyn k) value=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (n+3) (.mem (address q.id) k.1.toNat) (.bool value)).run y=(.ok (),z) ∧
      (Source.evalE G Fsrc (n+4) (sourceStructChildAssign layout sroot si sv)).run y=(.ok (.val (.bool value)),z) ∧
      (Source.execS G Fsrc (n+5) Γ.length none
        (.expr (sourceStructChildAssign layout sroot si sv) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal y.1),(.nil,z.2)) ∧
      Stmt.run σ (.assignMem (.index .dyn (.loc (.field (.var root hmf) child layout.child_type)) i) (.val v))=
        .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (structChildWriteCode b root child i v) m=.ok target 0 ∧
      SourceBoolStructAt z a out r address layout ∧ Source.MemOK E SH z ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap out) base target ∧
      z.1=y.1 ∧ target.stack=m.stack ∧ Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out) target ∧
      out.get r=σ.heap.get r ∧
      (∀ {R : RefTy} (t : HRef σ.H R),q.id≠t.id → out.get t=σ.heap.get t) ∧
      (∀ b,b≠address q.id → z.2.heap.get b=y.2.heap.get b) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  dsimp only
  let q := σ.heap.field r layout.child_type
  obtain ⟨out,z,hw,hs,hr',hmk,hl,hparent,hother,hsource,hex,hev,hlog,hfn⟩ := hr.write_child Fsrc (n+3) k value hk SH hmem
  let path : MPath C Δ (.ref (.array (.prim .bool))) := .loc (.field (.var root hmf) child layout.child_type)
  let ptr := [.mload (Evm.cellOf b root)] ++ Evm.Memory.readFieldCode (Evm.Memory.fieldOffset (structDef s) child)
  have hp : Evm.Memory.PtrFrag b path ptr := .field _ _ _ (.local root hmf)
  have hpath : path.mvalT σ=.ok q := by
    simp only [path,MPath.mvalT,MLoc.addrT,htroot,Heap.readAddr,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    rfl
  change σ.heap.writeAddr (.index q .dyn k) value=some out at hw
  have hi : TRun.assignMem (.index .dyn path i) (.val v) σ=.ok ⟨σ.withHeap out,List.prefix_refl _⟩ := by
    simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,hpath,hti,htv,hw,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  have cert := hp.writeArray hm i v (Evm.compileVal b i) (Evm.compileVal b v)
    (fun h' => Evm.val_sim i h'.core hif) (Evm.val_sim v hm.core hvf)
  rw [hi] at cert
  have he : (Source.evalE G Fsrc (n+4) (sourceStructChildAssign layout sroot si sv)).run y=(.ok (.val (.bool value)),z) := by
    rw [sourceStructChildAssign,Source.evalE,Source.Hoare.run_bind,source_local_value_run G Fsrc (n+2) y sv (.bool value) hsv]
    change ((Source.evalLoc G Fsrc (n+3) (sourceStructChildLoc layout sroot si)) >>= fun loc =>
      Source.writeLoc Fsrc (n+3) loc (.bool value) >>= fun _ => pure (Source.RVal.val (.bool value))).run y=_
    rw [Source.Hoare.run_bind,hr.eval_child_loc G Fsrc n sroot si k hsroot hsi hk]
    change (Source.writeLoc Fsrc (n+3) (.mem (address q.id) k.1.toNat) (.bool value) >>= fun _ => pure (Source.RVal.val (.bool value))).run y=_
    rw [Source.Hoare.run_bind,hs];rfl
  have hstmt := source_expr_statement_run G Fsrc (n+4) Γ.length _ y z (.val (.bool value)) he
  rcases cert with ⟨o,target,ho,hcode,hm',hstack,halloc⟩ | ⟨hbad,_⟩
  · cases Except.ok.inj ho
    refine ⟨out,z,target,hw,hs,he,?_,hi,hcode,hr',hmk,hm',hl,hstack,halloc,hparent,hother,hsource,hex,hev,hlog,hfn⟩
    simpa only [hl] using hstmt
  · cases hbad

def structChildReadCode {C : Contract} {Δ : Ctx} (b : Nat)
    (root : Idx Δ (.mem (.struct s))) (child : Name) (i : Val C Δ .uint) : List Evm.Instr :=
  ([.mload (Evm.cellOf b root)] ++ Evm.Memory.readFieldCode (Evm.Memory.fieldOffset (structDef s) child)) ++
    Evm.compileVal b i ++ Evm.Memory.readArrayStackCode

theorem SourceBoolStructAt.read_child_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {a : Nat} (layout : SourceBoolStructLayout E dn s tag child)
    (G : Source.Glob E) (Fsrc : Source.Fr) (n : Nat)
    (σ : State C Δ) (r : HRef σ.H (.struct s)) (address : Nat → Nat)
    (hr : SourceBoolStructAt y a σ.heap r address layout)
    (sroot : Source.Idx Γ (.struct .memory dn)) (si : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.struct s))) (i : Val C Δ .uint) (k : PrimTy.uint.Denote) (value : Bool)
    (hsroot : y.1.get sroot=.memRef rfl a) (hsi : y.1.get si=sourceUint k)
    (htroot : TEnv.get root σ.env=some r) (hti : i.evalT σ=.ok k)
    (hmf : (Ty.ref (.struct s)).mapFree=true)
    (hv : σ.heap.index (σ.heap.field r layout.child_type) .dyn k=some value)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) (hif : Evm.valIn F i=true) :
    (Source.evalE G Fsrc (n+3) (sourceStructChildRead layout sroot si)).run y=(.ok (.val (.bool value)),y) ∧
    Evm.run (structChildReadCode b root child i) m=.ok (m.push (.val (Evm.bword value))) 0 := by
  refine ⟨hr.eval_child_read G Fsrc n sroot si k value hsroot hsi hv,?_⟩
  let path : MPath C Δ (.ref (.array (.prim .bool))) := .loc (.field (.var root hmf) child layout.child_type)
  let ptr := [.mload (Evm.cellOf b root)] ++ Evm.Memory.readFieldCode (Evm.Memory.fieldOffset (structDef s) child)
  have hp : Evm.Memory.PtrFrag b path ptr := .field _ _ _ (.local root hmf)
  have hc := hp.readArray hm i (Evm.compileVal b i) (fun h' => Evm.val_sim i h'.core hif)
  have he : (Val.readMem (.index .dyn path i)).evalT σ=.ok value := by
    simp only [Val.evalT,MLoc.addrT,path,MPath.mvalT,htroot,hti,Heap.readAddr,hv,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  rw [he] at hc
  rcases hc with ⟨v,w,hv',hw,hcode⟩ | ⟨hbad,_⟩
  · cases Except.ok.inj hv'
    rw [hw.bool_inv] at hcode
    exact hcode
  · cases hbad

theorem SourceBoolStructAt.child_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (.struct s)}
    {address : Nat → Nat} {layout : SourceBoolStructLayout E dn s tag child}
    (hr : SourceBoolStructAt y a hp r address layout) (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (root : Source.Idx Γ (.struct .memory dn)) (i : Source.Idx Γ (.int .u256)) (rhs : Source.Idx Γ .bool)
    (k : PrimTy.uint.Denote) (v : Bool) (hroot : y.1.get root=.memRef rfl a)
    (hi : y.1.get i=sourceUint k) (hvr : y.1.get rhs=.bool v)
    (hk : hp.len (hp.field r layout.child_type) .dyn≤k.1.toNat) :
    (Source.evalLoc G F (n+3) (sourceStructChildLoc layout root i)).run y=
      (.error (.revert (Source.panicData .index)),y) ∧
    (Source.evalE G F (n+4) (sourceStructChildAssign layout root i rhs)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  have hl : (Source.evalLoc G F (n+3) (sourceStructChildLoc layout root i)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
    rw [sourceStructChildLoc,Source.evalLoc,Source.Hoare.run_bind,hr.eval_member_child G F n root hroot]
    change ((Source.evalE G F (n+2) (.local i)) >>= fun v => Source.indexNat v >>= fun k =>
      Source.indexLoc F (.memRef rfl (address (hp.field r layout.child_type).id) : Source.Val E.layout SourceBoolArrayTy) k).run y=_
    rw [Source.Hoare.run_bind,source_local_value_run G F (n+1) y i _ hi]
    exact hr.leaf.indexLoc_bounds F _ hk
  refine ⟨hl,?_⟩
  rw [sourceStructChildAssign,Source.evalE,Source.Hoare.run_bind,source_local_value_run G F (n+2) y rhs (.bool v) hvr]
  change ((Source.evalLoc G F (n+3) (sourceStructChildLoc layout root i)) >>= fun loc =>
    Source.writeLoc F (n+3) loc (.bool v) >>= fun _ => pure (Source.RVal.val (.bool v))).run y=_
  rw [Source.Hoare.run_bind,hl]

theorem source_struct_child_low_horizon {E : Source.Env} {Γ : Source.RCtx}
    (layout : SourceBoolStructLayout E dn s tag child) (G : Source.Glob E) (F : Source.Fr)
    (y : Source.EMState E Γ) (root : Source.Idx Γ (.struct .memory dn)) (i : Source.Idx Γ (.int .u256)) :
    ∀ n,n≤2 → (Source.evalE G F n (sourceStructChildRead layout root i)).run y=(.error .timeout,y) := by
  intro n hn
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | n+3 => omega


/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.eval_child_loc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructAt.eval_child_loc

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.eval_child_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructAt.eval_child_read

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.parent_ne_leaf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructAt.parent_ne_leaf

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.write_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructAt.write_child

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.assign_child_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructAt.assign_child_word

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.read_child_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructAt.read_child_word

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.child_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructAt.child_bounds

/-- info: 'Solidity.Backend.MemoryOps.source_struct_child_low_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_struct_child_low_horizon

end Solidity.Backend.MemoryOps
