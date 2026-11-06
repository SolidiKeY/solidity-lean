import Solidity.Backend.MemoryOps.SourceStructChild

/-! Actual deletion through the INITIAL named struct's selected Boolean child.
Existing Source syntax/default construction, intrinsic primitive delete and
published pointer/index/default-write code are composed read-only. -/
namespace Solidity.Backend.MemoryOps
open Semantics

def sourceStructChildDelete {E : Source.Env} {Γ : Source.RCtx}
    (layout : SourceBoolStructLayout E dn s tag child)
    (root : Source.Idx Γ (.struct .memory dn)) (i : Source.Idx Γ (.int .u256)) : Source.RExpr E Γ (.tuple []) :=
  .delete (sourceStructChildLoc layout root i)

def structChildDeleteCode {C : Contract} {Δ : Ctx} (b : Nat)
    (root : Idx Δ (.mem (.struct s))) (child : Name) (i : Val C Δ .uint) : List Evm.Instr :=
  structChildWriteCode b root child i (Evm.Memory.deleteDefaultValue .bool)

theorem SourceBoolStructAt.delete_child_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {a : Nat} (layout : SourceBoolStructLayout E dn s tag child)
    (G : Source.Glob E) (Fsrc : Source.Fr) (n : Nat)
    (σ : State C Δ) (r : HRef σ.H (.struct s)) (address : Nat → Nat)
    (hr : SourceBoolStructAt y a σ.heap r address layout)
    (sroot : Source.Idx Γ (.struct .memory dn)) (si : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.struct s))) (i : Val C Δ .uint) (k : PrimTy.uint.Denote)
    (hsroot : y.1.get sroot=.memRef rfl a) (hsi : y.1.get si=sourceUint k)
    (htroot : TEnv.get root σ.env=some r) (hti : i.evalT σ=.ok k)
    (hmf : (Ty.ref (.struct s)).mapFree=true)
    (hk : k.1.toNat<σ.heap.len (σ.heap.field r layout.child_type) .dyn)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) (hif : Evm.valIn F i=true) :
    let q := σ.heap.field r layout.child_type
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ) (target : Evm.Machine),
      σ.heap.writeAddr (.index q .dyn k) (PrimTy.dflt .bool)=some out ∧
      (Source.deleteLoc (E := E) (Γ := Γ) Fsrc (n+3) (τ := .bool) (.mem (address q.id) k.1.toNat)).run y=(.ok (),z) ∧
      (Source.evalE G Fsrc (n+4) (sourceStructChildDelete layout sroot si)).run y=(.ok Source.RVal.unit,z) ∧
      (Source.execS G Fsrc (n+5) Γ.length none
        (.expr (sourceStructChildDelete layout sroot si) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal y.1),(.nil,z.2)) ∧
      Stmt.run σ (.deleteMem (.loc (.index .dyn (.loc (.field (.var root hmf) child layout.child_type)) i)) rfl)=
        .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (structChildDeleteCode b root child i) m=.ok target 0 ∧
      SourceBoolStructAt z a out r address layout ∧ Source.MemOK E SH z ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap out) base target ∧
      z.1=y.1 ∧ target.stack=m.stack ∧ Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out) target ∧
      out.get r=σ.heap.get r ∧
      (∀ {R : RefTy} (t : HRef σ.H R),q.id≠t.id → out.get t=σ.heap.get t) ∧
      (∀ b,b≠address q.id → z.2.heap.get b=y.2.heap.get b) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  dsimp only
  let q := σ.heap.field r layout.child_type
  obtain ⟨out,z,hw,hs,hr',hmk,hl,hparent,hother,hsource,hex,hev,hlog,hfn⟩ := hr.write_child Fsrc (n+3) k false hk SH hmem
  have hdel : (Source.deleteLoc (E := E) (Γ := Γ) Fsrc (n+3) (τ := .bool) (.mem (address q.id) k.1.toNat)).run y=(.ok (),z) := hs
  let path : MPath C Δ (.ref (.array (.prim .bool))) := .loc (.field (.var root hmf) child layout.child_type)
  let ptr := [.mload (Evm.cellOf b root)] ++ Evm.Memory.readFieldCode (Evm.Memory.fieldOffset (structDef s) child)
  have hp : Evm.Memory.PtrFrag b path ptr := .field _ _ _ (.local root hmf)
  have hpath : path.mvalT σ=.ok q := by
    simp only [path,MPath.mvalT,MLoc.addrT,htroot,Heap.readAddr,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    rfl
  change σ.heap.writeAddr (.index q .dyn k) false=some out at hw
  have hi : TRun.assignMem (.index .dyn path i) (.val (Evm.Memory.deleteDefaultValue .bool)) σ=
      .ok ⟨σ.withHeap out,List.prefix_refl _⟩ := by
    simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,hpath,hti,Evm.Memory.deleteDefaultValue_eval,PrimTy.dflt,
      hw,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  have hdelete : TRun.deleteMem (.loc (.index .dyn path i)) σ=.ok ⟨σ.withHeap out,List.prefix_refl _⟩ := by
    rw [Evm.Memory.deleteMem_primitive_eq_assign]
    exact hi
  have cert := hp.writeArray hm i (Evm.Memory.deleteDefaultValue .bool) (Evm.compileVal b i)
    (Evm.compileVal b (Evm.Memory.deleteDefaultValue .bool))
    (fun h' => Evm.val_sim i h'.core hif) (Evm.val_sim (Evm.Memory.deleteDefaultValue .bool) hm.core rfl)
  rw [hi] at cert
  have he : (Source.evalE G Fsrc (n+4) (sourceStructChildDelete layout sroot si)).run y=(.ok Source.RVal.unit,z) := by
    rw [sourceStructChildDelete,Source.evalE,Source.Hoare.run_bind,hr.eval_child_loc G Fsrc n sroot si k hsroot hsi hk]
    change (Source.deleteLoc Fsrc (n+3) (τ := .bool) (.mem (address q.id) k.1.toNat) >>= fun _ => pure Source.RVal.unit).run y=_
    rw [Source.Hoare.run_bind,hdel];rfl
  have hstmt := source_expr_statement_run G Fsrc (n+4) Γ.length _ y z Source.RVal.unit he
  rcases cert with ⟨o,target,ho,hcode,hm',hstack,halloc⟩ | ⟨hbad,_⟩
  · cases Except.ok.inj ho
    refine ⟨out,z,target,hw,hdel,he,?_,hdelete,hcode,hr',hmk,hm',hl,hstack,halloc,hparent,hother,hsource,hex,hev,hlog,hfn⟩
    simpa only [hl] using hstmt
  · cases hbad

theorem SourceBoolStructAt.delete_child_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (.struct s)}
    {address : Nat → Nat} {layout : SourceBoolStructLayout E dn s tag child}
    (hr : SourceBoolStructAt y a hp r address layout) (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (root : Source.Idx Γ (.struct .memory dn)) (i : Source.Idx Γ (.int .u256)) (k : PrimTy.uint.Denote)
    (hroot : y.1.get root=.memRef rfl a) (hi : y.1.get i=sourceUint k)
    (hk : hp.len (hp.field r layout.child_type) .dyn≤k.1.toNat) :
    (Source.evalE G F (n+4) (sourceStructChildDelete layout root i)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  have hl : (Source.evalLoc G F (n+3) (sourceStructChildLoc layout root i)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
    rw [sourceStructChildLoc,Source.evalLoc,Source.Hoare.run_bind,hr.eval_member_child G F n root hroot]
    change ((Source.evalE G F (n+2) (.local i)) >>= fun v => Source.indexNat v >>= fun k =>
      Source.indexLoc F (.memRef rfl (address (hp.field r layout.child_type).id) : Source.Val E.layout SourceBoolArrayTy) k).run y=_
    rw [Source.Hoare.run_bind,source_local_value_run G F (n+1) y i _ hi]
    exact hr.leaf.indexLoc_bounds F _ hk
  rw [sourceStructChildDelete,Source.evalE,Source.Hoare.run_bind,hl]

theorem source_struct_delete_low_horizon {E : Source.Env} {Γ : Source.RCtx}
    (layout : SourceBoolStructLayout E dn s tag child) (G : Source.Glob E) (F : Source.Fr)
    (y : Source.EMState E Γ) (root : Source.Idx Γ (.struct .memory dn)) (i : Source.Idx Γ (.int .u256)) :
    ∀ n,n≤3 → (Source.evalE G F n (sourceStructChildDelete layout root i)).run y=(.error .timeout,y) := by
  intro n hn
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | n+4 => omega


/-- Operation-side Source application without an assumed word representation.
The actual primitive default and reached finite observer are derived. -/
theorem SourceBoolStructAt.delete_child_source {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (.struct s)}
    {address : Nat → Nat} {layout : SourceBoolStructLayout E dn s tag child}
    (hr : SourceBoolStructAt y a hp r address layout) (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (root : Source.Idx Γ (.struct .memory dn)) (i : Source.Idx Γ (.int .u256)) (k : PrimTy.uint.Denote)
    (hroot : y.1.get root=.memRef rfl a) (hi : y.1.get i=sourceUint k)
    (hk : k.1.toNat<hp.len (hp.field r layout.child_type) .dyn)
    (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    let q := hp.field r layout.child_type
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      hp.writeAddr (.index q .dyn k) (PrimTy.dflt .bool)=some out ∧
      (Source.evalE G F (n+4) (sourceStructChildDelete layout root i)).run y=(.ok Source.RVal.unit,z) ∧
      SourceBoolStructAt z a out r address layout ∧ Source.MemOK E SH z ∧
      z.1=y.1 ∧ out.get r=hp.get r := by
  dsimp only
  obtain ⟨out,z,hw,hs,hr',hm',hl,hparent,tail⟩ := hr.write_child F (n+3) k false hk SH hm
  have hd : (Source.deleteLoc (E := E) (Γ := Γ) F (n+3) (τ := .bool)
      (.mem (address (hp.field r layout.child_type).id) k.1.toNat)).run y=(.ok (),z) := hs
  refine ⟨out,z,hw,?_,hr',hm',hl,hparent⟩
  rw [sourceStructChildDelete,Source.evalE,Source.Hoare.run_bind,hr.eval_child_loc G F n root i k hroot hi hk]
  change (Source.deleteLoc F (n+3) (τ := .bool) (.mem (address (hp.field r layout.child_type).id) k.1.toNat) >>= fun _ => pure Source.RVal.unit).run y=_
  rw [Source.Hoare.run_bind,hd];rfl

/-- General reached rejection. Source panic payload and symbolic word revert
are deliberately separate; no heap/state is supplied for an unexecuted suffix. -/
theorem SourceBoolStructAt.delete_child_word_bounds
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {a : Nat} (layout : SourceBoolStructLayout E dn s tag child)
    (G : Source.Glob E) (Fsrc : Source.Fr) (n : Nat)
    (σ : State C Δ) (r : HRef σ.H (.struct s)) (address : Nat → Nat)
    (hr : SourceBoolStructAt y a σ.heap r address layout)
    (sroot : Source.Idx Γ (.struct .memory dn)) (si : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.struct s))) (i : Val C Δ .uint) (k : PrimTy.uint.Denote)
    (hsroot : y.1.get sroot=.memRef rfl a) (hsi : y.1.get si=sourceUint k)
    (htroot : TEnv.get root σ.env=some r) (hti : i.evalT σ=.ok k)
    (hmf : (Ty.ref (.struct s)).mapFree=true)
    (hk : σ.heap.len (σ.heap.field r layout.child_type) .dyn≤k.1.toNat)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) (hif : Evm.valIn F i=true) :
    (Source.evalE G Fsrc (n+4) (sourceStructChildDelete layout sroot si)).run y=
      (.error (.revert (Source.panicData .index)),y) ∧
    σ.heap.writeAddr (.index (σ.heap.field r layout.child_type) .dyn k) (PrimTy.dflt .bool)=none ∧
    Stmt.run σ (.deleteMem (.loc (.index .dyn (.loc (.field (.var root hmf) child layout.child_type)) i)) rfl)=.error .revert ∧
    Evm.run (structChildDeleteCode b root child i) m=.revert := by
  let q := σ.heap.field r layout.child_type
  have hn : σ.heap.writeAddr (.index q .dyn k) false=none := by
    unfold Heap.writeAddr Heap.setIndex
    exact if_neg (Nat.not_lt.mpr hk)
  let path : MPath C Δ (.ref (.array (.prim .bool))) := .loc (.field (.var root hmf) child layout.child_type)
  let ptr := [.mload (Evm.cellOf b root)] ++ Evm.Memory.readFieldCode (Evm.Memory.fieldOffset (structDef s) child)
  have hp : Evm.Memory.PtrFrag b path ptr := .field _ _ _ (.local root hmf)
  have hpath : path.mvalT σ=.ok q := by
    simp only [path,MPath.mvalT,MLoc.addrT,htroot,Heap.readAddr,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    rfl
  have hi : TRun.assignMem (.index .dyn path i) (.val (Evm.Memory.deleteDefaultValue .bool)) σ=.error .revert := by
    simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,hpath,hti,Evm.Memory.deleteDefaultValue_eval,PrimTy.dflt,
      hn,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  have hd : TRun.deleteMem (.loc (.index .dyn path i)) σ=.error .revert := by
    rw [Evm.Memory.deleteMem_primitive_eq_assign];exact hi
  have hc := hp.writeArray hm i (Evm.Memory.deleteDefaultValue .bool) (Evm.compileVal b i)
    (Evm.compileVal b (Evm.Memory.deleteDefaultValue .bool))
    (fun h' => Evm.val_sim i h'.core hif) (Evm.val_sim (Evm.Memory.deleteDefaultValue .bool) hm.core rfl)
  rw [hi] at hc
  refine ⟨hr.delete_child_bounds G Fsrc n sroot si k hsroot hsi hk,hn,hd,?_⟩
  rcases hc with ⟨o,_,he,_⟩ | ⟨_,hc⟩
  · cases he
  · exact hc


/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.delete_child_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructAt.delete_child_word

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.delete_child_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructAt.delete_child_bounds

/-- info: 'Solidity.Backend.MemoryOps.source_struct_delete_low_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_struct_delete_low_horizon

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.delete_child_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructAt.delete_child_source

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.delete_child_word_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructAt.delete_child_word_bounds

end Solidity.Backend.MemoryOps
