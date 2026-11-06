import Solidity.Backend.MemoryOps.SourceStructAssignment

/-! Actual local alias rebinding FROM an initially represented struct member.
The selected identity is derived from Source Data and the named intrinsic field,
not independently supplied initial source/target pointers. -/
namespace Solidity.Backend.MemoryOps
open Semantics

theorem SourceBoolStructAt.same_heaps {E : Source.Env} {Γ Γ' : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {z : Source.EMState E Γ'} {a : Nat} {hp hp' : Heap H}
    {r : HRef H (.struct s)} {address : Nat → Nat} {layout : SourceBoolStructLayout E dn s tag child}
    (hr : SourceBoolStructAt y a hp r address layout) (hs : z.2.heap=y.2.heap) (ht : hp'=hp) :
    SourceBoolStructAt z a hp' r address layout := by
  subst hp'
  refine ⟨?_,?_⟩
  · rw [hs];exact hr.parent
  · unfold SourceBoolMemoryAt
    rw [hs];exact hr.leaf

def sourceStructSelectedAlias {E : Source.Env} {Γ : Source.RCtx}
    (layout : SourceBoolStructLayout E dn s tag child)
    (dst : Source.Idx Γ SourceBoolArrayTy) (root : Source.Idx Γ (.struct .memory dn)) :
    Source.RExpr E Γ SourceBoolArrayTy :=
  .assign (.local dst) (.member (.local root) 1 layout.source_child_type)

def structSelectedAliasCode {Γ : Ctx} (b : Nat) (dst : Idx Γ (.mem (.array (.prim .bool))))
    (root : Idx Γ (.mem (.struct s))) (child : Name) : List Evm.Instr :=
  ([.mload (Evm.cellOf b root)] ++ Evm.Memory.readFieldCode (Evm.Memory.fieldOffset (structDef s) child)) ++
    [.mstore (Evm.cellOf b dst)]

theorem SourceBoolStructAt.eval_selected_alias {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (.struct s)}
    {address : Nat → Nat} {layout : SourceBoolStructLayout E dn s tag child}
    (hr : SourceBoolStructAt y a hp r address layout) (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (dst : Source.Idx Γ SourceBoolArrayTy) (root : Source.Idx Γ (.struct .memory dn))
    (hroot : y.1.get root=.memRef rfl a) :
    (Source.evalE G F (n+3) (sourceStructSelectedAlias layout dst root)).run y=
      (.ok (.val (.memRef rfl (address (hp.field r layout.child_type).id))),
        (y.1.set dst (.memRef rfl (address (hp.field r layout.child_type).id)),y.2)) := by
  rw [sourceStructSelectedAlias,Source.evalE,Source.Hoare.run_bind,hr.eval_member_child G F n root hroot]
  change ((Source.evalLoc G F (n+2) (.local dst)) >>= fun loc =>
    Source.writeLoc F (n+2) loc (.memRef rfl (address (hp.field r layout.child_type).id)) >>=
      fun _ => pure (Source.RVal.val (.memRef rfl (address (hp.field r layout.child_type).id)))).run y=_
  rw [Source.Hoare.run_bind,show (Source.evalLoc G F (n+2) (.local dst)).run y=(.ok (.local dst),y) from rfl]
  rfl

/-- INITIAL parent/child correspondence couples the SAME selected logical child
across Source and word/intrinsic local rebinding. Both heaps remain unchanged. -/
theorem SourceBoolStructAt.selected_alias_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {a : Nat} (layout : SourceBoolStructLayout E dn s tag child)
    (G : Source.Glob E) (Fsrc : Source.Fr) (n : Nat)
    (σ : State C Δ) (r : HRef σ.H (.struct s)) (address : Nat → Nat)
    (hr : SourceBoolStructAt y a σ.heap r address layout)
    (sdst : Source.Idx Γ SourceBoolArrayTy) (sroot : Source.Idx Γ (.struct .memory dn))
    (dst : Idx Δ (.mem (.array (.prim .bool)))) (root : Idx Δ (.mem (.struct s)))
    (hsroot : y.1.get sroot=.memRef rfl a) (htroot : TEnv.get root σ.env=some r)
    (hmf : (Ty.ref (.struct s)).mapFree=true) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) :
    let q := σ.heap.field r layout.child_type
    let z : Source.EMState E Γ := (y.1.set sdst (.memRef rfl (address q.id)),y.2)
    let st := σ.setLocal dst (some q)
    let target := Evm.Memory.writeMachine m (Evm.cellOf b dst) (.val (base q.id))
    (Source.evalE G Fsrc (n+3) (sourceStructSelectedAlias layout sdst sroot)).run y=
      (.ok (.val (.memRef rfl (address q.id))),z) ∧
    (Source.execS G Fsrc (n+4) Γ.length none
      (.expr (sourceStructSelectedAlias layout sdst sroot) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
    Stmt.run σ (.rebindMem dst (.alias (.loc (.field (.var root hmf) child layout.child_type))))=
      .ok ⟨st,List.prefix_refl _⟩ ∧
    Evm.run (structSelectedAliasCode b dst root child) m=.ok target 0 ∧
    SourceBoolStructAt z a st.heap r address layout ∧ SourceBoolMemoryAt z (address q.id) st.heap q .dyn ∧
    Source.MemOK E SH z ∧ Evm.Memory.StateRepr L b frame F st base target ∧
    z.2.heap=y.2.heap ∧ st.heap=σ.heap ∧
    z.1.get sdst=.memRef rfl (address q.id) ∧ TEnv.get dst st.env=some q ∧
    target.stack=m.stack ∧ Evm.Memory.KeepsAllocator b frame σ base m st target := by
  dsimp only
  let q := σ.heap.field r layout.child_type
  let z : Source.EMState E Γ := (y.1.set sdst (.memRef rfl (address q.id)),y.2)
  have he := hr.eval_selected_alias G Fsrc n sdst sroot hsroot
  have hs := source_expr_statement_run G Fsrc (n+3) Γ.length _ y z (.val (.memRef rfl (address q.id))) he
  have hvty : y.2.heap.ty (address q.id)=some SourceBoolArrayTy := by
    change (y.2.heap.get (address q.id)).map Sigma.fst=some _
    rw [hr.leaf];rfl
  have hm' := Source.writeLoc_memOK (E := E) (Γ := Γ) (H := SH) Fsrc (n+2)
    (.local sdst) (.memRef rfl (address q.id)) y ⟨hmem,⟨_,hvty,rfl⟩⟩
  have hw : (Source.writeLoc (E := E) (Γ := Γ) Fsrc (n+2) (.local sdst) (.memRef rfl (address q.id))).run y=(.ok (),z) := rfl
  rw [hw] at hm'
  let path : MPath C Δ (.ref (.array (.prim .bool))) := .loc (.field (.var root hmf) child layout.child_type)
  let code := [.mload (Evm.cellOf b root)] ++ Evm.Memory.readFieldCode (Evm.Memory.fieldOffset (structDef s) child)
  have ptr : Evm.Memory.PtrFrag b path code := .field _ _ _ (.local root hmf)
  have hp : path.mvalT σ=.ok q := by
    simp only [path,MPath.mvalT,MLoc.addrT,htroot,Heap.readAddr,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    rfl
  have hi : Stmt.run σ (.rebindMem dst (.alias path))=.ok ⟨σ.setLocal dst (some q),List.prefix_refl _⟩ := by
    change TRun.rebindMem dst (.alias path) σ=_
    simp only [TRun.rebindMem,MRhs.evalT,hp,bind,Except.bind,pure,Except.pure]
  have cert := ptr.rebind hm dst
  rw [show TRun.rebindMem dst (.alias path) σ=.ok ⟨σ.setLocal dst (some q),List.prefix_refl _⟩ from hi] at cert
  have hcode : Evm.run (structSelectedAliasCode b dst root child) m=
      .ok (Evm.Memory.writeMachine m (Evm.cellOf b dst) (.val (base q.id))) 0 := by
    rw [structSelectedAliasCode,Evm.run_append_ok (ptr.run_of_eval hm hp)]
    rfl
  rcases cert with ⟨o,m',ho,hc,hstate,hstack,halloc⟩ | ⟨hbad,_⟩
  · cases Except.ok.inj ho
    have ht := (Evm.Out.ok.inj (hc.symm.trans hcode)).1
    subst m'
    exact ⟨he,hs,hi,hcode,hr.same_heaps rfl rfl,hr.leaf,hm',hstate,rfl,rfl,
      source_locals_get_set _ _ _,TEnv.get_set _ _ _,hstack,halloc⟩
  · cases hbad

theorem source_struct_select_low_horizon {E : Source.Env} {Γ : Source.RCtx}
    (layout : SourceBoolStructLayout E dn s tag child) (G : Source.Glob E) (F : Source.Fr)
    (y : Source.EMState E Γ) (dst : Source.Idx Γ SourceBoolArrayTy) (root : Source.Idx Γ (.struct .memory dn)) :
    ∀ n,n≤2 → (Source.evalE G F n (sourceStructSelectedAlias layout dst root)).run y=(.error .timeout,y) := by
  intro n hn
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | n+3 => omega
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.same_heaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructAt.same_heaps

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.eval_selected_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructAt.eval_selected_alias

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.selected_alias_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructAt.selected_alias_word

/-- info: 'Solidity.Backend.MemoryOps.source_struct_select_low_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_struct_select_low_horizon

end Solidity.Backend.MemoryOps
