import Solidity.Backend.MemoryOps.SourceAlias

/-! INITIAL correspondence of the supported dynamic reference-array -> Boolean
array shape, over existing Source.Data/Source heap and intrinsic Heap/HRef.
This relation mentions no compiler or desired execution/preservation result.
No general graph, injectivity, byte-memory or deep-copy theorem is claimed. -/
namespace Solidity.Backend.MemoryOps
abbrev SourceBoolRefsTy : Source.STy := .array .memory (.array .memory .bool none) none
abbrev BoolRefsRef : RefTy := .array (.ref (.array (.prim .bool)))

def sourceBoolRefMemory {D : Source.Layout} {H : HTy} (address : Nat → Nat)
    (rs : List (HRef H (.array (.prim .bool)))) : Source.Data D SourceBoolRefsTy :=
  .array rs.length (fun _ h => by cases h)
    (fun i => .val (.memRef rfl (address rs[i].id)))

/-- An existing parent table and every actually selected child are represented.
Shared/repeated children are allowed. There is no reverse-address injectivity
premise; this is a read/unchanged-heap certificate, not mutation liveness. -/
structure SourceBoolRefsAt {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (parentAddress : Nat) (hp : Heap H)
    (r : HRef H BoolRefsRef) (address : Nat → Nat) : Prop where
  parent : y.2.heap.get parentAddress=some ⟨SourceBoolRefsTy,sourceBoolRefMemory address (MObj.elems .dyn (hp.get r))⟩
  children : ∀ q ∈ MObj.elems .dyn (hp.get r), SourceBoolMemoryAt y (address q.id) hp q .dyn

theorem SourceBoolRefsAt.parent_read {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {parentAddress : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress hp r address)
    (F : Source.Fr) (i : Nat) (q : HRef H (.array (.prim .bool)))
    (hq : (MObj.elems .dyn (hp.get r))[i]?=some q) :
    (Source.readLoc (E := E) (Γ := Γ) F (τ := .array .memory .bool none) (.mem parentAddress i)).run y=
      (.ok (.memRef rfl (address q.id)),y) := by
  obtain ⟨hi,he⟩ := List.getElem?_eq_some_iff.mp hq
  have hs : (Source.memElem (E := E) (Γ := Γ) parentAddress i (.array .memory .bool none)).run y=
      (.ok (.memRef rfl (address ((MObj.elems .dyn (hp.get r))[i]).id)),y) := by
    rw [Source.memElem,Source.Hoare.run_bind,source_heapObj_run y parentAddress _ hr.parent]
    simp only [sourceBoolRefMemory,hi,↓reduceDIte,Source.Data.asVal]
    rfl
  simpa only [he] using hs

theorem SourceBoolRefsAt.parent_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {parentAddress : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress hp r address)
    (F : Source.Fr) (i : PrimTy.uint.Denote) (hi : hp.len r .dyn≤i.1.toNat) :
    (Source.readLoc (E := E) (Γ := Γ) F (τ := .array .memory .bool none) (.mem parentAddress i.1.toNat)).run y=
      (.error (.revert (Source.panicData .index)),y) ∧ hp.index r .dyn i=none := by
  have hn : ¬i.1.toNat<(MObj.elems .dyn (hp.get r)).length := Nat.not_lt.mpr hi
  constructor
  · change (Source.memElem parentAddress i.1.toNat (.array .memory .bool none)).run y=_
    rw [Source.memElem,Source.Hoare.run_bind,source_heapObj_run y parentAddress _ hr.parent]
    simp only [sourceBoolRefMemory,hn,↓reduceDIte]
    rfl
  · exact List.getElem?_eq_none_iff.mpr hi

theorem SourceBoolRefsAt.child_at {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {parentAddress : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress hp r address)
    (i : Nat) (q : HRef H (.array (.prim .bool)))
    (hq : (MObj.elems .dyn (hp.get r))[i]?=some q) : SourceBoolMemoryAt y (address q.id) hp q .dyn := by
  obtain ⟨hi,he⟩ := List.getElem?_eq_some_iff.mp hq
  apply hr.children q
  rw [←he]
  exact List.getElem_mem hi

theorem SourceBoolRefsAt.index {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {parentAddress : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress hp r address)
    (F : Source.Fr) (i : PrimTy.uint.Denote) (hi : i.1.toNat<hp.len r .dyn) :
    ∃ q, hp.index r .dyn i=some q ∧
      (Source.readLoc (E := E) (Γ := Γ) F (τ := .array .memory .bool none) (.mem parentAddress i.1.toNat)).run y=
        (.ok (.memRef rfl (address q.id)),y) ∧ SourceBoolMemoryAt y (address q.id) hp q .dyn := by
  let rs := MObj.elems .dyn (hp.get r)
  have hq : rs[i.1.toNat]?=some rs[i.1.toNat] := List.getElem?_eq_some_iff.mpr ⟨hi,rfl⟩
  exact ⟨rs[i.1.toNat],hq,hr.parent_read F _ _ hq,hr.child_at _ _ hq⟩

theorem SourceBoolRefsAt.child_read_iff {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {parentAddress : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress hp r address)
    (F : Source.Fr) (i : Nat) (q : HRef H (.array (.prim .bool)))
    (hq : (MObj.elems .dyn (hp.get r))[i]?=some q) (j : PrimTy.uint.Denote) (value : Bool) :
    (Source.readLoc (E := E) (Γ := Γ) F (τ := .bool) (.mem (address q.id) j.1.toNat)).run y=(.ok (.bool value),y) ↔
      hp.index q .dyn j=some value := (hr.child_at i q hq).read_iff F j value

/-- The existing represented word parent and child give actual pointer/value
reads and cells for the SAME child selected by the initial cross-layer relation. -/
theorem SourceBoolRefsAt.word_observe {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {parentAddress : Nat} {σ : State C Δ} {r : HRef σ.H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress σ.heap r address)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m) (Fsrc : Source.Fr)
    (i j : Fin Evm.W) (q : HRef σ.H (.array (.prim .bool))) (value : Bool)
    (hq : σ.heap.index r .dyn (Evm.Memory.indexValue i)=some q)
    (hv : σ.heap.index q .dyn (Evm.Memory.indexValue j)=some value) :
    (Source.readLoc (E := E) (Γ := Γ) Fsrc (τ := .array .memory .bool none) (.mem parentAddress i.val)).run y=
      (.ok (.memRef rfl (address q.id)),y) ∧
    (Source.readLoc (E := E) (Γ := Γ) Fsrc (τ := .bool) (.mem (address q.id) j.val)).run y=(.ok (.bool value),y) ∧
    m.mem ((base r.id).val+1+i.val)=.val (base q.id) ∧
    m.mem ((base q.id).val+1+j.val)=.val (Evm.bword value) ∧
    Evm.run (Evm.Memory.readArrayCode (base r.id)) (m.push (.val i))=.ok (m.push (.val (base q.id))) 0 ∧
    Evm.run (Evm.Memory.readArrayCode (base q.id)) (m.push (.val j))=.ok (m.push (.val (Evm.bword value))) 0 := by
  have hqi : (MObj.elems .dyn (σ.heap.get r))[i.val]?=some q := by
    simpa only [Heap.index,Evm.Memory.indexValue,Int.toNat_natCast] using hq
  have hvj : (MObj.elems .dyn (σ.heap.get q))[j.val]?=some value := by
    simpa only [Heap.index,Evm.Memory.indexValue,Int.toNat_natCast] using hv
  have hs := (hr.child_read_iff Fsrc i.val q hqi (Evm.Memory.indexValue j) value).mpr hv
  have hp := (hm.arrays.arrays r).read i
  simp only [hq,TRes.ofOpt] at hp
  have hc := Evm.Memory.readArray_correct (hm.state.heap.arrays q) j
  simp only [hv,TRes.ofOpt] at hc
  rcases hp with ⟨q',hq',hprun⟩ | ⟨hbad,_⟩
  · cases Except.ok.inj hq'
    rcases hc with ⟨v,w,hv',hw,hcrun⟩ | ⟨hbad,_⟩
    · cases Except.ok.inj hv'
      have hw' : w=.val (Evm.bword value) := hw
      rw [hw'] at hcrun
      exact ⟨hr.parent_read Fsrc i.val q hqi,hs,(hm.arrays.arrays r).elements i.val q hqi,
        (hm.state.heap.arrays q).elements j.val value hvj,hprun,hcrun⟩
    · cases hbad
  · cases hbad

theorem SourceBoolRefsAt.same_heaps {E : Source.Env} {Γ Γ' : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {z : Source.EMState E Γ'} {parentAddress : Nat}
    {hp hp' : Heap H} {r : HRef H BoolRefsRef} {address : Nat → Nat}
    (hr : SourceBoolRefsAt y parentAddress hp r address) (hs : z.2.heap=y.2.heap) (ht : hp'=hp) :
    SourceBoolRefsAt z parentAddress hp' r address := by
  subst hp'
  refine ⟨?_,?_⟩
  · rw [hs];exact hr.parent
  · intro q hq
    unfold SourceBoolMemoryAt
    rw [hs]
    exact hr.children q hq

theorem SourceBoolRefsAt.length_run {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {parentAddress : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress hp r address) (F : Source.Fr) :
    (Source.lengthOf (E := E) (Γ := Γ) F (.memRef rfl parentAddress : Source.Val E.layout SourceBoolRefsTy)).run y=
      (.ok (hp.len r .dyn),y) := by
  simp only [Source.lengthOf,Source.Hoare.run_bind,Heap.len]
  rw [source_heapObj_run y parentAddress _ hr.parent]
  rfl

theorem SourceBoolRefsAt.indexLoc_run {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {parentAddress : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress hp r address) (F : Source.Fr)
    (i : Nat) (hi : i<hp.len r .dyn) :
    (Source.indexLoc (E := E) (Γ := Γ) F (.memRef rfl parentAddress : Source.Val E.layout SourceBoolRefsTy) i).run y=
      (.ok (.mem parentAddress i),y) := by
  rw [Source.indexLoc,Source.Hoare.run_bind,hr.length_run F]
  simp only [hi,↓reduceIte]
  rfl

theorem SourceBoolRefsAt.eval_parent_read {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {parentAddress : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress hp r address)
    (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (root : Source.Idx Γ SourceBoolRefsTy) (index : Source.Idx Γ (.int .u256))
    (k : PrimTy.uint.Denote) (q : HRef H (.array (.prim .bool)))
    (hroot : y.1.get root=.memRef rfl parentAddress) (hindex : y.1.get index=sourceUint k)
    (hq : hp.index r .dyn k=some q) :
    (Source.evalE G F (horizon+2) (.indexArray (.local root) (.local index) rfl)).run y=
      (.ok (.val (.memRef rfl (address q.id))),y) := by
  have hqi : (MObj.elems .dyn (hp.get r))[k.1.toNat]?=some q := hq
  have hk : k.1.toNat<hp.len r .dyn := (List.getElem?_eq_some_iff.mp hqi).1
  rw [Source.evalE,Source.Hoare.run_bind,source_local_value_run G F horizon y root _ hroot]
  change ((Source.evalE G F (horizon+1) (.local index)) >>= fun v => Source.indexNat v >>= fun i =>
    Source.indexLoc F (.memRef rfl parentAddress : Source.Val E.layout SourceBoolRefsTy) i >>= fun loc =>
    Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F horizon y index _ hindex]
  change (Source.indexLoc F (.memRef rfl parentAddress : Source.Val E.layout SourceBoolRefsTy) k.1.toNat >>= fun loc =>
    Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,hr.indexLoc_run F _ hk]
  change (Source.readLoc F (τ := .array .memory .bool none) (.mem parentAddress k.1.toNat) >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,hr.parent_read F _ _ hqi]
  rfl

theorem SourceBoolRefsAt.eval_nested_read {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {parentAddress : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress hp r address)
    (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (root : Source.Idx Γ SourceBoolRefsTy) (i j : Source.Idx Γ (.int .u256))
    (k l : PrimTy.uint.Denote) (q : HRef H (.array (.prim .bool))) (value : Bool)
    (hroot : y.1.get root=.memRef rfl parentAddress) (hi : y.1.get i=sourceUint k) (hj : y.1.get j=sourceUint l)
    (hq : hp.index r .dyn k=some q) (hv : hp.index q .dyn l=some value) :
    (Source.evalE G F (horizon+3) (.indexArray (.indexArray (.local root) (.local i) rfl) (.local j) rfl)).run y=
      (.ok (.val (.bool value)),y) := by
  have hqi : (MObj.elems .dyn (hp.get r))[k.1.toNat]?=some q := hq
  have hc := hr.child_at k.1.toNat q hqi
  have hjb : l.1.toNat<hp.len q .dyn := (List.getElem?_eq_some_iff.mp hv).1
  rw [Source.evalE,Source.Hoare.run_bind,hr.eval_parent_read G F horizon root i k q hroot hi hq]
  change ((Source.evalE G F (horizon+2) (.local j)) >>= fun v => Source.indexNat v >>= fun n =>
    Source.indexLoc F (.memRef rfl (address q.id) : Source.Val E.layout (.array .memory .bool none)) n >>= fun loc =>
    Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F (horizon+1) y j _ hj]
  change (Source.indexLoc F (.memRef rfl (address q.id) : Source.Val E.layout (.array .memory .bool none)) l.1.toNat >>= fun loc =>
    Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,hc.indexLoc_run F _ hjb]
  change (Source.readLoc F (τ := .bool) (.mem (address q.id) l.1.toNat) >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,(hc.read_iff F l value).mpr hv]
  rfl

/-- This supported shape's INITIAL actual table/content relation is transported
through the actual alias operation, not supplied as a reached/post premise. -/
theorem SourceBoolRefsAt.alias_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fsrc : Source.Fr) (horizon : Nat)
    (y : Source.EMState E Γ) (sdst ssrc : Source.Idx Γ SourceBoolRefsTy)
    (parentAddress : Nat) (hs : y.1.get ssrc=.memRef rfl parentAddress)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    (σ : State C Δ) (dst src : Idx Δ (.mem BoolRefsRef)) (r : HRef σ.H BoolRefsRef)
    (ht : TEnv.get src σ.env=some r) (address : Nat → Nat)
    (hr : SourceBoolRefsAt y parentAddress σ.heap r address)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m) :
    let z : Source.EMState E Γ := (y.1.set sdst (.memRef rfl parentAddress),y.2)
    let σ' := σ.setLocal dst (some r)
    let m' := Evm.Memory.writeMachine m (Evm.cellOf b dst) (.val (base r.id))
    (Source.evalE G Fsrc (horizon+2) (sourceLocalAlias sdst ssrc)).run y=(.ok (.val (.memRef rfl parentAddress)),z) ∧
    (Source.execS G Fsrc (horizon+3) Γ.length none
      (.expr (sourceLocalAlias sdst ssrc) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
    Stmt.run σ (.rebindMem dst (.alias (.var src rfl)))=.ok ⟨σ',List.prefix_refl _⟩ ∧
    Evm.run (Evm.Memory.aliasLocalCode b dst src) m=.ok m' 0 ∧
    SourceBoolRefsAt z parentAddress σ'.heap r address ∧ Source.MemOK E SH z ∧
    z.1.get sdst=.memRef rfl parentAddress ∧ TEnv.get dst σ'.env=some r ∧
    Evm.Memory.RefArrayStateRepr L b frame F σ' base m' ∧ m'.stack=m.stack ∧
    Evm.Memory.KeepsAllocator b frame σ base m σ' m' := by
  dsimp only
  obtain ⟨he,hsstmt,hi,hc,hmk,hsh,hth,hdst,hget,hrepr,hstack,ha⟩ :=
    source_alias_word G Fsrc horizon y sdst ssrc rfl parentAddress hs SH hmem σ dst src r ht rfl hm
  exact ⟨he,hsstmt,hi,hc,hr.same_heaps hsh hth,hmk,hdst,hget,hrepr,hstack,ha⟩

theorem SourceBoolRefsAt.indexLoc_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {parentAddress : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress hp r address) (F : Source.Fr)
    (i : Nat) (hi : hp.len r .dyn≤i) :
    (Source.indexLoc (E := E) (Γ := Γ) F (.memRef rfl parentAddress : Source.Val E.layout SourceBoolRefsTy) i).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  rw [Source.indexLoc,Source.Hoare.run_bind,hr.length_run F]
  simp only [show ¬i<hp.len r .dyn from Nat.not_lt.mpr hi,↓reduceIte]
  rfl

theorem SourceBoolRefsAt.eval_parent_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {parentAddress : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress hp r address)
    (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (root : Source.Idx Γ SourceBoolRefsTy) (index : Source.Idx Γ (.int .u256))
    (k : PrimTy.uint.Denote) (hroot : y.1.get root=.memRef rfl parentAddress)
    (hindex : y.1.get index=sourceUint k) (hk : hp.len r .dyn≤k.1.toNat) :
    (Source.evalE G F (horizon+2) (.indexArray (.local root) (.local index) rfl)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  rw [Source.evalE,Source.Hoare.run_bind,source_local_value_run G F horizon y root _ hroot]
  change ((Source.evalE G F (horizon+1) (.local index)) >>= fun v => Source.indexNat v >>= fun i =>
    Source.indexLoc F (.memRef rfl parentAddress : Source.Val E.layout SourceBoolRefsTy) i >>= fun loc =>
    Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F horizon y index _ hindex]
  change (Source.indexLoc F (.memRef rfl parentAddress : Source.Val E.layout SourceBoolRefsTy) k.1.toNat >>= fun loc =>
    Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,hr.indexLoc_bounds F _ hk]

theorem SourceBoolRefsAt.eval_nested_parent_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {parentAddress : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress hp r address)
    (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (root : Source.Idx Γ SourceBoolRefsTy) (i j : Source.Idx Γ (.int .u256))
    (k : PrimTy.uint.Denote) (hroot : y.1.get root=.memRef rfl parentAddress)
    (hi : y.1.get i=sourceUint k) (hk : hp.len r .dyn≤k.1.toNat) :
    (Source.evalE G F (horizon+3) (.indexArray (.indexArray (.local root) (.local i) rfl) (.local j) rfl)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  rw [Source.evalE,Source.Hoare.run_bind,hr.eval_parent_bounds G F horizon root i k hroot hi hk]

theorem SourceBoolRefsAt.eval_nested_child_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {parentAddress : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress hp r address)
    (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (root : Source.Idx Γ SourceBoolRefsTy) (i j : Source.Idx Γ (.int .u256))
    (k l : PrimTy.uint.Denote) (q : HRef H (.array (.prim .bool)))
    (hroot : y.1.get root=.memRef rfl parentAddress) (hi : y.1.get i=sourceUint k) (hj : y.1.get j=sourceUint l)
    (hq : hp.index r .dyn k=some q) (hl : hp.len q .dyn≤l.1.toNat) :
    (Source.evalE G F (horizon+3) (.indexArray (.indexArray (.local root) (.local i) rfl) (.local j) rfl)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  have hc := hr.child_at k.1.toNat q hq
  rw [Source.evalE,Source.Hoare.run_bind,hr.eval_parent_read G F horizon root i k q hroot hi hq]
  change ((Source.evalE G F (horizon+2) (.local j)) >>= fun v => Source.indexNat v >>= fun n =>
    Source.indexLoc F (.memRef rfl (address q.id) : Source.Val E.layout (.array .memory .bool none)) n >>= fun loc =>
    Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F (horizon+1) y j _ hj]
  change (Source.indexLoc F (.memRef rfl (address q.id) : Source.Val E.layout (.array .memory .bool none)) l.1.toNat >>= fun loc =>
    Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,hc.indexLoc_bounds F _ hl]

theorem SourceBoolRefsAt.word_parent_bounds {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {parentAddress : Nat} {σ : State C Δ} {r : HRef σ.H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress σ.heap r address)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m) (Fsrc : Source.Fr)
    (i : Fin Evm.W) (hi : σ.heap.len r .dyn≤i.val) :
    (Source.readLoc (E := E) (Γ := Γ) Fsrc (τ := .array .memory .bool none) (.mem parentAddress i.val)).run y=
      (.error (.revert (Source.panicData .index)),y) ∧
    σ.heap.index r .dyn (Evm.Memory.indexValue i)=none ∧
    Evm.run (Evm.Memory.readArrayCode (base r.id)) (m.push (.val i))=.revert := by
  have hs := hr.parent_bounds Fsrc (Evm.Memory.indexValue i) (by simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using hi)
  have hc := (hm.arrays.arrays r).read i
  simp only [hs.2,TRes.ofOpt] at hc
  rcases hc with ⟨q,hbad,_⟩ | ⟨_,hcode⟩
  · cases hbad
  · exact ⟨hs.1,hs.2,hcode⟩

theorem SourceBoolRefsAt.word_child_bounds {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {parentAddress : Nat} {σ : State C Δ} {r : HRef σ.H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress σ.heap r address)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m) (Fsrc : Source.Fr)
    (i j : Fin Evm.W) (q : HRef σ.H (.array (.prim .bool)))
    (hq : σ.heap.index r .dyn (Evm.Memory.indexValue i)=some q) (hj : σ.heap.len q .dyn≤j.val) :
    (Source.readLoc (E := E) (Γ := Γ) Fsrc (τ := .array .memory .bool none) (.mem parentAddress i.val)).run y=
      (.ok (.memRef rfl (address q.id)),y) ∧
    (Source.readLoc (E := E) (Γ := Γ) Fsrc (τ := .bool) (.mem (address q.id) j.val)).run y=
      (.error (.revert (Source.panicData .index)),y) ∧
    σ.heap.index q .dyn (Evm.Memory.indexValue j)=none ∧
    Evm.run (Evm.Memory.readArrayCode (base q.id)) (m.push (.val j))=.revert := by
  have hqi : (MObj.elems .dyn (σ.heap.get r))[i.val]?=some q := by
    simpa only [Heap.index,Evm.Memory.indexValue,Int.toNat_natCast] using hq
  have hb := source_bool_bounds y (address q.id) _ (hr.child_at i.val q hqi) j.val hj
  have hn : σ.heap.index q .dyn (Evm.Memory.indexValue j)=none := by
    simp only [Heap.index,Evm.Memory.indexValue,Int.toNat_natCast]
    exact List.getElem?_eq_none_iff.mpr hj
  have hc := Evm.Memory.readArray_correct (hm.state.heap.arrays q) j
  simp only [hn,TRes.ofOpt] at hc
  rcases hc with ⟨v,w,hbad,_⟩ | ⟨_,hcode⟩
  · cases hbad
  · exact ⟨hr.parent_read Fsrc _ _ hqi,hb,hn,hcode⟩

/-- Distinct Boolean observations force distinct Source child addresses. This
is derived local separation, not an assumed global identity injection. -/
theorem SourceBoolRefsAt.child_address_ne {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {parentAddress : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress hp r address)
    (F : Source.Fr) (i k : Nat) (q t : HRef H (.array (.prim .bool)))
    (hq : (MObj.elems .dyn (hp.get r))[i]?=some q) (ht : (MObj.elems .dyn (hp.get r))[k]?=some t)
    (j : PrimTy.uint.Denote) (v w : Bool) (hv : hp.index q .dyn j=some v)
    (hw : hp.index t .dyn j=some w) (hne : v≠w) : address q.id≠address t.id := by
  have hs := (hr.child_read_iff F i q hq j v).mpr hv
  have hu := (hr.child_read_iff F k t ht j w).mpr hw
  intro he
  rw [he] at hs
  have hval := congrArg Prod.fst (hs.symm.trans hu)
  exact hne (Source.Val.bool.inj (Except.ok.inj hval))

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.parent_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.parent_read
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.parent_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.parent_bounds
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.child_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.child_at
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.index
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.child_read_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.child_read_iff
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.word_observe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.word_observe
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.same_heaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.same_heaps
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.length_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.length_run
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.indexLoc_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.indexLoc_run
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.eval_parent_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.eval_parent_read
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.eval_nested_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.eval_nested_read
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.alias_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.alias_word
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.indexLoc_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.indexLoc_bounds
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.eval_parent_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.eval_parent_bounds
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.eval_nested_parent_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.eval_nested_parent_bounds
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.eval_nested_child_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.eval_nested_child_bounds
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.word_parent_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.word_parent_bounds
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.word_child_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.word_child_bounds
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.child_address_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.child_address_ne
end Solidity.Backend.MemoryOps
