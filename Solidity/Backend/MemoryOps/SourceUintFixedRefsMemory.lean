import Solidity.Backend.MemoryOps.SourceUintFixedAssignment

/-! Initial Source correspondence for an existing dynamic reference parent
whose children are genuine fixed uint arrays. No constructor/compiler, reverse
address injection, mutation-liveness or Source admission theorem is supplied. -/
namespace Solidity.Backend.MemoryOps

abbrev SourceUintFixedRefsTy (n : Nat) : Source.STy :=
  .array .memory (.array .memory (.int .u256) (some n)) none
abbrev UintFixedRefsRef (n : Nat) : RefTy := .array (.ref (.fixed (.prim .uint) n))

def sourceUintFixedRefMemory {D : Source.Layout} {H : HTy} {n : Nat} (address : Nat → Nat)
    (rs : List (HRef H (.fixed (.prim .uint) n))) : Source.Data D (SourceUintFixedRefsTy n) :=
  .array rs.length (fun _ h => by cases h) (fun i => .val (.memRef rfl (address rs[i].id)))

structure SourceUintFixedRefsAt {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    (y : Source.EMState E Γ) (parentAddress : Nat) (hp : Heap H)
    (r : HRef H (UintFixedRefsRef n)) (address : Nat → Nat) : Prop where
  parent : y.2.heap.get parentAddress=some ⟨SourceUintFixedRefsTy n,sourceUintFixedRefMemory address (MObj.elems .dyn (hp.get r))⟩
  children : ∀ q∈MObj.elems .dyn (hp.get r),SourceUintFixedAt y (address q.id) hp q

theorem SourceUintFixedRefsAt.parent_read {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (UintFixedRefsRef n)} {address : Nat → Nat}
    (hr : SourceUintFixedRefsAt y a hp r address) (F : Source.Fr) (i : Nat) (q : HRef H (.fixed (.prim .uint) n))
    (hit : (MObj.elems .dyn (hp.get r))[i]?=some q) :
    (Source.readLoc (E := E) (Γ := Γ) F (τ := .array .memory (.int .u256) (some n)) (.mem a i)).run y=
      (.ok (.memRef rfl (address q.id)),y) := by
  first
  | solve | simp only [] | omega
  | obtain ⟨hi,eq⟩ := List.getElem?_eq_some_iff.mp hit
    have run : (Source.memElem (E := E) (Γ := Γ) a i (.array .memory (.int .u256) (some n))).run y=
        (.ok (.memRef rfl (address ((MObj.elems .dyn (hp.get r))[i]).id)),y) := by
      rw [Source.memElem,Source.Hoare.run_bind,source_heapObj_run y a _ hr.parent]
      simp only [sourceUintFixedRefMemory,hi,↓reduceDIte,Source.Data.asVal]
      rfl
    simpa only [eq] using run

theorem SourceUintFixedRefsAt.parent_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (UintFixedRefsRef n)} {address : Nat → Nat}
    (hr : SourceUintFixedRefsAt y a hp r address) (F : Source.Fr) (i : PrimTy.uint.Denote) (hi : hp.len r .dyn≤i.1.toNat) :
    (Source.readLoc (E := E) (Γ := Γ) F (τ := .array .memory (.int .u256) (some n)) (.mem a i.1.toNat)).run y=
      (.error (.revert (Source.panicData .index)),y) ∧ hp.index r .dyn i=none := by
  first
  | solve | simp only [] | omega
  | have outside : ¬i.1.toNat<(MObj.elems .dyn (hp.get r)).length := Nat.not_lt.mpr hi
    constructor
    · change (Source.memElem a i.1.toNat (.array .memory (.int .u256) (some n))).run y=_
      rw [Source.memElem,Source.Hoare.run_bind,source_heapObj_run y a _ hr.parent]
      simp only [sourceUintFixedRefMemory,outside,↓reduceDIte]
      rfl
    · exact List.getElem?_eq_none_iff.mpr hi

theorem SourceUintFixedRefsAt.child_at {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (UintFixedRefsRef n)} {address : Nat → Nat}
    (hr : SourceUintFixedRefsAt y a hp r address) (i : Nat) (q : HRef H (.fixed (.prim .uint) n))
    (hit : (MObj.elems .dyn (hp.get r))[i]?=some q) : SourceUintFixedAt y (address q.id) hp q := by
  obtain ⟨hi,eq⟩ := List.getElem?_eq_some_iff.mp hit
  apply hr.children q
  rw [←eq]
  exact List.getElem_mem hi

theorem SourceUintFixedRefsAt.parent_ne_child {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (UintFixedRefsRef n)} {address : Nat → Nat}
    (hr : SourceUintFixedRefsAt y a hp r address) (q : HRef H (.fixed (.prim .uint) n))
    (member : q∈MObj.elems .dyn (hp.get r)) : a≠address q.id := by
  intro same
  have child := hr.children q member
  rw [←same] at child
  have types := congrArg Sigma.fst (Option.some.inj (hr.parent.symm.trans child))
  cases types

theorem SourceUintFixedRefsAt.length_run {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (UintFixedRefsRef n)} {address : Nat → Nat}
    (hr : SourceUintFixedRefsAt y a hp r address) (F : Source.Fr) :
    (Source.lengthOf (E := E) (Γ := Γ) F (.memRef rfl a : Source.Val E.layout (SourceUintFixedRefsTy n))).run y=
      (.ok (hp.len r .dyn),y) := by
  simp only [Source.lengthOf,Source.Hoare.run_bind,Heap.len]
  rw [source_heapObj_run y a _ hr.parent]
  rfl

theorem SourceUintFixedRefsAt.indexLoc_run {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (UintFixedRefsRef n)} {address : Nat → Nat}
    (hr : SourceUintFixedRefsAt y a hp r address) (F : Source.Fr) (i : Nat) (hi : i<hp.len r .dyn) :
    (Source.indexLoc (E := E) (Γ := Γ) F (.memRef rfl a : Source.Val E.layout (SourceUintFixedRefsTy n)) i).run y=
      (.ok (.mem a i),y) := by
  rw [Source.indexLoc,Source.Hoare.run_bind,hr.length_run F]
  simp only [hi,↓reduceIte]
  rfl

theorem SourceUintFixedRefsAt.eval_parent_read {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (UintFixedRefsRef n)} {address : Nat → Nat}
    (hr : SourceUintFixedRefsAt y a hp r address) (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (root : Source.Idx Γ (SourceUintFixedRefsTy n)) (index : Source.Idx Γ (.int .u256))
    (k : PrimTy.uint.Denote) (q : HRef H (.fixed (.prim .uint) n))
    (hroot : y.1.get root=.memRef rfl a) (hindex : y.1.get index=sourceUint k)
    (hq : hp.index r .dyn k=some q) :
    (Source.evalE G F (horizon+2) (.indexArray (.local root) (.local index) rfl)).run y=
      (.ok (.val (.memRef rfl (address q.id))),y) := by
  have hqi : (MObj.elems .dyn (hp.get r))[k.1.toNat]?=some q := hq
  have hk : k.1.toNat<hp.len r .dyn := (List.getElem?_eq_some_iff.mp hqi).1
  rw [Source.evalE,Source.Hoare.run_bind,source_local_value_run G F horizon y root _ hroot]
  change ((Source.evalE G F (horizon+1) (.local index)) >>= fun v => Source.indexNat v >>= fun i =>
    Source.indexLoc F (.memRef rfl a : Source.Val E.layout (SourceUintFixedRefsTy n)) i >>= fun loc =>
    Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F horizon y index _ hindex]
  change (Source.indexLoc F (.memRef rfl a : Source.Val E.layout (SourceUintFixedRefsTy n)) k.1.toNat >>= fun loc =>
    Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,hr.indexLoc_run F _ hk]
  change (Source.readLoc F (τ := .array .memory (.int .u256) (some n)) (.mem a k.1.toNat) >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,hr.parent_read F _ _ hqi]
  rfl

theorem SourceUintFixedRefsAt.eval_nested_read {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (UintFixedRefsRef n)} {address : Nat → Nat}
    (hr : SourceUintFixedRefsAt y a hp r address) (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (root : Source.Idx Γ (SourceUintFixedRefsTy n)) (i j : Source.Idx Γ (.int .u256))
    (k l : PrimTy.uint.Denote) (q : HRef H (.fixed (.prim .uint) n))
    (hroot : y.1.get root=.memRef rfl a) (hi : y.1.get i=sourceUint k) (hj : y.1.get j=sourceUint l)
    (hq : hp.index r .dyn k=some q) (hl : l.1.toNat<n) :
    let value := (hp.get q).1[l.1.toNat]'(by rw [(hp.get q).2];exact hl)
    hp.index q .fixed l=some value ∧
    (Source.evalE G F (horizon+3) (.indexArray (.indexArray (.local root) (.local i) rfl) (.local j) rfl)).run y=
      (.ok (.val (sourceUint value)),y) := by
  first
  | solve | simp only [] | omega
  | dsimp only
    have hqi : (MObj.elems .dyn (hp.get r))[k.1.toNat]?=some q := hq
    have child := hr.child_at k.1.toNat q hqi
    have fixedLoc : (Source.indexLoc (E := E) (Γ := Γ) F
        (.memRef rfl (address q.id) : Source.Val E.layout (.array .memory (.int .u256) (some n))) l.1.toNat).run y=
          (.ok (.mem (address q.id) l.1.toNat),y) := by
      rw [Source.indexLoc,Source.lengthOf]
      simp only [Source.Hoare.run_bind]
      change (if l.1.toNat<n then pure (Source.Loc.mem (address q.id) l.1.toNat : Source.Loc E.layout Γ (.int .u256)) else Source.EM.lift (Source.panic .index)).run y=_
      rw [if_pos hl]
      rfl
    constructor
    · change (MObj.elems .fixed (hp.get q))[l.1.toNat]?=some _
      rw [MObj.elems_fixed]
      exact List.getElem?_eq_getElem (by rw [(hp.get q).2];exact hl)
    · rw [Source.evalE,Source.Hoare.run_bind,hr.eval_parent_read G F horizon root i k q hroot hi hq]
      change ((Source.evalE G F (horizon+2) (.local j)) >>= fun v => Source.indexNat v >>= fun index =>
        Source.indexLoc F (.memRef rfl (address q.id) : Source.Val E.layout (.array .memory (.int .u256) (some n))) index >>= fun loc =>
        Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
      rw [Source.Hoare.run_bind,source_local_value_run G F (horizon+1) y j _ hj]
      change (Source.indexLoc F (.memRef rfl (address q.id) : Source.Val E.layout (.array .memory (.int .u256) (some n))) l.1.toNat >>= fun loc =>
        Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
      rw [Source.Hoare.run_bind,fixedLoc]
      change (Source.readLoc F (τ := .int .u256) (.mem (address q.id) l.1.toNat) >>= fun v => pure (Source.RVal.val v)).run y=_
      have childRead : (Source.readLoc (E := E) (Γ := Γ) F (τ := .int .u256) (.mem (address q.id) l.1.toNat)).run y=
          (.ok (sourceUint ((hp.get q).1[l.1.toNat]'(by rw [(hp.get q).2];exact hl))),y) := child.read l.1.toNat hl
      rw [Source.Hoare.run_bind,childRead]
      rfl

/-- Initial parent bounds select the child and value, with neither supplied
as an output premise. Parent length and declared child length stay arbitrary. -/
theorem SourceUintFixedRefsAt.observe {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (UintFixedRefsRef n)} {address : Nat → Nat}
    (hr : SourceUintFixedRefsAt y a hp r address) (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (root : Source.Idx Γ (SourceUintFixedRefsTy n)) (i j : Source.Idx Γ (.int .u256))
    (k l : PrimTy.uint.Denote) (hroot : y.1.get root=.memRef rfl a)
    (hi : y.1.get i=sourceUint k) (hj : y.1.get j=sourceUint l)
    (parentBound : k.1.toNat<hp.len r .dyn) (childBound : l.1.toNat<n) :
    ∃ (q : HRef H (.fixed (.prim .uint) n)) (value : PrimTy.uint.Denote),
      hp.index r .dyn k=some q ∧ hp.index q .fixed l=some value ∧
      SourceUintFixedAt y (address q.id) hp q ∧ a≠address q.id ∧
      (Source.evalE G F (horizon+3) (.indexArray (.indexArray (.local root) (.local i) rfl) (.local j) rfl)).run y=
        (.ok (.val (sourceUint value)),y) := by
  first
  | solve | simp only [] | omega
  | let q := (MObj.elems .dyn (hp.get r))[k.1.toNat]'parentBound
    have hit : (MObj.elems .dyn (hp.get r))[k.1.toNat]?=some q := List.getElem?_eq_getElem parentBound
    have typed : hp.index r .dyn k=some q := hit
    have nested := hr.eval_nested_read G F horizon root i j k l q hroot hi hj typed childBound
    exact ⟨q,_,typed,nested.1,hr.child_at k.1.toNat q hit,
      hr.parent_ne_child q (List.getElem_mem parentBound),nested.2⟩

theorem SourceUintFixedRefsAt.eval_parent_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (UintFixedRefsRef n)} {address : Nat → Nat}
    (hr : SourceUintFixedRefsAt y a hp r address) (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (root : Source.Idx Γ (SourceUintFixedRefsTy n)) (index : Source.Idx Γ (.int .u256))
    (k : PrimTy.uint.Denote) (hroot : y.1.get root=.memRef rfl a) (hindex : y.1.get index=sourceUint k)
    (hk : hp.len r .dyn≤k.1.toNat) :
    (Source.evalE G F (horizon+2) (.indexArray (.local root) (.local index) rfl)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  have loc : (Source.indexLoc (E := E) (Γ := Γ) F (.memRef rfl a : Source.Val E.layout (SourceUintFixedRefsTy n)) k.1.toNat).run y=
      (.error (.revert (Source.panicData .index)),y) := by
    rw [Source.indexLoc,Source.Hoare.run_bind,hr.length_run F]
    simp only [show ¬k.1.toNat<hp.len r .dyn from Nat.not_lt.mpr hk,↓reduceIte]
    rfl
  rw [Source.evalE,Source.Hoare.run_bind,source_local_value_run G F horizon y root _ hroot]
  change ((Source.evalE G F (horizon+1) (.local index)) >>= fun v => Source.indexNat v >>= fun i =>
    Source.indexLoc F (.memRef rfl a : Source.Val E.layout (SourceUintFixedRefsTy n)) i >>= fun loc =>
    Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F horizon y index _ hindex]
  change (Source.indexLoc F (.memRef rfl a : Source.Val E.layout (SourceUintFixedRefsTy n)) k.1.toNat >>= fun loc =>
    Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,loc]

theorem SourceUintFixedRefsAt.eval_nested_parent_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (UintFixedRefsRef n)} {address : Nat → Nat}
    (hr : SourceUintFixedRefsAt y a hp r address) (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (root : Source.Idx Γ (SourceUintFixedRefsTy n)) (i j : Source.Idx Γ (.int .u256))
    (k : PrimTy.uint.Denote) (hroot : y.1.get root=.memRef rfl a) (hi : y.1.get i=sourceUint k)
    (hk : hp.len r .dyn≤k.1.toNat) :
    (Source.evalE G F (horizon+3) (.indexArray (.indexArray (.local root) (.local i) rfl) (.local j) rfl)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  rw [Source.evalE,Source.Hoare.run_bind,hr.eval_parent_bounds G F horizon root i k hroot hi hk]

theorem SourceUintFixedRefsAt.eval_nested_child_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (UintFixedRefsRef n)} {address : Nat → Nat}
    (hr : SourceUintFixedRefsAt y a hp r address) (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (root : Source.Idx Γ (SourceUintFixedRefsTy n)) (i j : Source.Idx Γ (.int .u256))
    (k l : PrimTy.uint.Denote) (q : HRef H (.fixed (.prim .uint) n))
    (hroot : y.1.get root=.memRef rfl a) (hi : y.1.get i=sourceUint k) (hj : y.1.get j=sourceUint l)
    (hq : hp.index r .dyn k=some q) (outside : n≤l.1.toNat) :
    (Source.evalE G F (horizon+3) (.indexArray (.indexArray (.local root) (.local i) rfl) (.local j) rfl)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  have loc : (Source.indexLoc (E := E) (Γ := Γ) F
      (.memRef rfl (address q.id) : Source.Val E.layout (.array .memory (.int .u256) (some n))) l.1.toNat).run y=
        (.error (.revert (Source.panicData .index)),y) := by
    rw [Source.indexLoc,Source.lengthOf]
    simp only [Source.Hoare.run_bind]
    change (if l.1.toNat<n then pure (Source.Loc.mem (address q.id) l.1.toNat : Source.Loc E.layout Γ (.int .u256)) else Source.EM.lift (Source.panic .index)).run y=_
    rw [if_neg (Nat.not_lt.mpr outside)]
    rfl
  rw [Source.evalE,Source.Hoare.run_bind,hr.eval_parent_read G F horizon root i k q hroot hi hq]
  change ((Source.evalE G F (horizon+2) (.local j)) >>= fun v => Source.indexNat v >>= fun index =>
    Source.indexLoc F (.memRef rfl (address q.id) : Source.Val E.layout (.array .memory (.int .u256) (some n))) index >>= fun loc =>
    Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F (horizon+1) y j _ hj]
  change (Source.indexLoc F (.memRef rfl (address q.id) : Source.Val E.layout (.array .memory (.int .u256) (some n))) l.1.toNat >>= fun loc =>
    Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,loc]

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsAt.parent_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedRefsAt.parent_read
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsAt.parent_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedRefsAt.parent_bounds
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsAt.child_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedRefsAt.child_at
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsAt.parent_ne_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedRefsAt.parent_ne_child
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsAt.length_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedRefsAt.length_run
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsAt.indexLoc_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedRefsAt.indexLoc_run
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsAt.eval_parent_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedRefsAt.eval_parent_read
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsAt.eval_nested_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedRefsAt.eval_nested_read
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsAt.observe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedRefsAt.observe
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsAt.eval_parent_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedRefsAt.eval_parent_bounds
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsAt.eval_nested_parent_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedRefsAt.eval_nested_parent_bounds
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsAt.eval_nested_child_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedRefsAt.eval_nested_child_bounds
end Solidity.Backend.MemoryOps
