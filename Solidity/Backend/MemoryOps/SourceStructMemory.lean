import Solidity.Backend.MemoryOps.SourceReferenceSequence
import Solidity.Evm.MemoryRefWrite

/-! A finite INITIAL two-field struct correspondence. Source declaration names
and positions are checked against its real layout, while the intrinsic fields
retain named dependent types. Existing objects only; no constructor, evaluator,
allocator or general Source graph representation is introduced. -/
namespace Solidity.Backend.MemoryOps
open Semantics

abbrev SourceBoolArrayTy : Source.STy := .array .memory .bool none

structure SourceBoolStructLayout (E : Source.Env) (dn : Source.DeclName)
    (s tag child : Name) : Prop where
  source_fields : E.structFields dn .memory=some [(tag,.int .u256),(child,SourceBoolArrayTy)]
  target_fields : structDef s=[(tag,Ty.uint),(child,.ref (.array (.prim .bool)))]
  distinct : tag≠child

theorem SourceBoolStructLayout.source_types {E : Source.Env} {dn : Source.DeclName}
    {s tag child : Name} (h : SourceBoolStructLayout E dn s tag child) :
    E.layout.fields dn=[.int .u256,SourceBoolArrayTy] := by
  simp only [Source.Env.layout,h.source_fields,Option.getD_some,List.map_cons,List.map_nil]

theorem SourceBoolStructLayout.tag_type {E : Source.Env} {dn : Source.DeclName}
    {s tag child : Name} (h : SourceBoolStructLayout E dn s tag child) :
    lookupBy tag (structDef s)=some Ty.uint := by
  rw [h.target_fields]
  simp only [lookupBy,↓reduceIte]

theorem SourceBoolStructLayout.child_type {E : Source.Env} {dn : Source.DeclName}
    {s tag child : Name} (h : SourceBoolStructLayout E dn s tag child) :
    lookupBy child (structDef s)=some (.ref (.array (.prim .bool))) := by
  rw [h.target_fields]
  simp only [lookupBy,Ne.symm h.distinct,↓reduceIte]

private def pairFields {D : Source.Layout} (ts : List Source.STy)
    (h : ts=[.int .u256,SourceBoolArrayTy]) (n : PrimTy.uint.Denote) (a : Nat) : Source.DataList D ts :=
  h.symm ▸ (.cons (.val (sourceUint n)) (.cons (.val (.memRef rfl a)) .nil))

private theorem pairFields_tag {D : Source.Layout} (ts : List Source.STy)
    (h : ts=[.int .u256,SourceBoolArrayTy]) (n : PrimTy.uint.Denote) (a : Nat) :
    (pairFields (D := D) ts h n a).nth 0 (.int .u256)=.ok (.val (sourceUint n)) := by
  subst ts;rfl

private theorem pairFields_child {D : Source.Layout} (ts : List Source.STy)
    (h : ts=[.int .u256,SourceBoolArrayTy]) (n : PrimTy.uint.Denote) (a : Nat) :
    (pairFields (D := D) ts h n a).nth 1 SourceBoolArrayTy=.ok (.val (.memRef rfl a)) := by
  subst ts;rfl

private theorem pairFields_set_child {D : Source.Layout} (ts : List Source.STy)
    (h : ts=[.int .u256,SourceBoolArrayTy]) (n : PrimTy.uint.Denote) (a b : Nat) :
    (pairFields (D := D) ts h n a).setNth 1 (Source.Data.val (Source.Val.memRef (τ := SourceBoolArrayTy) rfl b))=
      .ok (pairFields ts h n b) := by
  subst ts;rfl

def sourceBoolStructData {D : Source.Layout} (dn : Source.DeclName)
    (h : D.fields dn=[.int .u256,SourceBoolArrayTy]) (n : PrimTy.uint.Denote) (a : Nat) :
    Source.Data D (.struct .memory dn) := .struct (pairFields _ h n a)

structure SourceBoolStructAt {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (a : Nat) (hp : Heap H) (r : HRef H (.struct s))
    (address : Nat → Nat) (layout : SourceBoolStructLayout E dn s tag child) : Prop where
  parent : y.2.heap.get a=some ⟨.struct .memory dn,
    sourceBoolStructData dn layout.source_types (hp.field r layout.tag_type)
      (address (hp.field r layout.child_type).id)⟩
  leaf : SourceBoolMemoryAt y (address (hp.field r layout.child_type).id) hp (hp.field r layout.child_type) .dyn

theorem SourceBoolStructAt.read_tag {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (.struct s)}
    {address : Nat → Nat} {layout : SourceBoolStructLayout E dn s tag child}
    (hr : SourceBoolStructAt y a hp r address layout) (F : Source.Fr) :
    (Source.readLoc (E := E) (Γ := Γ) F (τ := .int .u256) (.mem a 0)).run y=
      (.ok (sourceUint (hp.field r layout.tag_type)),y) := by
  change (Source.memElem a 0 (.int .u256)).run y=_
  rw [Source.memElem,Source.Hoare.run_bind,source_heapObj_run y a _ hr.parent]
  simp only [sourceBoolStructData,pairFields_tag]
  rfl

theorem SourceBoolStructAt.read_child {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (.struct s)}
    {address : Nat → Nat} {layout : SourceBoolStructLayout E dn s tag child}
    (hr : SourceBoolStructAt y a hp r address layout) (F : Source.Fr) :
    (Source.readLoc (E := E) (Γ := Γ) F (τ := SourceBoolArrayTy) (.mem a 1)).run y=
      (.ok (.memRef rfl (address (hp.field r layout.child_type).id)),y) := by
  change (Source.memElem a 1 SourceBoolArrayTy).run y=_
  rw [Source.memElem,Source.Hoare.run_bind,source_heapObj_run y a _ hr.parent]
  simp only [sourceBoolStructData,pairFields_child]
  rfl

/-- Actual Source DataList.setNth pointer replacement, not a replacement
struct update algorithm or an assumed final relation. -/
theorem source_struct_write {E : Source.Env} {Γ : Source.RCtx}
    (y : Source.EMState E Γ) (a : Nat) (dn : Source.DeclName)
    (h : E.layout.fields dn=[.int .u256,SourceBoolArrayTy]) (n : PrimTy.uint.Denote) (old fresh : Nat)
    (hr : y.2.heap.get a=some ⟨.struct .memory dn,sourceBoolStructData dn h n old⟩) :
    ∃ ht : y.2.heap.ty a=some (.struct .memory dn),
      (Source.memSet (E := E) (Γ := Γ) a 1 (.memRef (τ := SourceBoolArrayTy) rfl fresh)).run y=
        (.ok (), (y.1,{y.2 with heap := y.2.heap.write a (sourceBoolStructData dn h n fresh) ht})) := by
  have ht : y.2.heap.ty a=some (.struct .memory dn) := by
    change (y.2.heap.get a).map Sigma.fst=some _
    rw [hr];rfl
  refine ⟨ht,?_⟩
  rw [Source.memSet,Source.Hoare.run_bind,source_heapObj_run y a _ hr]
  simp only [sourceBoolStructData,pairFields_set_child]
  change (Source.heapPut a ⟨.struct .memory dn,sourceBoolStructData dn h n fresh⟩).run y=_
  simp only [Source.heapPut,Source.Hoare.run_bind]
  rw [show (Source.EM.st (E := E) (Γ := Γ)).run y=(.ok y.2,y) from rfl]
  simp only [ht,↓reduceDIte]
  rfl


theorem SourceBoolStructLayout.source_tag_type {E : Source.Env} {dn : Source.DeclName}
    {s tag child : Name} (h : SourceBoolStructLayout E dn s tag child) :
    E.fieldTy? dn .memory 0=some (.int .u256) := by
  simp only [Source.Env.fieldTy?,h.source_fields,Option.bind_some,List.getElem?_cons_zero,Option.map_some]

theorem SourceBoolStructLayout.source_child_type {E : Source.Env} {dn : Source.DeclName}
    {s tag child : Name} (h : SourceBoolStructLayout E dn s tag child) :
    E.fieldTy? dn .memory 1=some SourceBoolArrayTy := by
  simp only [Source.Env.fieldTy?,h.source_fields,Option.bind_some,List.getElem?_cons_succ,
    List.getElem?_cons_zero,Option.map_some]

theorem SourceBoolStructAt.eval_member_tag {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (.struct s)}
    {address : Nat → Nat} {layout : SourceBoolStructLayout E dn s tag child}
    (hr : SourceBoolStructAt y a hp r address layout) (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (root : Source.Idx Γ (.struct .memory dn)) (hroot : y.1.get root=.memRef rfl a) :
    (Source.evalE G F (n+2) (.member (.local root) 0 layout.source_tag_type)).run y=
      (.ok (.val (sourceUint (hp.field r layout.tag_type))),y) := by
  rw [Source.evalE,Source.Hoare.run_bind,source_local_value_run G F n y root _ hroot]
  change (Source.readLoc F (τ := .int .u256) (.mem a 0) >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,hr.read_tag F]
  rfl

theorem SourceBoolStructAt.eval_member_child {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (.struct s)}
    {address : Nat → Nat} {layout : SourceBoolStructLayout E dn s tag child}
    (hr : SourceBoolStructAt y a hp r address layout) (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (root : Source.Idx Γ (.struct .memory dn)) (hroot : y.1.get root=.memRef rfl a) :
    (Source.evalE G F (n+2) (.member (.local root) 1 layout.source_child_type)).run y=
      (.ok (.val (.memRef rfl (address (hp.field r layout.child_type).id))),y) := by
  rw [Source.evalE,Source.Hoare.run_bind,source_local_value_run G F n y root _ hroot]
  change (Source.readLoc F (τ := SourceBoolArrayTy) (.mem a 1) >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,hr.read_child F]
  rfl

/-- All reached content follows the actual existing Source setNth and intrinsic
setField; aliases to old children survive even when no longer selected. -/
theorem SourceBoolStructAt.write_reference {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (.struct s)}
    {address : Nat → Nat} {layout : SourceBoolStructLayout E dn s tag child}
    (hr : SourceBoolStructAt y a hp r address layout) (v : HRef H (.array (.prim .bool)))
    (hv : SourceBoolMemoryAt y (address v.id) hp v .dyn) (F : Source.Fr) (fuel : Nat)
    (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    ∃ z : Source.EMState E Γ,
      (Source.writeLoc (E := E) (Γ := Γ) F fuel (.mem (τ := SourceBoolArrayTy) a 1)
        (.memRef rfl (address v.id))).run y=(.ok (),z) ∧
      SourceBoolStructAt z a (hp.setField r layout.child_type v) r address layout ∧
      Source.MemOK E SH z ∧ z.1=y.1 ∧
      (hp.setField r layout.child_type v).field r layout.tag_type=hp.field r layout.tag_type ∧
      (hp.setField r layout.child_type v).field r layout.child_type=v ∧
      (∀ q : HRef H (.array (.prim .bool)),(hp.setField r layout.child_type v).get q=hp.get q) ∧
      (∀ q,SourceBoolMemoryAt y (address q.id) hp q .dyn →
        SourceBoolMemoryAt z (address q.id) (hp.setField r layout.child_type v) q .dyn) ∧
      (z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals) := by
  let out := hp.setField r layout.child_type v
  have htag : out.field r layout.tag_type=hp.field r layout.tag_type := by
    simp only [out,Heap.field,Heap.setField,Heap.get_set_same,
      MFields.get_set_ne _ _ _ _ (Ne.symm layout.distinct)]
  have hchild : out.field r layout.child_type=v := by
    simp only [out,Heap.field,Heap.setField,Heap.get_set_same,MFields.get_set_same]
  have hchildren : ∀ q : HRef H (.array (.prim .bool)),out.get q=hp.get q := by
    intro q
    apply Heap.get_set_ne
    intro he
    cases (HRef.heq_of_id r q he).1
  obtain ⟨ht,hw⟩ := source_struct_write y a dn layout.source_types (hp.field r layout.tag_type)
    (address (hp.field r layout.child_type).id) (address v.id) hr.parent
  let z : Source.EMState E Γ :=
    (y.1,{y.2 with heap := y.2.heap.write a (sourceBoolStructData dn layout.source_types (hp.field r layout.tag_type) (address v.id)) ht})
  have hs : (Source.writeLoc (E := E) (Γ := Γ) F fuel (.mem (τ := SourceBoolArrayTy) a 1)
      (.memRef rfl (address v.id))).run y=(.ok (),z) := hw
  have hvty : y.2.heap.ty (address v.id)=some SourceBoolArrayTy := by
    change (y.2.heap.get (address v.id)).map Sigma.fst=some _
    rw [hv];rfl
  have hmk := Source.writeLoc_memOK (E := E) (Γ := Γ) (H := SH) F fuel
    (.mem (τ := SourceBoolArrayTy) a 1) (.memRef rfl (address v.id)) y ⟨hm,⟨_,hvty,rfl⟩⟩
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
  refine ⟨z,hs,⟨?_,?_⟩,hmk,rfl,htag,hchild,hchildren,hsource,⟨rfl,rfl,rfl,rfl⟩⟩
  · change (y.2.heap.write _ _ ht).get a=some _
    rw [Source.Heap.write_get,htag,hchild]
  · rw [hchild]
    exact hsource v hv

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructLayout.source_types' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructLayout.source_types

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructLayout.tag_type' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructLayout.tag_type

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructLayout.child_type' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructLayout.child_type

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.read_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructAt.read_tag

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.read_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructAt.read_child

/-- info: 'Solidity.Backend.MemoryOps.source_struct_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_struct_write

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructLayout.source_tag_type' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructLayout.source_tag_type

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructLayout.source_child_type' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructLayout.source_child_type

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.eval_member_tag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructAt.eval_member_tag

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.eval_member_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructAt.eval_member_child

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.write_reference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructAt.write_reference

end Solidity.Backend.MemoryOps
