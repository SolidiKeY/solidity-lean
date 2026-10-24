import Solidity.Evm.Memory

/-!
# Primitive fields in memory structs

A memory struct reserves one word per member, including reference-valued
members. This relation interprets its primitive members at those offsets.
There is no array-length header. The interval bound rules out address wrap,
and equal object identities use the same base in the global relation.

These local instruction and frame lemmas support the source simulations and
checked compiler clauses in the modules above this representation layer.
-/
namespace Solidity.Evm.Memory
open Semantics

/-- Memory structs place each member in one word, in declaration order. -/
def fieldOffset : List (Name × Ty) → Name → Nat
  | [], _ => 0
  | (g, _) :: fs, f => if f = g then 0 else 1 + fieldOffset fs f

theorem fieldOffset_bound {fs : List (Name × Ty)} {f : Name} {T : Ty}
    (h : lookupBy f fs = some T) : fieldOffset fs f < fs.length := by
  induction fs with
  | nil => cases h
  | cons a fs ih =>
    obtain ⟨g, V⟩ := a
    by_cases he : f = g
    · simp only [fieldOffset, he, if_true, List.length_cons]; omega
    · simp only [fieldOffset, he, if_false, List.length_cons]
      have hh : fieldOffset fs f < fs.length := ih (SFields.lookupBy_cons_neg he h)
      omega

theorem fieldOffset_ne {fs : List (Name × Ty)} {f g : Name} {T U : Ty}
    (hf : lookupBy f fs = some T) (hg : lookupBy g fs = some U) (hne : f ≠ g) :
    fieldOffset fs f ≠ fieldOffset fs g := by
  induction fs with
  | nil => cases hf
  | cons a fs ih =>
    obtain ⟨a, V⟩ := a
    by_cases ef : f = a <;> by_cases eg : g = a
    · exact False.elim (hne (ef.trans eg.symm))
    · simp only [fieldOffset, ef, eg, if_true, if_false]; omega
    · simp only [fieldOffset, ef, eg, if_true, if_false]; omega
    · have hn : fieldOffset fs f ≠ fieldOffset fs g :=
        ih (SFields.lookupBy_cons_neg ef hf) (SFields.lookupBy_cons_neg eg hg)
      simp only [fieldOffset, ef, eg, if_false]
      omega

/-- One actual typed struct represented by its primitive member cells. -/
structure StructRepr {H : HTy} {s : Name} (hp : Heap H)
    (r : HRef H (.struct s)) (base : Fin W) (m : Machine) : Prop where
  space : base.val + (structDef s).length ≤ W
  fields : ∀ {f : Name} {p : PrimTy} (hf : lookupBy f (structDef s) = some (.prim p)),
    ReprV p (hp.field r hf) (m.mem (base.val + fieldOffset (structDef s) f))

theorem StructRepr.stack {H : HTy} {s : Name} {hp : Heap H}
    {r : HRef H (.struct s)} {base : Fin W} {m : Machine}
    (h : StructRepr hp r base m) (st : List Word) :
    StructRepr hp r base {m with stack := st} := ⟨h.space, h.fields⟩

/-- A runtime pointer is on top of the stack, above a value for a write. -/
def fieldAddrCode (offset : Nat) : List Instr := [.push (.val (wmod offset)), .add]
def readFieldCode (offset : Nat) : List Instr := fieldAddrCode offset ++ [.mloadAt]
def writeFieldCode (offset : Nat) : List Instr := fieldAddrCode offset ++ [.mstoreAt]

theorem fieldAddr_run (m : Machine) (base : Fin W) (offset : Nat) :
    run (fieldAddrCode offset) (m.push (.val base)) =
      .ok (m.push (.val (wmod (base.val + offset)))) 0 := by
  simp only [run, fieldAddrCode, Machine.push, exec_cons_zero, Instr.step,
    Machine.next, Out.ok_bind, exec_nil, wmod_def, Nat.add_mod, Nat.mod_mod,
    Nat.add_comm]

/-- A represented primitive field reads the source heap's actual typed value. -/
theorem readField_correct {H : HTy} {s f : Name} {p : PrimTy} {hp : Heap H}
    {r : HRef H (.struct s)} {base : Fin W} {m : Machine}
    (h : StructRepr hp r base m) (hf : lookupBy f (structDef s) = some (.prim p)) :
    ValOutT p (.ok (hp.field r hf))
      (run (readFieldCode (fieldOffset (structDef s) f)) (m.push (.val base))) m := by
  refine .inl ⟨_, _, rfl, h.fields hf, ?_⟩
  have hb : base.val + fieldOffset (structDef s) f < W := by
    have ho : fieldOffset (structDef s) f < (structDef s).length := fieldOffset_bound hf
    have hs : base.val + (structDef s).length ≤ W := h.space
    omega
  rw [readFieldCode, run_append_ok (fieldAddr_run m base _)]
  simp only [run, Machine.push, exec_cons_zero, Instr.step, Machine.next,
    wmod_of_lt hb, Out.ok_bind, exec_nil]

/-- A primitive member write preserves the other members of the object. -/
theorem StructRepr.set {H : HTy} {s f : Name} {p : PrimTy} {hp : Heap H}
    {r : HRef H (.struct s)} {base : Fin W} {m : Machine}
    (h : StructRepr hp r base m) (hf : lookupBy f (structDef s) = some (.prim p))
    (v : p.Denote) (w : Word) (hw : ReprV p v w) :
    StructRepr (hp.setField r hf v) r base
      (writeMachine m (base.val + fieldOffset (structDef s) f) w) := by
  refine ⟨h.space, ?_⟩
  intro g q hg
  by_cases e : f = g
  · subst g
    have et : p = q := Ty.prim.inj (Option.some.inj (hf.symm.trans hg))
    subst q
    simpa only [Heap.field, Heap.setField, Heap.get_set_same, MFields.get_set_same,
      writeMachine, upd_same] using hw
  · simp only [Heap.field, Heap.setField, Heap.get_set_same,
      MFields.get_set_ne _ _ _ _ e, writeMachine]
    have hn : fieldOffset (structDef s) f ≠ fieldOffset (structDef s) g := fieldOffset_ne hf hg e
    rw [upd_other _ _ (by omega)]
    exact h.fields hg

/-- A represented primitive write agrees with the typed source update. -/
theorem writeField_correct {H : HTy} {s f : Name} {p : PrimTy} {hp : Heap H}
    {r : HRef H (.struct s)} {base : Fin W} {m : Machine}
    (h : StructRepr hp r base m) (hf : lookupBy f (structDef s) = some (.prim p))
    (v : p.Denote) (w : Word) (hw : ReprV p v w) :
    hp.writeAddr (.field r hf) v = some (hp.setField r hf v) ∧
    run (writeFieldCode (fieldOffset (structDef s) f)) ((m.push w).push (.val base)) =
      .ok (writeMachine m (base.val + fieldOffset (structDef s) f) w) 0 ∧
    StructRepr (hp.setField r hf v) r base
      (writeMachine m (base.val + fieldOffset (structDef s) f) w) := by
  refine ⟨rfl, ?_, h.set hf v w hw⟩
  have hb : base.val + fieldOffset (structDef s) f < W := by
    have ho : fieldOffset (structDef s) f < (structDef s).length := fieldOffset_bound hf
    have hs : base.val + (structDef s).length ≤ W := h.space
    omega
  rw [writeFieldCode, run_append_ok (fieldAddr_run (m.push w) base _)]
  simp only [run, Machine.push, exec_cons_zero, Instr.step,
    wmod_of_lt hb, Out.ok_bind, exec_nil, writeMachine]

end Solidity.Evm.Memory
