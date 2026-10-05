import Solidity.Typing.Storage
import Solidity.Semantics.Properties

/-!
# Storage write core: `save` preserves typing

The write-side twin of `StorageTyping`'s read lemmas, and the first
layer of the type-soundness development (`State.lean`, then
`Soundness.lean`): saving a value of the path's layout type keeps
the whole storage well-typed.

- `save_hasTy` mirrors `find_hasTy` arm for arm: a `ty`-typed tree
  stays `ty`-typed when a `ty'`-typed value is saved at a
  `ty'`-typed path (`tyAtSegs`).
- `State.saveStorage_wellTyped` lifts it to `wellTypedStorageB` —
  under `nodupKeysB L.globals`, which is genuinely load-bearing: with
  a duplicated layout root the two rows check the *same* stored value
  against different types, and a save that satisfies one row can break
  the other (a counterexample removed with the untyped layer, to be
  ported — `docs/kernel-port.md`'s "Port later").
- The written values the interpreter produces are typed:
  `SVal.defaultOf_hasTy` (the `delete` default preserves the type,
  mapping members untouched), `defaultForTy_hasTy` under `defaultOk`
  (the fuel bound of `defaultForTyFuel` is real: a type nested deeper
  than the fuel bottoms out at `SVal.int 0`, ill-typed at reference
  types — refuted concretely in `PreservationNecessity`), and
  `int_hasTy_numeric` / `applyBinOp_arith_int` for the arithmetic
  write-back paths.
-/

namespace Solidity
namespace Semantics

open SemanticsProperties (lookupBy_setBy_self lookupBy_setBy_ne lookupBy_eq_some_mem)

/-! ## `hasTy` under the update primitives -/

theorem hasTyElems_of_forall_mem {elem : Ty} {elems : List SVal}
    (h : ∀ v ∈ elems, v.hasTy elem = true) :
    SVal.hasTy.hasTyElems elem elems = true := by
  induction elems with
  | nil => rfl
  | cons v rest ih =>
      simp only [SVal.hasTy.hasTyElems, Bool.and_eq_true]
      exact ⟨h v (List.Mem.head _), ih fun w hw => h w (List.Mem.tail _ hw)⟩

theorem hasTyElems_set {elem : Ty} {elems : List SVal} {i : Nat} {w : SVal}
    (hwt : SVal.hasTy.hasTyElems elem elems = true)
    (hw : w.hasTy elem = true) :
    SVal.hasTy.hasTyElems elem (elems.set i w) = true := by
  induction elems generalizing i with
  | nil => exact hwt
  | cons v rest ih =>
      simp only [SVal.hasTy.hasTyElems, Bool.and_eq_true] at hwt
      cases i with
      | zero =>
          simp only [List.set, SVal.hasTy.hasTyElems, Bool.and_eq_true]
          exact ⟨hw, hwt.2⟩
      | succ n =>
          simp only [List.set, SVal.hasTy.hasTyElems, Bool.and_eq_true]
          exact ⟨hwt.1, ih hwt.2⟩

theorem hasTyElems_append {elem : Ty} {xs ys : List SVal}
    (hx : SVal.hasTy.hasTyElems elem xs = true)
    (hy : SVal.hasTy.hasTyElems elem ys = true) :
    SVal.hasTy.hasTyElems elem (xs ++ ys) = true := by
  induction xs with
  | nil => exact hy
  | cons v rest ih =>
      simp only [SVal.hasTy.hasTyElems, Bool.and_eq_true] at hx
      simp only [List.cons_append, SVal.hasTy.hasTyElems, Bool.and_eq_true]
      exact ⟨hx.1, ih hx.2⟩

theorem hasTyElems_take {elem : Ty} {xs : List SVal} (n : Nat)
    (hx : SVal.hasTy.hasTyElems elem xs = true) :
    SVal.hasTy.hasTyElems elem (xs.take n) = true :=
  hasTyElems_of_forall_mem fun _ hv => hasTyElems_mem hx (List.mem_of_mem_take hv)

theorem hasTyElems_drop {elem : Ty} {xs : List SVal} (n : Nat)
    (hx : SVal.hasTy.hasTyElems elem xs = true) :
    SVal.hasTy.hasTyElems elem (xs.drop n) = true :=
  hasTyElems_of_forall_mem fun _ hv => hasTyElems_mem hx (List.mem_of_mem_drop hv)

theorem hasTyFields_setBy {s : Name} {fields : List (Name × SVal)}
    {n : Name} {w : SVal} {tyf : Ty}
    (hwt : SVal.hasTy.hasTyFields s fields = true)
    (hdef : lookupBy n (structDef s) = some tyf)
    (hw : w.hasTy tyf = true) :
    SVal.hasTy.hasTyFields s (setBy n w fields) = true := by
  induction fields with
  | nil => simp [setBy, SVal.hasTy.hasTyFields, hdef, hw]
  | cons p rest ih =>
      obtain ⟨k, v⟩ := p
      simp only [SVal.hasTy.hasTyFields, Bool.and_eq_true] at hwt
      by_cases hn : n = k
      · subst hn
        simp [setBy, SVal.hasTy.hasTyFields, hdef, hw, hwt.2]
      · simp [setBy, hn, SVal.hasTy.hasTyFields, hwt.1, ih hwt.2]

theorem hasTyEntries_setBy {value : Ty} {entries : List (Int × SVal)}
    {i : Int} {w : SVal}
    (hwt : SVal.hasTy.hasTyEntries value entries = true)
    (hw : w.hasTy value = true) :
    SVal.hasTy.hasTyEntries value (setBy i w entries) = true := by
  induction entries with
  | nil => simp [setBy, SVal.hasTy.hasTyEntries, hw]
  | cons p rest ih =>
      obtain ⟨j, v⟩ := p
      simp only [SVal.hasTy.hasTyEntries, Bool.and_eq_true] at hwt
      by_cases hi : i = j
      · subst hi
        simp [setBy, SVal.hasTy.hasTyEntries, hw, hwt.2]
      · simp [setBy, hi, SVal.hasTy.hasTyEntries, hwt.1, ih hwt.2]

/-! ## The written values the interpreter produces are typed -/

/-- `delete` keeps a list of elements as long as it was: a fixed-size
array's length survives it. -/
theorem SVal.defaultOfElems_length (elems : List SVal) :
    (SVal.defaultOf.defaultOfElems elems).length = elems.length := by
  induction elems with
  | nil => rfl
  | cons _ _ ih => simp [SVal.defaultOf.defaultOfElems, ih]

/-- A copy keeps a list of elements as long as the copied one. -/
theorem SVal.stripElems_length' (elems : List SVal) :
    (SVal.strip.stripElems elems).length = elems.length := by
  induction elems with
  | nil => rfl
  | cons _ _ ih => simp [SVal.strip.stripElems, ih]

/-- A copy over old elements is as long as the new ones. -/
theorem SVal.overlayElems_length (olds news : List SVal) :
    (SVal.overlay.overlayElems olds news).length = news.length := by
  induction news generalizing olds with
  | nil => cases olds <;> rfl
  | cons x xs ih =>
    cases olds with
    | nil => simp [SVal.overlay.overlayElems, SVal.stripElems_length']
    | cons o os => simp [SVal.overlay.overlayElems, ih]

mutual

/-- The `delete` default preserves the value's type: primitives reset,
arrays empty (an empty array inhabits every array type), struct fields
recurse, mapping members are untouched. -/
theorem SVal.defaultOf_hasTy {v : SVal} {ty : Ty}
    (h : v.hasTy ty = true) : v.defaultOf.hasTy ty = true := by
  cases v with
  | prim p =>
      cases p with
      | int n =>
          cases ty with
          | prim pt => cases pt <;> simp_all [SVal.hasTy, SVal.defaultOf]
          | ref r => simp [SVal.hasTy] at h
      | bool b =>
          cases ty with
          | prim pt => cases pt <;> simp_all [SVal.hasTy, SVal.defaultOf]
          | ref r => simp [SVal.hasTy] at h
  | struct fields =>
      cases ty with
      | prim pt => simp [SVal.hasTy] at h
      | ref r =>
          cases r with
          | struct sname =>
              simp only [SVal.hasTy] at h
              simpa only [SVal.defaultOf, SVal.hasTy] using
                defaultOfFields_hasTy h
          | array elem => simp [SVal.hasTy] at h
          | fixed elem _ => simp [SVal.hasTy] at h
          | mapping key value => simp [SVal.hasTy] at h
  | array elems shadow fx =>
      cases ty with
      | prim pt => simp [SVal.hasTy] at h
      | ref r =>
          cases r with
          | struct sname => simp [SVal.hasTy] at h
          | array elem =>
              cases fx
              · simp only [SVal.hasTy, Bool.and_eq_true] at h
                simp only [SVal.defaultOf, SVal.hasTy, Bool.and_eq_true]
                exact ⟨⟨rfl, rfl⟩, hasTyElems_append (SVal.defaultOfElems_hasTy h.1.2) h.2⟩
              · simp [SVal.hasTy] at h
          | fixed elem n =>
              cases fx
              · simp [SVal.hasTy] at h
              · simp only [SVal.hasTy, Bool.and_eq_true, beq_iff_eq] at h
                simp only [SVal.defaultOf, SVal.hasTy, Bool.and_eq_true, beq_iff_eq,
                  SVal.defaultOfElems_length]
                exact ⟨⟨h.1.1, SVal.defaultOfElems_hasTy h.1.2⟩, h.2⟩
          | mapping key value => simp [SVal.hasTy] at h
  | map entries dflt =>
      simpa only [SVal.defaultOf] using h

theorem SVal.defaultOfElems_hasTy {elem : Ty} {elems : List SVal}
    (h : SVal.hasTy.hasTyElems elem elems = true) :
    SVal.hasTy.hasTyElems elem (SVal.defaultOf.defaultOfElems elems) = true := by
  match elems with
  | [] => exact h
  | v :: rest =>
      simp only [SVal.hasTy.hasTyElems, Bool.and_eq_true] at h
      simp only [SVal.defaultOf.defaultOfElems, SVal.hasTy.hasTyElems, Bool.and_eq_true]
      exact ⟨SVal.defaultOf_hasTy h.1, SVal.defaultOfElems_hasTy h.2⟩

theorem SVal.defaultOfFields_hasTy {s : Name} {fields : List (Name × SVal)}
    (h : SVal.hasTy.hasTyFields s fields = true) :
    SVal.hasTy.hasTyFields s (SVal.defaultOf.defaultOfFields fields)
      = true := by
  match fields with
  | [] => exact h
  | (n, v) :: rest =>
      simp only [SVal.hasTy.hasTyFields, Bool.and_eq_true] at h
      simp only [SVal.defaultOf.defaultOfFields, SVal.hasTy.hasTyFields,
        Bool.and_eq_true]
      refine ⟨?_, SVal.defaultOfFields_hasTy h.2⟩
      cases hdef : lookupBy n (structDef s) with
      | none => rw [hdef] at h; exact Bool.noConfusion h.1
      | some tyf =>
          rw [hdef] at h
          exact SVal.defaultOf_hasTy h.1

end

/-! ## Copies keep types

A copy writes a value of the location's type over what is there
(`SVal.overlay`): every slot it writes holds a value of the slot's type, and
every slot it leaves (past the new length, or a mapping) held one. -/

mutual

/-- A value laid on fresh slots keeps its type: `strip` only forgets the
slots past an array's end. -/
theorem SVal.strip_hasTy {v : SVal} {ty : Ty} (h : v.hasTy ty = true) :
    v.strip.hasTy ty = true := by
  match v with
  | .prim _ => simpa [SVal.strip] using h
  | .struct fields =>
      cases ty with
      | prim _ => simp [SVal.hasTy] at h
      | ref r =>
          cases r with
          | struct sname =>
              simp only [SVal.hasTy] at h
              simpa only [SVal.strip, SVal.hasTy] using SVal.stripFields_hasTy h
          | array _ => simp [SVal.hasTy] at h
          | fixed _ _ => simp [SVal.hasTy] at h
          | mapping _ _ => simp [SVal.hasTy] at h
  | .array elems _ fx =>
      cases ty with
      | prim _ => simp [SVal.hasTy] at h
      | ref r =>
          cases r with
          | array elem =>
              simp only [SVal.hasTy, Bool.and_eq_true] at h
              simp only [SVal.strip, SVal.hasTy, Bool.and_eq_true]
              exact ⟨⟨h.1.1, SVal.stripElems_hasTy h.1.2⟩, rfl⟩
          | fixed elem n =>
              simp only [SVal.hasTy, Bool.and_eq_true, beq_iff_eq] at h
              simp only [SVal.strip, SVal.hasTy, Bool.and_eq_true, beq_iff_eq,
                SVal.stripElems_length']
              exact ⟨⟨h.1.1, SVal.stripElems_hasTy h.1.2⟩, rfl⟩
          | struct _ => simp [SVal.hasTy] at h
          | mapping _ _ => simp [SVal.hasTy] at h
  | .map _ _ => simpa [SVal.strip] using h

theorem SVal.stripFields_hasTy {s : Name} {fields : List (Name × SVal)}
    (h : SVal.hasTy.hasTyFields s fields = true) :
    SVal.hasTy.hasTyFields s (SVal.strip.stripFields fields) = true := by
  match fields with
  | [] => exact h
  | (n, v) :: rest =>
      simp only [SVal.hasTy.hasTyFields, Bool.and_eq_true] at h
      simp only [SVal.strip.stripFields, SVal.hasTy.hasTyFields, Bool.and_eq_true]
      refine ⟨?_, SVal.stripFields_hasTy h.2⟩
      cases hdef : lookupBy n (structDef s) with
      | none => rw [hdef] at h; exact Bool.noConfusion h.1
      | some tyf =>
          rw [hdef] at h
          exact SVal.strip_hasTy h.1

theorem SVal.stripElems_hasTy {elem : Ty} {elems : List SVal}
    (h : SVal.hasTy.hasTyElems elem elems = true) :
    SVal.hasTy.hasTyElems elem (SVal.strip.stripElems elems) = true := by
  match elems with
  | [] => exact h
  | v :: rest =>
      simp only [SVal.hasTy.hasTyElems, Bool.and_eq_true] at h
      simp only [SVal.strip.stripElems, SVal.hasTy.hasTyElems, Bool.and_eq_true]
      exact ⟨SVal.strip_hasTy h.1, SVal.stripElems_hasTy h.2⟩

end

mutual

/-- **A copy keeps the type**: `bob = alice;` over a `Person` leaves a
`Person`, each member laid over the old one. -/
theorem SVal.overlay_hasTy {old new : SVal} {ty : Ty} (ho : old.hasTy ty = true)
    (hn : new.hasTy ty = true) : (old.overlay new).hasTy ty = true := by
  match new with
  | .prim p => cases old <;> simpa [SVal.overlay, SVal.strip] using hn
  | .struct nfs =>
      cases old with
      | struct ofs =>
          cases ty with
          | prim _ => simp [SVal.hasTy] at hn
          | ref r =>
              cases r with
              | struct sname =>
                  simp only [SVal.hasTy] at ho hn
                  simpa only [SVal.overlay, SVal.hasTy] using SVal.overlayFields_hasTy ho hn
              | array _ => simp [SVal.hasTy] at hn
              | fixed _ _ => simp [SVal.hasTy] at hn
              | mapping _ _ => simp [SVal.hasTy] at hn
      | prim _ => simp only [SVal.overlay]; exact SVal.strip_hasTy hn
      | array _ _ _ => simp only [SVal.overlay]; exact SVal.strip_hasTy hn
      | map _ _ => simp only [SVal.overlay]; exact SVal.strip_hasTy hn
  | .array nel nsh nfx =>
      cases old with
      | array oel osh ofx =>
          cases ty with
          | prim _ => simp [SVal.hasTy] at hn
          | ref r =>
              cases r with
              | array elem =>
                  simp only [SVal.hasTy, Bool.and_eq_true] at ho hn
                  simp only [SVal.overlay, SVal.hasTy, Bool.and_eq_true]
                  exact ⟨⟨hn.1.1, SVal.overlayElems_hasTy (hasTyElems_append ho.1.2 ho.2) hn.1.2⟩,
                    hasTyElems_append (SVal.defaultOfElems_hasTy (hasTyElems_drop _ ho.1.2))
                      (hasTyElems_drop _ ho.2)⟩
              | fixed elem n =>
                  simp only [SVal.hasTy, Bool.and_eq_true, beq_iff_eq] at ho hn
                  simp only [SVal.overlay, SVal.hasTy, Bool.and_eq_true, beq_iff_eq,
                    SVal.overlayElems_length]
                  exact ⟨⟨⟨hn.1.1.1, hn.1.1.2⟩,
                    SVal.overlayElems_hasTy (hasTyElems_append ho.1.2 ho.2) hn.1.2⟩,
                    hasTyElems_append (SVal.defaultOfElems_hasTy (hasTyElems_drop _ ho.1.2))
                      (hasTyElems_drop _ ho.2)⟩
              | struct _ => simp [SVal.hasTy] at hn
              | mapping _ _ => simp [SVal.hasTy] at hn
      | prim _ => simp only [SVal.overlay]; exact SVal.strip_hasTy hn
      | struct _ => simp only [SVal.overlay]; exact SVal.strip_hasTy hn
      | map _ _ => simp only [SVal.overlay]; exact SVal.strip_hasTy hn
  | .map ne nd =>
      cases old with
      | map oe od => simpa only [SVal.overlay] using ho
      | prim _ => simp only [SVal.overlay]; exact SVal.strip_hasTy hn
      | struct _ => simp only [SVal.overlay]; exact SVal.strip_hasTy hn
      | array _ _ _ => simp only [SVal.overlay]; exact SVal.strip_hasTy hn

theorem SVal.overlayFields_hasTy {s : Name} {ofs nfs : List (Name × SVal)}
    (ho : SVal.hasTy.hasTyFields s ofs = true) (hn : SVal.hasTy.hasTyFields s nfs = true) :
    SVal.hasTy.hasTyFields s (SVal.overlay.overlayFields ofs nfs) = true := by
  match nfs with
  | [] => rfl
  | (n, v) :: rest =>
      simp only [SVal.hasTy.hasTyFields, Bool.and_eq_true] at hn
      simp only [SVal.overlay.overlayFields, SVal.hasTy.hasTyFields, Bool.and_eq_true]
      refine ⟨?_, SVal.overlayFields_hasTy ho hn.2⟩
      cases hdef : lookupBy n (structDef s) with
      | none => rw [hdef] at hn; exact Bool.noConfusion hn.1
      | some tyf =>
          rw [hdef] at hn
          simp only
          cases hl : lookupBy n ofs with
          | none => exact SVal.strip_hasTy hn.1
          | some o =>
              obtain ⟨T', hdef', hot⟩ := hasTyFields_lookup ho hl
              rw [hdef] at hdef'
              cases hdef'
              exact SVal.overlay_hasTy hot hn.1

theorem SVal.overlayElems_hasTy {elem : Ty} {olds news : List SVal}
    (ho : SVal.hasTy.hasTyElems elem olds = true) (hn : SVal.hasTy.hasTyElems elem news = true) :
    SVal.hasTy.hasTyElems elem (SVal.overlay.overlayElems olds news) = true := by
  match olds, news with
  | o :: os, v :: rest =>
      simp only [SVal.hasTy.hasTyElems, Bool.and_eq_true] at ho hn
      simp only [SVal.overlay.overlayElems, SVal.hasTy.hasTyElems, Bool.and_eq_true]
      exact ⟨SVal.overlay_hasTy ho.1 hn.1, SVal.overlayElems_hasTy ho.2 hn.2⟩
  | [], rest => simpa only [SVal.overlay.overlayElems] using SVal.stripElems_hasTy hn
  | _ :: _, [] => rfl

end

/-! ## The `defaultForTy` side condition

The depth charge the fuelled version carried is gone with the fuel:
`defaultForTy` is correct at every nesting depth now
(`Semantics.structDef_rank_lt`), so the no-duplicate-row condition is all
the content that is left. -/

mutual
/-- The side condition under which `defaultForTy` inhabits its type:
each `structDef` row is the one its field name looks up to, which rules
out duplicate field names. Decidable per concrete type. -/
def defaultOk : Ty -> Bool
  | Ty.prim _ => true
  | Ty.ref (RefTy.struct s) => defaultOkFields s (structDef s)
  | Ty.ref (RefTy.array _) => true
  | Ty.ref (RefTy.fixed e _) => defaultOk e
  | Ty.ref (RefTy.mapping _ value) => defaultOk value
termination_by ty => (tyRank ty, sizeOf ty)
decreasing_by
  · exact Prod.Lex.left _ _ (structDef_rank_lt _)
  all_goals first
    | (apply Prod.Lex.left; simp [tyRank]; done)
    | (apply Prod.Lex.right; simp; omega)

def defaultOkFields (s : Name) : List (Name × Ty) -> Bool
  | [] => true
  | (n, t) :: rest =>
      defaultOk t && (lookupBy n (structDef s) == some t) &&
        defaultOkFields s rest
termination_by l => (fieldsRank l, sizeOf l)
decreasing_by
  all_goals (apply lex_le_lt
             · simp only [fieldsRank]; omega
             · simp; omega)
end

/-- Fresh defaults inhabit their type. -/
theorem defaultForTy_hasTy : ∀ {ty : Ty}, defaultOk ty = true ->
    (defaultForTy ty).hasTy ty = true := by
  intro ty
  induction ty using defaultForTy.induct
    (motive2 := fun l => ∀ (s : Name), defaultOkFields s l = true ->
      SVal.hasTy.hasTyFields s (defaultForFields l) = true) with
  | case1 => intro _; simp [defaultForTy, SVal.hasTy]
  | case2 => intro _; simp [defaultForTy, SVal.hasTy]
  | case3 => intro _; simp [defaultForTy, SVal.hasTy]
  | case4 name ih =>
      intro h
      simp only [defaultOk] at h
      simpa only [defaultForTy, SVal.hasTy] using ih name h
  | case5 elem =>
      intro _
      simp [defaultForTy, SVal.hasTy, SVal.hasTy.hasTyElems]
  | case6 elem n ih =>
      intro h
      simp only [defaultOk] at h
      simp only [defaultForTy, SVal.hasTy, Bool.and_eq_true, beq_iff_eq, List.length_replicate]
      exact ⟨⟨⟨trivial, trivial⟩, hasTyElems_of_forall_mem fun v hv => by
        rw [List.eq_of_mem_replicate hv]; exact ih h⟩, rfl⟩
  | case7 key value ih =>
      intro h
      simp only [defaultOk] at h
      simp only [defaultForTy, SVal.hasTy, SVal.hasTy.hasTyEntries,
        Bool.true_and]
      exact ih h
  | case8 => simp [defaultForFields, SVal.hasTy.hasTyFields]
  | case9 n t rest iht ihrest =>
      rename_i s h
      simp only [defaultOkFields, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hok, hlook⟩, hrest⟩ := h
      simp only [defaultForFields, SVal.hasTy.hasTyFields, hlook,
        Bool.and_eq_true]
      exact ⟨iht hok, ihrest s hrest⟩

/-- An int inhabits every numeric type (`hasTy` carries no range
information; ranges are `checkArith`'s business). -/
theorem int_hasTy_numeric {ty : Ty} (h : isNumericTy ty = true)
    (n : Int) : (SVal.int n).hasTy ty = true := by
  cases ty with
  | prim pt => cases pt <;> first | rfl | exact Bool.noConfusion h
  | ref r => exact Bool.noConfusion h

/-- `asValue` round-trips through `toSVal`: reading a primitive out of
storage and writing it back is the identity. -/
theorem SVal.asValue_toSVal {v : SVal} {w : Value}
    (h : v.asValue = Except.ok w) : w.toSVal = v := by
  cases v with
  | prim p =>
      cases p <;> simp only [SVal.asValue] at h <;>
        simp [<- Except.ok.inj h, Value.toSVal]
  | struct fields => exact nomatch h
  | array elems => exact nomatch h
  | map entries dflt => exact nomatch h

/-- Arithmetic operators produce ints (comparisons and connectives are
the `Value.bool` results — that split is why `compoundAssign` needs
`op.isArith`, see `PreservationNecessity`). -/
theorem applyBinOp_arith_int {op : BinOp} {l r v : Value}
    (hop : op.isArith = true) (h : applyBinOp op l r = Except.ok v) :
    ∃ n, v = Value.int n := by
  cases op <;> simp only [BinOp.isArith] at hop <;>
    try exact Bool.noConfusion hop
  all_goals
    simp only [applyBinOp, bind, Except.bind] at h
  all_goals
    repeat' split at h
  all_goals
    first
    | exact ⟨_, (Except.ok.inj h).symm⟩
    | exact nomatch h

/-! ## The core write lemma -/

/-- Mirror of `find_hasTy` on the write side: saving a `ty'`-typed
value at a `ty'`-typed path keeps the tree at its type. -/
theorem save_hasTy {segs : List Seg} :
    ∀ {v : SVal} {ty ty' : Ty} {new w : SVal},
      v.hasTy ty = true -> tyAtSegs ty segs = some ty' ->
      new.hasTy ty' = true -> v.save segs new = Except.ok w ->
      w.hasTy ty = true := by
  induction segs with
  | nil =>
      intro v ty ty' new w hty hsegs hnew hsave
      simp [tyAtSegs] at hsegs
      simp [SVal.save] at hsave
      subst hsegs hsave
      exact hnew
  | cons seg rest ih =>
      intro v ty ty' new w hty hsegs hnew hsave
      simp only [tyAtSegs] at hsegs
      cases hseg : segTy ty seg with
      | none => rw [hseg] at hsegs; simp at hsegs
      | some tym =>
          rw [hseg] at hsegs
          simp at hsegs
          cases seg with
          | field n =>
              cases ty with
              | ref ref =>
                  cases ref with
                  | struct s =>
                      simp only [segTy] at hseg
                      cases v <;> simp [SVal.hasTy] at hty
                      case struct fields =>
                        simp only [SVal.save] at hsave
                        cases hlook : lookupBy n fields with
                        | none => rw [hlook] at hsave; simp at hsave
                        | some old =>
                            rw [hlook] at hsave
                            obtain ⟨updated, hup, hw⟩ :=
                              Semantics.bind_ok_inv hsave
                            simp at hw
                            obtain ⟨tyf, hdef, htyv⟩ :=
                              hasTyFields_lookup hty hlook
                            rw [hseg] at hdef
                            cases hdef
                            subst hw
                            show SVal.hasTy.hasTyFields s
                              (setBy n updated fields) = true
                            exact hasTyFields_setBy hty hseg
                              (ih htyv hsegs hnew hup)
                  | array elem => simp [segTy] at hseg
                  | fixed elem _ => simp [segTy] at hseg
                  | mapping key value => simp [segTy] at hseg
              | _ => simp [segTy] at hseg
          | «at» i =>
              cases ty with
              | ref ref =>
                  cases ref with
                  | struct s => simp [segTy] at hseg
                  | array elem =>
                      simp only [segTy] at hseg
                      cases hseg
                      cases v <;> simp [SVal.hasTy] at hty
                      case array elems shadow fx =>
                        simp only [SVal.save] at hsave
                        split at hsave
                        case isTrue hbound =>
                          obtain ⟨updated, hup, hw⟩ :=
                            Semantics.bind_ok_inv hsave
                          simp at hw
                          subst hw
                          simp only [SVal.hasTy, Bool.and_eq_true]
                          have hall := hasTyElems_set (i := i.toNat) (hasTyElems_append hty.1.2 hty.2)
                            (ih (hasTyElems_mem_append hty.1.2 hty.2 ((elems ++ shadow).get_mem _))
                              hsegs hnew hup)
                          exact ⟨⟨by simp [hty.1.1], hasTyElems_take _ hall⟩, hasTyElems_drop _ hall⟩
                        case isFalse => simp at hsave
                  | fixed elem n =>
                      simp only [segTy] at hseg
                      cases hseg
                      cases v <;> simp [SVal.hasTy] at hty
                      case array elems shadow fx =>
                        simp only [SVal.save] at hsave
                        split at hsave
                        case isTrue hbound =>
                          obtain ⟨updated, hup, hw⟩ :=
                            Semantics.bind_ok_inv hsave
                          simp at hw
                          subst hw
                          simp only [SVal.hasTy, Bool.and_eq_true, beq_iff_eq]
                          have hall := hasTyElems_set (i := i.toNat) (hasTyElems_append hty.1.2 hty.2)
                            (ih (hasTyElems_mem_append hty.1.2 hty.2 ((elems ++ shadow).get_mem _))
                              hsegs hnew hup)
                          refine ⟨⟨⟨hty.1.1.1, ?_⟩, hasTyElems_take _ hall⟩, hasTyElems_drop _ hall⟩
                          simp [hty.1.1.2]
                        case isFalse => simp at hsave
                  | mapping key value =>
                      simp only [segTy] at hseg
                      cases hseg
                      cases v <;> simp [SVal.hasTy] at hty
                      case map entries dflt =>
                        simp only [SVal.save] at hsave
                        cases hlook : lookupBy i entries with
                        | none =>
                            rw [hlook] at hsave
                            obtain ⟨updated, hup, hw⟩ :=
                              Semantics.bind_ok_inv hsave
                            simp at hw
                            subst hw
                            simp only [SVal.hasTy, Bool.and_eq_true]
                            exact ⟨hasTyEntries_setBy hty.1
                              (ih hty.2 hsegs hnew hup), hty.2⟩
                        | some old =>
                            rw [hlook] at hsave
                            obtain ⟨updated, hup, hw⟩ :=
                              Semantics.bind_ok_inv hsave
                            simp at hw
                            subst hw
                            simp only [SVal.hasTy, Bool.and_eq_true]
                            exact ⟨hasTyEntries_setBy hty.1
                              (ih (hasTyEntries_lookup hty.1 hlook)
                                hsegs hnew hup), hty.2⟩
              | _ => simp [segTy] at hseg

/-! ## Layout key uniqueness -/

/-! `nodupKeysB` (`AST.lean`): `wellTypedStorageB` checks every layout row
against the single stored value at its root, so a duplicated root would
check one value against two types — see the refutation that was the
removed `PreservationNecessity` counterexample (`docs/kernel-port.md`'s
"Port later"). -/

theorem lookupBy_isSome_of_mem [DecidableEq κ] {l : List (κ × α)}
    {k : κ} {v : α} (hmem : (k, v) ∈ l) :
    (lookupBy k l).isSome = true := by
  induction l with
  | nil => cases hmem
  | cons p rest ih =>
      obtain ⟨k', v'⟩ := p
      by_cases hk : k = k'
      · simp [lookupBy, hk]
      · cases hmem with
        | head => exact absurd rfl hk
        | tail _ hmem => simpa [lookupBy, hk] using ih hmem

/-- On a nodup-keyed association list, membership determines lookup. -/
theorem lookupBy_eq_of_nodup [DecidableEq κ] {l : List (κ × α)} {k : κ}
    {v : α} (hnd : nodupKeysB l = true) (hmem : (k, v) ∈ l) :
    lookupBy k l = some v := by
  induction l with
  | nil => cases hmem
  | cons p rest ih =>
      obtain ⟨k', v'⟩ := p
      simp only [nodupKeysB, Bool.and_eq_true] at hnd
      cases hmem with
      | head => simp [lookupBy]
      | tail _ hmem =>
          by_cases hk : k = k'
          · subst hk
            have := lookupBy_isSome_of_mem hmem
            rw [Option.isNone_iff_eq_none.mp hnd.1] at this
            exact Bool.noConfusion this
          · simpa [lookupBy, hk] using ih hnd.2 hmem

/-! ## State-level preservation -/

/-- THE preservation lemma: `saveStorage` at a layout-typed path with a
value of that type keeps the whole storage well-typed. Every
storage-mutating interpreter arm reduces to this. -/
theorem State.saveStorage_wellTyped {L : Layout} {s s' : State}
    {root : Name} {segs : List Seg} {ty' : Ty} {new : SVal}
    (hnd : nodupKeysB L.globals = true)
    (hst : wellTypedStorageB L s.storage = true)
    (hty : L.tyAt root segs = some ty')
    (hnew : new.hasTy ty' = true)
    (hsave : s.saveStorage root segs new = Except.ok s') :
    wellTypedStorageB L s'.storage = true := by
  obtain ⟨ty0, hglob, hty⟩ := Layout.tyAt_split hty
  obtain ⟨v0, updated, hroot, hup, rfl⟩ := SemanticsProperties.State.saveStorage_ok_inv hsave
  have hv0 : v0.hasTy ty0 = true := by
    simpa only [hroot] using (List.all_eq_true.mp hst) _ (lookupBy_eq_some_mem hglob)
  have hupd : updated.hasTy ty0 = true := save_hasTy hv0 hty hnew hup
  refine List.all_eq_true.mpr fun g hg => ?_
  show (match lookupBy g.1 (setBy root updated s.storage) with
    | some v => v.hasTy g.2
    | none => false) = true
  by_cases hgr : g.1 = root
  · have hgty : g.2 = ty0 := by
      have hl := lookupBy_eq_of_nodup hnd hg
      rw [hgr, hglob] at hl
      exact (Option.some.inj hl).symm
    rw [hgr, hgty]
    simpa only [lookupBy_setBy_self] using hupd
  · rw [lookupBy_setBy_ne hgr]
    exact (List.all_eq_true.mp hst) _ hg

/-! ## The recycled slot a `push` lands on

`Semantics.pushSlot` either hands back a slot a `pop` cleared — still an
element of the array, so still of the element type — or materialises the
type's default.  Both inhabit the element type, and the slots that are left
still do, which is what the `push` case of type soundness needs. -/

/-- The `isPrimitive` branch of `pushSlot` is redundant where the recycled
slot inhabits the element type: clearing a primitive gives the type's own
default.  So the two readings of "the slot a `push` lands on" agree on every
well-typed storage, and the branch buys the EVM layer its typing-free view. -/
theorem pushSlot_prim {elemTy : Ty} {c : SVal} {rest : List SVal}
    (hp : elemTy.isPrimitive = true) (hc : c.hasTy elemTy = true) :
    (pushSlot elemTy (c :: rest)).1 = c.defaultOf := by
  cases elemTy with
  | ref r => simp [Ty.isPrimitive] at hp
  | prim pt =>
      cases c with
      | prim p =>
          cases pt <;> cases p <;>
            simp_all [pushSlot, SVal.defaultOf, defaultForTy, SVal.hasTy,
              Ty.isPrimitive]
      | struct _ => cases pt <;> simp [SVal.hasTy] at hc
      | array _ _ => cases pt <;> simp [SVal.hasTy] at hc
      | map _ _ => cases pt <;> simp [SVal.hasTy] at hc

/-- The slots that are left after a `push` still inhabit the element type —
they are a tail of the ones that were there, so this needs no `defaultOk`. -/
theorem pushSlot_rest_hasTy {elemTy : Ty} {shadow : List SVal}
    (hsh : SVal.hasTy.hasTyElems elemTy shadow = true) :
    SVal.hasTy.hasTyElems elemTy (pushSlot elemTy shadow).2 = true := by
  cases shadow with
  | nil => rfl
  | cons c rest =>
      simp only [SVal.hasTy.hasTyElems, Bool.and_eq_true] at hsh
      exact hsh.2

theorem pushSlot_hasTy {elemTy : Ty} {shadow : List SVal}
    (hsh : SVal.hasTy.hasTyElems elemTy shadow = true)
    (hok : defaultOk elemTy = true) :
    (pushSlot elemTy shadow).1.hasTy elemTy = true ∧
      SVal.hasTy.hasTyElems elemTy (pushSlot elemTy shadow).2 = true := by
  cases shadow with
  | nil => exact ⟨defaultForTy_hasTy hok, rfl⟩
  | cons c rest =>
      simp only [SVal.hasTy.hasTyElems, Bool.and_eq_true] at hsh
      refine ⟨?_, hsh.2⟩
      simp only [pushSlot]
      split
      · exact defaultForTy_hasTy hok
      · exact hsh.1

end Semantics
end Solidity
