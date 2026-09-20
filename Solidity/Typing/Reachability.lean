import Solidity.Typing.Soundness
import Solidity.RewriteSoundness
import Solidity.Semantics.DecEq

/-!
# Tightness of `wellFormed(storage)`: every canonical storage is reachable

`TypeSoundness` shows the storage invariant is *sufficient* (preserved by
every well-typed statement) and `Counterexamples/PreservationNecessity`
that each conjunct is *necessary*. This module asks the third question —
is anything **missing**? "Everything that can be inferred about a
storage" is exactly what holds on every *reachable* storage, so the
invariant is complete iff it coincides with reachability from the
contract's initial state:

```
Reachable L s := ∃ prog Γ', blockWt [] L prog = some Γ' ∧
                            execBlock (initialState L) prog = .ok s
```

`reachable_wellTyped` (⇒) is a corollary of preservation. The converse
is a *constructibility* theorem: `writeProg` builds any storage from the
all-defaults initial state with literal assignments, `push()` and
`delete` (`storage_tight`), so any property that is inductive under
execution already follows from the invariant (`no_hidden_invariant`).

Constructibility does **not** hold for `wellTypedStorageB` itself: the
interpreter maintains four facts that `SVal.hasTy` forgets, and
`SVal.canonical` adds exactly those —

- a mapping's default is the type's default (`save`/`defaultOf` never
  touch `dflt`; `hasTy` only asks `dflt.hasTy value`);
- a mapping's entry keys are unique (they only grow by `setBy`);
- a struct carries exactly its declared fields, in declared order
  (`defaultForTy` creates them, `setBy` on an existing key keeps them;
  `hasTy` checks only the fields *present*).

Conversely `uint` range is **not** an invariant of this model: literals
and plain assignments are unchecked (`evalValue (intLit _ v) = .ok v`,
`wtExpr (intLit ty _) = isNumericTy ty`), so `total = -5;` is a
well-typed program (`uint_negative_reachable`) — and `canonical`
rightly does not demand a range.

The converse invariant "reachable ⇒ canonical" (needed to *refute*
reachability of the non-canonical witnesses below) is a second
`TypeSoundness`-sized traversal of the interpreter and is left open,
like `BlockStep.wellFounded`; env/heap tightness (up to renaming of
identities) is likewise future work.

It is open in a second sense since `pop` became faithful: a popped array
carries the slot it cleared (`SVal.array`'s second field, `Semantics.pushSlot`),
and `canonical` is the **shadow-free** fragment — the one `writeProg`
can build, since it builds with assignments and pushes and never a `pop`.
So `arr.push(); arr.pop();` is reachable and not canonical. Closing the
converse means either teaching `fill` to pop or carrying the recycled
slots in `canonical` and scoping `storage_tight` to the shadow-free part;
either is its own change.
-/

namespace Solidity
namespace Semantics

open SemanticsProperties (lookupBy_setBy_self lookupBy_setBy_ne
  HeapWellFormed)

/-! ## Infrastructure -/

/-- Checking concatenated blocks is monadic sequencing (twin of
`execBlock_append`). -/
theorem blockWt_append (Γ : Ctx) (L : Layout) (a b : List Stmt) :
    blockWt Γ L (a ++ b) =
      (blockWt Γ L a).bind fun Γ' => blockWt Γ' L b := by
  induction a generalizing Γ with
  | nil => rfl
  | cons stmt rest ih =>
      rw [List.cons_append, blockWt, blockWt]
      cases stmtWt Γ L stmt with
      | none => rfl
      | some Γ₁ => exact ih Γ₁

theorem lookupBy_map_snd [DecidableEq κ] (k : κ) (f : α -> β) :
    ∀ (l : List (κ × α)),
      lookupBy k (l.map fun p => (p.1, f p.2)) = (lookupBy k l).map f
  | [] => rfl
  | (k', v) :: rest => by
      simp only [List.map_cons, lookupBy]
      by_cases h : k = k' <;> simp [h, lookupBy_map_snd k f rest]

/-! ## Layout side condition -/

/-- `defaultOk` strengthened by nodup `structDef` rows and a fuel charge
on array element types, so that `push()` on every nested element type
is `stmtWt`-checkable. -/
def tyOkFuel : Nat -> Ty -> Bool
  | _, Ty.prim _ => true
  | 0, Ty.ref _ => false
  | fuel + 1, Ty.ref (RefTy.struct s) =>
      nodupKeysB (structDef s) &&
        (structDef s).all fun fld => tyOkFuel fuel fld.2
  | fuel + 1, Ty.ref (RefTy.array elem) => tyOkFuel fuel elem
  | fuel + 1, Ty.ref (RefTy.mapping _ value) => tyOkFuel fuel value

def tyOk (ty : Ty) : Bool := tyOkFuel 8 ty

/-- Nodup roots, every root type `tyOk`. -/
def layoutOkB (L : Layout) : Bool :=
  nodupKeysB L.globals && L.globals.all fun g => tyOk g.2

theorem tyOkFuel_mono : ∀ {n m : Nat} {ty : Ty}, n ≤ m ->
    tyOkFuel n ty = true -> tyOkFuel m ty = true := by
  intro n
  induction n with
  | zero =>
      intro m ty _ h
      cases ty with
      | prim pt => cases m <;> rfl
      | ref r => exact Bool.noConfusion h
  | succ n ih =>
      intro m ty hle h
      cases m with
      | zero => exact absurd hle (by omega)
      | succ m =>
          cases ty with
          | prim pt => rfl
          | ref r =>
              cases r with
              | struct s =>
                  simp only [tyOkFuel, List.all_eq_true,
                    Bool.and_eq_true] at h ⊢
                  exact ⟨h.1, fun fld hmem => ih (by omega) (h.2 fld hmem)⟩
              | array elem =>
                  simp only [tyOkFuel] at h ⊢
                  exact ih (by omega) h
              | mapping key value =>
                  simp only [tyOkFuel] at h ⊢
                  exact ih (by omega) h

/-- `tyOk` is still fuelled — it is the induction measure of the
canonical-storage development below — while `defaultOk` no longer is,
`defaultForTy` being correct at every depth now. The bridge therefore
needs no `n ≤ 8` side condition any more: any amount of `tyOkFuel`
implies `defaultOk`. -/
theorem tyOkFuel_defaultOk : ∀ {n : Nat} {ty : Ty},
    tyOkFuel n ty = true -> defaultOk ty = true := by
  intro n
  induction n with
  | zero =>
      intro ty h
      cases ty with
      | prim pt => simp [defaultOk]
      | ref r => exact Bool.noConfusion h
  | succ n ih =>
      intro ty h
      cases ty with
      | prim pt => simp [defaultOk]
      | ref r =>
          cases r with
          | struct s =>
              simp only [tyOkFuel, List.all_eq_true, Bool.and_eq_true] at h
              simp only [defaultOk]
              exact defaultOkFields_of_rows
                (fun p hp => lookupBy_eq_of_nodup h.1 hp)
                (fun p hp => ih (h.2 p hp))
          | array elem => simp [defaultOk]
          | mapping key value =>
              simp only [tyOkFuel] at h
              simp only [defaultOk]
              exact ih h

theorem tyOk_defaultOk {ty : Ty} (h : tyOk ty = true) : defaultOk ty = true :=
  tyOkFuel_defaultOk h

/-! ## The initial state and reachability -/

/-- The contract's initial state: every root at its type's default,
nothing else. -/
def initialState (L : Layout) : State :=
  { storage := L.globals.map fun g => (g.1, defaultForTy g.2) }

/-- The initial state satisfies the invariant — the missing base case of
"assume `wellFormed` once". -/
theorem initialState_wt {L : Layout} (hL : layoutOkB L = true) :
    StateWT [] [] L (initialState L) := by
  simp only [layoutOkB, Bool.and_eq_true] at hL
  refine ⟨hL.1, rfl, rfl, ?_, rfl, rfl, fun _ _ => rfl⟩
  apply List.all_eq_true.mpr
  intro g hg
  have hlook : lookupBy g.1 L.globals = some g.2 :=
    lookupBy_eq_of_nodup hL.1 hg
  show (match lookupBy g.1 (initialState L).storage with
        | some v => v.hasTy g.2
        | none => false) = true
  simp only [initialState, lookupBy_map_snd, hlook, Option.map_some]
  exact defaultForTy_hasTy (tyOk_defaultOk (List.all_eq_true.mp hL.2 g hg))

/-- A state is reachable when some `blockWt`-checked program produces it
from the initial state. -/
def Reachable (L : Layout) (s : State) : Prop :=
  ∃ (prog : List Stmt) (Γ' : Ctx),
    blockWt [] L prog = some Γ' ∧
      execBlock (initialState L) prog = Except.ok s

/-- Reachable ⇒ well-typed: preservation from the initial state. -/
theorem reachable_wellTyped {L : Layout} {s : State}
    (hL : layoutOkB L = true) (h : Reachable L s) :
    wellTypedStorageB L s.storage = true := by
  obtain ⟨prog, Γ', hwt, hexec⟩ := h
  exact execBlock_preserves_wellTyped (initialState_wt hL) hwt hexec

/-! ## The tight predicate -/

/-- The value is *the* default of the type: zero / `false`, a struct with
exactly the declared fields (in order) all default, an empty array, an
empty mapping whose default is default. -/
def SVal.isDefault : SVal -> Ty -> Bool
  | SVal.int n, Ty.uint => n == 0
  | SVal.int n, Ty.int => n == 0
  | SVal.bool b, Ty.bool => b == false
  | SVal.struct fields, Ty.ref (RefTy.struct s) =>
      (fields.map Prod.fst == (structDef s).map Prod.fst) &&
        isDefaultFields s fields
  | SVal.array elems shadow, Ty.ref (RefTy.array _) => elems.isEmpty && shadow.isEmpty
  | SVal.map entries dflt, Ty.ref (RefTy.mapping _ value) =>
      entries.isEmpty && dflt.isDefault value
  | _, _ => false
where
  isDefaultFields (s : Name) : List (Name × SVal) -> Bool
    | [] => true
    | (n, v) :: rest =>
        (match lookupBy n (structDef s) with
         | some ty => v.isDefault ty
         | none => false) && isDefaultFields s rest

/-- `hasTy` plus the facts execution maintains and `hasTy` forgets:
declared struct field set (in order), unique mapping keys, default
mapping default. -/
def SVal.canonical : SVal -> Ty -> Bool
  | SVal.int _, Ty.int => true
  | SVal.int _, Ty.uint => true
  | SVal.bool _, Ty.bool => true
  | SVal.struct fields, Ty.ref (RefTy.struct s) =>
      (fields.map Prod.fst == (structDef s).map Prod.fst) &&
        canonicalFields s fields
  -- No recycled slots: `writeProg` builds a storage by assignments and
  -- pushes, and rebuilding a slot a `pop` gave back would need the `pop`
  -- too.  So `canonical` is the *shadow-free* fragment — which keeps
  -- `storage_tight` (canonical ⇒ reachable) true and narrows only the
  -- converse, which is open anyway.
  | SVal.array elems shadow, Ty.ref (RefTy.array elem) =>
      canonicalElems elem elems && shadow.isEmpty
  | SVal.map entries dflt, Ty.ref (RefTy.mapping _ value) =>
      nodupKeysB entries && canonicalEntries value entries &&
        dflt.isDefault value
  | _, _ => false
where
  canonicalFields (s : Name) : List (Name × SVal) -> Bool
    | [] => true
    | (n, v) :: rest =>
        (match lookupBy n (structDef s) with
         | some ty => v.canonical ty
         | none => false) && canonicalFields s rest
  canonicalElems (elem : Ty) : List SVal -> Bool
    | [] => true
    | v :: rest => v.canonical elem && canonicalElems elem rest
  canonicalEntries (value : Ty) : List (Int × SVal) -> Bool
    | [] => true
    | (_, v) :: rest => v.canonical value && canonicalEntries value rest

/-- Exactly the layout's roots (in order), each canonical at its type. -/
def canonicalStorageB (L : Layout) (st : List (Name × SVal)) : Bool :=
  (st.map Prod.fst == L.globals.map Prod.fst) &&
  L.globals.all fun g =>
    match lookupBy g.1 st with
    | some v => v.canonical g.2
    | none => false

/-! ### `isDefault` and `canonical` imply `hasTy` -/

mutual

theorem SVal.isDefault_hasTy {v : SVal} {ty : Ty}
    (h : v.isDefault ty = true) : v.hasTy ty = true := by
  cases v with
  | prim p =>
      cases p with
      | int n =>
          cases ty with
          | prim pt => cases pt <;> simp_all [SVal.isDefault, SVal.hasTy]
          | ref r => simp [SVal.isDefault] at h
      | bool b =>
          cases ty with
          | prim pt => cases pt <;> simp_all [SVal.isDefault, SVal.hasTy]
          | ref r => simp [SVal.isDefault] at h
  | struct fields =>
      cases ty with
      | prim pt => simp [SVal.isDefault] at h
      | ref r =>
          cases r with
          | struct sname =>
              simp only [SVal.isDefault, Bool.and_eq_true] at h
              simpa only [SVal.hasTy] using SVal.isDefaultFields_hasTy h.2
          | array elem => simp [SVal.isDefault] at h
          | mapping key value => simp [SVal.isDefault] at h
  | array elems =>
      cases ty with
      | prim pt => simp [SVal.isDefault] at h
      | ref r =>
          cases r with
          | struct sname => simp [SVal.isDefault] at h
          | array elem =>
              cases elems with
              | nil =>
                  rename_i shadow
                  cases shadow with
                  | nil => rfl
                  | cons c cs => simp [SVal.isDefault] at h
              | cons x xs => simp [SVal.isDefault] at h
          | mapping key value => simp [SVal.isDefault] at h
  | map entries dflt =>
      cases ty with
      | prim pt => simp [SVal.isDefault] at h
      | ref r =>
          cases r with
          | struct sname => simp [SVal.isDefault] at h
          | array elem => simp [SVal.isDefault] at h
          | mapping key value =>
              cases entries with
              | nil =>
                  simp only [SVal.isDefault, List.isEmpty_nil,
                    Bool.true_and] at h
                  simp only [SVal.hasTy, SVal.hasTy.hasTyEntries,
                    Bool.true_and]
                  exact SVal.isDefault_hasTy h
              | cons e es => simp [SVal.isDefault] at h

theorem SVal.isDefaultFields_hasTy {s : Name} {fields : List (Name × SVal)}
    (h : SVal.isDefault.isDefaultFields s fields = true) :
    SVal.hasTy.hasTyFields s fields = true := by
  match fields with
  | [] => rfl
  | (n, v) :: rest =>
      simp only [SVal.isDefault.isDefaultFields, Bool.and_eq_true] at h
      simp only [SVal.hasTy.hasTyFields, Bool.and_eq_true]
      refine ⟨?_, SVal.isDefaultFields_hasTy h.2⟩
      cases hdef : lookupBy n (structDef s) with
      | none => rw [hdef] at h; exact Bool.noConfusion h.1
      | some tyf =>
          rw [hdef] at h
          exact SVal.isDefault_hasTy h.1

end

mutual

theorem SVal.canonical_hasTy {v : SVal} {ty : Ty}
    (h : v.canonical ty = true) : v.hasTy ty = true := by
  cases v with
  | prim p =>
      cases p with
      | int n =>
          cases ty with
          | prim pt => cases pt <;> simp_all [SVal.canonical, SVal.hasTy]
          | ref r => simp [SVal.canonical] at h
      | bool b =>
          cases ty with
          | prim pt => cases pt <;> simp_all [SVal.canonical, SVal.hasTy]
          | ref r => simp [SVal.canonical] at h
  | struct fields =>
      cases ty with
      | prim pt => simp [SVal.canonical] at h
      | ref r =>
          cases r with
          | struct sname =>
              simp only [SVal.canonical, Bool.and_eq_true] at h
              simpa only [SVal.hasTy] using SVal.canonicalFields_hasTy h.2
          | array elem => simp [SVal.canonical] at h
          | mapping key value => simp [SVal.canonical] at h
  | array elems =>
      cases ty with
      | prim pt => simp [SVal.canonical] at h
      | ref r =>
          cases r with
          | struct sname => simp [SVal.canonical] at h
          | array elem =>
              simp only [SVal.canonical, Bool.and_eq_true] at h
              obtain ⟨hlive, hsh⟩ := h
              rw [List.isEmpty_iff] at hsh
              subst hsh
              simpa only [SVal.hasTy, Bool.and_eq_true, SVal.hasTy.hasTyElems,
                Bool.and_true] using SVal.canonicalElems_hasTy hlive
          | mapping key value => simp [SVal.canonical] at h
  | map entries dflt =>
      cases ty with
      | prim pt => simp [SVal.canonical] at h
      | ref r =>
          cases r with
          | struct sname => simp [SVal.canonical] at h
          | array elem => simp [SVal.canonical] at h
          | mapping key value =>
              simp only [SVal.canonical, Bool.and_eq_true] at h
              simp only [SVal.hasTy, Bool.and_eq_true]
              exact ⟨SVal.canonicalEntries_hasTy h.1.2,
                SVal.isDefault_hasTy h.2⟩

theorem SVal.canonicalFields_hasTy {s : Name} {fields : List (Name × SVal)}
    (h : SVal.canonical.canonicalFields s fields = true) :
    SVal.hasTy.hasTyFields s fields = true := by
  match fields with
  | [] => rfl
  | (n, v) :: rest =>
      simp only [SVal.canonical.canonicalFields, Bool.and_eq_true] at h
      simp only [SVal.hasTy.hasTyFields, Bool.and_eq_true]
      refine ⟨?_, SVal.canonicalFields_hasTy h.2⟩
      cases hdef : lookupBy n (structDef s) with
      | none => rw [hdef] at h; exact Bool.noConfusion h.1
      | some tyf =>
          rw [hdef] at h
          exact SVal.canonical_hasTy h.1

theorem SVal.canonicalElems_hasTy {elem : Ty} {elems : List SVal}
    (h : SVal.canonical.canonicalElems elem elems = true) :
    SVal.hasTy.hasTyElems elem elems = true := by
  match elems with
  | [] => rfl
  | v :: rest =>
      simp only [SVal.canonical.canonicalElems, Bool.and_eq_true] at h
      simp only [SVal.hasTy.hasTyElems, Bool.and_eq_true]
      exact ⟨SVal.canonical_hasTy h.1, SVal.canonicalElems_hasTy h.2⟩

theorem SVal.canonicalEntries_hasTy {value : Ty}
    {entries : List (Int × SVal)}
    (h : SVal.canonical.canonicalEntries value entries = true) :
    SVal.hasTy.hasTyEntries value entries = true := by
  match entries with
  | [] => rfl
  | (k, v) :: rest =>
      simp only [SVal.canonical.canonicalEntries, Bool.and_eq_true] at h
      simp only [SVal.hasTy.hasTyEntries, Bool.and_eq_true]
      exact ⟨SVal.canonical_hasTy h.1, SVal.canonicalEntries_hasTy h.2⟩

end

theorem canonicalStorage_wellTyped {L : Layout} {st : List (Name × SVal)}
    (h : canonicalStorageB L st = true) : wellTypedStorageB L st = true := by
  simp only [canonicalStorageB, Bool.and_eq_true, List.all_eq_true] at h
  apply List.all_eq_true.mpr
  intro g hg
  have := h.2 g hg
  cases hl : lookupBy g.1 st with
  | none => rw [hl] at this; exact Bool.noConfusion this
  | some v =>
      rw [hl] at this
      exact SVal.canonical_hasTy this

/-! ### Defaults are canonical, unique, and `delete`-fixed -/

mutual

theorem SVal.isDefault_canonical {v : SVal} {ty : Ty}
    (h : v.isDefault ty = true) : v.canonical ty = true := by
  cases v with
  | prim p =>
      cases p with
      | int n =>
          cases ty with
          | prim pt => cases pt <;> simp_all [SVal.isDefault, SVal.canonical]
          | ref r => simp [SVal.isDefault] at h
      | bool b =>
          cases ty with
          | prim pt => cases pt <;> simp_all [SVal.isDefault, SVal.canonical]
          | ref r => simp [SVal.isDefault] at h
  | struct fields =>
      cases ty with
      | prim pt => simp [SVal.isDefault] at h
      | ref r =>
          cases r with
          | struct sname =>
              simp only [SVal.isDefault, Bool.and_eq_true] at h
              simp only [SVal.canonical, Bool.and_eq_true]
              exact ⟨h.1, SVal.isDefaultFields_canonical h.2⟩
          | array elem => simp [SVal.isDefault] at h
          | mapping key value => simp [SVal.isDefault] at h
  | array elems =>
      cases ty with
      | prim pt => simp [SVal.isDefault] at h
      | ref r =>
          cases r with
          | struct sname => simp [SVal.isDefault] at h
          | array elem =>
              cases elems with
              | nil =>
                  rename_i shadow
                  cases shadow with
                  | nil => rfl
                  | cons c cs => simp [SVal.isDefault] at h
              | cons x xs => simp [SVal.isDefault] at h
          | mapping key value => simp [SVal.isDefault] at h
  | map entries dflt =>
      cases ty with
      | prim pt => simp [SVal.isDefault] at h
      | ref r =>
          cases r with
          | struct sname => simp [SVal.isDefault] at h
          | array elem => simp [SVal.isDefault] at h
          | mapping key value =>
              cases entries with
              | nil =>
                  simp only [SVal.isDefault, List.isEmpty_nil,
                    Bool.true_and] at h
                  simp only [SVal.canonical, nodupKeysB,
                    SVal.canonical.canonicalEntries, Bool.true_and]
                  exact h
              | cons e es => simp [SVal.isDefault] at h

theorem SVal.isDefaultFields_canonical {s : Name}
    {fields : List (Name × SVal)}
    (h : SVal.isDefault.isDefaultFields s fields = true) :
    SVal.canonical.canonicalFields s fields = true := by
  match fields with
  | [] => rfl
  | (n, v) :: rest =>
      simp only [SVal.isDefault.isDefaultFields, Bool.and_eq_true] at h
      simp only [SVal.canonical.canonicalFields, Bool.and_eq_true]
      refine ⟨?_, SVal.isDefaultFields_canonical h.2⟩
      cases hdef : lookupBy n (structDef s) with
      | none => rw [hdef] at h; exact Bool.noConfusion h.1
      | some tyf =>
          rw [hdef] at h
          exact SVal.isDefault_canonical h.1

end

/-- The type's default *is* default. -/
theorem defaultForTy_isDefault : ∀ {ty : Ty}, defaultOk ty = true ->
    (defaultForTy ty).isDefault ty = true := by
  intro ty
  induction ty using defaultForTy.induct
    (motive2 := fun l => ∀ (s : Name), defaultOkFields s l = true ->
      SVal.isDefault.isDefaultFields s (defaultForFields l) = true) with
  | case1 => intro _; simp [defaultForTy, SVal.isDefault]
  | case2 => intro _; simp [defaultForTy, SVal.isDefault]
  | case3 => intro _; simp [defaultForTy, SVal.isDefault]
  | case4 name ih =>
      intro h
      simp only [defaultOk] at h
      simp only [defaultForTy, SVal.isDefault, Bool.and_eq_true]
      refine ⟨?_, ih name h⟩
      -- the field names of `defaultForFields l` are those of `l`
      clear ih h
      induction structDef name with
      | nil => simp [defaultForFields]
      | cons fld rest ihrows =>
          obtain ⟨n, t⟩ := fld
          simpa [defaultForFields] using ihrows
  | case5 elem => intro _; simp [defaultForTy, SVal.isDefault]
  | case6 key value ih =>
      intro h
      simp only [defaultOk] at h
      simp only [defaultForTy, SVal.isDefault, List.isEmpty_nil,
        Bool.true_and]
      exact ih h
  | case7 => simp [defaultForFields, SVal.isDefault.isDefaultFields]
  | case8 n t rest iht ihrest =>
      rename_i s h
      simp only [defaultOkFields, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hok, hlook⟩, hrest⟩ := h
      simp only [defaultForFields, SVal.isDefault.isDefaultFields, hlook,
        Bool.and_eq_true]
      exact ⟨iht hok, ihrest s hrest⟩

mutual

/-- `delete` is the identity on a default value. -/
theorem SVal.defaultOf_of_isDefault {v : SVal} {ty : Ty}
    (h : v.isDefault ty = true) : v.defaultOf = v := by
  cases v with
  | prim p =>
      cases p with
      | int n =>
          cases ty with
          | prim pt => cases pt <;> simp_all [SVal.isDefault, SVal.defaultOf]
          | ref r => simp [SVal.isDefault] at h
      | bool b =>
          cases ty with
          | prim pt => cases pt <;> simp_all [SVal.isDefault, SVal.defaultOf]
          | ref r => simp [SVal.isDefault] at h
  | struct fields =>
      cases ty with
      | prim pt => simp [SVal.isDefault] at h
      | ref r =>
          cases r with
          | struct sname =>
              simp only [SVal.isDefault, Bool.and_eq_true] at h
              simp only [SVal.defaultOf]
              rw [SVal.defaultOfFields_of_isDefault h.2]
          | array elem => simp [SVal.isDefault] at h
          | mapping key value => simp [SVal.isDefault] at h
  | array elems =>
      cases ty with
      | prim pt => simp [SVal.isDefault] at h
      | ref r =>
          cases r with
          | struct sname => simp [SVal.isDefault] at h
          | array elem =>
              cases elems with
              | nil =>
                  rename_i shadow
                  cases shadow with
                  | nil => rfl
                  | cons c cs => simp [SVal.isDefault] at h
              | cons x xs => simp [SVal.isDefault] at h
          | mapping key value => simp [SVal.isDefault] at h
  | map entries dflt => rfl

theorem SVal.defaultOfFields_of_isDefault {s : Name}
    {fields : List (Name × SVal)}
    (h : SVal.isDefault.isDefaultFields s fields = true) :
    SVal.defaultOf.defaultOfFields fields = fields := by
  match fields with
  | [] => rfl
  | (n, v) :: rest =>
      simp only [SVal.isDefault.isDefaultFields, Bool.and_eq_true] at h
      simp only [SVal.defaultOf.defaultOfFields]
      rw [SVal.defaultOfFields_of_isDefault h.2]
      cases hdef : lookupBy n (structDef s) with
      | none => rw [hdef] at h; exact Bool.noConfusion h.1
      | some tyf =>
          rw [hdef] at h
          rw [SVal.defaultOf_of_isDefault h.1]

end

mutual

/-- Two defaults of one type are equal — the honest reading of
"`dflt = defaultForTy value`" without fuel arithmetic. -/
theorem SVal.isDefault_unique {v w : SVal} {ty : Ty}
    (hv : v.isDefault ty = true) (hw : w.isDefault ty = true) : v = w := by
  cases v with
  | prim p =>
      cases p with
      | int n =>
          cases ty with
          | prim pt =>
              cases pt <;> cases w with
              | prim q => cases q <;> simp_all [SVal.isDefault]
              | _ => simp [SVal.isDefault] at hw
          | ref r => simp [SVal.isDefault] at hv
      | bool b =>
          cases ty with
          | prim pt =>
              cases pt <;> cases w with
              | prim q => cases q <;> simp_all [SVal.isDefault]
              | _ => simp [SVal.isDefault] at hw
          | ref r => simp [SVal.isDefault] at hv
  | struct fields =>
      cases ty with
      | prim pt => simp [SVal.isDefault] at hv
      | ref r =>
          cases r with
          | struct sname =>
              cases w with
              | struct gs =>
                  simp only [SVal.isDefault, Bool.and_eq_true,
                    beq_iff_eq] at hv hw
                  rw [SVal.isDefaultFields_unique (hv.1.trans hw.1.symm)
                    hv.2 hw.2]
              | _ => simp [SVal.isDefault] at hw
          | array elem => simp [SVal.isDefault] at hv
          | mapping key value => simp [SVal.isDefault] at hv
  | array elems =>
      cases ty with
      | prim pt => simp [SVal.isDefault] at hv
      | ref r =>
          cases r with
          | struct sname => simp [SVal.isDefault] at hv
          | array elem =>
              cases w with
              | array ws wsh =>
                  cases elems with
                  | cons x xs => simp [SVal.isDefault] at hv
                  | nil =>
                      cases ws with
                      | cons y ys => simp [SVal.isDefault] at hw
                      | nil =>
                          rename_i shadow
                          cases shadow with
                          | cons c cs => simp [SVal.isDefault] at hv
                          | nil =>
                              cases wsh with
                              | cons c cs => simp [SVal.isDefault] at hw
                              | nil => rfl
              | _ => simp [SVal.isDefault] at hw
          | mapping key value => simp [SVal.isDefault] at hv
  | map entries dflt =>
      cases ty with
      | prim pt => simp [SVal.isDefault] at hv
      | ref r =>
          cases r with
          | struct sname => simp [SVal.isDefault] at hv
          | array elem => simp [SVal.isDefault] at hv
          | mapping key value =>
              cases w with
              | map ws wd =>
                  cases entries with
                  | cons e es => simp [SVal.isDefault] at hv
                  | nil =>
                      cases ws with
                      | cons f fs => simp [SVal.isDefault] at hw
                      | nil =>
                          simp only [SVal.isDefault, List.isEmpty_nil,
                            Bool.true_and] at hv hw
                          rw [SVal.isDefault_unique hv hw]
              | _ => simp [SVal.isDefault] at hw

theorem SVal.isDefaultFields_unique {s : Name}
    {fs gs : List (Name × SVal)}
    (hnames : fs.map Prod.fst = gs.map Prod.fst)
    (hf : SVal.isDefault.isDefaultFields s fs = true)
    (hg : SVal.isDefault.isDefaultFields s gs = true) : fs = gs := by
  match fs, gs with
  | [], [] => rfl
  | [], _ :: _ => simp at hnames
  | _ :: _, [] => simp at hnames
  | (n, v) :: fr, (m, w) :: gr =>
      simp only [List.map_cons, List.cons.injEq] at hnames
      obtain ⟨hnm, hrest⟩ := hnames
      subst hnm
      simp only [SVal.isDefault.isDefaultFields, Bool.and_eq_true] at hf hg
      rw [SVal.isDefaultFields_unique hrest hf.2 hg.2]
      cases hdef : lookupBy n (structDef s) with
      | none => rw [hdef] at hf; exact Bool.noConfusion hf.1
      | some tyf =>
          rw [hdef] at hf hg
          rw [SVal.isDefault_unique hf.1 hg.1]

end

/-! ## Total read/write twins of `find`/`save`

`fill_exec` needs the *exact* state a write produces. `get` is `find`
without the `length` arm and *strict* on mapping keys (an absent key is
`none`, not the default), as an `Option`; `put` is `save` made total
(the identity on its stuck/revert arms). On a path `get` succeeds on —
a fully materialised path — `find` and `save` are `get` and `put`; the
one absent-key step `writeProg` takes (`delete` to materialise a mapping
entry) goes through the `_append_of_get` lemmas instead. -/

def SVal.get : SVal -> List Seg -> Option SVal
  | v, [] => some v
  | SVal.struct fields, Seg.field name :: rest =>
      match lookupBy name fields with
      | some v => v.get rest
      | none => none
  | SVal.array elems _, Seg.at i :: rest =>
      if h : 0 ≤ i ∧ i.toNat < elems.length then
        (elems.get ⟨i.toNat, h.2⟩).get rest
      else none
  | SVal.map entries _, Seg.at i :: rest =>
      match lookupBy i entries with
      | some v => v.get rest
      | none => none
  | _, _ => none

def SVal.put : SVal -> List Seg -> SVal -> SVal
  | _, [], new => new
  | SVal.struct fields, Seg.field name :: rest, new =>
      match lookupBy name fields with
      | some old => SVal.struct (setBy name (old.put rest new) fields)
      | none => SVal.struct fields
  | SVal.array elems shadow, Seg.at i :: rest, new =>
      if h : 0 ≤ i ∧ i.toNat < elems.length then
        SVal.array (elems.set i.toNat ((elems.get ⟨i.toNat, h.2⟩).put rest new)) shadow
      else SVal.array elems shadow
  | SVal.map entries dflt, Seg.at i :: rest, new =>
      match lookupBy i entries with
      | some old => SVal.map (setBy i (old.put rest new) entries) dflt
      | none => SVal.map (setBy i (dflt.put rest new) entries) dflt
  | v, _ :: _, _ => v

theorem setBy_setBy_same [DecidableEq κ] (k : κ) (a b : α) :
    ∀ (l : List (κ × α)), setBy k b (setBy k a l) = setBy k b l
  | [] => by simp [setBy]
  | (k', v) :: rest => by
      by_cases h : k = k'
      · subst h; simp [setBy]
      · simp [setBy, h, setBy_setBy_same k a b rest]

theorem SVal.find_of_get : ∀ {p : List Seg} {v x : SVal},
    v.get p = some x -> v.find p = Except.ok x
  | [], v, x, h => by
      simp only [SVal.get, Option.some.injEq] at h
      subst h
      simp [SVal.find]
  | Seg.field n :: rest, v, x, h => by
      cases v with
      | struct fs =>
          simp only [SVal.get] at h
          cases hl : lookupBy n fs with
          | none => rw [hl] at h; exact Option.noConfusion h
          | some c =>
              rw [hl] at h
              simp only [SVal.find, hl]
              exact SVal.find_of_get h
      | _ => simp [SVal.get] at h
  | Seg.at i :: rest, v, x, h => by
      cases v with
      | array es =>
          simp only [SVal.get] at h
          split at h
          · rename_i hb
            simp only [SVal.find, dif_pos hb]
            exact SVal.find_of_get h
          · exact Option.noConfusion h
      | map es d =>
          simp only [SVal.get] at h
          cases hl : lookupBy i es with
          | none => rw [hl] at h; exact Option.noConfusion h
          | some c =>
              rw [hl] at h
              simp only [SVal.find, hl]
              exact SVal.find_of_get h
      | _ => simp [SVal.get] at h

theorem SVal.save_of_get : ∀ {p : List Seg} {v x new : SVal},
    v.get p = some x -> v.save p new = Except.ok (v.put p new)
  | [], v, x, new, _ => by simp [SVal.save, SVal.put]
  | Seg.field n :: rest, v, x, new, h => by
      cases v with
      | struct fs =>
          simp only [SVal.get] at h
          cases hl : lookupBy n fs with
          | none => rw [hl] at h; exact Option.noConfusion h
          | some c =>
              rw [hl] at h
              simp only [SVal.save, SVal.put, hl, SVal.save_of_get h, bind,
                Except.bind]
      | _ => simp [SVal.get] at h
  | Seg.at i :: rest, v, x, new, h => by
      cases v with
      | array es =>
          simp only [SVal.get] at h
          split at h
          · rename_i hb
            simp only [SVal.save, SVal.put, dif_pos hb, SVal.save_of_get h,
              bind, Except.bind]
          · exact Option.noConfusion h
      | map es d =>
          simp only [SVal.get] at h
          cases hl : lookupBy i es with
          | none => rw [hl] at h; exact Option.noConfusion h
          | some c =>
              rw [hl] at h
              simp only [SVal.save, SVal.put, hl, SVal.save_of_get h, bind,
                Except.bind]
      | _ => simp [SVal.get] at h

theorem SVal.get_put_self : ∀ {p : List Seg} {v x new : SVal},
    v.get p = some x -> (v.put p new).get p = some new
  | [], v, x, new, _ => by simp [SVal.put, SVal.get]
  | Seg.field n :: rest, v, x, new, h => by
      cases v with
      | struct fs =>
          simp only [SVal.get] at h
          cases hl : lookupBy n fs with
          | none => rw [hl] at h; exact Option.noConfusion h
          | some c =>
              rw [hl] at h
              simp only [SVal.put, SVal.get, hl, lookupBy_setBy_self]
              exact SVal.get_put_self h
      | _ => simp [SVal.get] at h
  | Seg.at i :: rest, v, x, new, h => by
      cases v with
      | array es =>
          simp only [SVal.get] at h
          split at h
          · rename_i hb
            have hb' : 0 ≤ i ∧ i.toNat <
                (es.set i.toNat ((es[i.toNat]'hb.2).put rest new)).length := by
              simpa [List.length_set] using hb
            simp only [SVal.put, SVal.get, dif_pos hb, List.get_eq_getElem]
            rw [dif_pos hb']
            simp only [List.getElem_set_self]
            exact SVal.get_put_self h
          · exact Option.noConfusion h
      | map es d =>
          simp only [SVal.get] at h
          cases hl : lookupBy i es with
          | none => rw [hl] at h; exact Option.noConfusion h
          | some c =>
              rw [hl] at h
              simp only [SVal.put, SVal.get, hl, lookupBy_setBy_self]
              exact SVal.get_put_self h
      | _ => simp [SVal.get] at h

theorem SVal.put_put_same : ∀ {p : List Seg} {v x a b : SVal},
    v.get p = some x -> (v.put p a).put p b = v.put p b
  | [], v, x, a, b, _ => by simp [SVal.put]
  | Seg.field n :: rest, v, x, a, b, h => by
      cases v with
      | struct fs =>
          simp only [SVal.get] at h
          cases hl : lookupBy n fs with
          | none => rw [hl] at h; exact Option.noConfusion h
          | some c =>
              rw [hl] at h
              simp only [SVal.put, hl, lookupBy_setBy_self, setBy_setBy_same,
                SVal.put_put_same h]
      | _ => simp [SVal.get] at h
  | Seg.at i :: rest, v, x, a, b, h => by
      cases v with
      | array es =>
          simp only [SVal.get] at h
          split at h
          · rename_i hb
            have hb' : 0 ≤ i ∧ i.toNat <
                (es.set i.toNat ((es[i.toNat]'hb.2).put rest a)).length := by
              simpa [List.length_set] using hb
            simp only [SVal.put, dif_pos hb, List.get_eq_getElem]
            rw [dif_pos hb']
            simp only [List.getElem_set_self, List.set_set]
            have h' : (es[i.toNat]'hb.2).get rest = some x := h
            rw [SVal.put_put_same h']
          · exact Option.noConfusion h
      | map es d =>
          simp only [SVal.get] at h
          cases hl : lookupBy i es with
          | none => rw [hl] at h; exact Option.noConfusion h
          | some c =>
              rw [hl] at h
              simp only [SVal.put, hl, lookupBy_setBy_self, setBy_setBy_same,
                SVal.put_put_same h]
      | _ => simp [SVal.get] at h

theorem SVal.get_snoc : ∀ {p : List Seg} (v : SVal) (seg : Seg),
    v.get (p ++ [seg]) = (v.get p).bind fun c => c.get [seg]
  | [], v, seg => by simp [SVal.get]
  | Seg.field n :: rest, v, seg => by
      cases v with
      | struct fs =>
          simp only [List.cons_append, SVal.get]
          cases lookupBy n fs with
          | none => rfl
          | some c => exact SVal.get_snoc c seg
      | _ => simp [SVal.get]
  | Seg.at i :: rest, v, seg => by
      cases v with
      | array es =>
          simp only [List.cons_append, SVal.get]
          split
          · exact SVal.get_snoc _ seg
          · rfl
      | map es d =>
          simp only [List.cons_append, SVal.get]
          cases lookupBy i es with
          | none => rfl
          | some c => exact SVal.get_snoc c seg
      | _ => simp [SVal.get]

theorem SVal.put_snoc : ∀ {p : List Seg} {v c : SVal} (seg : Seg) (x : SVal),
    v.get p = some c -> v.put (p ++ [seg]) x = v.put p (c.put [seg] x)
  | [], v, c, seg, x, h => by
      simp only [SVal.get, Option.some.injEq] at h
      subst h
      simp [SVal.put]
  | Seg.field n :: rest, v, c, seg, x, h => by
      cases v with
      | struct fs =>
          simp only [SVal.get] at h
          cases hl : lookupBy n fs with
          | none => rw [hl] at h; exact Option.noConfusion h
          | some old =>
              rw [hl] at h
              simp only [List.cons_append, SVal.put, hl, SVal.put_snoc seg x h]
      | _ => simp [SVal.get] at h
  | Seg.at i :: rest, v, c, seg, x, h => by
      cases v with
      | array es =>
          simp only [SVal.get] at h
          split at h
          · rename_i hb
            simp only [List.cons_append, SVal.put, dif_pos hb,
              SVal.put_snoc seg x h]
          · exact Option.noConfusion h
      | map es d =>
          simp only [SVal.get] at h
          cases hl : lookupBy i es with
          | none => rw [hl] at h; exact Option.noConfusion h
          | some old =>
              rw [hl] at h
              simp only [List.cons_append, SVal.put, hl, SVal.put_snoc seg x h]
      | _ => simp [SVal.get] at h

/-! ### One-segment computation rules -/

theorem SVal.get_field (fs : List (Name × SVal)) (n : Name) :
    (SVal.struct fs).get [Seg.field n] = lookupBy n fs := by
  simp only [SVal.get]
  cases lookupBy n fs <;> rfl

theorem SVal.put_field {fs : List (Name × SVal)} {n : Name} {old : SVal}
    (hl : lookupBy n fs = some old) (x : SVal) :
    (SVal.struct fs).put [Seg.field n] x = SVal.struct (setBy n x fs) := by
  simp [SVal.put, hl]

theorem SVal.get_at_array_last (es sh : List SVal) (d : SVal) :
    (SVal.array (es ++ [d]) sh).get [Seg.at (es.length : Int)] = some d := by
  have hb : 0 ≤ (es.length : Int) ∧
      (es.length : Int).toNat < (es ++ [d]).length := by
    simp
  simp only [SVal.get, List.get_eq_getElem, Int.toNat_natCast]
  simp

theorem SVal.put_at_array_last (es sh : List SVal) (d x : SVal) :
    (SVal.array (es ++ [d]) sh).put [Seg.at (es.length : Int)] x =
      SVal.array (es ++ [x]) sh := by
  have hb : 0 ≤ (es.length : Int) ∧
      (es.length : Int).toNat < (es ++ [d]).length := by
    simp
  simp only [SVal.put, Int.toNat_natCast]
  simp [List.set_append_right]

theorem SVal.get_at_map (es : List (Int × SVal)) (d : SVal) (i : Int) :
    (SVal.map es d).get [Seg.at i] = lookupBy i es := by
  simp only [SVal.get]
  cases lookupBy i es <;> rfl

theorem SVal.put_at_map (es : List (Int × SVal)) (d : SVal) (i : Int)
    (x : SVal) :
    (SVal.map es d).put [Seg.at i] x = SVal.map (setBy i x es) d := by
  simp only [SVal.put]
  cases lookupBy i es <;> rfl

/-! ### State level -/

theorem State.findStorage_of_get {s : State} {r : Name} {p : List Seg}
    {v0 x : SVal} (hroot : lookupBy r s.storage = some v0)
    (hget : v0.get p = some x) : s.findStorage r p = Except.ok x := by
  simp only [State.findStorage, hroot]
  exact SVal.find_of_get hget

theorem State.saveStorage_of_get {s : State} {r : Name} {p : List Seg}
    {v0 x : SVal} (hroot : lookupBy r s.storage = some v0)
    (hget : v0.get p = some x) (new : SVal) :
    s.saveStorage r p new =
      Except.ok { s with storage := setBy r (v0.put p new) s.storage } := by
  simp only [State.saveStorage, hroot, SVal.save_of_get hget, bind, Except.bind]

/-! ## Literal storage places

The place shapes `writeProg` emits: a global root, field selections,
and *literal* indices (`intLit Ty.uint k`). Everything the checker and
the interpreter need about them follows by induction on the derivation. -/

inductive LitPlace (L : Layout) : WrappedExpr -> Name -> List Seg -> Ty -> Prop
  | root (r : Name) (ty : Ty) (h : lookupBy r L.globals = some ty) :
      LitPlace L (WrappedExpr.var Kind.storage ty
        { name := r, ty := ty, origin := some StorageOrigin.global }) r [] ty
  | field {base : WrappedExpr} {r : Name} {p : List Seg} {bty : Ty}
      (n : Name) (fty : Ty) (hb : LitPlace L base r p bty)
      (hseg : segTy bty (Seg.field n) = some fty) :
      LitPlace L (WrappedExpr.field Kind.storage fty base
        { name := n, ty := fty, origin := none }) r (p ++ [Seg.field n]) fty
  | index {base : WrappedExpr} {r : Name} {p : List Seg} {bty : Ty}
      (k : Int) (ety : Ty) (hb : LitPlace L base r p bty)
      (hel : elemTy bty = some ety) :
      LitPlace L (WrappedExpr.index Kind.storage ety base
        (WrappedExpr.intLit Ty.uint k)) r (p ++ [Seg.at k]) ety

namespace LitPlace

variable {L : Layout} {e : WrappedExpr} {r : Name} {p : List Seg} {t : Ty}

theorem ty (h : LitPlace L e r p t) : e.ty = t := by
  cases h <;> rfl

theorem kind (h : LitPlace L e r p t) : e.kind = Kind.storage := by
  cases h <;> rfl

theorem wt (h : LitPlace L e r p t) : wtExpr [] L e = true := by
  induction h with
  | root r ty hl => simp [Semantics.wtExpr, lookupBy, hl]
  | field n fty hb hseg ih => simp [Semantics.wtExpr, ih, hb.ty, hseg]
  | index k ety hb hel ih =>
      simp [Semantics.wtExpr, ih, hb.ty, hel, isNumericTy, PrimTy.isNumeric]

theorem resolveS_eq (h : LitPlace L e r p t) (s : State) (hs : s.env = []) :
    resolveS s e = Except.ok (s, r, p) := by
  induction h with
  | root r ty hl => simp [resolveS, hs, lookupBy]
  | field n fty hb hseg ih => simp [resolveS, ih, bind, Except.bind]
  | index k ety hb hel ih =>
      simp [resolveS, ih, bind, Except.bind, evalInt, evalValue, Value.asInt]

theorem resolveLoc_eq (h : LitPlace L e r p t) (s : State) (hs : s.env = []) :
    resolveLoc s e = Except.ok (s, Loc.storage r p) := by
  have hres := h.resolveS_eq s hs
  cases h with
  | root => simp [resolveLoc]
  | field =>
      simp only [resolveLoc]
      rw [resolveS_field_ty_irrel s Kind.storage Ty.uint t]
      simp [hres, bind, Except.bind]
  | index _ _ hb =>
      simp [resolveLoc, hb.resolveS_eq s hs, bind, Except.bind, evalInt,
        evalValue, Value.asInt]

end LitPlace

/-! ## Single-statement lemmas on literal places -/

section Stmts

variable {L : Layout} {pl : PlaceExpr} {r : Name} {p : List Seg} {s : State}
  {v0 x : SVal}

theorem exec_assign_int {ty : Ty} (h : LitPlace L pl.expr r p ty)
    (hnum : isNumericTy ty = true) (hs : s.env = [])
    (hroot : lookupBy r s.storage = some v0) (hget : v0.get p = some x)
    (z : Int) :
    execStmt s (Stmt.assign pl (WrappedExpr.intLit ty z)) =
      Except.ok { s with storage := setBy r (v0.put p (SVal.int z)) s.storage } := by
  have hprim : ty.isPrimitive = true := by
    cases ty with
    | prim pt => rfl
    | ref _ => simp [isNumericTy] at hnum
  have hrty : (WrappedExpr.intLit ty z).ty = ty := rfl
  have hloc := h.resolveLoc_eq s hs
  have hk := h.kind
  obtain ⟨e, hass⟩ := pl
  rw [execStmt.eq_def]
  dsimp only
  cases h with
  | root =>
      simp [execAssign, rhsToSVal, hrty, hprim, evalValue, Value.toSVal, bind,
        Except.bind, State.saveStorage_of_get hroot hget, SVal.put]
  | field =>
      simp [execAssign, execAssignNested, hk, rhsToSVal, hrty, hprim,
        evalValue, Value.toSVal, bind, Except.bind, hloc,
        State.saveStorage_of_get hroot hget]
  | index =>
      simp [execAssign, execAssignNested, hk, rhsToSVal, hrty, hprim,
        evalValue, Value.toSVal, bind, Except.bind, hloc,
        State.saveStorage_of_get hroot hget]

theorem exec_assign_bool (h : LitPlace L pl.expr r p Ty.bool) (hs : s.env = [])
    (hroot : lookupBy r s.storage = some v0) (hget : v0.get p = some x)
    (b : Bool) :
    execStmt s (Stmt.assign pl (WrappedExpr.bool b)) =
      Except.ok { s with storage := setBy r (v0.put p (SVal.bool b)) s.storage } := by
  have hrty : (WrappedExpr.bool b).ty = Ty.bool := rfl
  have hloc := h.resolveLoc_eq s hs
  have hk := h.kind
  obtain ⟨e, hass⟩ := pl
  rw [execStmt.eq_def]
  dsimp only
  cases h with
  | root =>
      simp [execAssign, rhsToSVal, hrty, Ty.isPrimitive, evalValue,
        Value.toSVal, bind, Except.bind, State.saveStorage_of_get hroot hget,
        SVal.put]
  | field =>
      simp [execAssign, execAssignNested, hk, rhsToSVal, hrty, Ty.isPrimitive,
        evalValue, Value.toSVal, bind, Except.bind, hloc,
        State.saveStorage_of_get hroot hget]
  | index =>
      simp [execAssign, execAssignNested, hk, rhsToSVal, hrty, Ty.isPrimitive,
        evalValue, Value.toSVal, bind, Except.bind, hloc,
        State.saveStorage_of_get hroot hget]

theorem exec_delete {ty : Ty} (h : LitPlace L pl.expr r p ty) (hs : s.env = [])
    (hroot : lookupBy r s.storage = some v0) (hget : v0.get p = some x) :
    execStmt s (Stmt.delete pl) =
      Except.ok { s with storage := setBy r (v0.put p x.defaultOf) s.storage } := by
  rw [execStmt.eq_def]
  dsimp only
  simp only [h.kind]
  simp [h.resolveS_eq s hs, State.findStorage_of_get hroot hget,
    State.saveStorage_of_get hroot hget, bind, Except.bind]

theorem exec_push_none {ety : Ty}
    (h : LitPlace L pl.expr r p (Ty.ref (RefTy.array ety))) (hs : s.env = [])
    (hroot : lookupBy r s.storage = some v0) {es sh : List SVal}
    (hget : v0.get p = some (SVal.array es sh)) :
    execStmt s (Stmt.push pl none) =
      Except.ok { s with storage := setBy r (v0.put p
        (SVal.array (es ++ [(pushSlot ety sh).1]) (pushSlot ety sh).2)) s.storage } := by
  rw [execStmt.eq_def]
  dsimp only
  simp [h.resolveS_eq s hs, State.findStorage_of_get hroot hget, h.ty,
    State.saveStorage_of_get hroot hget, bind, Except.bind, pure, Except.pure]

theorem stmtWt_assign_int {ty : Ty} (h : LitPlace L pl.expr r p ty)
    (hnum : isNumericTy ty = true) (n : Int) :
    stmtWt [] L (Stmt.assign pl (WrappedExpr.intLit ty n)) = some [] := by
  have hrty : (WrappedExpr.intLit ty n).ty = ty := rfl
  simp only [stmtWt]
  simp [h.wt, h.ty, hrty, wtExpr, hnum]

theorem stmtWt_assign_bool (h : LitPlace L pl.expr r p Ty.bool) (b : Bool) :
    stmtWt [] L (Stmt.assign pl (WrappedExpr.bool b)) = some [] := by
  have hrty : (WrappedExpr.bool b).ty = Ty.bool := rfl
  simp only [stmtWt]
  simp [h.wt, h.ty, hrty, wtExpr]

theorem stmtWt_delete {ty : Ty} (h : LitPlace L pl.expr r p ty) :
    stmtWt [] L (Stmt.delete pl) = some [] := by
  simp only [stmtWt]
  simp [h.wt, h.kind]

theorem stmtWt_push_none {ety : Ty}
    (h : LitPlace L pl.expr r p (Ty.ref (RefTy.array ety)))
    (hok : defaultOk ety = true) :
    stmtWt [] L (Stmt.push pl none) = some [] := by
  simp only [stmtWt]
  simp [h.wt, h.ty, hok]

end Stmts

/-! ## Association-list facts for the loop invariants -/

theorem lookupBy_append_of_none [DecidableEq κ] {k : κ} :
    ∀ {l₁ : List (κ × α)} (l₂ : List (κ × α)), lookupBy k l₁ = none ->
      lookupBy k (l₁ ++ l₂) = lookupBy k l₂
  | [], _, _ => rfl
  | (k', v) :: rest, l₂, h => by
      simp only [lookupBy] at h
      by_cases hk : k = k'
      · rw [if_pos hk] at h; exact Option.noConfusion h
      · rw [if_neg hk] at h
        simp only [List.cons_append, lookupBy, if_neg hk]
        exact lookupBy_append_of_none l₂ h

theorem setBy_append_of_none [DecidableEq κ] {k : κ} (v : α) :
    ∀ {l₁ : List (κ × α)} (l₂ : List (κ × α)), lookupBy k l₁ = none ->
      setBy k v (l₁ ++ l₂) = l₁ ++ setBy k v l₂
  | [], _, _ => rfl
  | (k', v') :: rest, l₂, h => by
      simp only [lookupBy] at h
      by_cases hk : k = k'
      · rw [if_pos hk] at h; exact Option.noConfusion h
      · rw [if_neg hk] at h
        simp only [List.cons_append, setBy, if_neg hk]
        rw [setBy_append_of_none v l₂ h]

theorem lookupBy_append_cons_self [DecidableEq κ] {k : κ} {l₁ : List (κ × α)}
    (h : lookupBy k l₁ = none) (v : α) (l₂ : List (κ × α)) :
    lookupBy k (l₁ ++ (k, v) :: l₂) = some v := by
  rw [lookupBy_append_of_none _ h]
  simp [lookupBy]

theorem setBy_append_cons [DecidableEq κ] {k : κ} {l₁ : List (κ × α)}
    (h : lookupBy k l₁ = none) (v v' : α) (l₂ : List (κ × α)) :
    setBy k v' (l₁ ++ (k, v) :: l₂) = l₁ ++ (k, v') :: l₂ := by
  rw [setBy_append_of_none _ _ h]
  simp [setBy]

theorem setBy_lookup_self [DecidableEq κ] {k : κ} {v : α} :
    ∀ {l : List (κ × α)}, lookupBy k l = some v -> setBy k v l = l
  | [], h => Option.noConfusion h
  | (k', v') :: rest, h => by
      simp only [lookupBy] at h
      by_cases hk : k = k'
      · rw [if_pos hk] at h
        cases Option.some.inj h
        subst hk
        simp [setBy]
      · rw [if_neg hk] at h
        simp only [setBy, if_neg hk]
        rw [setBy_lookup_self h]

theorem nodupKeysB_append_cons [DecidableEq κ] {k : κ} {v : α}
    {l₂ : List (κ × α)} :
    ∀ {l₁ : List (κ × α)}, nodupKeysB (l₁ ++ (k, v) :: l₂) = true ->
      lookupBy k l₁ = none
  | [], _ => rfl
  | (k', v') :: rest, h => by
      simp only [List.cons_append, nodupKeysB, Bool.and_eq_true] at h
      have ih := nodupKeysB_append_cons h.2
      by_cases hk : k = k'
      · subst hk
        rw [lookupBy_append_of_none _ ih] at h
        simp [lookupBy] at h
      · simp only [lookupBy, if_neg hk]
        exact ih

theorem lookupBy_isNone_of_map_fst_eq [DecidableEq κ] {k : κ} :
    ∀ {l : List (κ × α)} {l' : List (κ × β)},
      l.map Prod.fst = l'.map Prod.fst ->
      (lookupBy k l).isNone = (lookupBy k l').isNone
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | (k₁, _) :: r₁, (k₂, _) :: r₂, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨hk, hrest⟩ := h
      subst hk
      by_cases hkk : k = k₁
      · simp [lookupBy, hkk]
      · simp only [lookupBy, if_neg hkk]
        exact lookupBy_isNone_of_map_fst_eq hrest

theorem nodupKeysB_of_map_fst_eq [DecidableEq κ] :
    ∀ {l : List (κ × α)} {l' : List (κ × β)},
      l.map Prod.fst = l'.map Prod.fst -> nodupKeysB l' = true ->
      nodupKeysB l = true
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | (k₁, _) :: r₁, (k₂, _) :: r₂, h, hnd => by
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨hk, hrest⟩ := h
      subst hk
      simp only [nodupKeysB, Bool.and_eq_true] at hnd ⊢
      exact ⟨by rw [lookupBy_isNone_of_map_fst_eq hrest]; exact hnd.1,
        nodupKeysB_of_map_fst_eq hrest hnd.2⟩

theorem SVal.put_get_self : ∀ {p : List Seg} {v c : SVal},
    v.get p = some c -> v.put p c = v
  | [], v, c, h => by
      simp only [SVal.get, Option.some.injEq] at h
      subst h
      simp [SVal.put]
  | Seg.field n :: rest, v, c, h => by
      cases v with
      | struct fs =>
          simp only [SVal.get] at h
          cases hl : lookupBy n fs with
          | none => rw [hl] at h; exact Option.noConfusion h
          | some old =>
              rw [hl] at h
              simp only [SVal.put, hl, SVal.put_get_self h, setBy_lookup_self hl]
      | _ => simp [SVal.get] at h
  | Seg.at i :: rest, v, c, h => by
      cases v with
      | array es =>
          simp only [SVal.get] at h
          split at h
          · rename_i hb
            have h' : (es[i.toNat]'hb.2).get rest = some c := h
            simp only [SVal.put, dif_pos hb, List.get_eq_getElem]
            rw [SVal.put_get_self h', List.set_getElem_self]
          · exact Option.noConfusion h
      | map es d =>
          simp only [SVal.get] at h
          cases hl : lookupBy i es with
          | none => rw [hl] at h; exact Option.noConfusion h
          | some old =>
              rw [hl] at h
              simp only [SVal.put, hl, SVal.put_get_self h, setBy_lookup_self hl]
      | _ => simp [SVal.get] at h

/-! ### Reads and writes below a materialised prefix -/

theorem SVal.find_append_of_get : ∀ {p : List Seg} {v c : SVal} (q : List Seg),
    v.get p = some c -> v.find (p ++ q) = c.find q
  | [], v, c, q, h => by
      simp only [SVal.get, Option.some.injEq] at h
      subst h
      rfl
  | Seg.field n :: rest, v, c, q, h => by
      cases v with
      | struct fs =>
          simp only [SVal.get] at h
          cases hl : lookupBy n fs with
          | none => rw [hl] at h; exact Option.noConfusion h
          | some old =>
              rw [hl] at h
              simp only [List.cons_append, SVal.find, hl]
              exact SVal.find_append_of_get q h
      | _ => simp [SVal.get] at h
  | Seg.at i :: rest, v, c, q, h => by
      cases v with
      | array es =>
          simp only [SVal.get] at h
          split at h
          · rename_i hb
            simp only [List.cons_append, SVal.find, dif_pos hb]
            exact SVal.find_append_of_get q h
          · exact Option.noConfusion h
      | map es d =>
          simp only [SVal.get] at h
          cases hl : lookupBy i es with
          | none => rw [hl] at h; exact Option.noConfusion h
          | some old =>
              rw [hl] at h
              simp only [List.cons_append, SVal.find, hl]
              exact SVal.find_append_of_get q h
      | _ => simp [SVal.get] at h

theorem SVal.save_append_of_get : ∀ {p : List Seg} {v c : SVal} {q : List Seg}
    {x c' : SVal}, v.get p = some c -> c.save q x = Except.ok c' ->
    v.save (p ++ q) x = Except.ok (v.put p c')
  | [], v, c, q, x, c', h, hsave => by
      simp only [SVal.get, Option.some.injEq] at h
      subst h
      simpa [SVal.put] using hsave
  | Seg.field n :: rest, v, c, q, x, c', h, hsave => by
      cases v with
      | struct fs =>
          simp only [SVal.get] at h
          cases hl : lookupBy n fs with
          | none => rw [hl] at h; exact Option.noConfusion h
          | some old =>
              rw [hl] at h
              simp only [List.cons_append, SVal.save, SVal.put, hl,
                SVal.save_append_of_get h hsave, bind, Except.bind]
      | _ => simp [SVal.get] at h
  | Seg.at i :: rest, v, c, q, x, c', h, hsave => by
      cases v with
      | array es =>
          simp only [SVal.get] at h
          split at h
          · rename_i hb
            simp only [List.cons_append, SVal.save, SVal.put, dif_pos hb,
              SVal.save_append_of_get h hsave, bind, Except.bind]
          · exact Option.noConfusion h
      | map es d =>
          simp only [SVal.get] at h
          cases hl : lookupBy i es with
          | none => rw [hl] at h; exact Option.noConfusion h
          | some old =>
              rw [hl] at h
              simp only [List.cons_append, SVal.save, SVal.put, hl,
                SVal.save_append_of_get h hsave, bind, Except.bind]
      | _ => simp [SVal.get] at h

theorem State.findStorage_append_of_get {s : State} {r : Name} {p : List Seg}
    {v0 c : SVal} (hroot : lookupBy r s.storage = some v0)
    (hget : v0.get p = some c) (q : List Seg) :
    s.findStorage r (p ++ q) = c.find q := by
  simp only [State.findStorage, hroot]
  exact SVal.find_append_of_get q hget

theorem State.saveStorage_append_of_get {s : State} {r : Name} {p : List Seg}
    {v0 c : SVal} {q : List Seg} {x c' : SVal}
    (hroot : lookupBy r s.storage = some v0) (hget : v0.get p = some c)
    (hsave : c.save q x = Except.ok c') :
    s.saveStorage r (p ++ q) x =
      Except.ok { s with storage := setBy r (v0.put p c') s.storage } := by
  simp only [State.saveStorage, hroot, SVal.save_append_of_get hget hsave, bind,
    Except.bind]

/-- `delete m[k];` on an *absent* key reads the mapping's default through
the key and writes its `defaultOf` back — materialising the entry. -/
theorem exec_delete_absent {L : Layout} {pl : PlaceExpr} {r : Name}
    {p : List Seg} {s : State} {v0 : SVal} {vty : Ty}
    {es : List (Int × SVal)} {d : SVal} {k : Int}
    (h : LitPlace L pl.expr r (p ++ [Seg.at k]) vty) (hs : s.env = [])
    (hroot : lookupBy r s.storage = some v0)
    (hget : v0.get p = some (SVal.map es d)) (habs : lookupBy k es = none) :
    execStmt s (Stmt.delete pl) =
      Except.ok { s with storage := setBy r (v0.put p (SVal.map (setBy k d.defaultOf es) d)) s.storage } := by
  have hfind : (SVal.map es d).find [Seg.at k] = Except.ok d := by
    simp [SVal.find, habs]
  have hsave : (SVal.map es d).save [Seg.at k] d.defaultOf =
      Except.ok (SVal.map (setBy k d.defaultOf es) d) := by
    simp [SVal.save, habs, bind, Except.bind]
  rw [execStmt.eq_def]
  dsimp only
  simp only [h.kind]
  simp [h.resolveS_eq s hs, State.findStorage_append_of_get hroot hget, hfind,
    State.saveStorage_append_of_get hroot hget hsave, bind, Except.bind]

/-! ## The writing program -/

theorem execBlock_cons (s : State) (a : Stmt) (b : List Stmt) :
    execBlock s (a :: b) = (execStmt s a >>= fun t => execBlock t b) := rfl

theorem execBlock_nil (s : State) : execBlock s [] = Except.ok s := rfl

theorem blockWt_cons {Γ Γ' : Ctx} {L : Layout} {a : Stmt} (b : List Stmt)
    (h : stmtWt Γ L a = some Γ') : blockWt Γ L (a :: b) = blockWt Γ' L b := by
  rw [blockWt, h]

mutual

/-- Statements that turn the default at `pl : ty` into `v`: literal
assignments at the leaves; `push()`-then-fill per array element;
`delete`-then-fill per mapping entry; recursion into every struct
field (all present from the default). -/
def fill (pl : PlaceExpr) (ty : Ty) : SVal -> List Stmt
  | SVal.prim (PrimVal.int z) => [Stmt.assign pl (WrappedExpr.intLit ty z)]
  | SVal.prim (PrimVal.bool b) => [Stmt.assign pl (WrappedExpr.bool b)]
  | SVal.struct fields =>
      match ty with
      | Ty.ref (RefTy.struct sname) => fillFields pl sname fields
      | _ => []
  | SVal.array elems _ =>
      match ty with
      | Ty.ref (RefTy.array ety) => fillElems pl ety 0 elems
      | _ => []
  | SVal.map entries _ =>
      match ty with
      | Ty.ref (RefTy.mapping _ vty) => fillEntries pl vty entries
      | _ => []

def fillFields (pl : PlaceExpr) (sname : Name) : List (Name × SVal) -> List Stmt
  | [] => []
  | (n, v) :: rest =>
      (match lookupBy n (structDef sname) with
       | some fty =>
           fill (PlaceExpr.field Kind.storage fty pl.expr
             { name := n, ty := fty, origin := none }) fty v
       | none => []) ++ fillFields pl sname rest

def fillElems (pl : PlaceExpr) (ety : Ty) (i : Nat) : List SVal -> List Stmt
  | [] => []
  | v :: rest =>
      Stmt.push pl none ::
        (fill (PlaceExpr.index Kind.storage ety pl.expr
            (WrappedExpr.intLit Ty.uint (i : Int))) ety v ++
          fillElems pl ety (i + 1) rest)

def fillEntries (pl : PlaceExpr) (vty : Ty) : List (Int × SVal) -> List Stmt
  | [] => []
  | (k, v) :: rest =>
      Stmt.delete (PlaceExpr.index Kind.storage vty pl.expr
          (WrappedExpr.intLit Ty.uint k)) ::
        (fill (PlaceExpr.index Kind.storage vty pl.expr
            (WrappedExpr.intLit Ty.uint k)) vty v ++
          fillEntries pl vty rest)

end

/-- The whole program: fill every root. -/
def writeProg (L : Layout) (st : List (Name × SVal)) : List Stmt :=
  st.flatMap fun rv =>
    match lookupBy rv.1 L.globals with
    | some ty =>
        fill (PlaceExpr.var Kind.storage ty
          { name := rv.1, ty := ty, origin := some StorageOrigin.global }) ty rv.2
    | none => []

/-! ### The program is well-typed -/

theorem canonical_prim_int {ty : Ty} {z : Int}
    (h : (SVal.int z).canonical ty = true) : isNumericTy ty = true := by
  cases ty with
  | prim pt => cases pt <;> simp_all [SVal.canonical, isNumericTy, PrimTy.isNumeric]
  | ref r => simp [SVal.canonical] at h

theorem canonical_prim_bool {ty : Ty} {b : Bool}
    (h : (SVal.bool b).canonical ty = true) : ty = Ty.bool := by
  cases ty with
  | prim pt => cases pt <;> simp_all [SVal.canonical]
  | ref r => simp [SVal.canonical] at h

mutual

theorem fill_wt {L : Layout} : ∀ (v : SVal) (ty : Ty) (m : Nat), m ≤ 8 ->
    tyOkFuel m ty = true -> v.canonical ty = true ->
    ∀ (pl : PlaceExpr) (r : Name) (p : List Seg), LitPlace L pl.expr r p ty ->
      blockWt [] L (fill pl ty v) = some []
  | SVal.prim (PrimVal.int z), ty, m, hm, hok, hcan, pl, r, p, hpl => by
      simp only [fill]
      rw [blockWt_cons _ (stmtWt_assign_int hpl (canonical_prim_int hcan) z)]
      rfl
  | SVal.prim (PrimVal.bool b), ty, m, hm, hok, hcan, pl, r, p, hpl => by
      have := canonical_prim_bool hcan
      subst this
      simp only [fill]
      rw [blockWt_cons _ (stmtWt_assign_bool hpl b)]
      rfl
  | SVal.struct fields, ty, m, hm, hok, hcan, pl, r, p, hpl => by
      cases ty with
      | prim pt => simp [SVal.canonical] at hcan
      | ref rf =>
          cases rf with
          | struct sname =>
              cases m with
              | zero => exact Bool.noConfusion hok
              | succ m =>
                  simp only [tyOkFuel, Bool.and_eq_true] at hok
                  simp only [SVal.canonical, Bool.and_eq_true] at hcan
                  simp only [fill]
                  exact fillFields_wt fields (by omega) hok.2 hpl hcan.2
          | array elem => simp [SVal.canonical] at hcan
          | mapping key value => simp [SVal.canonical] at hcan
  | SVal.array elems shadow, ty, m, hm, hok, hcan, pl, r, p, hpl => by
      cases ty with
      | prim pt => simp [SVal.canonical] at hcan
      | ref rf =>
          cases rf with
          | struct sname => simp [SVal.canonical] at hcan
          | array ety =>
              cases m with
              | zero => exact Bool.noConfusion hok
              | succ m =>
                  simp only [tyOkFuel] at hok
                  simp only [SVal.canonical, Bool.and_eq_true] at hcan
                  simp only [fill]
                  exact fillElems_wt elems 0 (by omega) hok hpl hcan.1
          | mapping key value => simp [SVal.canonical] at hcan
  | SVal.map entries dflt, ty, m, hm, hok, hcan, pl, r, p, hpl => by
      cases ty with
      | prim pt => simp [SVal.canonical] at hcan
      | ref rf =>
          cases rf with
          | struct sname => simp [SVal.canonical] at hcan
          | array elem => simp [SVal.canonical] at hcan
          | mapping kty vty =>
              cases m with
              | zero => exact Bool.noConfusion hok
              | succ m =>
                  simp only [tyOkFuel] at hok
                  simp only [SVal.canonical, Bool.and_eq_true] at hcan
                  simp only [fill]
                  exact fillEntries_wt entries (by omega) hok hpl hcan.1.2

theorem fillFields_wt {L : Layout} {sname : Name} {pl : PlaceExpr} {r : Name}
    {p : List Seg} {m : Nat} :
    ∀ (todo : List (Name × SVal)), m ≤ 8 ->
      ((structDef sname).all fun fld => tyOkFuel m fld.2) = true ->
      LitPlace L pl.expr r p (Ty.ref (RefTy.struct sname)) ->
      SVal.canonical.canonicalFields sname todo = true ->
      blockWt [] L (fillFields pl sname todo) = some []
  | [], _, _, _, _ => rfl
  | (n, w) :: rest, hm, hok, hpl, hcan => by
      simp only [SVal.canonical.canonicalFields, Bool.and_eq_true] at hcan
      cases hdef : lookupBy n (structDef sname) with
      | none => rw [hdef] at hcan; exact Bool.noConfusion hcan.1
      | some fty =>
          rw [hdef] at hcan
          have hokf : tyOkFuel m fty = true :=
            List.all_eq_true.mp hok _ (lookupBy_eq_some_mem hdef)
          have hpl' := LitPlace.field (L := L) n fty hpl hdef
          simp only [fillFields, hdef, blockWt_append,
            fill_wt w fty m hm hokf hcan.1
              (PlaceExpr.field Kind.storage fty pl.expr
                { name := n, ty := fty, origin := none })
              r (p ++ [Seg.field n]) hpl', Option.bind_some]
          exact fillFields_wt rest hm hok hpl hcan.2

theorem fillElems_wt {L : Layout} {ety : Ty} {pl : PlaceExpr} {r : Name}
    {p : List Seg} {m : Nat} :
    ∀ (todo : List SVal) (i : Nat), m ≤ 8 -> tyOkFuel m ety = true ->
      LitPlace L pl.expr r p (Ty.ref (RefTy.array ety)) ->
      SVal.canonical.canonicalElems ety todo = true ->
      blockWt [] L (fillElems pl ety i todo) = some []
  | [], _, _, _, _, _ => rfl
  | w :: rest, i, hm, hok, hpl, hcan => by
      simp only [SVal.canonical.canonicalElems, Bool.and_eq_true] at hcan
      have hpl' := LitPlace.index (L := L) (i : Int) ety hpl rfl
      simp only [fillElems]
      rw [blockWt_cons _ (stmtWt_push_none hpl (tyOkFuel_defaultOk hok))]
      simp only [blockWt_append,
        fill_wt w ety m hm hok hcan.1
          (PlaceExpr.index Kind.storage ety pl.expr
            (WrappedExpr.intLit Ty.uint (i : Int)))
          r (p ++ [Seg.at (i : Int)]) hpl', Option.bind_some]
      exact fillElems_wt rest (i + 1) hm hok hpl hcan.2

theorem fillEntries_wt {L : Layout} {kty vty : Ty} {pl : PlaceExpr} {r : Name}
    {p : List Seg} {m : Nat} :
    ∀ (todo : List (Int × SVal)), m ≤ 8 -> tyOkFuel m vty = true ->
      LitPlace L pl.expr r p (Ty.ref (RefTy.mapping kty vty)) ->
      SVal.canonical.canonicalEntries vty todo = true ->
      blockWt [] L (fillEntries pl vty todo) = some []
  | [], _, _, _, _ => rfl
  | (k, w) :: rest, hm, hok, hpl, hcan => by
      simp only [SVal.canonical.canonicalEntries, Bool.and_eq_true] at hcan
      have hpl' := LitPlace.index (L := L) k vty hpl rfl
      simp only [fillEntries]
      rw [blockWt_cons _ (stmtWt_delete hpl')]
      simp only [blockWt_append,
        fill_wt w vty m hm hok hcan.1
          (PlaceExpr.index Kind.storage vty pl.expr
            (WrappedExpr.intLit Ty.uint k))
          r (p ++ [Seg.at k]) hpl', Option.bind_some]
      exact fillEntries_wt rest hm hok hpl hcan.2

end

/-! ### The program builds the value -/

mutual

theorem fill_exec {L : Layout} : ∀ (v : SVal) (ty : Ty) (m : Nat), m ≤ 8 ->
    tyOkFuel m ty = true -> v.canonical ty = true ->
    ∀ (pl : PlaceExpr) (r : Name) (p : List Seg) (s : State) (v0 cur : SVal),
      LitPlace L pl.expr r p ty -> s.env = [] ->
      lookupBy r s.storage = some v0 -> v0.get p = some cur ->
      cur.isDefault ty = true ->
      execBlock s (fill pl ty v) =
        Except.ok { s with storage := setBy r (v0.put p v) s.storage }
  | SVal.prim (PrimVal.int z), ty, m, hm, hok, hcan, pl, r, p, s, v0, cur, hpl,
      hs, hroot, hget, hcur => by
      simp only [fill, execBlock_cons, execBlock_nil,
        exec_assign_int hpl (canonical_prim_int hcan) hs hroot hget z, bind,
        Except.bind]
  | SVal.prim (PrimVal.bool b), ty, m, hm, hok, hcan, pl, r, p, s, v0, cur, hpl,
      hs, hroot, hget, hcur => by
      have := canonical_prim_bool hcan
      subst this
      simp only [fill, execBlock_cons, execBlock_nil,
        exec_assign_bool hpl hs hroot hget b, bind, Except.bind]
  | SVal.struct fields, ty, m, hm, hok, hcan, pl, r, p, s, v0, cur, hpl, hs,
      hroot, hget, hcur => by
      cases ty with
      | prim pt => simp [SVal.canonical] at hcan
      | ref rf =>
          cases rf with
          | struct sname =>
              cases m with
              | zero => exact Bool.noConfusion hok
              | succ m =>
                  simp only [tyOkFuel, Bool.and_eq_true] at hok
                  simp only [SVal.canonical, Bool.and_eq_true, beq_iff_eq] at hcan
                  cases cur with
                  | struct cf =>
                      simp only [SVal.isDefault, Bool.and_eq_true, beq_iff_eq]
                        at hcur
                      simp only [fill]
                      have hnames : cf.map Prod.fst = fields.map Prod.fst :=
                        hcur.1.trans hcan.1.symm
                      have hnd : nodupKeysB ([] ++ fields) = true :=
                        nodupKeysB_of_map_fst_eq hcan.1 hok.1
                      exact fillFields_exec fields (by omega) hok.2 hpl [] cf s v0
                        hs hroot hget hcan.2 hcur.2 hnames hnd
                  | _ => simp [SVal.isDefault] at hcur
          | array elem => simp [SVal.canonical] at hcan
          | mapping key value => simp [SVal.canonical] at hcan
  | SVal.array elems shadow, ty, m, hm, hok, hcan, pl, r, p, s, v0, cur, hpl, hs,
      hroot, hget, hcur => by
      cases ty with
      | prim pt => simp [SVal.canonical] at hcan
      | ref rf =>
          cases rf with
          | struct sname => simp [SVal.canonical] at hcan
          | array ety =>
              cases m with
              | zero => exact Bool.noConfusion hok
              | succ m =>
                  simp only [tyOkFuel] at hok
                  simp only [SVal.canonical] at hcan
                  cases cur with
                  | array ce csh =>
                      cases ce with
                      | cons x xs => simp [SVal.isDefault] at hcur
                      | nil =>
                          simp only [Bool.and_eq_true] at hcan
                          obtain ⟨hlive, hsh⟩ := hcan
                          rw [List.isEmpty_iff] at hsh
                          subst hsh
                          -- the target slot is the type's default, so it has
                          -- no recycled slots either
                          have hcsh : csh = [] := by
                            simp only [SVal.isDefault, List.isEmpty_nil,
                              Bool.true_and, List.isEmpty_iff] at hcur
                            exact hcur
                          subst hcsh
                          simp only [fill]
                          exact fillElems_exec elems (by omega) hok hpl [] s v0 hs
                            hroot hget hlive
                  | _ => simp [SVal.isDefault] at hcur
          | mapping key value => simp [SVal.canonical] at hcan
  | SVal.map entries d, ty, m, hm, hok, hcan, pl, r, p, s, v0, cur, hpl, hs,
      hroot, hget, hcur => by
      cases ty with
      | prim pt => simp [SVal.canonical] at hcan
      | ref rf =>
          cases rf with
          | struct sname => simp [SVal.canonical] at hcan
          | array elem => simp [SVal.canonical] at hcan
          | mapping kty vty =>
              cases m with
              | zero => exact Bool.noConfusion hok
              | succ m =>
                  simp only [tyOkFuel] at hok
                  simp only [SVal.canonical, Bool.and_eq_true] at hcan
                  cases cur with
                  | map ce dc =>
                      cases ce with
                      | cons x xs => simp [SVal.isDefault] at hcur
                      | nil =>
                          simp only [SVal.isDefault, List.isEmpty_nil,
                            Bool.true_and] at hcur
                          have hd : d = dc := SVal.isDefault_unique hcan.2 hcur
                          subst hd
                          simp only [fill]
                          exact fillEntries_exec entries (by omega) hok hpl [] d s
                            v0 hs hroot hget hcur hcan.1.2 hcan.1.1
                  | _ => simp [SVal.isDefault] at hcur
termination_by structural v => v

theorem fillFields_exec {L : Layout} {sname : Name} {pl : PlaceExpr} {r : Name}
    {p : List Seg} {m : Nat} :
    ∀ (todo : List (Name × SVal)), m ≤ 8 ->
      ((structDef sname).all fun fld => tyOkFuel m fld.2) = true ->
      LitPlace L pl.expr r p (Ty.ref (RefTy.struct sname)) ->
      ∀ (done cf : List (Name × SVal)) (s : State) (v0 : SVal),
        s.env = [] -> lookupBy r s.storage = some v0 ->
        v0.get p = some (SVal.struct (done ++ cf)) ->
        SVal.canonical.canonicalFields sname todo = true ->
        SVal.isDefault.isDefaultFields sname cf = true ->
        cf.map Prod.fst = todo.map Prod.fst ->
        nodupKeysB (done ++ todo) = true ->
        execBlock s (fillFields pl sname todo) =
          Except.ok { s with storage := setBy r (v0.put p (SVal.struct (done ++ todo))) s.storage }
  | [], hm, hok, hpl, done, cf, s, v0, hs, hroot, hget, hcan, hdef, hnames,
      hnd => by
      cases cf with
      | cons _ _ => simp at hnames
      | nil =>
          simp only [fillFields, execBlock_nil, List.append_nil] at hget ⊢
          rw [SVal.put_get_self hget, setBy_lookup_self hroot]
  | (n, w) :: rest, hm, hok, hpl, done, cf, s, v0, hs, hroot, hget, hcan, hdef,
      hnames, hnd => by
      cases cf with
      | nil => simp at hnames
      | cons hd cf' =>
          obtain ⟨n', d⟩ := hd
          simp only [List.map_cons, List.cons.injEq] at hnames
          obtain ⟨hn, hnames'⟩ := hnames
          subst hn
          simp only [SVal.canonical.canonicalFields, Bool.and_eq_true] at hcan
          simp only [SVal.isDefault.isDefaultFields, Bool.and_eq_true] at hdef
          cases hlook : lookupBy n' (structDef sname) with
          | none => rw [hlook] at hcan; exact Bool.noConfusion hcan.1
          | some fty =>
              rw [hlook] at hcan hdef
              have hnone : lookupBy n' done = none := nodupKeysB_append_cons hnd
              have hokf : tyOkFuel m fty = true :=
                List.all_eq_true.mp hok _ (lookupBy_eq_some_mem hlook)
              have hpl' := LitPlace.field (L := L) n' fty hpl hlook
              have hget' : v0.get (p ++ [Seg.field n']) = some d := by
                simp only [SVal.get_snoc, hget, Option.bind_some, SVal.get_field]
                exact lookupBy_append_cons_self hnone d cf'
              have h1 := fill_exec w fty m hm hokf hcan.1
                (PlaceExpr.field Kind.storage fty pl.expr
                  { name := n', ty := fty, origin := none })
                r (p ++ [Seg.field n']) s v0 d hpl' hs hroot hget' hdef.1
              simp only [SVal.put_snoc _ w hget,
                SVal.put_field (lookupBy_append_cons_self hnone d cf'),
                setBy_append_cons hnone d w cf'] at h1
              have hget₁ : (v0.put p (SVal.struct (done ++ (n', w) :: cf'))).get p =
                  some (SVal.struct ((done ++ [(n', w)]) ++ cf')) := by
                rw [SVal.get_put_self hget, ← List.append_cons]
              have h2 := fillFields_exec rest hm hok hpl (done ++ [(n', w)]) cf'
                { s with storage :=
                    setBy r (v0.put p (SVal.struct (done ++ (n', w) :: cf'))) s.storage }
                (v0.put p (SVal.struct (done ++ (n', w) :: cf')))
                hs (lookupBy_setBy_self _ _ _) hget₁ hcan.2 hdef.2 hnames'
                (by rwa [← List.append_cons])
              simp only [fillFields, hlook, execBlock_append, h1, bind, Except.bind,
                h2, setBy_setBy_same, SVal.put_put_same hget, ← List.append_cons]
termination_by structural todo => todo

theorem fillElems_exec {L : Layout} {ety : Ty} {pl : PlaceExpr} {r : Name}
    {p : List Seg} {m : Nat} :
    ∀ (todo : List SVal), m ≤ 8 -> tyOkFuel m ety = true ->
      LitPlace L pl.expr r p (Ty.ref (RefTy.array ety)) ->
      ∀ (done : List SVal) (s : State) (v0 : SVal),
        s.env = [] -> lookupBy r s.storage = some v0 ->
        v0.get p = some (SVal.array done []) ->
        SVal.canonical.canonicalElems ety todo = true ->
        execBlock s (fillElems pl ety done.length todo) =
          Except.ok { s with storage := setBy r (v0.put p (SVal.array (done ++ todo) [])) s.storage }
  | [], hm, hok, hpl, done, s, v0, hs, hroot, hget, hcan => by
      simp only [fillElems, execBlock_nil, List.append_nil]
      rw [SVal.put_get_self hget, setBy_lookup_self hroot]
  | w :: rest, hm, hok, hpl, done, s, v0, hs, hroot, hget, hcan => by
      simp only [SVal.canonical.canonicalElems, Bool.and_eq_true] at hcan
      have hdok : defaultOk ety = true := tyOkFuel_defaultOk hok
      have hpl' := LitPlace.index (L := L) (done.length : Int) ety hpl rfl
      have h0 := exec_push_none hpl hs hroot hget
      simp only [pushSlot] at h0
      have hget₁ : (v0.put p (SVal.array (done ++ [defaultForTy ety]) [])).get
          (p ++ [Seg.at (done.length : Int)]) = some (defaultForTy ety) := by
        simp only [SVal.get_snoc, SVal.get_put_self hget, Option.bind_some,
          SVal.get_at_array_last]
      have h1 := fill_exec w ety m hm hok hcan.1
        (PlaceExpr.index Kind.storage ety pl.expr
          (WrappedExpr.intLit Ty.uint (done.length : Int)))
        r (p ++ [Seg.at (done.length : Int)])
        { s with storage :=
            setBy r (v0.put p (SVal.array (done ++ [defaultForTy ety]) [])) s.storage }
        (v0.put p (SVal.array (done ++ [defaultForTy ety]) [])) (defaultForTy ety)
        hpl' hs (lookupBy_setBy_self _ _ _) hget₁ (defaultForTy_isDefault hdok)
      simp only [SVal.put_snoc _ w (SVal.get_put_self hget), SVal.put_at_array_last,
        SVal.put_put_same hget, setBy_setBy_same] at h1
      have hget₂ : (v0.put p (SVal.array (done ++ [w]) [])).get p =
          some (SVal.array (done ++ [w]) []) := SVal.get_put_self hget
      have h2 := fillElems_exec rest hm hok hpl (done ++ [w])
        { s with storage := setBy r (v0.put p (SVal.array (done ++ [w]) [])) s.storage }
        (v0.put p (SVal.array (done ++ [w]) [])) hs (lookupBy_setBy_self _ _ _) hget₂
        hcan.2
      rw [List.length_append, List.length_singleton] at h2
      simp only [fillElems, execBlock_cons, h0, bind, Except.bind, execBlock_append,
        h1, h2, setBy_setBy_same, SVal.put_put_same hget, List.append_assoc,
        List.singleton_append]
termination_by structural todo => todo

theorem fillEntries_exec {L : Layout} {kty vty : Ty} {pl : PlaceExpr} {r : Name}
    {p : List Seg} {m : Nat} :
    ∀ (todo : List (Int × SVal)), m ≤ 8 -> tyOkFuel m vty = true ->
      LitPlace L pl.expr r p (Ty.ref (RefTy.mapping kty vty)) ->
      ∀ (done : List (Int × SVal)) (d : SVal) (s : State) (v0 : SVal),
        s.env = [] -> lookupBy r s.storage = some v0 ->
        v0.get p = some (SVal.map done d) -> d.isDefault vty = true ->
        SVal.canonical.canonicalEntries vty todo = true ->
        nodupKeysB (done ++ todo) = true ->
        execBlock s (fillEntries pl vty todo) =
          Except.ok { s with storage := setBy r (v0.put p (SVal.map (done ++ todo) d)) s.storage }
  | [], hm, hok, hpl, done, d, s, v0, hs, hroot, hget, hd, hcan, hnd => by
      simp only [fillEntries, execBlock_nil, List.append_nil]
      rw [SVal.put_get_self hget, setBy_lookup_self hroot]
  | (k, w) :: rest, hm, hok, hpl, done, d, s, v0, hs, hroot, hget, hd, hcan,
      hnd => by
      simp only [SVal.canonical.canonicalEntries, Bool.and_eq_true] at hcan
      have hnone : lookupBy k done = none := nodupKeysB_append_cons hnd
      have hpl' := LitPlace.index (L := L) k vty hpl rfl
      have h0 := exec_delete_absent
        (pl := PlaceExpr.index Kind.storage vty pl.expr (WrappedExpr.intLit Ty.uint k))
        hpl' hs hroot hget hnone
      rw [SVal.defaultOf_of_isDefault hd, setBy_eq_append_of_fresh hnone] at h0
      have hget₁ : (v0.put p (SVal.map (done ++ [(k, d)]) d)).get (p ++ [Seg.at k]) =
          some d := by
        simp only [SVal.get_snoc, SVal.get_put_self hget, Option.bind_some,
          SVal.get_at_map]
        exact lookupBy_append_cons_self hnone d []
      have h1 := fill_exec w vty m hm hok hcan.1
        (PlaceExpr.index Kind.storage vty pl.expr (WrappedExpr.intLit Ty.uint k))
        r (p ++ [Seg.at k])
        { s with storage := setBy r (v0.put p (SVal.map (done ++ [(k, d)]) d)) s.storage }
        (v0.put p (SVal.map (done ++ [(k, d)]) d)) d hpl' hs
        (lookupBy_setBy_self _ _ _) hget₁ hd
      simp only [SVal.put_snoc _ w (SVal.get_put_self hget), SVal.put_at_map,
        setBy_append_cons hnone d w [], SVal.put_put_same hget, setBy_setBy_same]
        at h1
      have hget₂ : (v0.put p (SVal.map (done ++ [(k, w)]) d)).get p =
          some (SVal.map (done ++ [(k, w)]) d) := SVal.get_put_self hget
      have h2 := fillEntries_exec rest hm hok hpl (done ++ [(k, w)]) d
        { s with storage := setBy r (v0.put p (SVal.map (done ++ [(k, w)]) d)) s.storage }
        (v0.put p (SVal.map (done ++ [(k, w)]) d)) hs (lookupBy_setBy_self _ _ _)
        hget₂ hd hcan.2 (by rwa [← List.append_cons])
      simp only [fillEntries, execBlock_cons, h0, bind, Except.bind,
        execBlock_append, h1, h2, setBy_setBy_same, SVal.put_put_same hget,
        List.append_assoc, List.singleton_append]
termination_by structural todo => todo

end

/-! ## Witnesses -/

namespace Witness

def uintLayout : Layout := ⟨[("total", Ty.uint)]⟩

def totalPlace : PlaceExpr :=
  PlaceExpr.var Kind.storage Ty.uint
    { name := "total", ty := Ty.uint, origin := some StorageOrigin.global }

/-- `total = -5;` — well-typed, executes, lands `-5` in a `uint` cell. -/
def negProg : List Stmt :=
  [Stmt.assign totalPlace (WrappedExpr.intLit Ty.uint (-5))]

theorem uint_negative_reachable :
    Reachable uintLayout { storage := [("total", SVal.int (-5))] } :=
  ⟨negProg, [], by native_decide, by native_decide⟩

/-- `uint` range is not an invariant of the model: literals and plain
assignments are unchecked (only arithmetic goes through `checkArith`). -/
theorem uint_range_not_invariant :
    ¬ ∀ s, Reachable uintLayout s ->
      ∀ n, lookupBy "total" s.storage = some (SVal.int n) -> 0 ≤ n := by
  intro h
  have := h _ uint_negative_reachable (-5) (by native_decide)
  omega

-- …and `canonical` rightly admits it.
example : canonicalStorageB uintLayout [("total", SVal.int (-5))] = true := by
  native_decide

def mapLayout : Layout :=
  ⟨[("balances", Ty.ref (RefTy.mapping Ty.uint Ty.uint))]⟩

/-- A mapping whose default is `7`: well-typed, never produced. -/
def badDfltStorage : List (Name × SVal) :=
  [("balances", SVal.map [] (SVal.int 7))]

example : wellTypedStorageB mapLayout badDfltStorage = true := by native_decide
example : canonicalStorageB mapLayout badDfltStorage = false := by native_decide

/-- Duplicate mapping keys: well-typed, never produced. -/
def dupKeyStorage : List (Name × SVal) :=
  [("balances", SVal.map [(1, SVal.int 0), (1, SVal.int 0)] (SVal.int 0))]

example : wellTypedStorageB mapLayout dupKeyStorage = true := by native_decide
example : canonicalStorageB mapLayout dupKeyStorage = false := by native_decide

def acctLayout : Layout := ⟨[("acct", Ty.ref (RefTy.struct "Account"))]⟩

/-- An `Account` missing its `token` field: well-typed, never produced. -/
def missingFieldStorage : List (Name × SVal) :=
  [("acct", SVal.struct [("balance", SVal.int 0)])]

example : wellTypedStorageB acctLayout missingFieldStorage = true := by
  native_decide
example : canonicalStorageB acctLayout missingFieldStorage = false := by
  native_decide

end Witness

/-! ## Headline: every canonical storage is reachable -/

theorem initialState_canonical {L : Layout} (hL : layoutOkB L = true) :
    canonicalStorageB L (initialState L).storage = true := by
  simp only [layoutOkB, Bool.and_eq_true] at hL
  simp only [canonicalStorageB, Bool.and_eq_true, beq_iff_eq]
  refine ⟨by simp [initialState], ?_⟩
  apply List.all_eq_true.mpr
  intro g hg
  have hlook : lookupBy g.1 L.globals = some g.2 :=
    lookupBy_eq_of_nodup hL.1 hg
  show (match lookupBy g.1 (initialState L).storage with
        | some v => v.canonical g.2
        | none => false) = true
  simp only [initialState, lookupBy_map_snd, hlook, Option.map_some]
  exact SVal.isDefault_canonical
    (defaultForTy_isDefault (tyOk_defaultOk (List.all_eq_true.mp hL.2 g hg)))

theorem layoutOkB_all {L : Layout} (hL : layoutOkB L = true) :
    (L.globals.all fun g => tyOk g.2) = true := by
  simp only [layoutOkB, Bool.and_eq_true] at hL
  exact hL.2

theorem writeProg_wt {L : Layout} (hL : layoutOkB L = true) :
    ∀ (st : List (Name × SVal)),
      (∀ rv ∈ st, ∃ ty, lookupBy rv.1 L.globals = some ty ∧
        rv.2.canonical ty = true) ->
      blockWt [] L (writeProg L st) = some []
  | [], _ => rfl
  | (n, v) :: rest, h => by
      obtain ⟨ty, hlook, hcan⟩ := h (n, v) (List.Mem.head _)
      have hok : tyOk ty = true :=
        List.all_eq_true.mp (layoutOkB_all hL) _ (lookupBy_eq_some_mem hlook)
      simp only [writeProg, List.flatMap_cons, hlook, blockWt_append,
        fill_wt v ty 8 (Nat.le_refl 8) hok hcan
          (PlaceExpr.var Kind.storage ty
            { name := n, ty := ty, origin := some StorageOrigin.global })
          n [] (LitPlace.root n ty hlook), Option.bind_some]
      exact writeProg_wt hL rest fun rv hm => h rv (List.Mem.tail _ hm)

theorem writeProg_exec {L : Layout} (hL : layoutOkB L = true) :
    ∀ (todo done cf : List (Name × SVal)) (s : State),
      s.env = [] -> s.storage = done ++ cf ->
      (∀ rv ∈ todo, ∃ ty, lookupBy rv.1 L.globals = some ty ∧
        rv.2.canonical ty = true) ->
      (∀ rv ∈ cf, ∃ ty, lookupBy rv.1 L.globals = some ty ∧
        rv.2 = defaultForTy ty) ->
      cf.map Prod.fst = todo.map Prod.fst ->
      nodupKeysB (done ++ todo) = true ->
      execBlock s (writeProg L todo) = Except.ok { s with storage := done ++ todo }
  | [], done, cf, s, hs, hst, _, _, hnames, _ => by
      cases cf with
      | cons _ _ => simp at hnames
      | nil =>
          simp only [List.append_nil] at hst
          simp only [writeProg, List.flatMap_nil, execBlock_nil, List.append_nil,
            ← hst]
  | (n, v) :: rest, done, cf, s, hs, hst, hcan, hdef, hnames, hnd => by
      cases cf with
      | nil => simp at hnames
      | cons hd cf' =>
          obtain ⟨n', d⟩ := hd
          simp only [List.map_cons, List.cons.injEq] at hnames
          obtain ⟨hn, hnames'⟩ := hnames
          subst hn
          obtain ⟨ty, hlook, hcanv⟩ := hcan (n', v) (List.Mem.head _)
          obtain ⟨ty', hlook', hd⟩ := hdef (n', d) (List.Mem.head _)
          dsimp only at hlook hcanv hlook' hd
          rw [hlook] at hlook'
          cases Option.some.inj hlook'
          subst hd
          have hok : tyOk ty = true :=
            List.all_eq_true.mp (layoutOkB_all hL) _ (lookupBy_eq_some_mem hlook)
          have hnone : lookupBy n' done = none := nodupKeysB_append_cons hnd
          have hroot : lookupBy n' s.storage = some (defaultForTy ty) := by
            rw [hst]; exact lookupBy_append_cons_self hnone _ cf'
          have h1 := fill_exec v ty 8 (Nat.le_refl 8) hok hcanv
            (PlaceExpr.var Kind.storage ty
              { name := n', ty := ty, origin := some StorageOrigin.global })
            n' [] s (defaultForTy ty) (defaultForTy ty) (LitPlace.root n' ty hlook)
            hs hroot (by simp [SVal.get]) (defaultForTy_isDefault (tyOk_defaultOk hok))
          have hput : ∀ x : SVal, x.put [] v = v := fun x => by cases x <;> rfl
          rw [hput, hst, setBy_append_cons hnone] at h1
          have h2 := writeProg_exec hL rest (done ++ [(n', v)]) cf'
            { s with storage := done ++ (n', v) :: cf' } hs
            (List.append_cons done (n', v) cf')
            (fun rv hm => hcan rv (List.Mem.tail _ hm))
            (fun rv hm => hdef rv (List.Mem.tail _ hm)) hnames'
            (by rwa [← List.append_cons])
          rw [← List.append_cons] at h2
          simp only [writeProg, List.flatMap_cons, hlook, execBlock_append, h1, bind,
            Except.bind]
          exact h2

/-- **Tightness**: every canonical storage is produced from the initial
state by a `blockWt`-checked program — `writeProg` itself. -/
theorem storage_tight {L : Layout} (hL : layoutOkB L = true)
    {st : List (Name × SVal)} (hc : canonicalStorageB L st = true) :
    blockWt [] L (writeProg L st) = some [] ∧
      execBlock (initialState L) (writeProg L st) = Except.ok { storage := st } := by
  have hL' := hL
  simp only [layoutOkB, Bool.and_eq_true] at hL'
  simp only [canonicalStorageB, Bool.and_eq_true, beq_iff_eq] at hc
  have hstnd : nodupKeysB st = true := nodupKeysB_of_map_fst_eq hc.1 hL'.1
  have hroots : ∀ rv ∈ st, ∃ ty, lookupBy rv.1 L.globals = some ty ∧
      rv.2.canonical ty = true := by
    intro rv hmem
    have hname : rv.1 ∈ L.globals.map Prod.fst := by
      rw [← hc.1]; exact List.mem_map_of_mem hmem
    obtain ⟨g, hg, hg1⟩ := List.mem_map.mp hname
    have hlook : lookupBy rv.1 L.globals = some g.2 := by
      rw [← hg1]; exact lookupBy_eq_of_nodup hL'.1 hg
    refine ⟨g.2, hlook, ?_⟩
    have := List.all_eq_true.mp hc.2 g hg
    rw [hg1, lookupBy_eq_of_nodup hstnd hmem] at this
    exact this
  have hdefs : ∀ rv ∈ (initialState L).storage, ∃ ty,
      lookupBy rv.1 L.globals = some ty ∧ rv.2 = defaultForTy ty := by
    intro rv hmem
    obtain ⟨g, hg, hgeq⟩ := List.mem_map.mp hmem
    subst hgeq
    exact ⟨g.2, lookupBy_eq_of_nodup hL'.1 hg, rfl⟩
  have hnames : (initialState L).storage.map Prod.fst = st.map Prod.fst := by
    rw [hc.1]; simp [initialState]
  refine ⟨writeProg_wt hL st hroots, ?_⟩
  have := writeProg_exec hL st [] (initialState L).storage (initialState L) rfl rfl
    hroots hdefs hnames hstnd
  simpa [initialState] using this

theorem canonical_reachable {L : Layout} (hL : layoutOkB L = true)
    {st : List (Name × SVal)} (hc : canonicalStorageB L st = true) :
    Reachable L { storage := st } :=
  ⟨writeProg L st, [], (storage_tight hL hc).1, (storage_tight hL hc).2⟩

/-- **Nothing inferable is missing**: any storage property that holds
initially and is preserved by every well-typed program run from a
well-typed state already holds on every canonical storage.  (The
`StateWT` premise on `hstep` matters: preservation is only demanded along
the states execution can actually be in — from an ill-typed state, e.g.
one with a stray `spath` binding shadowing a global, a `blockWt`-checked
program can break storage typing.) -/
theorem no_hidden_invariant {L : Layout} (hL : layoutOkB L = true)
    (P : List (Name × SVal) -> Prop) (hinit : P (initialState L).storage)
    (hstep : ∀ (s s' : State) (prog : List Stmt) (Γ' : Ctx),
      StateWT [] [] L s ->
      blockWt [] L prog = some Γ' -> execBlock s prog = Except.ok s' ->
      P s.storage -> P s'.storage) :
    ∀ st, canonicalStorageB L st = true -> P st := by
  intro st hc
  obtain ⟨hwt, hexec⟩ := storage_tight hL hc
  exact hstep _ _ _ _ (initialState_wt hL) hwt hexec hinit

/-- The two directions side by side: canonical ⇒ reachable, reachable ⇒
well-typed. -/
theorem tight_and_sound {L : Layout} (hL : layoutOkB L = true) :
    (∀ st, canonicalStorageB L st = true -> Reachable L { storage := st }) ∧
    (∀ s, Reachable L s -> wellTypedStorageB L s.storage = true) :=
  ⟨fun _ hc => canonical_reachable hL hc, fun _ h => reachable_wellTyped hL h⟩

namespace Witness

-- The three non-canonical witnesses are well-typed but not canonical, so
-- tightness does not produce them. That they are *unreachable* needs the
-- converse invariant "reachable ⇒ canonical" — a second
-- `TypeSoundness`-sized traversal of the interpreter, left open here
-- (see the module docstring), like `BlockStep.wellFounded`.

/-- Open: mapping defaults are never written, so no program produces `7`. -/
theorem map_default_not_reachable :
    ¬ Reachable mapLayout { storage := badDfltStorage } := by
  sorry

/-- Open: no operation removes a struct field, so `token` is never absent. -/
theorem struct_missing_field_not_reachable :
    ¬ Reachable acctLayout { storage := missingFieldStorage } := by
  sorry

/-! ### Smoke test: the theorem on a concrete storage

`Wallet` = `{ owner : uint, stash : mapping(uint => uint) }`. The
target storage has a written struct field, two mapping entries and a
two-element array; `writeProg` really produces it. -/

def demoLayout : Layout :=
  ⟨[("w", Ty.ref (RefTy.struct "Wallet")),
    ("xs", Ty.ref (RefTy.array Ty.uint))]⟩

def demoStorage : List (Name × SVal) :=
  [("w", SVal.struct
      [("owner", SVal.int 9),
       ("stash", SVal.map [(3, SVal.int 30), (1, SVal.int 10)] (SVal.int 0))]),
   ("xs", SVal.array [SVal.int 5, SVal.int 6] [])]

example : layoutOkB demoLayout = true := by native_decide
example : canonicalStorageB demoLayout demoStorage = true := by native_decide

-- The instance of the theorem…
example : Reachable demoLayout { storage := demoStorage } :=
  canonical_reachable (by native_decide) (by native_decide)

-- …and the program it exhibits, run through the interpreter.
example : execBlock (initialState demoLayout) (writeProg demoLayout demoStorage) =
    Except.ok { storage := demoStorage } := by native_decide
example : blockWt [] demoLayout (writeProg demoLayout demoStorage) = some [] := by
  native_decide

end Witness

end Semantics
end Solidity
