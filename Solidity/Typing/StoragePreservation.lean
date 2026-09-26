import Solidity.Typing.Storage
import Solidity.Semantics.Properties

/-!
# Storage write core: `save` preserves typing

The write-side twin of `StorageTyping`'s read lemmas, and the first
layer of the type-soundness development (`State.lean`,
`Soundness.lean`): saving a value of the path's layout type keeps
the whole storage well-typed.

- `save_hasTy` mirrors `find_hasTy` arm for arm: a `ty`-typed tree
  stays `ty`-typed when a `ty'`-typed value is saved at a
  `ty'`-typed path (`tyAtSegs`).
- `State.saveStorage_wellTyped` lifts it to `wellTypedStorageB` —
  under `nodupKeysB L.globals`, which is genuinely load-bearing: with
  a duplicated layout root the two rows check the *same* stored value
  against different types, and a save that satisfies one row can break
  the other (`Counterexamples/PreservationNecessity.lean`).
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

open SemanticsProperties (lookupBy_setBy_self lookupBy_setBy_ne)

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
          | mapping key value => simp [SVal.hasTy] at h
  | array elems shadow =>
      cases ty with
      | prim pt => simp [SVal.hasTy] at h
      | ref r =>
          cases r with
          | struct sname => simp [SVal.hasTy] at h
          | array elem => simp [SVal.defaultOf, SVal.hasTy,
              SVal.hasTy.hasTyElems]
          | mapping key value => simp [SVal.hasTy] at h
  | map entries dflt =>
      simpa only [SVal.defaultOf] using h

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
  | Ty.ref (RefTy.mapping _ value) => defaultOk value
termination_by ty => (tyRank ty, sizeOf ty)
decreasing_by
  · exact Prod.Lex.left _ _ (structDef_rank_lt _)
  · apply Prod.Lex.right; simp; omega

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

/-- `defaultOkFields` from the two facts its rows have to satisfy: each
row is the one its name looks up to, and each row type is `defaultOk`.
Stated over an arbitrary row list so the caller can induct on a sublist
of `structDef s` while looking up in the whole table. -/
theorem defaultOkFields_of_rows {s : Name} :
    ∀ {rows : List (Name × Ty)},
      (∀ p ∈ rows, lookupBy p.1 (structDef s) = some p.2) ->
      (∀ p ∈ rows, defaultOk p.2 = true) ->
      defaultOkFields s rows = true := by
  intro rows
  induction rows with
  | nil => intro _ _; simp [defaultOkFields]
  | cons fld rest ih =>
      intro hlook hok
      obtain ⟨n, t⟩ := fld
      simp only [defaultOkFields, Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨hok _ (List.mem_cons_self ..), hlook _ (List.mem_cons_self ..)⟩,
        ih (fun p hp => hlook p (List.mem_cons_of_mem _ hp))
           (fun p hp => hok p (List.mem_cons_of_mem _ hp))⟩

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
  | case6 key value ih =>
      intro h
      simp only [defaultOk] at h
      simp only [defaultForTy, SVal.hasTy, SVal.hasTy.hasTyEntries,
        Bool.true_and]
      exact ih h
  | case7 => simp [defaultForFields, SVal.hasTy.hasTyFields]
  | case8 n t rest iht ihrest =>
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
                      case array elems shadow =>
                        simp only [SVal.save] at hsave
                        split at hsave
                        case isTrue hbound =>
                          obtain ⟨updated, hup, hw⟩ :=
                            Semantics.bind_ok_inv hsave
                          simp at hw
                          subst hw
                          simp only [SVal.hasTy, Bool.and_eq_true]
                          exact ⟨hasTyElems_set hty.1
                            (ih (hasTyElems_mem hty.1 (elems.get_mem _))
                              hsegs hnew hup), hty.2⟩
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

/-- No duplicate keys. `wellTypedStorageB` checks every layout row
against the single stored value at its root, so a duplicated root would
check one value against two types — see the refutation in
`Counterexamples/PreservationNecessity.lean`. -/
def nodupKeysB [DecidableEq κ] : List (κ × α) -> Bool
  | [] => true
  | (k, _) :: rest => (lookupBy k rest).isNone && nodupKeysB rest

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
  simp only [Layout.tyAt] at hty
  cases hglob : lookupBy root L.globals with
  | none => rw [hglob] at hty; simp at hty
  | some ty0 =>
      rw [hglob] at hty
      simp only [State.saveStorage] at hsave
      cases hroot : lookupBy root s.storage with
      | none => rw [hroot] at hsave; simp at hsave
      | some v0 =>
          rw [hroot] at hsave
          obtain ⟨updated, hup, hs'⟩ := Semantics.bind_ok_inv hsave
          simp at hs'
          have hv0 : v0.hasTy ty0 = true := by
            have hmem := lookupBy_eq_some_mem hglob
            have hall := (List.all_eq_true.mp hst) _ hmem
            simpa [hroot] using hall
          have hupd : updated.hasTy ty0 = true :=
            save_hasTy hv0 hty hnew hup
          subst hs'
          refine List.all_eq_true.mpr ?_
          intro g hg
          show (match lookupBy g.1 (setBy root updated s.storage) with
            | some v => v.hasTy g.2
            | none => false) = true
          by_cases hgr : g.1 = root
          · have hgty : g.2 = ty0 := by
              have hl := lookupBy_eq_of_nodup hnd hg
              rw [hgr, hglob] at hl
              exact (Option.some.inj hl).symm
            rw [hgr, hgty]
            simpa [lookupBy_setBy_self] using hupd
          · rw [lookupBy_setBy_ne hgr]
            exact (List.all_eq_true.mp hst) _ hg

/-- A memory write leaves storage untouched. -/
theorem writeLoc_storage_frame {s s' : State} {loc : Addr} {v : Value}
    (h : writeLoc s loc v = Except.ok s') : s'.storage = s.storage := by
  cases loc with
  | memoryField id fld =>
      simp only [writeLoc, State.getObj, bind, Except.bind] at h
      repeat' split at h
      all_goals first
        | (cases Except.ok.inj h; rfl)
        | exact nomatch h
  | memoryIndex id i =>
      simp only [writeLoc, State.getObj, bind, Except.bind] at h
      repeat' split at h
      all_goals first
        | (cases Except.ok.inj h; rfl)
        | exact nomatch h

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
      · exact SVal.defaultOf_hasTy hsh.1

end Semantics
end Solidity
