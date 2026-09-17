import Solidity.Reachability

/-!
# What the taclets consume from `wellFormed(storage)`

The operational "nothing missing" check: every fact a taclet needs about
a symbolic storage, stated over the interpreter and proved from the
invariant — `wellTypedStorageB` where the type suffices,
`canonicalStorageB` (`Reachability.lean`) where it does not. A row that
cannot be proved is a missing conjunct.

| # | KeY consumer | row | invariant |
|---|---|---|---|
| C1 | `storagePopSave` non-empty branch: `find<[int]>(storage, consr(sp, size)) >= 0` | `length_read_nonneg` | well-typed for the *read* (the `length` cell resolves to the element count); `≥ 0` itself is structural — a `Nat` cast |
| C2 | `storageIndexRead*`: in bounds ⇒ typed value, out of bounds ⇒ revert | `index_read_in_bounds` / `index_read_out_of_bounds` | well-typed |
| C3 | `selectSt`/`defaultValue` on an unwritten key | `absent_key_reads_default` / `_defaultForTy` | **canonical** — `Witness.badDfltStorage` refutes it for well-typed |
| C4 | `selectSt` on a declared member is defined | `declared_field_read_ok` | **canonical** — `Witness.missingFieldStorage` refutes it for well-typed |
| C5 | `find<[int]>` at a numeric path is an int | `TypeSoundness.run_then_find_int` | well-typed |
| C6 | `delete` keeps the invariant | value level: `SVal.defaultOf_canonical` (twin of `defaultOf_hasTy`); state level: `saveStorage_canonical`, **open** (`sorry`) | canonical |
-/

namespace Solidity
namespace Semantics

/-! ## Reads below a typed prefix -/

theorem SVal.find_append_typed {segs : List Seg} :
    ∀ {v : SVal} {ty ty' : Ty} {c : SVal} (q : List Seg),
      v.hasTy ty = true -> tyAtSegs ty segs = some ty' ->
      v.find segs = Except.ok c -> v.find (segs ++ q) = c.find q := by
  induction segs with
  | nil =>
      intro v ty ty' c q hty hsegs hfind
      simp [SVal.find] at hfind
      subst hfind
      rfl
  | cons seg rest ih =>
      intro v ty ty' c q hty hsegs hfind
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
                        simp only [List.cons_append, SVal.find] at hfind ⊢
                        cases hlook : lookupBy n fields with
                        | none => rw [hlook] at hfind; simp at hfind
                        | some v' =>
                            rw [hlook] at hfind
                            obtain ⟨tyf, hdef, htyv⟩ :=
                              hasTyFields_lookup hty hlook
                            rw [hseg] at hdef
                            cases hdef
                            exact ih q htyv hsegs hfind
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
                        simp only [List.cons_append, SVal.find] at hfind ⊢
                        split at hfind
                        · rename_i hb
                          rw [dif_pos hb]
                          exact ih q (hasTyElems_mem hty.1 (elems.get_mem _))
                            hsegs hfind
                        · simp at hfind
                  | mapping key value =>
                      simp only [segTy] at hseg
                      cases hseg
                      cases v <;> simp [SVal.hasTy] at hty
                      case map entries dflt =>
                        simp only [List.cons_append, SVal.find] at hfind ⊢
                        cases hlook : lookupBy i entries with
                        | none =>
                            rw [hlook] at hfind
                            exact ih q hty.2 hsegs hfind
                        | some v' =>
                            rw [hlook] at hfind
                            exact ih q (hasTyEntries_lookup hty.1 hlook) hsegs
                              hfind
              | _ => simp [segTy] at hseg

theorem State.findStorage_append_typed {L : Layout} {s : State} {r : Name}
    {p : List Seg} {ty : Ty} {c : SVal}
    (hst : wellTypedStorageB L s.storage = true) (hty : L.tyAt r p = some ty)
    (hfind : s.findStorage r p = Except.ok c) (q : List Seg) :
    s.findStorage r (p ++ q) = c.find q := by
  simp only [Layout.tyAt] at hty
  cases hglob : lookupBy r L.globals with
  | none => rw [hglob] at hty; simp at hty
  | some ty0 =>
      rw [hglob] at hty
      have hall := (List.all_eq_true.mp hst) _ (lookupBy_eq_some_mem hglob)
      simp only [State.findStorage] at hfind ⊢
      cases hroot : lookupBy r s.storage with
      | none => rw [hroot] at hfind; simp at hfind
      | some v =>
          rw [hroot] at hfind hall
          try dsimp only at hall
          exact SVal.find_append_typed q hall hty hfind

/-! ## C1 / C2 — arrays: `size ≥ 0`, bounds -/

theorem length_read_nonneg {L : Layout} {s : State} {r : Name} {p : List Seg}
    {elem : Ty} {es : List SVal}
    (hst : wellTypedStorageB L s.storage = true)
    (hty : L.tyAt r p = some (Ty.ref (RefTy.array elem)))
    (hfind : s.findStorage r p = Except.ok (SVal.array es sh)) :
    s.findStorage r (p ++ [Seg.field "length"]) =
        Except.ok (SVal.int es.length) ∧ (0 : Int) ≤ es.length := by
  refine ⟨?_, by omega⟩
  rw [State.findStorage_append_typed hst hty hfind]
  simp [SVal.find]

theorem index_read_in_bounds {L : Layout} {s : State} {r : Name} {p : List Seg}
    {elem : Ty} {es : List SVal} {i : Int}
    (hst : wellTypedStorageB L s.storage = true)
    (hty : L.tyAt r p = some (Ty.ref (RefTy.array elem)))
    (hfind : s.findStorage r p = Except.ok (SVal.array es sh))
    (hb : 0 ≤ i ∧ i.toNat < es.length) :
    ∃ v, s.findStorage r (p ++ [Seg.at i]) = Except.ok v ∧ v.hasTy elem = true := by
  have hval := findStorage_hasTy hst hty hfind
  simp only [SVal.hasTy, Bool.and_eq_true] at hval
  rw [State.findStorage_append_typed hst hty hfind]
  refine ⟨es.get ⟨i.toNat, hb.2⟩, ?_, hasTyElems_mem hval.1 (es.get_mem _)⟩
  simp [SVal.find, hb]

theorem index_read_out_of_bounds {L : Layout} {s : State} {r : Name}
    {p : List Seg} {elem : Ty} {es : List SVal} {i : Int}
    (hst : wellTypedStorageB L s.storage = true)
    (hty : L.tyAt r p = some (Ty.ref (RefTy.array elem)))
    (hfind : s.findStorage r p = Except.ok (SVal.array es sh))
    (hb : ¬ (0 ≤ i ∧ i.toNat < es.length)) :
    s.findStorage r (p ++ [Seg.at i]) = Except.error Halt.revert := by
  rw [State.findStorage_append_typed hst hty hfind]
  simp [SVal.find, hb]

/-! ## `find` preserves canonicity along typed paths -/

theorem canonicalFields_lookup {s : Name} {fields : List (Name × SVal)}
    {n : Name} {v : SVal}
    (h : SVal.canonical.canonicalFields s fields = true)
    (hl : lookupBy n fields = some v) :
    ∃ ty, lookupBy n (structDef s) = some ty ∧ v.canonical ty = true := by
  induction fields with
  | nil => simp [lookupBy] at hl
  | cons pr rest ih =>
      obtain ⟨n', v'⟩ := pr
      simp only [SVal.canonical.canonicalFields, Bool.and_eq_true] at h
      by_cases hn : n = n'
      · subst hn
        simp [lookupBy] at hl
        subst hl
        cases hdef : lookupBy n (structDef s) with
        | none => rw [hdef] at h; exact Bool.noConfusion h.1
        | some ty => rw [hdef] at h; exact ⟨ty, rfl, h.1⟩
      · simp [lookupBy, hn] at hl
        exact ih h.2 hl

theorem canonicalElems_mem {elem : Ty} {elems : List SVal} {v : SVal}
    (h : SVal.canonical.canonicalElems elem elems = true) (hmem : v ∈ elems) :
    v.canonical elem = true := by
  induction elems with
  | nil => cases hmem
  | cons w rest ih =>
      simp only [SVal.canonical.canonicalElems, Bool.and_eq_true] at h
      cases hmem with
      | head => exact h.1
      | tail _ hmem => exact ih h.2 hmem

theorem canonicalEntries_lookup {value : Ty} {entries : List (Int × SVal)}
    {i : Int} {v : SVal}
    (h : SVal.canonical.canonicalEntries value entries = true)
    (hl : lookupBy i entries = some v) : v.canonical value = true := by
  induction entries with
  | nil => simp [lookupBy] at hl
  | cons pr rest ih =>
      obtain ⟨j, w⟩ := pr
      simp only [SVal.canonical.canonicalEntries, Bool.and_eq_true] at h
      by_cases hi : i = j
      · subst hi
        simp [lookupBy] at hl
        subst hl
        exact h.1
      · simp [lookupBy, hi] at hl
        exact ih h.2 hl

theorem SVal.find_canonical {segs : List Seg} :
    ∀ {v : SVal} {ty ty' : Ty} {w : SVal},
      v.canonical ty = true -> tyAtSegs ty segs = some ty' ->
      v.find segs = Except.ok w -> w.canonical ty' = true := by
  induction segs with
  | nil =>
      intro v ty ty' w hty hsegs hfind
      simp [tyAtSegs] at hsegs
      simp [SVal.find] at hfind
      subst hsegs hfind
      exact hty
  | cons seg rest ih =>
      intro v ty ty' w hty hsegs hfind
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
                      cases v with
                      | prim p => cases p <;> simp [SVal.canonical] at hty
                      | array _ => simp [SVal.canonical] at hty
                      | map _ _ => simp [SVal.canonical] at hty
                      | struct fields =>
                        simp only [SVal.canonical, Bool.and_eq_true] at hty
                        simp only [SVal.find] at hfind
                        cases hlook : lookupBy n fields with
                        | none => rw [hlook] at hfind; simp at hfind
                        | some v' =>
                            rw [hlook] at hfind
                            obtain ⟨tyf, hdef, htyv⟩ :=
                              canonicalFields_lookup hty.2 hlook
                            rw [hseg] at hdef
                            cases hdef
                            exact ih htyv hsegs hfind
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
                      cases v with
                      | prim p => cases p <;> simp [SVal.canonical] at hty
                      | struct _ => simp [SVal.canonical] at hty
                      | map _ _ => simp [SVal.canonical] at hty
                      | array elems shadow =>
                        simp only [SVal.canonical, Bool.and_eq_true] at hfind hty
                        simp only [SVal.find] at hfind
                        split at hfind
                        · exact ih (canonicalElems_mem hty.1 (elems.get_mem _))
                            hsegs hfind
                        · simp at hfind
                  | mapping key value =>
                      simp only [segTy] at hseg
                      cases hseg
                      cases v with
                      | prim p => cases p <;> simp [SVal.canonical] at hty
                      | struct _ => simp [SVal.canonical] at hty
                      | array _ => simp [SVal.canonical] at hty
                      | map entries dflt =>
                        simp only [SVal.canonical, Bool.and_eq_true] at hty
                        simp only [SVal.find] at hfind
                        cases hlook : lookupBy i entries with
                        | none =>
                            rw [hlook] at hfind
                            exact ih (SVal.isDefault_canonical hty.2) hsegs hfind
                        | some v' =>
                            rw [hlook] at hfind
                            exact ih (canonicalEntries_lookup hty.1.2 hlook) hsegs
                              hfind
              | _ => simp [segTy] at hseg

theorem State.findStorage_canonical {L : Layout} {s : State} {r : Name}
    {p : List Seg} {ty' : Ty} {v : SVal}
    (hc : canonicalStorageB L s.storage = true)
    (hty : L.tyAt r p = some ty')
    (hfind : s.findStorage r p = Except.ok v) : v.canonical ty' = true := by
  simp only [canonicalStorageB, Bool.and_eq_true] at hc
  simp only [Layout.tyAt] at hty
  cases hglob : lookupBy r L.globals with
  | none => rw [hglob] at hty; simp at hty
  | some ty0 =>
      rw [hglob] at hty
      have hall := (List.all_eq_true.mp hc.2) _ (lookupBy_eq_some_mem hglob)
      simp only [State.findStorage] at hfind
      cases hroot : lookupBy r s.storage with
      | none => rw [hroot] at hfind; simp at hfind
      | some v0 =>
          rw [hroot] at hfind hall
          try dsimp only at hall
          exact SVal.find_canonical hall hty hfind

/-! ## C3 / C4 — the rows that need the canonical conjuncts -/

theorem absent_key_reads_default {L : Layout} {s : State} {r : Name}
    {p : List Seg} {kty vty : Ty} {es : List (Int × SVal)} {d : SVal} {i : Int}
    (hc : canonicalStorageB L s.storage = true)
    (hty : L.tyAt r p = some (Ty.ref (RefTy.mapping kty vty)))
    (hfind : s.findStorage r p = Except.ok (SVal.map es d))
    (habs : lookupBy i es = none) :
    s.findStorage r (p ++ [Seg.at i]) = Except.ok d ∧ d.isDefault vty = true := by
  have hval := State.findStorage_canonical hc hty hfind
  simp only [SVal.canonical, Bool.and_eq_true] at hval
  refine ⟨?_, hval.2⟩
  rw [State.findStorage_append_typed (canonicalStorage_wellTyped hc) hty hfind]
  simp [SVal.find, habs]

theorem absent_key_reads_defaultForTy {L : Layout} {s : State} {r : Name}
    {p : List Seg} {kty vty : Ty} {es : List (Int × SVal)} {d : SVal} {i : Int}
    (hc : canonicalStorageB L s.storage = true)
    (hty : L.tyAt r p = some (Ty.ref (RefTy.mapping kty vty)))
    (hfind : s.findStorage r p = Except.ok (SVal.map es d))
    (habs : lookupBy i es = none) (hok : defaultOk vty = true) :
    s.findStorage r (p ++ [Seg.at i]) = Except.ok (defaultForTy vty) := by
  obtain ⟨h1, h2⟩ := absent_key_reads_default hc hty hfind habs
  rw [h1, SVal.isDefault_unique h2 (defaultForTy_isDefault hok)]

theorem declared_field_read_ok {L : Layout} {s : State} {r : Name}
    {p : List Seg} {sname n : Name} {fty : Ty} {fs : List (Name × SVal)}
    (hc : canonicalStorageB L s.storage = true)
    (hty : L.tyAt r p = some (Ty.ref (RefTy.struct sname)))
    (hfind : s.findStorage r p = Except.ok (SVal.struct fs))
    (hdef : lookupBy n (structDef sname) = some fty) :
    ∃ v, s.findStorage r (p ++ [Seg.field n]) = Except.ok v ∧
      v.canonical fty = true := by
  have hval := State.findStorage_canonical hc hty hfind
  simp only [SVal.canonical, Bool.and_eq_true, beq_iff_eq] at hval
  have hsome : (lookupBy n fs).isNone = false := by
    rw [lookupBy_isNone_of_map_fst_eq hval.1, hdef]; rfl
  cases hl : lookupBy n fs with
  | none => rw [hl] at hsome; exact Bool.noConfusion hsome
  | some v =>
      obtain ⟨ty', hdef', hcan⟩ := canonicalFields_lookup hval.2 hl
      rw [hdef] at hdef'
      cases Option.some.inj hdef'
      refine ⟨v, ?_, hcan⟩
      rw [State.findStorage_append_typed (canonicalStorage_wellTyped hc) hty hfind]
      simp [SVal.find, hl]

namespace Witness

-- Well-typed is not enough for C3/C4: the two non-canonical witnesses.
example : State.findStorage { storage := badDfltStorage } "balances" [Seg.at 0] =
    Except.ok (SVal.int 7) := by native_decide
example : State.findStorage { storage := missingFieldStorage } "acct"
    [Seg.field "token"] = Except.error Halt.stuck := by native_decide

end Witness

/-! ## C6 — `delete` keeps canonicity

Value level, proved: the default of a canonical value is canonical.  State
level, open: see `saveStorage_canonical` at the end of the file. -/

theorem SVal.defaultOfFields_map_fst :
    ∀ (fs : List (Name × SVal)),
      (SVal.defaultOf.defaultOfFields fs).map Prod.fst = fs.map Prod.fst
  | [] => rfl
  | (n, v) :: rest => by
      simp only [SVal.defaultOf.defaultOfFields, List.map_cons]
      rw [SVal.defaultOfFields_map_fst rest]

mutual

theorem SVal.defaultOf_canonical {v : SVal} {ty : Ty}
    (h : v.canonical ty = true) : v.defaultOf.canonical ty = true := by
  cases v with
  | prim p =>
      cases p with
      | int n =>
          cases ty with
          | prim pt => cases pt <;> simp_all [SVal.canonical, SVal.defaultOf]
          | ref r => simp [SVal.canonical] at h
      | bool b =>
          cases ty with
          | prim pt => cases pt <;> simp_all [SVal.canonical, SVal.defaultOf]
          | ref r => simp [SVal.canonical] at h
  | struct fields =>
      cases ty with
      | prim pt => simp [SVal.canonical] at h
      | ref r =>
          cases r with
          | struct sname =>
              simp only [SVal.canonical, Bool.and_eq_true, beq_iff_eq] at h
              simp only [SVal.defaultOf, SVal.canonical, Bool.and_eq_true,
                beq_iff_eq]
              exact ⟨by rw [SVal.defaultOfFields_map_fst, h.1],
                SVal.defaultOfFields_canonical h.2⟩
          | array elem => simp [SVal.canonical] at h
          | mapping key value => simp [SVal.canonical] at h
  | array elems =>
      cases ty with
      | prim pt => simp [SVal.canonical] at h
      | ref r =>
          cases r with
          | struct sname => simp [SVal.canonical] at h
          | array elem =>
              simp [SVal.defaultOf, SVal.canonical, SVal.canonical.canonicalElems]
          | mapping key value => simp [SVal.canonical] at h
  | map entries dflt => simpa only [SVal.defaultOf] using h

theorem SVal.defaultOfFields_canonical {s : Name} {fields : List (Name × SVal)}
    (h : SVal.canonical.canonicalFields s fields = true) :
    SVal.canonical.canonicalFields s (SVal.defaultOf.defaultOfFields fields)
      = true := by
  match fields with
  | [] => exact h
  | (n, v) :: rest =>
      simp only [SVal.canonical.canonicalFields, Bool.and_eq_true] at h
      simp only [SVal.defaultOf.defaultOfFields, SVal.canonical.canonicalFields,
        Bool.and_eq_true]
      refine ⟨?_, SVal.defaultOfFields_canonical h.2⟩
      cases hdef : lookupBy n (structDef s) with
      | none => rw [hdef] at h; exact Bool.noConfusion h.1
      | some tyf =>
          rw [hdef] at h
          exact SVal.defaultOf_canonical h.1

end

/-- C6 at the state level, **open**: writing the default over a canonical
storage keeps it canonical — the `delete` instance of "reachable ⇒
canonical" (`Reachability.lean`), the direction the tightness development
leaves open.  `SVal.defaultOf_canonical` is the value-level ingredient; the
missing piece is the `saveStorage`/`canonicalStorageB` preservation
argument (the canonical twin of `State.saveStorage_wellTyped`).  Stated,
not proved: a `sorry` rather than a row that only says what the value
lemma says. -/
theorem saveStorage_canonical {L : Layout} {s s' : State} {r : Name}
    {p : List Seg} {cur : SVal}
    (hc : canonicalStorageB L s.storage = true)
    (hfind : s.findStorage r p = Except.ok cur)
    (hsave : s.saveStorage r p cur.defaultOf = Except.ok s') :
    canonicalStorageB L s'.storage = true := by
  sorry

end Semantics
end Solidity
