import Solidity.Correctness.Lowering.Total.RawTypeAgreement.Leaf
import Solidity.Correctness.Lowering.Total.StructTableAgreement

/-!
# A retained `RawTy` against its model type and resolved struct types

Closes the `RawTy` agreement `StructTableAgreement` leaves open. For a type as read
`R` with `rawType C loc R = .ok t` and the elaborator's own reading
`elabTyW C R = .ok (T, ws)`, `rawType_agrees` derives that the Source type `τ` of `t`
(`rawType_typed`, with its `RawRep`) represents the model type: `Rep` of `T` at the
key `key`, in any width table that agrees with the generated rows rebased there
(`rebase key ws`) on the keys the spelling of `T` reads. `agree_below` gives that
agreement for the generated rows among rows of other binders. The struct resolution
is derived, in `E.decls = pre ++ ps.collect (some c) ++ post` with
`decode C = .ok ps`, from table facts: `Closed`, `Free`, and `Keyed` of each struct
leaf (`keyed_agrees`, through `StructTableAgreement.agrees`); `leaf_agrees` gives
each struct leaf its `Agrees`.

The domain is the common one. `Plain` excludes an elementary name that is also an
enum of the contract (`elabTyW` reads the enum). `rawType` errors stay errors:
enum, function-type, `bytes`/`string` and member-spelling names, keys that are not
elementary names, zero lengths, mappings outside storage (`mapping_outside`), where
`elabTyW` may succeed. `Rep`, not a `spellType` equation, is the conclusion:
`bytes1[]` has one and no `spellType` spelling. A table without one written name has
no `Rep` (`unwritten_no_rep`); conflicting rows give another type (`Rep.prim_elem`).
Left to the decoder lane: `Closed`, `Free`, `Keyed` and the row shape over the
production domain, binding declarations, frames and semantics.
-/
namespace Solidity.Correctness.Lowering.Total.RawTypeAgreement

open Solidity.Semantics (lookupBy isEnc)
open Source (Syn STy DataLoc)
open ReferenceDecode (rawElem rawLeaf rawKey rawType rawNames RawRep Rep Resolved written?
  readTy readRef leafKeys rawKey_ok bind_ok rawType_typed written?_iff)
open StructDecode (Free decode)
open StructRows (Agree elemB_congr)
open StructTableAgreement (Agrees Closed agrees lookupBy_mem lookupBy_some_of_filter)

/-- Every name of a type as read, mapping keys included. -/
def names : RawTy → List String
  | .named s => [s]
  | .array T | .fixed T _ => names T
  | .mapping K V => names K ++ names V

/-- No elementary name of the type is also an enum of the contract. -/
def Plain (C : Contract) (R : RawTy) : Prop :=
  ∀ s ∈ names R, (rawElem s).isSome → lookupBy s C.enums = none
instance (C : Contract) (R : RawTy) : Decidable (Plain C R) := by unfold Plain; infer_instance

/-- Table facts of a struct name: one entry keys it, and one identifier writes that
entry's table (no alias, not shadowed). -/
def Keyed (C : Contract) (s : Name) : Prop :=
  (C.structs.filter (·.1 == s)).length = 1 ∧
    ∀ table ∈ lookupBy s C.structs, (written? C table).isSome
instance (C : Contract) (s : Name) : Decidable (Keyed C s) := by unfold Keyed; infer_instance

/-- Every struct leaf of the type is `Keyed`. -/
def Tabled (C : Contract) (R : RawTy) : Prop :=
  ∀ s ∈ rawNames R, rawElem s = none → (C.structName? s).isSome → Keyed C s
instance (C : Contract) (R : RawTy) : Decidable (Tabled C R) := by unfold Tabled; infer_instance

variable {C : Contract} {c : String} {E : Source.Env} {scope : Option String}
  {pre post : List Source.Decl} {widths : List (Name × Nat)}

/-! ## `elabTyW` of a compound type -/

theorem elabTyW_array {R : RawTy} {T : Ty} {ws : List (String × Nat)}
    (h : elabTyW C (.array R) = .ok (T, ws)) : ∃ T' w, elabTyW C R = .ok (T', w) ∧
      T = .ref (.array T') ∧ ws = w.map fun (k, n) => ("[]" ++ k, n) := by
  rw [elabTyW] at h
  cases h' : elabTyW C R with
  | error e => simp [h', bind, Except.bind] at h
  | ok x =>
    simp only [h', bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨x.1, x.2, rfl, h.1.symm, h.2.symm⟩

theorem elabTyW_fixed {R : RawTy} {m : Nat} {T : Ty} {ws : List (String × Nat)}
    (h : elabTyW C (.fixed R m) = .ok (T, ws)) : ∃ T' w, elabTyW C R = .ok (T', w) ∧
      T = .ref (.fixed T' m) ∧ ws = w.map fun (k, n) => ("[]" ++ k, n) := by
  rw [elabTyW] at h
  cases h' : elabTyW C R with
  | error e => simp [h', bind, Except.bind] at h
  | ok x =>
    simp only [h', bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨x.1, x.2, rfl, h.1.symm, h.2.symm⟩

/-- A mapping whose key name is a primitive to `elabTyW`: the key rows under `{}`,
then the value rows under `[]`. -/
theorem elabTyW_mapping {k : String} {V : RawTy} {p : PrimTy} {kw : List (String × Nat)}
    {T : Ty} {ws : List (String × Nat)} (hk : elabTyW C (.named k) = .ok (.prim p, kw))
    (h : elabTyW C (.mapping (.named k) V) = .ok (T, ws)) :
    ∃ vt vw, elabTyW C V = .ok (vt, vw) ∧ T = .ref (.mapping p vt) ∧
      ws = kw.map (fun (k, n) => ("{}" ++ k, n)) ++ vw.map fun (k, n) => ("[]" ++ k, n) := by
  have dyn : dynBytesTy k = false := by
    cases d : dynBytesTy k with
    | false => rfl
    | true => rw [elabTyW, if_pos d] at hk; cases hk
  rw [elabTyW] at h
  cases h' : elabTyW C V with
  | error e => simp [dyn, hk, h', bind, Except.bind, pure, Except.pure] at h
  | ok x =>
    simp only [dyn, hk, h', bind, Except.bind, pure, Except.pure, Bool.false_eq_true, if_false,
      Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨x.1, x.2, rfl, h.1.symm, h.2.symm⟩

/-- Every name outside a key of a spelled type is itself spelled. -/
theorem rawType_leaf : (R : RawTy) → (loc : DataLoc) → (t : Syn .typeName) →
    rawType C loc R = .ok t → ∀ s ∈ rawNames R, ∃ t', rawLeaf C s = .ok t'
  | .named s, _, t, h, s', hs => by
      simp only [rawNames, List.mem_singleton] at hs; subst hs
      exact ⟨t, by simpa only [rawType] using h⟩
  | .array R, loc, t, h, s, hs => by
      simp only [rawType, bind_ok] at h
      obtain ⟨t', ht, -⟩ := h
      exact rawType_leaf R loc t' ht s (by simpa only [rawNames] using hs)
  | .fixed R n, loc, t, h, s, hs => by
      simp only [rawType] at h
      split at h; · cases h
      simp only [bind_ok] at h
      obtain ⟨t', ht, -⟩ := h
      exact rawType_leaf R loc t' ht s (by simpa only [rawNames] using hs)
  | .mapping K V, loc, t, h, s, hs => by
      simp only [rawType] at h
      split at h
      · simp only [bind_ok] at h
        obtain ⟨_, -, t', ht, -⟩ := h
        exact rawType_leaf V .storage t' ht s (by simpa only [rawNames] using hs)
      · cases h

/-! ## The bridge, over the written names of the struct leaves -/

/-- The Source type a spelled `RawTy` denotes represents the model type `elabTyW`
reads, at the generated rows rebased at the key; each struct leaf's table written by
the leaf's own name. -/
theorem rep : ∀ (R : RawTy) (loc : DataLoc) (t : Syn .typeName) (τ : STy) (T : Ty)
    (ws : List (String × Nat)) (key : Name), rawType C loc R = .ok t →
    RawRep C E scope loc R τ → elabTyW C R = .ok (T, ws) → Plain C R →
    (∀ s ∈ rawNames R, rawElem s = none → ∀ table, C.structName? s = some table →
      written? C table = some s) →
    Agree (readTy key T) (rebase key ws) widths → Rep C widths E scope key loc T τ
  | .named s, loc, t, τ, T, ws, key, raw, rr, el, plain, wr, ag => by
      cases he : rawElem s with
      | some e =>
        obtain ⟨p, ws', el', read⟩ := leaf_elem (C := C) he
          (plain s (by simp [names]) (by rw [he]; rfl))
        rw [el] at el'; cases el'
        cases rr with
        | struct none => rw [he] at none; cases none
        | elem he' =>
          rw [he] at he'; cases he'
          have hel : Decode.elemB widths key p = some e := by
            rw [← elemB_congr (by simpa only [readTy] using ag) p, elemB_rebase]; exact read
          exact .prim hel (ReferenceDecode.elemB_prim hel loc)
      | none =>
        obtain ⟨table, ht, -, -, el'⟩ := leaf_struct (by simpa only [rawType] using raw) he
        rw [el] at el'; cases el'
        cases rr with
        | elem he' => rw [he] at he'; cases he'
        | struct _ _ _ hd => exact .struct (wr s (by simp [rawNames]) he table ht) hd
  | .array R, loc, t, τ, T, ws, key, raw, rr, el, plain, wr, ag => by
      simp only [rawType, bind_ok] at raw
      obtain ⟨t', ht, -⟩ := raw
      obtain ⟨T', w, el', rfl, rfl⟩ := elabTyW_array el
      cases rr with
      | array r => exact .array (rep R loc t' _ T' w _ ht r el' plain wr (by
          rw [← rebase_nest]; simpa only [readTy, readRef] using ag))
  | .fixed R n, loc, t, τ, T, ws, key, raw, rr, el, plain, wr, ag => by
      simp only [rawType] at raw
      split at raw; · cases raw
      simp only [bind_ok] at raw
      obtain ⟨t', ht, -⟩ := raw
      obtain ⟨T', w, el', rfl, rfl⟩ := elabTyW_fixed el
      cases rr with
      | fixed pos r => exact .fixed pos (rep R loc t' _ T' w _ ht r el' plain wr (by
          rw [← rebase_nest]; simpa only [readTy, readRef] using ag))
  | .mapping K V, loc, t, τ, T, ws, key, raw, rr, el, plain, wr, ag => by
      simp only [rawType] at raw
      split at raw
      · simp only [bind_ok] at raw
        obtain ⟨_, hk, t', ht, -⟩ := raw
        obtain ⟨k, e, _, rfl, -, he⟩ := rawKey_ok hk
        obtain ⟨p, kw, elk, read⟩ := leaf_elem (C := C) he
          (plain k (by simp [names]) (by rw [he]; rfl))
        obtain ⟨vt, vw, elv, rfl, rfl⟩ := elabTyW_mapping elk el
        have ag' := ag
        simp only [readTy] at ag'
        cases rr with
        | mapping he' r =>
          rw [he] at he'; cases he'
          have hel : Decode.elemB widths (key ++ "{}") p = some e := by
            rw [← elemB_congr (Agree.key ag') p, elemB_rebase]; exact read
          exact .mapping hel (ReferenceDecode.elemB_prim hel .memory)
            (rep V .storage t' _ vt vw _ ht r elv
              (fun s ms => plain s (by simp only [names, List.mem_append]; exact .inr ms))
              wr (Agree.value ag'))
      · cases raw

section Unit
variable {ps : Syn (.list (.part false))} (h : decode C = .ok ps)
  (hE : E.decls = pre ++ ps.collect (some c) ++ post)
include h hE

/-- **A struct leaf resolved from the tables**: a `Keyed` plain name is the one
written name of its entry's table and agrees with it (`StructTableAgreement.Agrees`:
the generated declaration, its `Resolved` identity, its fields). -/
theorem keyed_agrees (free : Free C c (pre ++ post)) (closed : Closed C) {s : Name}
    (keyed : Keyed C s) (enc : isEnc s = false) :
    ∃ table, C.structName? s = some table ∧ written? C table = some s ∧ Agrees C E c s table := by
  obtain ⟨table, ht⟩ := lookupBy_some_of_filter (w := s) (l := C.structs) fun hn => by
    have := keyed.1; rw [hn] at this; cases this
  have name : C.structName? s = some table := by unfold Contract.structName?; rw [ht]
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (keyed.2 table ht)
  cases (written?_iff hw s).1 ⟨name, enc⟩
  exact ⟨table, name, hw, agrees h hE free hw keyed.1 (closed _ (lookupBy_mem ht))⟩

/-- **Written struct leaves**: each struct leaf of a spelled type is, to `elabTyW`,
the table its name is keyed to, and agrees with that table. -/
theorem leaf_agrees (free : Free C c (pre ++ post)) (closed : Closed C) {R : RawTy}
    {loc : DataLoc} {t : Syn .typeName} (raw : rawType C loc R = .ok t) (tabled : Tabled C R)
    {s : Name} (ms : s ∈ rawNames R) (he : rawElem s = none) :
    ∃ table, C.structName? s = some table ∧
      elabTyW C (.named s) = .ok (.ref (.struct table), []) ∧
      written? C table = some s ∧ Agrees C E c s table := by
  obtain ⟨t', leaf⟩ := rawType_leaf R loc t raw s ms
  obtain ⟨table, ht, enc, -, el⟩ := leaf_struct leaf he
  obtain ⟨table', ht', hw, ag⟩ := keyed_agrees h hE free closed
    (tabled s ms he (by rw [ht]; rfl)) enc
  rw [ht] at ht'; cases ht'
  exact ⟨table, ht, el, hw, ag⟩

/-- **The bridge**: the Source type produced for a spelled `RawTy` represents the
model type `elabTyW` returns, at the generated rows rebased at the enclosing key,
with its struct leaves resolved from the decoded struct environment. -/
theorem rawType_agrees (free : Free C c (pre ++ post)) (closed : Closed C) {R : RawTy}
    {loc : DataLoc} {t : Syn .typeName} {T : Ty} {ws : List (String × Nat)} {key : Name}
    (raw : rawType C loc R = .ok t) (el : elabTyW C R = .ok (T, ws)) (plain : Plain C R)
    (tabled : Tabled C R) (rows : Agree (readTy key T) (rebase key ws) widths) :
    ∃ τ, t.tys E (some c) loc = some [τ] ∧ RawRep C E (some c) loc R τ ∧
      Rep C widths E (some c) key loc T τ := by
  obtain ⟨τ, typed, rr⟩ := rawType_typed R loc t raw fun s ms he => by
    obtain ⟨_, -, -, -, ag⟩ := leaf_agrees h hE free closed raw tabled ms he
    exact ⟨_, ag.resolved⟩
  refine ⟨τ, typed, rr, rep R loc t τ T ws key raw rr el plain (fun s ms he table ht => ?_) rows⟩
  obtain ⟨table', ht', -, hw, -⟩ := leaf_agrees h hE free closed raw tabled ms he
  rw [ht] at ht'; cases ht'; exact hw

/-- **The bridge among other binders' rows**: the generated rows of the key, between
rows that are not at or below it. -/
theorem rawType_agrees_below (free : Free C c (pre ++ post)) (closed : Closed C) {R : RawTy}
    {loc : DataLoc} {t : Syn .typeName} {T : Ty} {ws : List (String × Nat)} {key : Name}
    (raw : rawType C loc R = .ok t) (el : elabTyW C R = .ok (T, ws)) (plain : Plain C R)
    (tabled : Tabled C R) {before after : List (Name × Nat)}
    (apart : ∀ r ∈ before ++ after, ReferenceDecode.below key r.1 = false) :
    ∃ τ, t.tys E (some c) loc = some [τ] ∧ RawRep C E (some c) loc R τ ∧
      Rep C (before ++ rebase key ws ++ after) E (some c) key loc T τ :=
  rawType_agrees h hE free closed raw el plain tabled (agree_below apart)
end Unit

/-! ## Boundaries kept apart -/

/-- **Invalid location**: a mapping outside storage has no spelling, whatever
`elabTyW` reads. -/
theorem mapping_outside (K V : RawTy) {loc : DataLoc} (out : loc ≠ .storage) :
    ∃ err, rawType C loc (.mapping K V) = .error err := by
  simp only [rawType, if_neg out]; exact ⟨_, rfl⟩

/-- **Ambiguous or absent written name**: a table that no single identifier writes
is represented by no Source type. -/
theorem unwritten_no_rep {table key : Name} {loc : DataLoc} {τ : STy}
    (none : written? C table = none) :
    ¬ Rep C widths E scope key loc (.ref (.struct table)) τ := fun r => by
  cases r with
  | struct hw _ => rw [none] at hw; cases hw

/-- **Conflicting rows**: a primitive is represented only by the elementary type the
rows at its key spell. -/
theorem Rep.prim_elem {key : Name} {loc : DataLoc} {p : PrimTy} {τ : STy}
    (r : Rep C widths E scope key loc (.prim p) τ) :
    ∃ e, Decode.elemB widths key p = some e ∧ τ = e.ty loc := by
  cases r with
  | prim he _ => exact ⟨_, he, rfl⟩

end Solidity.Correctness.Lowering.Total.RawTypeAgreement
