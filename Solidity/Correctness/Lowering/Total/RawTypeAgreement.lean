import Solidity.Correctness.Lowering.Total.RawTypeAgreement.Leaf
import Solidity.Correctness.Lowering.Total.StructTableAgreement

/-!
# A retained `RawTy` against its model type and resolved struct types

Closes the `RawTy` agreement `StructTableAgreement` leaves open. For `rawType C loc R = .ok t`
and the elaborator's own `elabTyW C R = .ok (T, ws)`, `rawType_agrees` derives that the Source
type of `t` (`rawType_typed`, with its `RawRep`) is `Rep` of `T` at a key, in any width table
agreeing with the generated rows rebased there (`rebase key ws`) on the keys the spelling of `T`
reads; `agree_surround` gives that among rows that are not read. Struct resolution is derived, in
`E.decls = pre ++ ps.collect (some c) ++ post` with `decode C = .ok ps`, from table facts
(`Closed`, `Free`, `Keyed` leaves) through `StructTableAgreement.agrees` (`leaf_agrees`).
Domain: `Plain` excludes an elementary name that is also an enum (`elabTyW` reads the enum).
`rawType` errors stay errors (enum, function, `bytes`/`string`, member-spelling names, other
keys, zero lengths, mappings outside storage), though `elabTyW` may succeed. The conclusion is
`Rep`, not a `spellType` equation (`bytes1[]` has no spelling there); an aliased table has no
`Rep`. Left to the decoder lane: these facts over the production domain, binding, frames.
-/
namespace Solidity.Correctness.Lowering.Total.RawTypeAgreement

open Solidity.Semantics (lookupBy isEnc)
open Source (Syn STy DataLoc)
open ReferenceDecode (rawElem rawLeaf rawType rawNames RawRep Rep written? readTy readRef
  rawKey_ok bind_ok rawType_typed written?_iff)
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
/-- Table facts of a struct name: one entry keys it, and one identifier writes that entry's
table (no alias, not shadowed). -/
def Keyed (C : Contract) (s : Name) : Prop := (C.structs.filter (·.1 == s)).length = 1 ∧
  ∀ table ∈ lookupBy s C.structs, (written? C table).isSome
instance (C : Contract) (s : Name) : Decidable (Keyed C s) := by unfold Keyed; infer_instance
/-- Every struct leaf of the type is `Keyed`. -/
def Tabled (C : Contract) (R : RawTy) : Prop :=
  ∀ s ∈ rawNames R, rawElem s = none → (C.structName? s).isSome → Keyed C s

variable {C : Contract} {c : String} {E : Source.Env} {scope : Option String}
  {pre post : List Source.Decl} {widths : List (Name × Nat)}

/-- `elabTyW` of an array or a fixed array: the element's rows under `[]`. -/
theorem elabTyW_array {R : RawTy} {m : Nat} {T : Ty} {ws : List (String × Nat)}
    (h : elabTyW C (.array R) = .ok (T, ws) ∨ elabTyW C (.fixed R m) = .ok (T, ws)) :
    ∃ T' w, elabTyW C R = .ok (T', w) ∧ ws = w.map (fun (k, n) => ("[]" ++ k, n)) ∧
      (T = .ref (.array T') ∨ T = .ref (.fixed T' m)) := by
  rw [elabTyW, elabTyW] at h
  cases h' : elabTyW C R with
  | error e => simp [h', bind, Except.bind] at h
  | ok x =>
    simp only [h', bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with h | h
    · exact ⟨x.1, x.2, rfl, h.2.symm, .inl h.1.symm⟩
    · exact ⟨x.1, x.2, rfl, h.2.symm, .inr h.1.symm⟩

/-- A mapping whose key name is a primitive to `elabTyW`: key rows under `{}`, value rows `[]`. -/
theorem elabTyW_mapping {k : String} {V : RawTy} {p : PrimTy} {kw : List (String × Nat)}
    {T : Ty} {ws : List (String × Nat)} (hk : elabTyW C (.named k) = .ok (.prim p, kw))
    (h : elabTyW C (.mapping (.named k) V) = .ok (T, ws)) :
    ∃ vt vw, elabTyW C V = .ok (vt, vw) ∧ T = .ref (.mapping p vt) ∧
      ws = kw.map (fun (k, n) => ("{}" ++ k, n)) ++ vw.map fun (k, n) => ("[]" ++ k, n) := by
  have dyn : dynBytesTy k = false := by
    cases d : dynBytesTy k <;> first | rfl | (rw [elabTyW, if_pos d] at hk; cases hk)
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
      simp only [rawType, bind_ok] at h; obtain ⟨t', ht, -⟩ := h
      exact rawType_leaf R loc t' ht s (by simpa only [rawNames] using hs)
  | .fixed R n, loc, t, h, s, hs => by
      simp only [rawType] at h; split at h; · cases h
      simp only [bind_ok] at h; obtain ⟨t', ht, -⟩ := h
      exact rawType_leaf R loc t' ht s (by simpa only [rawNames] using hs)
  | .mapping K V, loc, t, h, s, hs => by
      simp only [rawType] at h; split at h <;> first | cases h | skip
      simp only [bind_ok] at h; obtain ⟨_, -, t', ht, -⟩ := h
      exact rawType_leaf V .storage t' ht s (by simpa only [rawNames] using hs)

/-- The Source type a spelled `RawTy` denotes represents the model type `elabTyW` reads, at the
generated rows rebased at the key; each struct leaf's table written by the leaf's own name. -/
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
      simp only [rawType, bind_ok] at raw; obtain ⟨t', ht, -⟩ := raw
      obtain ⟨T', w, el', rfl, rfl | bad⟩ := elabTyW_array (m := 0) (.inl el)
      · cases rr with
        | array r => exact .array (rep R loc t' _ T' w _ ht r el' plain wr (by
            rw [← rebase_nest]; simpa only [readTy, readRef] using ag))
      · rw [elabTyW, el'] at el; subst bad; cases el
  | .fixed R n, loc, t, τ, T, ws, key, raw, rr, el, plain, wr, ag => by
      simp only [rawType] at raw; split at raw; · cases raw
      simp only [bind_ok] at raw; obtain ⟨t', ht, -⟩ := raw
      obtain ⟨T', w, el', rfl, bad | rfl⟩ := elabTyW_array (.inr el)
      · rw [elabTyW, el'] at el; subst bad; cases el
      · cases rr with
        | fixed pos r => exact .fixed pos (rep R loc t' _ T' w _ ht r el' plain wr (by
            rw [← rebase_nest]; simpa only [readTy, readRef] using ag))
  | .mapping K V, loc, t, τ, T, ws, key, raw, rr, el, plain, wr, ag => by
      simp only [rawType] at raw; split at raw <;> first | cases raw | skip
      simp only [bind_ok] at raw; obtain ⟨_, hk, t', ht, -⟩ := raw
      obtain ⟨k, e, _, rfl, -, he⟩ := rawKey_ok hk
      obtain ⟨p, kw, elk, read⟩ := leaf_elem (C := C) he
        (plain k (by simp [names]) (by rw [he]; rfl))
      obtain ⟨vt, vw, elv, rfl, rfl⟩ := elabTyW_mapping elk el
      simp only [readTy] at ag
      cases rr with
      | mapping he' r =>
        rw [he] at he'; cases he'
        have hel : Decode.elemB widths (key ++ "{}") p = some e := by
          rw [← elemB_congr (Agree.keyRows ag) p, elemB_rebase]; exact read
        exact .mapping hel (ReferenceDecode.elemB_prim hel .memory) (rep V .storage t' _ vt vw _ ht r
          elv (fun s ms => plain s (by simp only [names, List.mem_append]; exact .inr ms)) wr
          (Agree.valueRows ag))

variable {ps : Syn (.list (.part false))} (h : decode C = .ok ps)
  (hE : E.decls = pre ++ ps.collect (some c) ++ post) (free : Free C c (pre ++ post))
  (closed : Closed C) {R : RawTy} {loc : DataLoc} {t : Syn .typeName}
include h hE free closed

/-- **Written struct leaves**: each struct leaf of a spelled type is, to `elabTyW`, the table
its name is keyed to, is that table's one written name, and agrees with the table
(`StructTableAgreement.Agrees`: the generated declaration, its `Resolved` identity, its fields). -/
theorem leaf_agrees (raw : rawType C loc R = .ok t) (tabled : Tabled C R) {s : Name}
    (ms : s ∈ rawNames R) (he : rawElem s = none) : ∃ table, C.structName? s = some table ∧
      elabTyW C (.named s) = .ok (.ref (.struct table), []) ∧ written? C table = some s ∧
      Agrees C E c s table := by
  obtain ⟨t', leaf⟩ := rawType_leaf R loc t raw s ms
  obtain ⟨table, name, enc, -, el⟩ := leaf_struct leaf he
  have keyed := tabled s ms he (by rw [name]; rfl)
  obtain ⟨table', ht⟩ := lookupBy_some_of_filter (w := s) (l := C.structs) fun hn => by
    have := keyed.1; rw [hn] at this; cases this
  cases name.symm.trans (show C.structName? s = some table' by unfold Contract.structName?; rw [ht])
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (keyed.2 table ht)
  cases (written?_iff hw s).1 ⟨name, enc⟩
  exact ⟨table, name, el, hw, agrees h hE free hw keyed.1 (closed _ (lookupBy_mem ht))⟩

/-- **The bridge**: the Source type produced for a spelled `RawTy` represents the model type
`elabTyW` returns, at the generated rows rebased at the enclosing key, with its struct leaves
resolved from the decoded struct environment. -/
theorem rawType_agrees {T : Ty} {ws : List (String × Nat)} {key : Name}
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

end Solidity.Correctness.Lowering.Total.RawTypeAgreement
