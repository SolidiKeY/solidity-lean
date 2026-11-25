import Solidity.Correctness.Lowering.Total.StructDecode

/-!
# Struct references of a model type and the table entry of a written name

`refsTy` lists a type's struct table types with their elaboration location (a mapping
value in storage); `Rep.leaf` finds each one's `Rep.struct` leaf. `written_entry`: a
written name's first entry is the table type, or it has none and is the
`structName?` fallback. `decode_written`: a successful decoding writes every reference.
-/
namespace Solidity.Correctness.Lowering.Total.StructTableAgreement

open Solidity.Semantics (lookupBy structDef structWidths isEnc)
open Source (STy DataLoc)
open ReferenceDecode (spellType spellRef written? Resolved Rep structsTy structsRef bind_ok)
open StructDecode (Pairs members decode)

mutual
/-- The struct table types of a type, each at the location it is elaborated at. -/
def refsTy (loc : DataLoc) : Ty → List (Name × DataLoc)
  | .prim _ => []
  | .ref R => refsRef loc R
/-- `refsTy` of a reference type: a mapping's value is in storage. -/
def refsRef (loc : DataLoc) : RefTy → List (Name × DataLoc)
  | .struct s => [(s, loc)]
  | .array T | .fixed T _ => refsTy loc T
  | .mapping _ V => refsTy .storage V
end

mutual
theorem refsTy_names : (loc : DataLoc) → (T : Ty) → (refsTy loc T).map (·.1) = structsTy T
  | _, .prim _ => rfl
  | loc, .ref R => by simpa only [refsTy, structsTy] using refsRef_names loc R
theorem refsRef_names : (loc : DataLoc) → (R : RefTy) → (refsRef loc R).map (·.1) = structsRef R
  | _, .struct _ => rfl
  | loc, .array T | loc, .fixed T _ => by simpa only [refsRef, structsRef] using refsTy_names loc T
  | _, .mapping _ V => by simpa only [refsRef, structsRef] using refsTy_names .storage V
end

theorem mem_structsTy {loc : DataLoc} {T : Ty} {p : Name × DataLoc} (h : p ∈ refsTy loc T) :
    p.1 ∈ structsTy T := by
  rw [← refsTy_names loc T]; exact List.mem_map_of_mem h

variable {C : Contract} {widths : List (Name × Nat)} {E : Source.Env} {scope : Option String}

/-- **Every reference has its `Rep.struct` leaf**: at the listed location, with the
written name of its table type and the declaration that name resolves to. -/
theorem Rep.leaf {key : Name} {loc : DataLoc} {T : Ty} {τ : STy}
    (h : Rep C widths E scope key loc T τ) : ∀ p ∈ refsTy loc T, ∃ key' w d,
      written? C p.1 = some w ∧ Resolved E scope w d ∧
      Rep C widths E scope key' p.2 (.ref (.struct p.1)) (.struct p.2 d) := by
  induction h with
  | prim => intro p hp; simp [refsTy] at hp
  | array _ ih => intro p hp; exact ih p (by simpa only [refsTy, refsRef] using hp)
  | fixed _ _ ih => intro p hp; exact ih p (by simpa only [refsTy, refsRef] using hp)
  | mapping _ _ _ ih => intro p hp; exact ih p (by simpa only [refsTy, refsRef] using hp)
  | @struct key' _ _ w _ hw hd =>
    intro p hp
    simp only [refsTy, refsRef, List.mem_singleton] at hp
    subst hp
    exact ⟨key', w, _, hw, hd, .struct hw hd⟩

/-- A resolved name denotes the identity of the one declaration its lookup returns. -/
theorem Resolved.eq {w : Name} {d : Source.DeclName} {decl : Source.Decl}
    (h : Resolved E scope w d) (look : E.lookup scope w = [decl]) :
    d = ⟨decl.scope, decl.name⟩ := by
  obtain ⟨decl', look', _, rfl⟩ := h
  rw [look] at look'; cases look'; rfl

theorem Pairs.mem {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β}
    (h : Pairs R as bs) {a : α} (ha : a ∈ as) : ∃ b ∈ bs, R a b := by
  induction h with
  | nil => cases ha
  | cons r _ ih =>
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, r⟩
    · obtain ⟨b, hb, rb⟩ := ih ha; exact ⟨b, List.mem_cons_of_mem _ hb, rb⟩

/-- The first row of a key is a row. -/
theorem lookupBy_mem {α : Type} {w : Name} {e : α} {l : List (Name × α)}
    (h : lookupBy w l = some e) : (w, e) ∈ l := by
  rw [StructDecode.lookupBy_filter] at h
  cases hf : (l.filter (·.1 == w)) with
  | nil => rw [hf] at h; cases h
  | cons p ps =>
    rw [hf] at h; cases h
    have mem : p ∈ l.filter (·.1 == w) := by rw [hf]; exact List.mem_cons_self
    obtain ⟨inl, key⟩ := List.mem_filter.1 mem
    have : p.1 = w := by simpa using key
    rw [← this]; exact inl

theorem lookupBy_none {α : Type} {w : Name} {l : List (Name × α)}
    (h : lookupBy w l = none) : l.filter (·.1 == w) = [] := by
  rw [StructDecode.lookupBy_filter] at h
  cases hf : (l.filter (·.1 == w)) with
  | nil => rfl
  | cons p ps => rw [hf] at h; cases h

theorem lookupBy_some_of_filter {α : Type} {w : Name} {l : List (Name × α)}
    (h : l.filter (·.1 == w) ≠ []) : ∃ e, lookupBy w l = some e := by
  cases hl : lookupBy w l <;> first | exact absurd (lookupBy_none hl) h | exact ⟨_, rfl⟩

/-- **The entry of a written name**: its first entry is keyed to the table type, or it
has no entry and is the table name itself (the implicit fallback of `structName?`). -/
theorem written_entry {s w : Name} (hw : written? C s = some w) :
    lookupBy w C.structs = some s ∨ (lookupBy w C.structs = none ∧ w = s ∧
      (structDef s).isEmpty = false) := by
  have hn := ((ReferenceDecode.written?_iff hw w).2 rfl).1
  unfold Contract.structName? at hn
  split at hn
  · rename_i e he; cases hn; exact .inl he
  · rename_i he
    split at hn
    · cases hn
    · rename_i ne; cases hn; exact .inr ⟨he, rfl, by simpa using ne⟩

/-- **First entry**: whenever the written name has an entry, its first entry is the
table type, whatever later entries of the name hold. -/
theorem written_first {s w e : Name} (hw : written? C s = some w)
    (he : lookupBy w C.structs = some e) : e = s := by
  rcases written_entry hw with h | ⟨h, -⟩ <;> rw [he] at h <;> cases h; rfl

mutual
/-- A spelling that succeeds writes every struct it mentions. -/
theorem spellType_written : (T : Ty) → (key : Name) → (loc : DataLoc) → (t : Source.Syn .typeName) →
    spellType C widths key loc T = .ok t → ∀ s ∈ structsTy T, ∃ w, written? C s = some w
  | .prim _, _, _, _, _ => by simp [structsTy]
  | .ref R, key, loc, t, h => by
      simpa only [structsTy] using spellRef_written R key loc t (by simpa only [spellType] using h)
theorem spellRef_written : (R : RefTy) → (key : Name) → (loc : DataLoc) → (t : Source.Syn .typeName) →
    spellRef C widths key loc R = .ok t → ∀ s ∈ structsRef R, ∃ w, written? C s = some w
  | .struct s, key, loc, t, h => by
      simp only [spellRef] at h
      split at h
      · rename_i w hw; intro s' hs'
        simp only [structsRef, List.mem_singleton] at hs'; subst hs'; exact ⟨w, hw⟩
      · cases h
  | .array T, key, loc, t, h | .fixed T _, key, loc, t, h => by
      simp only [spellRef] at h; repeat' split at h
      all_goals first | cases h | obtain ⟨t', ht, -⟩ := bind_ok.1 h
      all_goals simpa only [structsRef] using spellType_written T _ loc t' ht
  | .mapping K V, key, loc, t, h => by
      simp only [spellRef] at h; repeat' split at h
      all_goals first | cases h | obtain ⟨t', ht, -⟩ := bind_ok.1 h
      simpa only [structsRef] using spellType_written V _ .storage t' ht
end

theorem members_written : ∀ {fs : List (Name × Ty)} {ms : Source.Syn (.list .structMember)},
    members C widths fs = .ok ms → ∀ x ∈ fs, ∀ s ∈ structsTy x.2, ∃ w, written? C s = some w
  | [], _, _, x, hx => by cases hx
  | y :: ys, ms, h, x, hx => by
      unfold members at h
      split at h
      · cases h
      · rename_i t ht
        simp only [bind_ok] at h
        obtain ⟨ms', hms, -⟩ := h
        rcases List.mem_cons.1 hx with rfl | hx
        · exact spellType_written _ _ _ t ht
        · exact members_written hms x hx

/-- **No absent or ambiguous written name** after a successful decoding: every struct a
member of an entry mentions is written by exactly one identifier. -/
theorem decode_written {ps : Source.Syn (.list (.part false))} (h : decode C = .ok ps)
    {entry : Name × Name} (he : entry ∈ C.structs) {x : Name × Ty} (hx : x ∈ structDef entry.2)
    {s : Name} (hs : s ∈ structsTy x.2) : ∃ w, written? C s = some w := by
  obtain ⟨⟨m, ms, hm⟩, -⟩ := (StructDecode.decode_ok_iff C).1 ⟨ps, h⟩ entry he
  exact members_written hm x hx s hs

end Solidity.Correctness.Lowering.Total.StructTableAgreement
