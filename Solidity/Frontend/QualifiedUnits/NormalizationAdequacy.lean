import Solidity.Frontend.QualifiedUnits.SignatureNormalization
import Solidity.Frontend.QualifiedUnits.ReferenceCoverage

/-! Structural adequacy of signature normalization against Source elaboration.

`erase` forgets the original declaration identity of a nominal leaf,
keeping only the `DeclName` (scope and spelling) that `Source.Syn.tys` uses.
Away from nominal leaves the two elaborators must coincide: `types_sound`
shows every normalized key list erases to the Source elaboration, and
`types_complete` shows every type the Source elaborator accepts in a
supported signature category (type names, parameters, event and error
parameters, and their lists) normalizes. Their premises speak only about
the nominal leaves written in the syntax itself (`references s`): `userTy`
versus qualified `nominal` lookup, exactly where the two are meant to
differ, identities versus spellings. Where Source `userTy` cannot follow
(unit aliases, deeper paths, homonyms visible to its flat environment) the
premises fail for that syntax and the theorems say nothing about it.
`TargetControls.adequacy_instance` discharges them for a cross-unit program
with a same-spelled enum in an unimported unit. The statement concerns
`types`, the parameter elaboration that `normalize` uses.

Array lengths reuse `Source.arrayLen` in both; no constant evaluator is
added. Struct members and variable declarations are outside signature
categories and normalize to `none`; `fields_refused` records that. This is
adequacy relative to the existing Source elaborator, not solc type
checking (G13) or external Solidity correctness. -/
namespace Solidity.Frontend.QualifiedUnits.NormalizationAdequacy
open Solidity.Source SignatureNormalization

/-- The Source-level name of an original declaration identity. -/
def declName (P : UnitSet) (i : DeclId) : DeclName :=
  match P.decl? i with
  | some d => ⟨d.scope, d.name⟩
  | none => ⟨none, ""⟩

mutual

/-- Forget nominal identities, keeping the Source `DeclName`. -/
def erase {P : UnitSet} : TypeKey P → STy
  | .integer t => .int t
  | .boolean => .bool
  | .address p => .address p
  | .fixedBytes n v => .fixedBytes n v
  | .fixedPoint t => .fixed t
  | .bytes l => .bytes l
  | .string l => .string l
  | .enumeration r => .enum (declName P r.val)
  | .valueType r => .udvt (declName P r.val)
  | .contract r => .contract (declName P r.val)
  | .record l r => .struct l (declName P r.val)
  | .array l e n => .array l (erase e) n
  | .mapping k v => .mapping (erase k) (erase v)
  | .callable e ps rs m => .fn e (eraseList ps) (eraseList rs) m

def eraseList {P : UnitSet} : List (TypeKey P) → List STy
  | [] => []
  | k :: ks => erase k :: eraseList ks

end

theorem eraseList_eq {P : UnitSet} : (ks : List (TypeKey P)) → eraseList ks = ks.map erase
  | [] => rfl
  | k :: ks => by simp only [eraseList, List.map_cons, eraseList_eq ks]

theorem elementary_erase {P : UnitSet} (loc : DataLoc) (e : Elem) :
    erase (elementary P loc e) = e.ty loc := by
  cases e with
  | fixed s dims => cases dims <;> rfl
  | _ => rfl

/-- On the paths `S`, normalized nominal leaves erase to the Source user type.
The theorems below take `S := references s`: only the paths written in the
signature syntax itself, not every path of the program. -/
abbrev LeafSound (P : UnitSet) (R : List Remapping) (u : String) (scope : Option DeclId)
    (E : Env) (sc : Option String) (S : List IdPath) : Prop :=
  ∀ loc p k, p ∈ S → nominal P R u scope loc p = some k → E.userTy sc loc p = some (erase k)

/-- On the paths `S`, every Source user type also has a qualified nominal leaf. -/
abbrev LeafComplete (P : UnitSet) (R : List Remapping) (u : String) (scope : Option DeclId)
    (E : Env) (sc : Option String) (S : List IdPath) : Prop :=
  ∀ loc p τ, p ∈ S → E.userTy sc loc p = some τ → ∃ k, nominal P R u scope loc p = some k

theorem root_refs {c : Cat} {s : Syn c} {S : List IdPath} (hS : ∀ p, p ∈ references s → p ∈ S) :
    ∀ p, p ∈ rootReferences s → p ∈ S := fun p hp =>
  hS p (by rw [references_eq]; exact List.mem_append_left _ hp)

theorem child_refs {c c' : Cat} {s : Syn c} {t : Syn c'} {S : List IdPath}
    (hS : ∀ p, p ∈ references s → p ∈ S) (h : (⟨c', t⟩ : Σ c, Syn c) ∈ s.children) :
    ∀ p, p ∈ references t → p ∈ S := fun p hp =>
  hS p (by rw [references_eq s]; exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, h, hp⟩))

theorem keyType_sound {P : UnitSet} {R : List Remapping} {u : String} {scope : Option DeclId}
    {E : Env} {sc : Option String} {S : List IdPath} (hl : LeafSound P R u scope E sc S) {k : MapKey}
    (hk : ∀ p, p ∈ k.paths → p ∈ S) {key : TypeKey P}
    (h : keyType P R u scope k = some key) : E.keyTy sc k = some (erase key) := by
  cases k with
  | elem e _ =>
    simp only [keyType, Option.some.injEq] at h
    subst key
    simp only [Env.keyTy, elementary_erase]
  | path p =>
    simp only [keyType] at h
    cases hn : nominal P R u scope .memory p with
    | none => rw [hn] at h; cases h
    | some r =>
      rw [hn] at h
      have hu := hl _ _ _ (hk p (List.mem_singleton_self p)) hn
      cases r <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst key <;>
        simp only [Env.keyTy, hu, erase]

theorem keyType_complete {P : UnitSet} {R : List Remapping} {u : String} {scope : Option DeclId}
    {E : Env} {sc : Option String} {S : List IdPath} (hl : LeafSound P R u scope E sc S)
    (hc : LeafComplete P R u scope E sc S) {k : MapKey} (hk : ∀ p, p ∈ k.paths → p ∈ S)
    {τ : STy} (h : E.keyTy sc k = some τ) : ∃ key, keyType P R u scope k = some key := by
  cases k with
  | elem e _ => exact ⟨_, rfl⟩
  | path p =>
    simp only [Env.keyTy] at h
    cases hu : E.userTy sc .memory p with
    | none => rw [hu] at h; cases h
    | some σ =>
      have hp := hk p (List.mem_singleton_self p)
      obtain ⟨r, hr⟩ := hc _ _ _ hp hu
      have he := hl _ _ _ hp hr
      rw [hu, Option.some.injEq] at he
      simp only [keyType, hr]
      cases r with
      | record l ref =>
        subst σ
        simp only [hu, erase, reduceCtorEq] at h
      | _ => exact ⟨_, rfl⟩

/-- Soundness: every normalized key list erases to the Source elaboration. -/
theorem types_sound {P : UnitSet} {R : List Remapping} {u : String} {scope : Option DeclId}
    {E : Env} {sc : Option String} {S : List IdPath} (hl : LeafSound P R u scope E sc S) :
    ∀ {c : Cat} (s : Syn c), (∀ p, p ∈ references s → p ∈ S) → ∀ {loc : DataLoc} {ks : List (TypeKey P)},
      types P R u scope loc s = some ks → s.tys E sc loc = some (ks.map erase) := by
  intro c s
  induction s
  all_goals intro hS loc ks h
  all_goals first | exact Option.noConfusion h | skip
  case nil =>
    change some [] = some ks at h
    cases h; rfl
  case cons a rest iha ihr =>
    change (match types P R u scope loc a, types P R u scope loc rest with
      | some first, some rest => some (first ++ rest)
      | _, _ => none) = some ks at h
    split at h
    · rename_i first tail ha hr
      cases h
      simp only [Syn.tys, iha (child_refs hS (by first | exact List.mem_cons_self | exact List.mem_cons_of_mem _ List.mem_cons_self)) ha, ihr (child_refs hS (by first | exact List.mem_cons_self | exact List.mem_cons_of_mem _ List.mem_cons_self)) hr, List.map_append]
    · cases h
  case eventParam t _ _ ih =>
    change types P R u scope .memory t = some ks at h
    simp only [Syn.tys]; exact ih (child_refs hS (by first | exact List.mem_cons_self | exact List.mem_cons_of_mem _ List.mem_cons_self)) h
  case errorParam t _ ih =>
    change types P R u scope .memory t = some ks at h
    simp only [Syn.tys]; exact ih (child_refs hS (by first | exact List.mem_cons_self | exact List.mem_cons_of_mem _ List.mem_cons_self)) h
  case param t l _ ih =>
    change types P R u scope (l.getD loc) t = some ks at h
    simp only [Syn.tys]; exact ih (child_refs hS (by first | exact List.mem_cons_self | exact List.mem_cons_of_mem _ List.mem_cons_self)) h
  case elem e =>
    change some [elementary P loc e] = some ks at h
    cases h
    simp only [Syn.tys, List.map_cons, List.map_nil, elementary_erase]
  case fnType ps vis m rs ihp ihr =>
    change (match types P R u scope .memory ps, types P R u scope .memory rs with
      | some ps, some rs => some [TypeKey.callable (vis == some .external) ps rs m]
      | _, _ => none) = some ks at h
    split at h
    · rename_i a b ha hb
      cases h
      simp only [Syn.tys, ihp (child_refs hS (by first | exact List.mem_cons_self | exact List.mem_cons_of_mem _ List.mem_cons_self)) ha, ihr (child_refs hS (by first | exact List.mem_cons_self | exact List.mem_cons_of_mem _ List.mem_cons_self)) hb, List.map_cons, List.map_nil, erase, eraseList_eq]
    · cases h
  case mapping k kn v vn ih =>
    change (if loc = .storage then
      (match keyType P R u scope k, types P R u scope .storage v with
        | some k, some [v] => some [TypeKey.mapping k v]
        | _, _ => none) else none) = some ks at h
    split at h
    · rename_i hs
      split at h
      · rename_i key val hk hv
        cases h
        have := ih (child_refs hS (by first | exact List.mem_cons_self | exact List.mem_cons_of_mem _ List.mem_cons_self)) hv
        simp only [List.map_cons, List.map_nil] at this
        have hkey := keyType_sound hl (root_refs (s := .mapping k kn v vn) hS) hk
        simp only [Syn.tys, hs, if_true, hkey, this, List.map_cons, List.map_nil, erase]
      · cases h
    · cases h
  case userType p =>
    change (nominal P R u scope loc p).map ([·]) = some ks at h
    cases hn : nominal P R u scope loc p with
    | none => rw [hn] at h; cases h
    | some k =>
      rw [hn] at h; cases h
      simp only [Syn.tys, hl _ _ _ (root_refs (s := .userType p) hS p (List.mem_singleton_self p)) hn,
        Option.map_some, List.map_cons, List.map_nil]
  case array t len iht _ =>
    change (match types P R u scope loc t, arrayLen len with
      | some [element], some length => some [TypeKey.array loc element length]
      | _, _ => none) = some ks at h
    split at h
    · rename_i el n ht hn
      cases h
      have := iht (child_refs hS (by first | exact List.mem_cons_self | exact List.mem_cons_of_mem _ List.mem_cons_self)) ht
      simp only [List.map_cons, List.map_nil] at this
      simp only [Syn.tys, this, hn, List.map_cons, List.map_nil, erase]
    · cases h

/-- Signature categories: type names, parameters, event/error parameters and lists. -/
def Supported : Cat → Bool
  | .typeName | .param | .eventParam | .errorParam => true
  | .list c => Supported c
  | _ => false

/-- Supported-type completeness: every type the Source elaborator accepts in a
signature category has a normalized key list. -/
theorem types_complete {P : UnitSet} {R : List Remapping} {u : String} {scope : Option DeclId}
    {E : Env} {sc : Option String} {S : List IdPath} (hl : LeafSound P R u scope E sc S)
    (hc : LeafComplete P R u scope E sc S) :
    ∀ {c : Cat} (s : Syn c), Supported c = true → (∀ p, p ∈ references s → p ∈ S) →
      ∀ {loc : DataLoc} {τs : List STy}, s.tys E sc loc = some τs → ∃ ks, types P R u scope loc s = some ks := by
  intro c s
  induction s
  all_goals intro hs hS loc τs h
  all_goals first | (simp only [Supported, Bool.false_eq_true] at hs; done) | skip
  case nil => exact ⟨[], rfl⟩
  case cons a rest iha ihr =>
    simp only [Syn.tys] at h
    split at h
    · rename_i x y ha hb
      obtain ⟨first, hf⟩ := iha hs (child_refs hS (by first | exact List.mem_cons_self | exact List.mem_cons_of_mem _ List.mem_cons_self)) ha
      obtain ⟨tail, ht⟩ := ihr hs (child_refs hS (by first | exact List.mem_cons_self | exact List.mem_cons_of_mem _ List.mem_cons_self)) hb
      refine ⟨first ++ tail, ?_⟩
      show (match types P R u scope loc a, types P R u scope loc rest with
        | some first, some rest => some (first ++ rest)
        | _, _ => none) = _
      rw [hf, ht]
    · cases h
  case eventParam t _ _ ih =>
    simp only [Syn.tys] at h
    exact ih rfl (child_refs hS (by first | exact List.mem_cons_self | exact List.mem_cons_of_mem _ List.mem_cons_self)) h
  case errorParam t _ ih =>
    simp only [Syn.tys] at h
    exact ih rfl (child_refs hS (by first | exact List.mem_cons_self | exact List.mem_cons_of_mem _ List.mem_cons_self)) h
  case param t l _ ih =>
    simp only [Syn.tys] at h
    exact ih rfl (child_refs hS (by first | exact List.mem_cons_self | exact List.mem_cons_of_mem _ List.mem_cons_self)) h
  case elem e => exact ⟨_, rfl⟩
  case fnType ps vis m rs ihp ihr =>
    simp only [Syn.tys] at h
    split at h
    · rename_i x y ha hb
      obtain ⟨a, hpa⟩ := ihp rfl (child_refs hS (by first | exact List.mem_cons_self | exact List.mem_cons_of_mem _ List.mem_cons_self)) ha
      obtain ⟨b, hrb⟩ := ihr rfl (child_refs hS (by first | exact List.mem_cons_self | exact List.mem_cons_of_mem _ List.mem_cons_self)) hb
      refine ⟨[TypeKey.callable (vis == some Visibility.external) a b m], ?_⟩
      show (match types P R u scope .memory ps, types P R u scope .memory rs with
        | some ps, some rs => some [TypeKey.callable (vis == some Visibility.external) ps rs m]
        | _, _ => none) = _
      rw [hpa, hrb]
    · cases h
  case mapping k kn v vn ih =>
    simp only [Syn.tys] at h
    split at h
    · rename_i hst
      split at h
      · rename_i τk τv hk hv
        obtain ⟨key, hkey⟩ := keyType_complete hl hc (root_refs (s := .mapping k kn v vn) hS) hk
        have hv' := child_refs (t := v) hS (by first | exact List.mem_cons_self | exact List.mem_cons_of_mem _ List.mem_cons_self)
        obtain ⟨vals, hvals⟩ := ih rfl hv' hv
        have hsv := types_sound hl v hv' hvals
        rw [hv, Option.some.injEq] at hsv
        cases vals with
        | nil => cases hsv
        | cons val rest =>
          cases rest with
          | cons _ _ => cases hsv
          | nil =>
            refine ⟨[TypeKey.mapping key val], ?_⟩
            show (if loc = .storage then
              (match keyType P R u scope k, types P R u scope .storage v with
                | some k, some [v] => some [TypeKey.mapping k v]
                | _, _ => none) else none) = _
            rw [if_pos hst, hkey, hvals]
      · cases h
    · cases h
  case userType p =>
    simp only [Syn.tys] at h
    cases hu : E.userTy sc loc p with
    | none => rw [hu] at h; cases h
    | some τ =>
      obtain ⟨k, hk⟩ := hc _ _ _ (root_refs (s := .userType p) hS p (List.mem_singleton_self p)) hu
      refine ⟨[k], ?_⟩
      show (nominal P R u scope loc p).map ([·]) = _
      rw [hk]; rfl
  case array t len iht _ =>
    simp only [Syn.tys] at h
    split at h
    · rename_i τ n ht hn
      have ht' := child_refs (t := t) hS (by first | exact List.mem_cons_self | exact List.mem_cons_of_mem _ List.mem_cons_self)
      obtain ⟨els, hels⟩ := iht rfl ht' ht
      have hse := types_sound hl t ht' hels
      rw [ht, Option.some.injEq] at hse
      cases els with
      | nil => cases hse
      | cons el rest =>
        cases rest with
        | cons _ _ => cases hse
        | nil =>
          refine ⟨[TypeKey.array loc el n], ?_⟩
          show (match types P R u scope loc t, arrayLen len with
            | some [element], some length => some [TypeKey.array loc element length]
            | _, _ => none) = _
          rw [hels, hn]
    · cases h

/-- Adequacy: on signature categories normalization erases exactly to the
existing Source elaboration, success and failure alike. -/
theorem types_adequate {P : UnitSet} {R : List Remapping} {u : String} {scope : Option DeclId}
    {E : Env} {sc : Option String} {c : Cat} (s : Syn c)
    (hl : LeafSound P R u scope E sc (references s)) (hc : LeafComplete P R u scope E sc (references s))
    (hs : Supported c = true) (loc : DataLoc) :
    (types P R u scope loc s).map (·.map erase) = s.tys E sc loc := by
  cases ht : types P R u scope loc s with
  | some ks => rw [types_sound hl s (fun _ hp => hp) ht]; rfl
  | none =>
    cases hty : s.tys E sc loc with
    | none => rfl
    | some τs =>
      obtain ⟨ks, hks⟩ := types_complete hl hc s hs (fun _ hp => hp) hty
      rw [ht] at hks; cases hks

/-- Struct members and variable declarations are not signature syntax. -/
theorem fields_refused {P : UnitSet} {R : List Remapping} {u : String} {scope : Option DeclId}
    (loc : DataLoc) (t : Syn .typeName) (n : String) (l : Option DataLoc) :
    types P R u scope loc (.structMember t n) = none ∧ types P R u scope loc (.varDecl t l n) = none :=
  ⟨rfl, rfl⟩

end Solidity.Frontend.QualifiedUnits.NormalizationAdequacy
