import Solidity.Yul.CatalogLaws

/-! Checked external-reference construction for a supplied intrinsic declaration
table. Declaration provenance, namespace freshness and whole-block checking are
separate obligations; no physical or dirty-word execution meaning is asserted. -/
namespace Solidity.Yul

abbrev ExternalDeclRef (X : List ExternalType) := (ty : ExternalType) × Member X ty
abbrev ExternalNames (X : List ExternalType) := List (String × ExternalDeclRef X)

/-- Independent spelling of the supported external attributes. -/
inductive SuffixD : List String → Attribute → Prop where
  | plain : SuffixD [] .plain
  | slot : SuffixD ["slot"] .slot
  | offset : SuffixD ["offset"] .offset
  | length : SuffixD ["length"] .length
  | selector : SuffixD ["selector"] .selector
  | address : SuffixD ["address"] .address

def checkSuffix : List String → Option Attribute
  | [] => some .plain
  | [name] =>
    if name = "slot" then some .slot else
    if name = "offset" then some .offset else
    if name = "length" then some .length else
    if name = "selector" then some .selector else
    if name = "address" then some .address else none
  | _ => none

theorem SuffixD.complete {suffix a} (d : SuffixD suffix a) : checkSuffix suffix = some a := by
  cases d <;> rfl

theorem checkSuffix_sound {suffix : List String} {a : Attribute}
    (h : checkSuffix suffix = some a) : SuffixD suffix a := by
  cases suffix with
  | nil => cases h; exact .plain
  | cons name rest =>
    cases rest with
    | cons _ _ => cases h
    | nil =>
      dsimp only [checkSuffix] at h
      split at h
      · next hn => subst name; cases h; exact .slot
      · split at h
        · next hn => subst name; cases h; exact .offset
        · split at h
          · next hn => subst name; cases h; exact .length
          · split at h
            · next hn => subst name; cases h; exact .selector
            · split at h
              · next hn => subst name; cases h; exact .address
              · cases h

/-- Exact capability completeness, not only an isSome test. -/
theorem Access.complete {ty a w} (cap : Access ty a w) : checkAccess ty a w = some cap := by
  cases cap <;> first | rfl | (rename_i l t; cases l <;> rfl)

/-- Independent declaration lookup, suffix spelling and typed capability. -/
inductive ExternalD {X : List ExternalType} (decls : ExternalNames X) (write : Bool) :
    String → List String → ExternalRef X write → Type where
  | intro {name suffix ty} (index : Member X ty) {attr : Attribute}
      (binding : Resolves decls name ⟨ty, index⟩) (spelling : SuffixD suffix attr)
      (cap : Access ty attr write) :
      ExternalD decls write name suffix ⟨index, attr, cap⟩

def LegalExternal {X : List ExternalType} (decls : ExternalNames X)
    (name : String) (suffix : List String) (write : Bool) : Prop :=
  ∃ (ty : ExternalType) (index : Member X ty) (attr : Attribute),
    Resolves decls name ⟨ty, index⟩ ∧ SuffixD suffix attr ∧ LegalAccess ty attr write

/-- Build the intrinsic reference only after declaration, attribute and direction
checking. This is static construction; tier/safety admission remains separate. -/
def checkExternal {X : List ExternalType} (decls : ExternalNames X)
    (name : String) (suffix : List String) (write : Bool) :
    Option ((ref : ExternalRef X write) × ExternalD decls write name suffix ref) :=
  match hs : checkSuffix suffix with
  | none => none
  | some attr => match hd : resolve decls name with
    | none => none
    | some ⟨ty, index⟩ => match _hc : checkAccess ty attr write with
      | none => none
      | some cap => some ⟨⟨index, attr, cap⟩, .intro index (resolve_sound hd) (checkSuffix_sound hs) cap⟩

theorem ExternalD.complete {X decls write name suffix ref}
    (d : @ExternalD X decls write name suffix ref) : checkExternal decls name suffix write = some ⟨ref, d⟩ := by
  cases d with
  | @intro ty index attr binding spelling cap =>
    unfold checkExternal
    split
    · next hs => have hc := spelling.complete; rw [hs] at hc; cases hc
    · next a hs =>
      have he : a = attr := Option.some.inj (hs.symm.trans spelling.complete)
      subst a
      split
      · next hd => have hc := resolve_complete binding; rw [hd] at hc; cases hc
      · next ty' index' hd =>
        have he := Option.some.inj (hd.symm.trans (resolve_complete binding))
        cases he
        split
        · next hc => have hh := cap.complete; rw [hc] at hh; cases hh
        · next cap' hc =>
          have he : cap' = cap := Option.some.inj (hc.symm.trans cap.complete)
          subst cap'
          rfl

theorem ExternalD.legal {X decls write name suffix ref}
    (d : @ExternalD X decls write name suffix ref) : LegalExternal decls name suffix write := by
  cases d with
  | intro index binding spelling cap =>
    refine ⟨_, index, _, binding, spelling, ?_⟩
    apply (checkAccess_iff _ _ _).mp
    rw [cap.complete]
    rfl

/-- Sound and complete against independent lookup/spelling/access legality.
No declaration-environment validity, tier or memory-safety premise is inferred. -/
theorem checkExternal_iff {X : List ExternalType} (decls : ExternalNames X)
    (name : String) (suffix : List String) (write : Bool) :
    (checkExternal decls name suffix write).isSome = true ↔ LegalExternal decls name suffix write := by
  constructor
  · intro h
    cases hc : checkExternal decls name suffix write with
    | none => rw [hc] at h; cases h
    | some result => exact result.2.legal
  · rintro ⟨ty, index, attr, binding, spelling, legal⟩
    have h := (checkAccess_iff ty attr write).mpr legal
    cases hc : checkAccess ty attr write with
    | none => rw [hc] at h; cases h
    | some cap =>
      rw [ExternalD.complete (.intro index binding spelling cap)]
      rfl

end Solidity.Yul
