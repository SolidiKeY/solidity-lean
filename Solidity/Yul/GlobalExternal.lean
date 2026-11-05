import Solidity.Yul.ExternalCheck

/-! Function-boundary external resolution. Resolve in the original visible
Solidity declaration table BEFORE checking capturability; filtering declarations
first could incorrectly expose a shadowed global. Provenance/freshness of the
supplied table, whole-block construction and execution remain separate. -/
namespace Solidity.Yul

/-- Reindex a global declaration into the function's global-only context. -/
def Member.intoGlobals {X : List ExternalType} {ty : ExternalType} (i : Member X ty)
    (h : ty.isGlobal = true) : Member (globals X) ty := by
  apply Member.casesOn (motive := fun X ty _ => ty.isGlobal = true → Member (globals X) ty) i
  case here =>
    intro a rest ha
    simp only [globals, List.filter_cons, ha, ↓reduceIte]
    exact .here
  case there =>
    intro a b rest j ha
    by_cases hb : b.isGlobal = true
    · simp only [globals, List.filter_cons, hb, ↓reduceIte]
      exact .there (j.intoGlobals ha)
    · simp only [globals, List.filter_cons, hb]
      exact j.intoGlobals ha
  case a => exact h
termination_by structural i

def ExternalRef.toGlobals {X : List ExternalType} {w : Bool} (ref : ExternalRef X w)
    (h : ref.ty.isGlobal = true) : ExternalRef (globals X) w :=
  ⟨ref.index.intoGlobals h, ref.attr, ref.access⟩

/-- No global Solidity binding has a writable Yul suffix/plain capability.
World-effect builtins such as sstore are not external-variable assignments. -/
theorem Access.write_not_global {ty attr} (cap : Access ty attr true) : ty.isGlobal = false := by
  cases cap <;> rfl

inductive GlobalExternalD {X : List ExternalType} (decls : ExternalNames X) (write : Bool)
    (name : String) (suffix : List String) : ExternalRef (globals X) write → Type where
  | intro {ref : ExternalRef X write} (resolution : ExternalD decls write name suffix ref)
      (global : ref.ty.isGlobal = true) : GlobalExternalD decls write name suffix (ref.toGlobals global)

def LegalGlobalExternal {X : List ExternalType} (decls : ExternalNames X)
    (name : String) (suffix : List String) (write : Bool) : Prop :=
  ∃ (ty : ExternalType) (index : Member X ty) (attr : Attribute),
    Resolves decls name ⟨ty, index⟩ ∧ SuffixD suffix attr ∧ LegalAccess ty attr write ∧ ty.isGlobal = true

/-- No fallback is made when the visible declaration is local or its attribute
is illegal. Globals are reindexed only after original-scope resolution. -/
def checkGlobalExternal {X : List ExternalType} (decls : ExternalNames X)
    (name : String) (suffix : List String) (write : Bool) :
    Option ((ref : ExternalRef (globals X) write) × GlobalExternalD decls write name suffix ref) :=
  match checkExternal decls name suffix write with
  | none => none
  | some ⟨ref, resolution⟩ =>
    if h : ref.ty.isGlobal = true then some ⟨ref.toGlobals h, .intro resolution h⟩ else none

theorem GlobalExternalD.complete {X decls write name suffix ref}
    (d : @GlobalExternalD X decls write name suffix ref) :
    checkGlobalExternal decls name suffix write = some ⟨ref, d⟩ := by
  cases d with
  | intro resolution global =>
    unfold checkGlobalExternal
    rw [resolution.complete]
    simp only [dif_pos global]

theorem GlobalExternalD.legal {X decls write name suffix ref}
    (d : @GlobalExternalD X decls write name suffix ref) : LegalGlobalExternal decls name suffix write := by
  cases d with
  | intro resolution global =>
    cases resolution with
    | intro index binding spelling cap =>
      refine ⟨_, index, _, binding, spelling, ?_, global⟩
      apply (checkAccess_iff _ _ _).mp
      rw [cap.complete]
      rfl

theorem GlobalExternalD.noWrites {X decls name suffix ref}
    (d : @GlobalExternalD X decls true name suffix ref) : False := by
  cases d with
  | intro resolution global =>
    cases resolution with
    | intro index binding spelling cap =>
      have h := cap.write_not_global
      rw [global] at h
      cases h

/-- Independent original-scope resolution plus global-only visibility is both
necessary and sufficient; filtering a shadowing table is not the relation. -/
theorem checkGlobalExternal_iff {X : List ExternalType} (decls : ExternalNames X)
    (name : String) (suffix : List String) (write : Bool) :
    (checkGlobalExternal decls name suffix write).isSome = true ↔ LegalGlobalExternal decls name suffix write := by
  constructor
  · intro h
    cases hc : checkGlobalExternal decls name suffix write with
    | none => rw [hc] at h; cases h
    | some result => exact result.2.legal
  · rintro ⟨ty, index, attr, binding, spelling, legal, global⟩
    have h := (checkAccess_iff ty attr write).mpr legal
    cases hc : checkAccess ty attr write with
    | none => rw [hc] at h; cases h
    | some cap =>
      rw [GlobalExternalD.complete (.intro (.intro index binding spelling cap) global)]
      rfl

theorem checkGlobalExternal_write_refused {X : List ExternalType} (decls : ExternalNames X)
    (name : String) (suffix : List String) :
    (checkGlobalExternal decls name suffix true).isSome = false := by
  cases hc : checkGlobalExternal decls name suffix true with
  | none => rfl
  | some result => exact False.elim result.2.noWrites

end Solidity.Yul
