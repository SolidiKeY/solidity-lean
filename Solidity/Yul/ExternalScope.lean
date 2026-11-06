import Solidity.Yul.GlobalExternal

/-! Nested Yul-function external contexts. Resolve in the ORIGINAL supplied
Solidity declaration table before lifting the selected occurrence through each
function boundary. No declaration filtering/retry can expose a shadowed global.
Names/table provenance and whole-block construction remain separate. -/
namespace Solidity.Yul

inductive ExternalScope (rootTypes : List ExternalType) : List ExternalType → Type where
  | root : ExternalScope rootTypes rootTypes
  | function {X} : ExternalScope rootTypes X → ExternalScope rootTypes (globals X)

/-- Independent occurrence-preserving visibility/reindexing across boundaries. -/
inductive ScopeIndexD {rootTypes : List ExternalType} :
    {X : List ExternalType} → ExternalScope rootTypes X →
      {ty : ExternalType} → Member rootTypes ty → Member X ty → Type where
  | root {ty} (index : Member rootTypes ty) : ScopeIndexD .root index index
  | function {X ty} {scope : ExternalScope rootTypes X}
      {original : Member rootTypes ty} {current : Member X ty} :
      ScopeIndexD scope original current → (global : ty.isGlobal = true) →
      ScopeIndexD (.function scope) original (current.intoGlobals global)

def ExternalScope.index {rootTypes X} (scope : ExternalScope rootTypes X) :
    {ty : ExternalType} → (original : Member rootTypes ty) →
      Option ((current : Member X ty) × ScopeIndexD scope original current) := by
  apply ExternalScope.casesOn
    (motive := fun X scope => {ty : ExternalType} → (original : Member rootTypes ty) →
      Option ((current : Member X ty) × ScopeIndexD scope original current)) scope
  case root => exact fun {_} original => some ⟨original, .root original⟩
  case function =>
    intro X parent
    exact fun {ty} original =>
      if global : ty.isGlobal = true then do
        let ⟨current, d⟩ ← parent.index original
        pure ⟨current.intoGlobals global, .function d global⟩
      else none
termination_by structural scope

theorem ScopeIndexD.complete {rootTypes X scope ty original current}
    (d : @ScopeIndexD rootTypes X scope ty original current) :
    scope.index original = some ⟨current, d⟩ := by
  induction d with
  | root index => rfl
  | @function X ty scope original current d global ih =>
    change (if h : ty.isGlobal = true then
      (scope.index original).bind (fun ⟨j, dj⟩ =>
        some (⟨j.intoGlobals h, ScopeIndexD.function dj h⟩ :
          ((k : Member (globals X) ty) × ScopeIndexD (.function scope) original k))) else none) = _
    rw [dif_pos global, ih]
    rfl

/-- The reference retains exactly the root declaration, attribute and capability. -/
inductive ScopedExternalD {rootTypes X} (decls : ExternalNames rootTypes)
    (scope : ExternalScope rootTypes X) (write : Bool) (name : String) (suffix : List String) :
    ExternalRef X write → Type where
  | intro {rootRef : ExternalRef rootTypes write} {current : Member X rootRef.ty} :
      ExternalD decls write name suffix rootRef →
      ScopeIndexD scope rootRef.index current →
      ScopedExternalD decls scope write name suffix ⟨current, rootRef.attr, rootRef.access⟩

def checkScopedExternal {rootTypes X} (decls : ExternalNames rootTypes)
    (scope : ExternalScope rootTypes X) (name : String) (suffix : List String) (write : Bool) :
    Option ((ref : ExternalRef X write) × ScopedExternalD decls scope write name suffix ref) := do
  let ⟨rootRef, resolution⟩ ← checkExternal decls name suffix write
  let ⟨current, visibility⟩ ← scope.index rootRef.index
  pure ⟨⟨current, rootRef.attr, rootRef.access⟩, .intro resolution visibility⟩

theorem ScopedExternalD.complete {rootTypes X decls scope write name suffix ref}
    (d : @ScopedExternalD rootTypes X decls scope write name suffix ref) :
    checkScopedExternal decls scope name suffix write = some ⟨ref, d⟩ := by
  cases d with
  | intro resolution visibility =>
    unfold checkScopedExternal
    rw [resolution.complete]
    change (scope.index _).bind _ = _
    rw [visibility.complete]
    rfl

theorem checkScopedExternal_iff {rootTypes X} (decls : ExternalNames rootTypes)
    (scope : ExternalScope rootTypes X) (name : String) (suffix : List String) (write : Bool) :
    (checkScopedExternal decls scope name suffix write).isSome = true ↔
      ∃ ref, Nonempty (ScopedExternalD decls scope write name suffix ref) := by
  constructor
  · intro h
    cases found : checkScopedExternal decls scope name suffix write with
    | none => rw [found] at h; cases h
    | some pair => exact ⟨pair.1, ⟨pair.2⟩⟩
  · rintro ⟨ref, ⟨d⟩⟩
    rw [d.complete]
    rfl

def ExternalScope.inFunction {rootTypes X} (scope : ExternalScope rootTypes X) : Bool :=
  ExternalScope.casesOn (motive := fun _ _ => Bool) scope
    (root := false) (function := fun _ => true)

theorem ScopeIndexD.global_if_function {rootTypes X scope ty original current}
    (d : @ScopeIndexD rootTypes X scope ty original current) :
    scope.inFunction = true → ty.isGlobal = true := by
  induction d with
  | root index => intro h; cases h
  | function _ global _ => intro _; exact global

theorem ScopeIndexD.function_global {rootTypes X ty} {scope : ExternalScope rootTypes X}
    {original : Member rootTypes ty} {current : Member (globals X) ty}
    (d : ScopeIndexD (.function scope) original current) : ty.isGlobal = true :=
  d.global_if_function rfl

/-- Every global occurrence survives every number of function boundaries. -/
theorem ExternalScope.index_global {rootTypes X} (scope : ExternalScope rootTypes X)
    {ty} (original : Member rootTypes ty) (global : ty.isGlobal = true) :
    (scope.index original).isSome = true := by
  induction scope with
  | root => rfl
  | @function X parent ih =>
    change (if h : ty.isGlobal = true then
      (parent.index original).bind (fun ⟨j, dj⟩ =>
        some (⟨j.intoGlobals h, ScopeIndexD.function dj h⟩ :
          ((k : Member (globals X) ty) × ScopeIndexD (.function parent) original k))) else none).isSome = true
    rw [dif_pos global]
    cases found : parent.index original with
    | none => rw [found] at ih; cases ih
    | some pair => rfl

theorem ExternalScope.index_function_iff {rootTypes X} (scope : ExternalScope rootTypes X)
    {ty} (original : Member rootTypes ty) :
    ((ExternalScope.function scope).index original).isSome = true ↔ ty.isGlobal = true := by
  constructor
  · intro h
    cases found : (ExternalScope.function scope).index original with
    | none => rw [found] at h; cases h
    | some pair => exact pair.2.function_global
  · intro global
    exact (ExternalScope.function scope).index_global original global

/-- This is external-variable assignment, not a ban on sstore/tstore effects. -/
theorem ScopedExternalD.function_noWrites {rootTypes X decls name suffix ref}
    {scope : ExternalScope rootTypes X}
    (d : ScopedExternalD decls (.function scope) true name suffix ref) : False := by
  cases d with
  | intro resolution visibility =>
    have global := visibility.function_global
    cases resolution with
    | intro index binding spelling cap =>
      have nonglobal := cap.write_not_global
      rw [global] at nonglobal
      cases nonglobal

theorem checkScopedExternal_function_write_refused {rootTypes X}
    (decls : ExternalNames rootTypes) (scope : ExternalScope rootTypes X)
    (name : String) (suffix : List String) :
    (checkScopedExternal decls (.function scope) name suffix true).isSome = false := by
  cases found : checkScopedExternal decls (.function scope) name suffix true with
  | none => rfl
  | some pair => exact False.elim pair.2.function_noWrites

theorem checkScopedExternal_root {X} (decls : ExternalNames X) (name : String)
    (suffix : List String) (write : Bool) :
    (checkScopedExternal decls .root name suffix write).map (fun pair => pair.1) =
      (checkExternal decls name suffix write).map (fun pair => pair.1) := by
  unfold checkScopedExternal
  cases found : checkExternal decls name suffix write with
  | none => rfl
  | some pair => rfl

end Solidity.Yul
