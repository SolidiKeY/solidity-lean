import Solidity.Yul.ExternalKeys
import Solidity.Yul.ExternalScope
import Solidity.Yul.AssignmentCheck
import Solidity.Yul.FunctionScope

/-!
# Constructed scoped external names

Every candidate is checked against the ORIGINAL declaration table before
retaining a reference. Duplicate names never expose an older declaration
after suffix, capability or capture refusal. Names are metadata over existing
intrinsic references, not another program representation.

The no-dot namespace premise is real: arbitrary Strings and unique declaration
IDs do not imply it. Source providers must additionally preserve original
resolution before classification of unsupported Source types. Nothing here
attaches solc occurrences, establishes actual Source namespaces or interprets
physical/dirty words.
-/
namespace Solidity.Yul.ScopedNames
open ExternalKeys

def Canonical {root : List ExternalType} (decls : ExternalNames root) : Prop :=
  ∀ name ∈ decls.map Prod.fst, NoDot name

instance {root} (decls : ExternalNames root) : Decidable (Canonical decls) :=
  inferInstanceAs (Decidable (∀ name ∈ decls.map Prod.fst, NoDot name))

private theorem resolves_mem {α} {table : List (String × α)} {name value}
    (d : Resolves table name value) : (name, value) ∈ table := by
  induction d with
  | head => exact List.mem_cons_self
  | tail _ _ ih => exact List.mem_cons_of_mem _ ih

private theorem resolves_name_mem {α} {table : List (String × α)} {name value}
    (d : Resolves table name value) : name ∈ table.map Prod.fst :=
  List.mem_map.mpr ⟨(name, value), resolves_mem d, rfl⟩

theorem external_name_mem {root decls write name parts ref}
    (d : @ExternalD root decls write name parts ref) :
    name ∈ decls.map Prod.fst := by
  cases d with
  | intro index binding spelled capability => exact resolves_name_mem binding

theorem scoped_name_mem {root X decls scope write name parts ref}
    (d : @ScopedExternalD root X decls scope write name parts ref) :
    name ∈ decls.map Prod.fst := by
  cases d with
  | intro resolution visibility => exact external_name_mem resolution

theorem scoped_suffix {root X decls scope write name parts ref}
    (d : @ScopedExternalD root X decls scope write name parts ref) :
    SuffixD parts ref.attr := by
  cases d with
  | intro resolution visibility =>
      cases resolution with
      | intro index binding spelled capability => exact spelled

structure Entry {root X} (decls : ExternalNames root)
    (scope : ExternalScope root X) (write : Bool) where
  base : String
  attr : Attribute
  reference : ExternalRef X write
  derivation : ScopedExternalD decls scope write base (suffix attr) reference

def Entry.key {root X decls scope write} (entry : @Entry root X decls scope write) : String :=
  externalKey entry.base (suffix entry.attr)

def entry? {root X} (decls : ExternalNames root)
    (scope : ExternalScope root X) (write : Bool) (base : String) (a : Attribute) :
    Option (Entry decls scope write) := do
  let ⟨reference, derivation⟩ ← checkScopedExternal decls scope base (suffix a) write
  pure ⟨base, a, reference, derivation⟩

theorem Entry.complete {root X decls scope write}
    (entry : @Entry root X decls scope write) :
    entry? decls scope write entry.base entry.attr = some entry := by
  cases entry with
  | mk base attr reference derivation =>
      unfold entry?
      rw [derivation.complete]
      rfl

/-- Only successful references are retained, but resolution always sees decls.
The repeated original names are harmless: equal keys have equal references by
the real checker reconstruction law, not an assumed namespace agreement. -/
def entries {root X} (decls : ExternalNames root) (scope : ExternalScope root X)
    (write : Bool) : List (Entry decls scope write) :=
  decls.flatMap fun binding => attributes.filterMap (entry? decls scope write binding.1)

def names {root X} (decls : ExternalNames root) (scope : ExternalScope root X)
    (write : Bool) : List (String × ExternalRef X write) :=
  (entries decls scope write).map fun entry => (entry.key, entry.reference)

theorem Entry.mem_entries {root X decls scope write}
    (entry : @Entry root X decls scope write) : entry ∈ entries decls scope write := by
  have present := scoped_name_mem entry.derivation
  obtain ⟨binding, member, same⟩ := List.mem_map.mp present
  apply List.mem_flatMap.mpr
  refine ⟨binding, member, List.mem_filterMap.mpr ?_⟩
  refine ⟨entry.attr, attribute_mem _, ?_⟩
  rw [same]
  exact entry.complete

private theorem entry_key_sound {root X decls scope write}
    (canonical : @Canonical root decls) (entry : @Entry root X decls scope write)
    {name parts} (query : NoDot name)
    (same : entry.key = externalKey name parts) :
    Nonempty (ScopedExternalD decls scope write name parts entry.reference) := by
  have valid := canonical entry.base (scoped_name_mem entry.derivation)
  obtain ⟨nameEq, partsEq⟩ := key_suffix_unique query valid same.symm
  subst name
  subst parts
  exact ⟨entry.derivation⟩

theorem names_member_sound {root X decls scope write name parts ref}
    (canonical : @Canonical root decls) (query : NoDot name)
    (member : (externalKey name parts, ref) ∈ @names root X decls scope write) :
    Nonempty (ScopedExternalD decls scope write name parts ref) := by
  obtain ⟨entry, present, same⟩ := List.mem_map.mp member
  have keyEq := congrArg Prod.fst same
  have valueEq := congrArg Prod.snd same
  change entry.reference = ref at valueEq
  subst ref
  exact entry_key_sound canonical entry query keyEq

theorem lookup_sound {root X decls scope write name parts ref}
    (canonical : @Canonical root decls) (query : NoDot name)
    (found : resolve (@names root X decls scope write) (externalKey name parts) = some ref) :
    Nonempty (ScopedExternalD decls scope write name parts ref) :=
  names_member_sound canonical query (resolves_mem (resolve_sound found))

private theorem resolve_of_mem_consistent {α} (table : List (String × α))
    (key : String) (value : α) (present : (key, value) ∈ table)
    (consistent : ∀ other, (key, other) ∈ table → other = value) :
    resolve table key = some value := by
  induction table with
  | nil => cases present
  | cons binding rest ih =>
      rcases binding with ⟨name, previous⟩
      by_cases same : key = name
      · subst name
        have equal := consistent previous List.mem_cons_self
        simp only [resolve, if_true, equal]
      · change (if key = name then some previous else resolve rest key) = _
        rw [if_neg same]
        apply ih
        · rcases List.mem_cons.mp present with first | later
          · have wrong := congrArg Prod.fst first
            exact False.elim (same wrong)
          · exact later
        · exact fun other h => consistent other (List.mem_cons_of_mem _ h)

theorem lookup_complete {root X decls scope write name parts ref}
    (canonical : @Canonical root decls)
    (d : @ScopedExternalD root X decls scope write name parts ref) :
    resolve (names decls scope write) (externalKey name parts) = some ref := by
  have query := canonical name (scoped_name_mem d)
  have spelling := suffix_canonical (scoped_suffix d)
  subst parts
  let entry : Entry decls scope write := ⟨name, ref.attr, ref, d⟩
  apply resolve_of_mem_consistent
  · exact List.mem_map.mpr ⟨entry, entry.mem_entries, rfl⟩
  · intro other present
    obtain ⟨otherD⟩ := names_member_sound canonical query present
    have same := Option.some.inj (otherD.complete.symm.trans d.complete)
    exact congrArg Sigma.fst same

/-- Exact concrete lookup composition, including refusals. The no-dot query
premise rules out a forged head "a.slot" matching the legal path a.slot. -/
theorem lookup_agrees {root X} (decls : ExternalNames root)
    (scope : ExternalScope root X) (write : Bool) (canonical : Canonical decls)
    (name : String) (parts : List String) (query : NoDot name) :
    resolve (names decls scope write) (externalKey name parts) =
      (checkScopedExternal decls scope name parts write).map Sigma.fst := by
  cases actual : checkScopedExternal decls scope name parts write with
  | some pair =>
      rw [lookup_complete canonical pair.2]
      rfl
  | none =>
      cases found : resolve (names decls scope write) (externalKey name parts) with
      | none => rfl
      | some ref =>
          obtain ⟨d⟩ := lookup_sound canonical query found
          have bad := d.complete
          rw [actual] at bad
          cases bad

structure Checked {root} (decls : ExternalNames root) : Type where
  canonical : Canonical decls

def check {root} (decls : ExternalNames root) : Option (Checked decls) :=
  if h : Canonical decls then some ⟨h⟩ else none

theorem Checked.complete {root decls} (c : @Checked root decls) :
    check decls = some c := by
  cases c with
  | mk canonical => exact dif_pos canonical

def Checked.readEnv {root X F n decls} (_checked : @Checked root decls)
    (scope : ExternalScope root X) (locals : List (String × Fin n))
    (functions : FunctionNames F) : ExprEnv F X n :=
  ⟨locals, functions, names decls scope false⟩


/-- Concrete external-expression typing for the constructed existing Env.
The local-priority premise is the actual existing ExprD side condition. -/
def Checked.externalExpr {root X F n decls name parts ref}
    (checked : @Checked root decls) (scope : ExternalScope root X)
    (locals : List (String × Fin n)) (functions : FunctionNames F)
    (d : ScopedExternalD decls scope false name parts ref)
    (priority : parts ≠ [] ∨ NoBinding locals name) :
    ExprD (checked.readEnv scope locals functions) (.yulPath name parts) 1 :=
  .external priority (resolve_sound (lookup_complete checked.canonical d))

theorem Checked.infer_external_complete {root X F n decls name parts ref}
    (checked : @Checked root decls) (scope : ExternalScope root X)
    (locals : List (String × Fin n)) (functions : FunctionNames F)
    (d : ScopedExternalD decls scope false name parts ref)
    (priority : parts ≠ [] ∨ NoBinding locals name) :
    inferExpr (checked.readEnv scope locals functions) (.yulPath name parts) =
      some ⟨1, checked.externalExpr scope locals functions d priority⟩ :=
  (checked.externalExpr scope locals functions d priority).complete

theorem Checked.externalExpr_term {root X F n decls name parts ref}
    (checked : @Checked root decls) (scope : ExternalScope root X)
    (locals : List (String × Fin n)) (functions : FunctionNames F)
    (d : ScopedExternalD decls scope false name parts ref)
    (priority : parts ≠ [] ∨ NoBinding locals name) :
    (checked.externalExpr scope locals functions d priority).term = .external ref := rfl

/-- Root targets use the exact original declaration list. In functions all
permitted external types are readonly; empty is proved complete below. This
does not forbid world-effect builtins such as sstore/tstore. -/
def targetDeclarations {root X} (decls : ExternalNames root)
    (scope : ExternalScope root X) : ExternalNames X := by
  apply ExternalScope.casesOn (motive := fun X _ => ExternalNames X) scope
  case root => exact decls
  case function => intro X parent; exact []

private theorem external_empty (X : List ExternalType) (name : String)
    (parts : List String) (write : Bool) :
    checkExternal ([] : ExternalNames X) name parts write = none := by
  unfold checkExternal
  split <;> rfl

theorem function_write_entries_empty {root X} (decls : ExternalNames root)
    (scope : ExternalScope root X) : entries decls (.function scope) true = [] := by
  cases h : entries decls (.function scope) true with
  | nil => rfl
  | cons first rest => exact False.elim first.derivation.function_noWrites

theorem target_lookup_agrees {root X} (decls : ExternalNames root)
    (scope : ExternalScope root X) (name : String) (parts : List String) :
    (checkExternal (targetDeclarations decls scope) name parts true).map Sigma.fst =
      (checkScopedExternal decls scope name parts true).map Sigma.fst := by
  cases scope with
  | root => exact (checkScopedExternal_root decls name parts true).symm
  | function parent =>
      change (checkExternal ([] : ExternalNames _) name parts true).map Sigma.fst = _
      rw [external_empty]
      cases found : checkScopedExternal decls (.function parent) name parts true with
      | none => rfl
      | some pair => exact False.elim pair.2.function_noWrites

def targetEnv {root X n} (decls : ExternalNames root) (scope : ExternalScope root X)
    (locals : List (String × Fin n)) : TargetEnv X n :=
  ⟨locals, targetDeclarations decls scope⟩

private theorem target_resolution {root X decls scope name parts ref}
    (d : @ScopedExternalD root X decls scope true name parts ref) :
    Nonempty (ExternalD (targetDeclarations decls scope) true name parts ref) := by
  have found := target_lookup_agrees decls scope name parts
  rw [d.complete] at found
  cases actual : checkExternal (targetDeclarations decls scope) name parts true with
  | none => rw [actual] at found; cases found
  | some pair =>
      rw [actual] at found
      have same : pair.1 = ref := Option.some.inj found
      cases same
      exact ⟨pair.2⟩

/-- The actual existing target checker receives the same scoped declarations.
This is external-variable assignment, not physical storage/writeback semantics. -/
theorem checkTarget_external_complete {root X n decls scope name parts ref}
    (locals : List (String × Fin n))
    (d : @ScopedExternalD root X decls scope true name parts ref)
    (priority : parts ≠ [] ∨ NoBinding locals name) :
    (checkTarget (targetEnv decls scope locals) name parts).map Sigma.fst =
      some (.external ref) := by
  obtain ⟨resolution⟩ := target_resolution d
  have typed : TargetD (targetEnv decls scope locals) name parts (.external ref) :=
    .external priority resolution
  rw [typed.complete]
  rfl


theorem check_iff {root} (decls : ExternalNames root) :
    (check decls).isSome = true ↔ Canonical decls := by
  unfold check
  split
  · next canonical => exact ⟨fun _ => canonical, fun _ => rfl⟩
  · next invalid =>
      constructor
      · intro impossible; cases impossible
      · intro canonical; exact False.elim (invalid canonical)

/-- Soundness in the opposite direction for an actual external-target
typing certificate from the constructed existing target environment. -/
theorem target_derivation_scoped {root X n decls scope name parts ref}
    (locals : List (String × Fin n))
    (d : TargetD (@targetEnv root X n decls scope locals) name parts (.external ref)) :
    Nonempty (ScopedExternalD decls scope true name parts ref) := by
  cases d with
  | external priority resolution =>
      change ExternalD (targetDeclarations decls scope) true name parts ref at resolution
      have known : (checkExternal (targetDeclarations decls scope) name parts true).map
          Sigma.fst = some ref := by
        rw [resolution.complete]
        rfl
      rw [target_lookup_agrees] at known
      cases actual : checkScopedExternal decls scope name parts true with
      | none => rw [actual] at known; cases known
      | some pair =>
          rw [actual] at known
          have same : pair.1 = ref := Option.some.inj known
          cases same
          exact ⟨pair.2⟩

end Solidity.Yul.ScopedNames
