import Solidity.Frontend.SolcJson.YulMetadata
import Solidity.Yul.BlockScope

/-! Source-name/solc-ID namespace preparation relative to explicit original
bindings and an intrinsic declaration table. Aliases may have different visible
names from Declaration.name. Resolve ORIGINAL names before checking identity/
type availability; blocked/unknown bindings never expose an older declaration.
Actual Source context/import provenance and AST/span/role attachment remain
separate obligations. No frontend admission is installed. -/
namespace Solidity.Frontend.YulJson.Names
open Solidity.Yul

/-- None records a binding with no eligible single declaration. A known ID may
also have no typed table entry. Both block older bindings of the SAME name.
This is metadata, not a second program or untyped value representation. -/
abbrev Original := List (String × Option Nat)

inductive BindingD {X} (table : DeclarationTable X) (original : Original)
    (name : String) : Declaration X → Prop where
  | intro {id declaration}
      (named : Resolves original name (some id))
      (identified : IdentityD table.entries id declaration) :
      BindingD table original name declaration

def select {X} (table : DeclarationTable X) (original : Original) (name : String) :
    Option {declaration : Declaration X // BindingD table original name declaration} :=
  match named : resolve original name with
  | none | some none => none
  | some (some id) =>
    match identify table.entries id with
    | none => none
    | some declaration => some ⟨declaration.val,
        .intro (resolve_sound named) declaration.property⟩

theorem BindingD.complete {X table original name declaration}
    (d : @BindingD X table original name declaration) :
    select table original name = some ⟨declaration,d⟩ := by
  cases d with
  | intro named identified =>
    have hr := resolve_complete named
    have hi := identified.complete
    unfold select
    split <;> (try simp_all only [Option.some.injEq, reduceCtorEq])
    all_goals subst_vars
    all_goals split <;> simp_all only [Option.some.injEq, reduceCtorEq]

theorem BindingD.unique {X table original name first second}
    (one : @BindingD X table original name first)
    (two : BindingD table original name second) : first = second := by
  exact congrArg Subtype.val (Option.some.inj (one.complete.symm.trans two.complete))

theorem select_iff {X} (table : DeclarationTable X) (original : Original) (name : String) :
    (select table original name).isSome = true ↔ ∃ declaration, BindingD table original name declaration := by
  constructor
  · intro valid
    cases chosen : select table original name with
    | none => rw [chosen] at valid; cases valid
    | some result => exact ⟨result.val,result.property⟩
  · rintro ⟨declaration,proof⟩
    rw [proof.complete]
    rfl

theorem select_blocked {X} (table : DeclarationTable X) (original : Original) (name : String)
    (blocked : resolve original name = some none) : select table original name = none := by
  unfold select
  split <;> simp_all only [Option.some.injEq, reduceCtorEq]

theorem select_unknown {X} (table : DeclarationTable X) (original : Original) (name : String)
    (id : Nat) (named : resolve original name = some (some id))
    (missing : identify table.entries id = none) : select table original name = none := by
  unfold select
  split <;> (try simp_all only [Option.some.injEq, reduceCtorEq])
  all_goals subst_vars
  all_goals split <;> simp_all only [reduceCtorEq]

/-- Visible aliases are checked by identity, not by comparing with the stored
declaration spelling. No occurrence/span/role provenance is implied here. -/
structure ReferenceD {X} (table : DeclarationTable X) (original : Original)
    (visible : String) (reference : Reference table) : Type where
  named : Resolves original visible (some reference.declarationId)

def checkReference {X} (table : DeclarationTable X) (original : Original)
    (visible : String) (reference : Reference table) :
    Option (ReferenceD table original visible reference) :=
  if named : resolve original visible = some (some reference.declarationId) then
    some ⟨resolve_sound named⟩ else none

theorem ReferenceD.complete {X table original visible reference}
    (d : @ReferenceD X table original visible reference) :
    checkReference table original visible reference = some d := by
  unfold checkReference
  simp only [resolve_complete d.named, dif_pos]

theorem checkReference_iff {X} (table : DeclarationTable X) (original : Original)
    (visible : String) (reference : Reference table) :
    (checkReference table original visible reference).isSome = true ↔
      Nonempty (ReferenceD table original visible reference) := by
  constructor
  · intro valid
    cases found : checkReference table original visible reference with
    | none => rw [found] at valid; cases valid
    | some proof => exact ⟨proof⟩
  · rintro ⟨proof⟩
    rw [proof.complete]
    rfl

def ReferenceD.binding {X table original visible reference}
    (d : @ReferenceD X table original visible reference) :
    BindingD table original visible reference.declaration :=
  .intro d.named reference.identified

structure Entry {X} (table : DeclarationTable X) (original : Original) where
  visible : String
  declaration : Declaration X
  selected : BindingD table original visible declaration

def entry? {X} (table : DeclarationTable X) (original : Original) (name : String) :
    Option (Entry table original) :=
  (select table original name).map (fun result => ⟨name,result.val,result.property⟩)

def entries {X} (table : DeclarationTable X) (original : Original) : List (Entry table original) :=
  original.filterMap (fun binding => entry? table original binding.1)

def declarations {X} (table : DeclarationTable X) (original : Original) : ExternalNames X :=
  (entries table original).map (fun entry =>
    (entry.visible,⟨entry.declaration.ty,entry.declaration.index⟩))

end Solidity.Frontend.YulJson.Names
