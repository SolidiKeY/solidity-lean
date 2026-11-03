import Solidity.Yul.Syntax

/-!
# Independent static obligations and their checks

These laws concern symbol environments, literal decoding and external-reference
capabilities. They are preparation for the whole-block checker, not a claim that
all solc JSON or grammar trees have already been elaborated.
-/
namespace Solidity.Yul

/-- External-reference legality from the Solidity assembly documentation. -/
def LegalAccess (ty : ExternalType) (attr : Attribute) (write : Bool) : Prop :=
  match ty with
  | .value _ | .memory | .calldataStatic | .internalFunction => attr = .plain
  | .calldataDynamic => attr = .offset ∨ attr = .length
  | .storage isLocal _ =>
      (attr = .slot ∧ (write = false ∨ isLocal = true)) ∨
      (attr = .offset ∧ write = false)
  | .externalFunction => attr = .selector ∨ attr = .address
  | .constant _ | .library => attr = .plain ∧ write = false

instance (ty : ExternalType) (attr : Attribute) (w : Bool) : Decidable (LegalAccess ty attr w) := by
  unfold LegalAccess; split <;> infer_instance

/-- Construct the intrinsic capability only at permitted attributes/directions. -/
def checkAccess : (ty : ExternalType) → (a : Attribute) → (w : Bool) → Option (Access ty a w)
  | .value _, .plain, false => some .valueRead
  | .value _, .plain, true => some .valueWrite
  | .memory, .plain, false => some .memoryRead
  | .memory, .plain, true => some .memoryWrite
  | .calldataStatic, .plain, false => some .staticRead
  | .calldataStatic, .plain, true => some .staticWrite
  | .calldataDynamic, .offset, false => some .offsetRead
  | .calldataDynamic, .offset, true => some .offsetWrite
  | .calldataDynamic, .length, false => some .lengthRead
  | .calldataDynamic, .length, true => some .lengthWrite
  | .storage _ _, .slot, false => some .slotRead
  | .storage true _, .slot, true => some .slotWrite
  | .storage _ _, .offset, false => some .storageOffset
  | .externalFunction, .selector, false => some .selectorRead
  | .externalFunction, .selector, true => some .selectorWrite
  | .externalFunction, .address, false => some .addressRead
  | .externalFunction, .address, true => some .addressWrite
  | .constant _, .plain, false => some .constantRead
  | .library, .plain, false => some .libraryRead
  | .internalFunction, .plain, false => some .internalRead
  | .internalFunction, .plain, true => some .internalWrite
  | _, _, _ => none

/-- The capability checker is sound AND complete against the independent
attribute/direction relation, including tiers whose execution is not implemented. -/
theorem checkAccess_iff (ty : ExternalType) (a : Attribute) (w : Bool) :
    (checkAccess ty a w).isSome = true ↔ LegalAccess ty a w := by
  cases ty with
  | storage l t => cases l <;> cases a <;> cases w <;> (dsimp only [checkAccess, LegalAccess, Option.isSome]; decide)
  | value e => cases a <;> cases w <;> (dsimp only [checkAccess, LegalAccess, Option.isSome]; decide)
  | memory | calldataStatic | calldataDynamic | externalFunction | internalFunction | library =>
      cases a <;> cases w <;> (dsimp only [checkAccess, LegalAccess, Option.isSome]; decide)
  | constant v => cases a <;> cases w <;> (dsimp only [checkAccess, LegalAccess, Option.isSome]; decide)

/-- Independently scoped lookup: a binding can be used if it is visible at the
head, or occurs in a tail past a differently named declaration. -/
inductive Resolves {α : Type} : List (String × α) → String → α → Prop where
  | head {name value rest} : Resolves ((name, value) :: rest) name value
  | tail {name other value v rest} : name ≠ other → Resolves rest name value →
      Resolves ((other, v) :: rest) name value

/-- Typed symbol lookup; the payload can be a local position, a function
signature/reference, or an external declaration/reference. -/
def resolve {α : Type} : List (String × α) → String → Option α
  | [], _ => none
  | (n, v) :: rest, name => if name = n then some v else resolve rest name

/-- Soundness of executable lookup against lexical visibility. -/
theorem resolve_sound {α : Type} {env : List (String × α)} {name : String} {value : α}
    (h : resolve env name = some value) : Resolves env name value := by
  induction env with
  | nil => cases h
  | cons b rest ih =>
      rcases b with ⟨n, v⟩
      unfold resolve at h
      split at h
      · next he => cases he; cases h; exact .head
      · next hn => exact .tail hn (ih h)

/-- Completeness: every independently scoped binding is returned by lookup. -/
theorem resolve_complete {α : Type} {env : List (String × α)} {name : String} {value : α}
    (h : Resolves env name value) : resolve env name = some value := by
  induction h with
  | head => exact if_pos rfl
  | tail hn _ ih => exact (if_neg hn).trans ih

/-- Freshness forbids shadowing even names unavailable for capture in a function.
`visible` therefore includes outer names, not only executable local references. -/
def Fresh (visible introduced : List String) : Prop :=
  introduced.Nodup ∧ ∀ n ∈ introduced, n ∉ visible

def fresh (visible introduced : List String) : Bool :=
  decide introduced.Nodup && introduced.all (fun n => !visible.contains n)

/-- Freshness is checked against the entire visible namespace. -/
theorem fresh_iff (visible introduced : List String) :
    fresh visible introduced = true ↔ Fresh visible introduced := by
  simp only [fresh, List.contains_eq_mem, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Fresh]

/-- Numeric Yul literals must fit without truncation. -/
def LiteralRange (n : Nat) : Prop := n < 2 ^ 256

def checkLiteral (n : Nat) : Option Word :=
  if h : n < 2 ^ 256 then some ⟨n, h⟩ else none

/-- The literal checker never wraps an out-of-range literal into a different one. -/
theorem checkLiteral_iff (n : Nat) :
    (checkLiteral n).isSome = true ↔ LiteralRange n := by
  unfold checkLiteral LiteralRange
  split <;> simp only [Option.isSome_some, Option.isSome_none, Bool.false_eq_true,
    true_iff, false_iff] <;> assumption

/-- A checked literal retains every source bit. -/
theorem checkLiteral_value {n : Nat} {w : Word} (h : checkLiteral n = some w) : w.val = n := by
  unfold checkLiteral at h
  split at h
  · cases h; rfl
  · cases h

/-- Typed internal function pointers have compiler-dependent code addresses;
representing their syntax does not authorize observing those addresses. -/
def admitExternal (tier : Tier) (ty : ExternalType) : Except Refusal Unit :=
  match ty with
  | .internalFunction => .error (.compilerDependent "internal function address")
  | .value _ | .externalFunction | .constant _ => .ok ()
  | _ => if tier.includes .B then .ok () else .error (.needsTier .B)

end Solidity.Yul
