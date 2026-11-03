import Solidity.Yul.ExpressionCheck
import Solidity.Yul.ExternalCheck

/-!
# Canonical external lookup keys

The existing expression table flattens a base and suffix with ".". This is
injective on the documented suffix domain only with a real delimiter-free
base premise. Arbitrary supplied Strings do not establish that premise.
These laws do not attach a name to Source declarations or solc occurrences.
-/
namespace Solidity.Yul.ExternalKeys

def suffix : Attribute → List String
  | .plain => []
  | .slot => ["slot"]
  | .offset => ["offset"]
  | .length => ["length"]
  | .selector => ["selector"]
  | .address => ["address"]

def attributes : List Attribute :=
  [.plain, .slot, .offset, .length, .selector, .address]

theorem attribute_mem (a : Attribute) : a ∈ attributes := by
  cases a <;> decide

theorem attributes_distinct : attributes.Nodup := by decide

theorem suffix_derivation (a : Attribute) : SuffixD (suffix a) a := by
  cases a
  · exact .plain
  · exact .slot
  · exact .offset
  · exact .length
  · exact .selector
  · exact .address

theorem suffix_complete (a : Attribute) : checkSuffix (suffix a) = some a :=
  (suffix_derivation a).complete

theorem suffix_canonical {parts a} (d : SuffixD parts a) : parts = suffix a := by
  cases d <;> rfl

def NoDot (base : String) : Prop := '.' ∉ base.data

instance (base : String) : Decidable (NoDot base) :=
  inferInstanceAs (Decidable ('.' ∉ base.data))

private def tail : Attribute → List Char
  | .plain => []
  | .slot => ['.', 's', 'l', 'o', 't']
  | .offset => ['.', 'o', 'f', 'f', 's', 'e', 't']
  | .length => ['.', 'l', 'e', 'n', 'g', 't', 'h']
  | .selector => ['.', 's', 'e', 'l', 'e', 'c', 't', 'o', 'r']
  | .address => ['.', 'a', 'd', 'd', 'r', 'e', 's', 's']

private theorem key_data (base : String) (a : Attribute) :
    (externalKey base (suffix a)).data = base.data ++ tail a := by
  cases a
  · change base.data = base.data ++ []
    exact (List.append_nil _).symm
  · change ((base ++ ".") ++ "slot").data = base.data ++ tail .slot
    rw [String.data_append, String.data_append, List.append_assoc]
    rfl
  · change ((base ++ ".") ++ "offset").data = base.data ++ tail .offset
    rw [String.data_append, String.data_append, List.append_assoc]
    rfl
  · change ((base ++ ".") ++ "length").data = base.data ++ tail .length
    rw [String.data_append, String.data_append, List.append_assoc]
    rfl
  · change ((base ++ ".") ++ "selector").data = base.data ++ tail .selector
    rw [String.data_append, String.data_append, List.append_assoc]
    rfl
  · change ((base ++ ".") ++ "address").data = base.data ++ tail .address
    rw [String.data_append, String.data_append, List.append_assoc]
    rfl

private def keyBase (key : String) : String :=
  ⟨key.data.takeWhile (fun c => decide (c ≠ '.'))⟩

private theorem tail_prefix (a : Attribute) :
    (tail a).takeWhile (fun c => decide (c ≠ '.')) = [] := by
  cases a <;> rfl

private theorem prefix_key {base : String} (canonical : NoDot base) (a : Attribute) :
    keyBase (externalKey base (suffix a)) = base := by
  apply String.ext
  change (externalKey base (suffix a)).data.takeWhile (fun c => decide (c ≠ '.')) = _
  have good : ∀ c ∈ base.data, decide (c ≠ '.') = true := by
    intro c hc
    simp only [decide_eq_true_eq]
    intro same
    subst c
    exact canonical hc
  rw [key_data, List.takeWhile_append_of_pos good, tail_prefix]
  exact List.append_nil _

private theorem tail_injective (a b : Attribute) : tail a = tail b → a = b := by
  cases a <;> cases b <;> decide

/-- The no-dot premises concern BOTH actual base names. They cannot be
inferred from the external declaration table's type or unique IDs. -/
theorem key_injective {left right : String} {a b : Attribute}
    (leftCanonical : NoDot left) (rightCanonical : NoDot right)
    (same : externalKey left (suffix a) = externalKey right (suffix b)) :
    left = right ∧ a = b := by
  have names := congrArg keyBase same
  rw [prefix_key leftCanonical, prefix_key rightCanonical] at names
  cases names
  have chars := congrArg String.data same
  rw [key_data, key_data] at chars
  exact ⟨rfl, tail_injective _ _ (List.append_cancel_left chars)⟩

private def payload (parts : List String) : List Char :=
  parts.flatMap (fun part => '.' :: part.data)

private theorem key_data_all (base : String) (parts : List String) :
    (externalKey base parts).data = base.data ++ payload parts := by
  induction parts generalizing base with
  | nil =>
      change base.data = base.data ++ []
      exact (List.append_nil _).symm
  | cons first rest ih =>
      change (externalKey ((base ++ ".") ++ first) rest).data =
        base.data ++ payload (first :: rest)
      rw [ih, String.data_append, String.data_append]
      simp only [payload, List.flatMap_cons, List.append_assoc]
      rfl

private theorem prefix_key_all {base : String} (canonical : NoDot base)
    (parts : List String) : keyBase (externalKey base parts) = base := by
  apply String.ext
  change (externalKey base parts).data.takeWhile (fun c => decide (c ≠ '.')) = _
  have good : ∀ c ∈ base.data, decide (c ≠ '.') = true := by
    intro c hc
    simp only [decide_eq_true_eq]
    intro same
    subst c
    exact canonical hc
  rw [key_data_all, List.takeWhile_append_of_pos good]
  cases parts with
  | nil => exact List.append_nil _
  | cons first rest =>
      change base.data ++ [] = base.data
      exact List.append_nil _

private theorem parts_le_dots (parts : List String) :
    parts.length ≤ (payload parts).count '.' := by
  induction parts with
  | nil => exact Nat.le_refl 0
  | cons first rest ih =>
      simp only [payload, List.flatMap_cons, List.count_append, List.count_cons,
        beq_self_eq_true, ↓reduceIte, List.length_cons] at *
      omega

private theorem suffix_dots_le_one (a : Attribute) :
    (payload (suffix a)).count '.' ≤ 1 := by
  cases a <;> decide

/-- A successful key match cannot smuggle in an arbitrary malformed suffix.
Only the two base names need the no-dot premises; query parts are arbitrary. -/
theorem key_suffix_unique {left right : String} {parts : List String} {a : Attribute}
    (leftCanonical : NoDot left) (rightCanonical : NoDot right)
    (same : externalKey left parts = externalKey right (suffix a)) :
    left = right ∧ parts = suffix a := by
  have names := congrArg keyBase same
  rw [prefix_key_all leftCanonical, prefix_key rightCanonical] at names
  cases names
  have chars := congrArg String.data same
  rw [key_data_all, key_data_all] at chars
  have tails : payload parts = payload (suffix a) := List.append_cancel_left chars
  have size : parts.length ≤ 1 := by
    have lower := parts_le_dots parts
    rw [tails] at lower
    exact Nat.le_trans lower (suffix_dots_le_one a)
  constructor
  · rfl
  · cases parts with
    | nil =>
        cases a <;> first
          | rfl
          | (cases tails)
    | cons first rest =>
        cases rest with
        | cons second more =>
            simp only [List.length_cons] at size
            omega
        | nil =>
            cases a
            · cases tails
            all_goals
              simp only [payload, suffix, List.flatMap_cons, List.flatMap_nil,
                List.append_nil] at tails
              apply congrArg (fun name : String => [name])
              apply String.ext
              exact (List.cons.inj tails).2

/-- A concrete collision outside the premise, retained as a negative control. -/
example : externalKey "a.slot" [] = externalKey "a" ["slot"] := rfl
example : ¬ NoDot "a.slot" := by decide
example : NoDot "a" := by decide

end Solidity.Yul.ExternalKeys
