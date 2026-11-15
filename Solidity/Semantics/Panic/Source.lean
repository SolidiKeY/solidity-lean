import Solidity.Semantics.Panic.Origins

/-!
# Width-aware source panic producers

An additive V2 interface for source checks. The original producers and origins
are embedded unchanged. Narrow arithmetic checks retain the result value and
its source width: a failed uint8 check is not a failed uint256 operation.
This local interface does not claim that the opaque elaborator emits a check,
or relate whole-program V1 and V2 results. Narrowing models the arithmetic
panic branch only: source ignoring mode assumes false, and ordinary legacy
mode requires the condition. Source association must establish the actual
numeric condition and mode. Each fixed-result producer carrier stays in Type;
this is not a universal existential package of all result types.
-/

namespace Solidity.Panic.Source

/-- The source range check, including the elaborator's full-width bypass.
For unsigned values the intrinsic type has already checked the lower bound. -/
def fits (p : PrimTy) (width : Nat) (value : p.Denote) : Bool :=
  if 256 ≤ width then true
  else if p = .int then
    decide (-((2 ^ (width - 1) : Nat) : Int) ≤ PrimTy.key value ∧
      PrimTy.key value ≤ ((2 ^ (width - 1) - 1 : Nat) : Int))
  else decide (PrimTy.key value ≤ ((2 ^ width - 1 : Nat) : Int))

/-- Numeric narrowing retains the source width and the evaluated value. -/
inductive Narrowing : Type → Type where
  | unsigned (width : Nat) (value : PrimTy.uint.Denote) : Narrowing PrimTy.uint.Denote
  | signed (width : Nat) (value : PrimTy.int.Denote) : Narrowing PrimTy.int.Denote

def Narrowing.value {α : Type} : Narrowing α → α
  | .unsigned _ value => value
  | .signed _ value => value

def Narrowing.width {α : Type} : Narrowing α → Nat
  | .unsigned width _ => width
  | .signed width _ => width

def Narrowing.passed {α : Type} : Narrowing α → Bool
  | .unsigned width value => fits .uint width value
  | .signed width value => fits .int width value

theorem Narrowing.full {α : Type} :
    (check : Narrowing α) → 256 ≤ check.width → check.passed = true
  | .unsigned _ _, full => if_pos full
  | .signed _ _, full => if_pos full

/-- V2 extends the producer family without changing any V1 producer.
The result type is a parameter, so each carrier remains small. -/
inductive ProducerV2 (α : Type) : Type where
  | original (producer : Producer α)
  | narrowing (check : Narrowing α)

def ProducerV2.run {α : Type} : ProducerV2 α → Except (Option Site) α
  | .original producer => producer.run
  | .narrowing check =>
      if check.passed then .ok check.value else .error (some .arithmetic)

def OriginV2 {α : Type} (producer : ProducerV2 α) (site : Site) : Prop :=
  producer.run = .error (some site)

/-- Both directions preserve the complete existing origin predicate. -/
theorem original_origin_iff {α : Type} (producer : Producer α) (site : Site) :
    OriginV2 (.original producer) site ↔ Origin producer site := Iff.rfl

theorem narrowing_origin {α : Type} (check : Narrowing α)
    (failed : check.passed = false) :
    OriginV2 (.narrowing check) .arithmetic := by
  simp only [OriginV2, ProducerV2.run, failed, Bool.false_eq_true, ↓reduceIte]

theorem narrowing_success {α : Type} (check : Narrowing α)
    (passed : check.passed = true) :
    (ProducerV2.narrowing check).run = .ok check.value := if_pos passed

theorem full_width {α : Type} (check : Narrowing α) (full : 256 ≤ check.width) :
    (ProducerV2.narrowing check).run = .ok check.value :=
  narrowing_success check (check.full full)

/-- No freely attached code can override the producer's failure. -/
theorem OriginV2.unique {α : Type} {producer : ProducerV2 α} {a b : Site}
    (ha : OriginV2 producer a) (hb : OriginV2 producer b) : a = b :=
  Option.some.inj (Except.error.inj (ha.symm.trans hb))

/-- The motivating boundary: 256 fits uint256, but not uint8. -/
example : fits .uint 8 ⟨256, by decide⟩ = false := by decide
example : fits .uint 256 ⟨256, by decide⟩ = true := by decide
example : fits .int 8 ⟨128, by decide⟩ = false := by decide
example : fits .int 8 ⟨-128, by decide⟩ = true := by decide

end Solidity.Panic.Source
