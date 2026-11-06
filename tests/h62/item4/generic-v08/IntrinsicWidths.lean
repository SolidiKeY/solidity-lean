import Solidity.Source.Types

/-!
Isolated H62 backfill: width admission at the existing intrinsic Source.STy.
This does not assert argument evaluation, state transport, or ABI agreement.
The two fixture rows retain the binary/maximal original width cases from
FixedBytesCallableArgumentControls; original execution theorems are read-only.
-/
namespace Solidity.H62.GenericV08
open Solidity.Source

/-- Widening composes at the existing type-indexed source admission relation. -/
theorem fixedBytes_widening (isBase : DeclName → DeclName → Bool)
    (n m k : Nat) (hn : 1 ≤ n ∧ n ≤ 32) (_hm : 1 ≤ m ∧ m ≤ 32)
    (hk : 1 ≤ k ∧ k ≤ 32) (nm : n ≤ m) (mk : m ≤ k) :
    STy.implicit isBase (.fixedBytes n hn) (.fixedBytes k hk) = true := by
  change decide (n ≤ k) = true
  exact decide_eq_true (Nat.le_trans nm mk)

/-- Every legal width admits identity conversion, without enumerating widths. -/
theorem fixedBytes_identity (isBase : DeclName → DeclName → Bool)
    (n : Nat) (hn : 1 ≤ n ∧ n ≤ 32) :
    STy.implicit isBase (.fixedBytes n hn) (.fixedBytes n hn) = true :=
  fixedBytes_widening isBase n n n hn hn hn (Nat.le_refl n) (Nat.le_refl n)

/-- Strict narrowing is refused by that same published admission relation. -/
theorem fixedBytes_narrowing (isBase : DeclName → DeclName → Bool)
    (n m : Nat) (hn : 1 ≤ n ∧ n ≤ 32) (_hm : 1 ≤ m ∧ m ≤ 32) (lt : m < n) :
    STy.implicit isBase (.fixedBytes n hn) (.fixedBytes m _hm) = false := by
  change decide (n ≤ m) = false
  exact decide_eq_false (Nat.not_le_of_gt lt)

/-- Width bounds live in the fixture, exactly as in the original source types. -/
structure WidthFixture where
  width : Nat
  bound : 1 ≤ width ∧ width ≤ 32
  old : List UInt8
  rhs : List UInt8

def WidthFixture.type (fixture : WidthFixture) : STy :=
  .fixedBytes fixture.width fixture.bound

/-- Exact binary and maximal input lists from the original declarations. -/
def widthFixtures : List WidthFixture :=
  [⟨2, by decide, [255,128], [0,1]⟩,
   ⟨32, by decide, [], List.replicate 32 255⟩]

/-- The fixture table consumes a general theorem; no decide table proves it. -/
theorem fixture_identity (isBase : DeclName → DeclName → Bool) (fixture : WidthFixture) :
    STy.implicit isBase fixture.type fixture.type = true :=
  fixedBytes_identity isBase fixture.width fixture.bound

/-- Every retained table row uses the same all-width admission proof. -/
theorem table_identity (isBase : DeclName → DeclName → Bool) :
    ∀ fixture ∈ widthFixtures, STy.implicit isBase fixture.type fixture.type = true := by
  intro fixture _member
  exact fixture_identity isBase fixture

#print axioms table_identity
#print axioms fixedBytes_widening
#print axioms fixedBytes_identity
#print axioms fixedBytes_narrowing
#print axioms fixture_identity
end Solidity.H62.GenericV08
