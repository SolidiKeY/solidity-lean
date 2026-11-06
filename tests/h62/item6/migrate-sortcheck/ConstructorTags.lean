import Solidity.SortCheck.Annotations

/-! Frozen numeric constructor-tag expectations, independent of either
compiler's generated implementation. The H76 migration restores the same
legacy aliases in production; these expectations apply on both toolchains. -/
namespace SortCheckMigrationTags
open Solidity.TacletAnnotations

def expectedDomain : ReadDomain → Nat
  | .storage => 0 | .memory => 1 | .net => 2

def expectedSite : ReadSite → Nat
  | .value => 0 | .length => 1 | .net => 2 | .dflt => 3

def expectedVarcond : SortVarcond → Nat
  | .hasSort => 0 | .hasFieldSort => 1 | .hasElementSort => 2
  | .hasMemoryFieldSort => 3 | .hasMemoryElementSort => 4

/-- Solidity storage/memory/net tags retain the original 0/1/2 values. -/
example (d : ReadDomain) : d.toCtorIdx = expectedDomain d := by
  cases d <;> rfl

/-- Solidity value/length/net/default tags retain original 0/1/2/3 values. -/
example (s : ReadSite) : s.toCtorIdx = expectedSite s := by
  cases s <;> rfl

/-- All five Solidity sort-varcond tags retain original numeric values. -/
example (v : SortVarcond) : v.toCtorIdx = expectedVarcond v := by
  cases v <;> rfl
end SortCheckMigrationTags
