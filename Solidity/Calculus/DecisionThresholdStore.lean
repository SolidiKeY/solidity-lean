import Solidity.Semantics.Storage
import Solidity.Semantics.State

/-!
# Threshold-uniform storages: symbolic countermodel regions

One storage per `Fill`: every dynamic array has `len` slots, every fixed
array its own length, every mapping one default and no entries, and every
primitive leaf reads `lo` when each array index on its path is below `n`,
`hi` otherwise. A whole storage of the contract is built this way, without
listing keys or slots of a mapping: a mapping is its default. It is the
candidate countermodel of literal-bounded blocks (`Calculus/DecisionBlockRefute.lean`),
where reads at an index below the bound see `lo` and a read past it sees `hi`
or halts.

The construction follows `SVal.dflt`: recursion on a rank bound, and inside
one rank structurally on the type. No property of the result is assumed by
its consumers; each candidate is checked.
-/
namespace Solidity.Decide.ThresholdStore
open Semantics (structDef tyRank fieldsRank)

/-- The parameters of one region. -/
structure Fill where
  n : Nat
  len : Nat
  hlen : len < 2 ^ 256
  lo : (p : PrimTy) → p.Denote
  hi : (p : PrimTy) → p.Denote

/-- `m` values, the `j`-th (from `off`) given by `f`. -/
def build {E : Ty} (f : Nat → SVal E) : (m : Nat) → (off : Nat) → SVec E m
  | 0, _ => .nil
  | m + 1, off => .cons (f off) (build f m (off + 1))

mutual
/-- The region's values of rank at most `k`, given those below. -/
def valAt (F : Fill) (k : Nat) (ih : (T : Ty) → Bool → tyRank T < k → SVal T) :
    (T : Ty) → Bool → tyRank T < k + 1 → SVal T
  | .prim p, b, _ => .prim (if b then F.lo p else F.hi p)
  | .ref R, b, h => refAt F k ih R b h

def refAt (F : Fill) (k : Nat) (ih : (T : Ty) → Bool → tyRank T < k → SVal T) :
    (R : RefTy) → Bool → tyRank (.ref R) < k + 1 → SVal (.ref R)
  | .struct s, b, h =>
    .struct (SFields.dfltBelow k (fun T hT => ih T b hT) (structDef s)
      (Nat.lt_of_lt_of_le (Semantics.structDef_rank_lt s) (Nat.le_of_lt_succ h)))
  | .array E, b, h =>
    .array (build (fun j => valAt F k ih E (b && decide (j < F.n))
      (by simpa only [tyRank] using h)) F.len 0) .nil F.hlen
  | .fixed E n, b, h =>
    .fixed (build (fun j => valAt F k ih E (b && decide (j < F.n))
      (Nat.lt_of_succ_lt (by simpa only [tyRank] using h))) n 0)
  | .mapping _ V, b, h => .map .nil (valAt F k ih V b (by simpa only [tyRank] using h))
end

/-- The region's values below rank `k`. -/
def valBelow (F : Fill) : (k : Nat) → (T : Ty) → Bool → tyRank T < k → SVal T
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, T, b, h => valAt F k (valBelow F k) T b h

/-- The region's value of `T`, below the threshold. -/
def val (F : Fill) (T : Ty) : SVal T :=
  valBelow F (rankBound T + 1) T true (Nat.lt_succ_of_le (tyRank_le_rankBound T))

/-- Every member at its region value. -/
def fields (F : Fill) : (fs : List (Name × Ty)) → SFields fs
  | [] => .nil
  | (_, T) :: fs => .cons (val F T) (fields F fs)

/-- The whole storage of a contract in the region. -/
def storage (F : Fill) (C : Contract) : Storage C := fields F C.vars

/-- The initial state with the region's storage. -/
def state (F : Fill) (C : Contract) : State C [] := (State.init C).withStorage (storage F C)

end Solidity.Decide.ThresholdStore
