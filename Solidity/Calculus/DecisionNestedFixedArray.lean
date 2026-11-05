import Solidity.Calculus.FixedArrayRoot

/-!
# Independent flooring of both fixed-array dimensions

Reconstruct intrinsic rows before flooring the outer vector. Both length
breakpoints are required; this interface makes no classifier or verdict claim.
-/
namespace Solidity.Decide

/-- Floor every intrinsic row while keeping the outer length. -/
def fixedFloorRows {E : Ty} {m : Nat} (B : List Int) :
    {n : Nat} → SVec (.ref (.fixed E m)) n → SVec (.ref (.fixed E m)) n
  | _, .nil => .nil
  | _, .cons row rows => .cons (fixedFloorValue B row) (fixedFloorRows B rows)

/-- The reconstruction changes rows pointwise, without adding or removing rows. -/
theorem fixedFloorRows_toList {E : Ty} {m : Nat} (B : List Int) :
    {n : Nat} → (v : SVec (.ref (.fixed E m)) n) →
    (fixedFloorRows B v).toList = v.toList.map (fixedFloorValue B)
  | _, .nil => by simp only [fixedFloorRows, SVec.toList_nil, List.map_nil]
  | _, .cons row rows => by
    rw [fixedFloorRows, SVec.toList_cons, SVec.toList_cons, List.map_cons,
      fixedFloorRows_toList B rows]

/-- Rebuild both dimensions, each with its own finite breakpoint list. -/
def nestedFixedFloor {E : Ty} {m n : Nat} (outer inner : List Int)
    (v : SVec (.ref (.fixed E m)) n) : SVal (.ref (.fixed (.ref (.fixed E m)) n)) :=
  .fixed (fixedFloorVec outer (fixedFloorRows inner v))

/-- Both length breakpoints preserve every optional two-index continuation. -/
theorem nestedFixedFloor_find {E U : Ty} {m n : Nat} (outer inner : List Int)
    (v : SVec (.ref (.fixed E m)) n) (hn : (n : Int) ∈ outer)
    (hm : (m : Int) ∈ inner) (i j : PrimTy.uint.Denote) (q : Path E U) :
    (nestedFixedFloor outer inner v).findM (.atF i (.atF j q)) =
      (SVal.fixed v).findM
        (.atF (fixedFloorIndex outer i) (.atF (fixedFloorIndex inner j) q)) := by
  rw [nestedFixedFloor, fixedFloorVec_find outer (fixedFloorRows inner v) hn]
  simp only [SVal.findM, fixedFloorRows_toList, List.getElem?_map]
  cases h : v.toList[(fixedFloorIndex outer i).1.toNat]? with
  | none => rfl
  | some row => exact fixedFloorValue_find inner row hm j q

end Solidity.Decide
