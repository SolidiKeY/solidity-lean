import Solidity.Yul.Composition.Concrete
import Solidity.Yul.Compilation.NestedWrites

/-! Concrete computed-result transport through an actual newer-local prefix.
Target-only; no source modifier/function/library calling convention is assumed.
-/
namespace Solidity.Yul.Composition
open Solidity.Backend Scalar
open Solidity.Yul.Compilation

def computedOuterWrite {n k : Nat} (newer : Vector Word k) (i : Fin n)
    (accessible : k + i.val < 16) (a b : UInt8) : Program :=
  (pushPrefix newer.toList ++ (literalSum a b).code) ++
    (writeSlot ⟨k + i.val, accessible⟩ ++ popPrefix k)

/-- The actual ADD result, including values greater than255, is stored into an indexed
outer local. Newer locals are removed and the caller tail is retained exactly.
This does not identify target words with Solidity narrow/dirty source locals. -/
theorem computed_outer_write {n k : Nat} (locals : Vector Word n)
    (newer : Vector Word k) (i : Fin n) (accessible : k + i.val < 16)
    (a b : UInt8) (tail : Stack) :
    run (computedOuterWrite newer i accessible a b) (locals.toList ++ tail) =
      some ((locals.set i.val (BitVec.ofNat 256 a.toNat + BitVec.ofNat 256 b.toNat) i.isLt).toList ++ tail) := by
  unfold computedOuterWrite
  apply run_comp
  · exact run_comp (pushPrefix_run newer.toList (locals.toList ++ tail))
      (literalSum_run a b (newer.toList ++ (locals.toList ++ tail)))
  · apply run_comp (write_under_prefix locals newer i accessible
      (BitVec.ofNat 256 a.toNat + BitVec.ofNat 256 b.toNat) tail)
    simpa only [Vector.length_toList] using popPrefix_run newer.toList
      ((locals.set i.val (BitVec.ofNat 256 a.toNat + BitVec.ofNat 256 b.toNat) i.isLt).toList ++ tail)

theorem computed_outer_read {n k : Nat} (locals : Vector Word n)
    (newer : Vector Word k) (i : Fin n) (accessible : k + i.val < 16)
    (a b : UInt8) (tail : Stack) :
    run (computedOuterWrite newer i accessible a b ++
      [readSlot ⟨i.val, by omega⟩]) (locals.toList ++ tail) =
      some ((BitVec.ofNat 256 a.toNat + BitVec.ofNat 256 b.toNat) ::
        ((locals.set i.val (BitVec.ofNat 256 a.toNat + BitVec.ofNat 256 b.toNat) i.isLt).toList ++ tail)) := by
  apply run_comp (computed_outer_write locals newer i accessible a b tail)
  simp only [run]
  rw [read_local, Vector.getElem_set_self]
  rfl

example : run (computedOuterWrite #v[42] (n := 2) ⟨1, by decide⟩ (by decide) 250 9)
    [7,8,99] = some [7,259,99] := by decide +kernel
example : run (computedOuterWrite #v[42] (n := 2) ⟨0, by decide⟩ (by decide) 250 9)
    [7,8,99] ≠ some [7,259,99] := by decide +kernel
#print axioms computed_outer_write
#print axioms computed_outer_read
end Solidity.Yul.Composition
