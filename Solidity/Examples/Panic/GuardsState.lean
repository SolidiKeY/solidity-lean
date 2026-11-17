import Solidity.Correctness.Panic.Guards.State

/-!
# State guard regressions

Each state guard family at a concrete failing evaluation: an index past a
storage array (dynamic and fixed), an index past a memory array (dynamic and
fixed) and a pop of an empty array. The emitted code is read off the site
(`0x32`, `0x31`); the last valid index is the control that the guard passes.
-/

namespace Solidity.Examples.Panic.GuardsState
open Solidity Semantics Solidity.Correctness.Panic

private def u (n : Nat) : PrimTy.uint.Denote := uintOfNat n
private def C : Contract :=
  contract!{ uint[] values; uint[2] pair; mapping(uint => uint) table; }
private def σ₀ : State C [] := State.init C

private def values : SPath C [] (.ref (.array (.prim .uint))) := .loc (.root "values" rfl)
private def pair : SPath C [] (.ref (.fixed (.prim .uint) 2)) := .loc (.root "pair" rfl)
private def table : SPath C [] (.ref (.mapping .uint (.prim .uint))) := .loc (.root "table" rfl)
private def lit (n : Nat) (h : PrimTy.uint.inRange (n : Int) = true := by decide) :
    Val C [] .uint := Checked.litU n h

/-- `values[0]` on the empty array: the guard is false, so the association
gives the bounds origin, V1's bare revert and solc's `Panic(0x32)` bytes. -/
theorem storage_dyn_past_end :
    Panic.Origin (.storageIndex σ₀.storage (.ofRoot "values" rfl) .dyn (u 0)) .bounds ∧
    (Loc.index (.arr .dyn) values (lit 0)).resolveT σ₀ = .error .revert ∧
    (panicStmt 0x32 (Checked.cmpU .lt rfl rfl (lit 0) (.len values rfl))).runR σ₀ =
      .error (THalt.ofData (encodePanic 0x32)) :=
  (storage_dyn_index_source σ₀ values (lit 0) (.ofRoot "values" rfl) (u 0) rfl rfl
    ((storage_dyn_index_guard_eval σ₀ values (lit 0) (.ofRoot "values" rfl) (u 0) _ rfl rfl
      rfl).trans (congrArg Except.ok (by rfl)))).2

/-- The whole index location's guards are exactly the generated bounds check. -/
example : (Loc.index (.arr .dyn) values (lit 0)).panics =
    [(0x32, Checked.cmpU .lt rfl rfl (lit 0) (.len values rfl))] :=
  storage_dyn_index_guards values (lit 0)

/-- `pair[2]` of a `uint[2]`: one past the last element. -/
theorem storage_fixed_past_end :
    Checked.idxPG (.arr .fixed) pair (lit 2) =
      [(0x32, Checked.cmpU .lt rfl rfl (lit 2) (Checked.litU 2 (by decide)))] ∧
    Panic.Origin (.storageIndex σ₀.storage (.ofRoot "pair" rfl) .fixed (u 2)) .bounds ∧
    (Loc.index (.arr .fixed) pair (lit 2)).resolveT σ₀ = .error .revert ∧
    (panicStmt 0x32 (Checked.cmpU .lt rfl rfl (lit 2) (Checked.litU 2 (by decide)))).runR σ₀ =
      .error (THalt.ofData (encodePanic 0x32)) :=
  storage_fixed_index_source σ₀ pair (lit 2) (.ofRoot "pair" rfl) (u 2) _ (by decide) rfl rfl
    rfl ((fixed_index_guard_eval σ₀ (lit 2) (u 2) 2 (by decide) rfl).trans (congrArg Except.ok (by rfl)))

/-- Control: `pair[1]`, the last element, passes the same guard. -/
example : (Checked.cmpU .lt rfl rfl (lit 1) (Checked.litU 2 (by decide))).evalT σ₀ = .ok true :=
  (fixed_index_guard_eval σ₀ (lit 1) (u 1) 2 (by decide) rfl).trans (congrArg Except.ok (by rfl))

/-- A mapping read has no bounds guard: every key is taken. -/
example : (Loc.index .map table (lit 5)).panics = [] :=
  storage_mapping_index_no_guard table (lit 5)

/-- `values.pop()` on the empty array: the empty-pop origin in the statement's
own shadow mode, V1's bare revert and solc's `Panic(0x31)` bytes. -/
theorem pop_empty :
    (Stmt.pop values).panics = [(0x31, Checked.cmpU .gt rfl rfl (.len values rfl)
      (Checked.litU 0 (by decide)))] ∧
    Panic.Origin (.pop σ₀.storage (Ty.prim .uint).isMapping (.ofRoot "values" rfl)) .emptyPop ∧
    (Stmt.pop values).runR σ₀ = .error .revert ∧
    (panicStmt 0x31 (Checked.cmpU .gt rfl rfl (.len values rfl)
      (Checked.litU 0 (by decide)))).runR σ₀ = .error (THalt.ofData (encodePanic 0x31)) :=
  pop_source σ₀ values (.ofRoot "values" rfl) _ rfl rfl

/-- `true && values[0] == 0`: the index guard is emitted under the left
operand, and its failure is the bare guard's, so the same origin follows. -/
example (failed : (Checked.orB (Checked.notB Checked.tt)
      (Checked.cmpU .lt rfl rfl (lit 0) (.len values rfl))).evalT σ₀ = .ok false) :
    Panic.Origin (.storageIndex σ₀.storage (.ofRoot "values" rfl) .dyn (u 0)) .bounds :=
  (storage_dyn_index_guard_origin σ₀ values (lit 0) (.ofRoot "values" rfl) (u 0) rfl rfl
    (guard_under_failed σ₀ _ _ failed).2).1

private abbrev A : RefTy := .array (.prim .uint)
private abbrev F : RefTy := .fixed (.prim .uint) 2
private def dynObj : MObj [] A := ⟨[u 7], by decide⟩
private def fixObj : MObj [A] F := ⟨[u 7, u 8], rfl⟩
private def dynRef : HRef [A, F] A := ⟨0, rfl⟩
private def fixRef : HRef [A, F] F := ⟨1, rfl⟩

/-- A state with a one-element `uint[] memory` and a `uint[2] memory`. -/
private def σₘ : State C [.mem F, .mem A] :=
  { storage := Storage.init C, H := [A, F],
    heap := (((Heap.empty.alloc dynObj).1).alloc fixObj).1,
    env := (some fixRef, some dynRef, ()) }

private def mdyn : MPath C [.mem F, .mem A] (.ref A) := .var (.there .here) rfl
private def mfix : MPath C [.mem F, .mem A] (.ref F) := .var .here rfl
private def mlit (n : Nat) (h : PrimTy.uint.inRange (n : Int) = true := by decide) :
    Val C [.mem F, .mem A] .uint := Checked.litU n h

/-- `m[1]` of a one-element memory array: the guard read the heap length the
producer indexes, and fails with the bounds origin and `Panic(0x32)`. -/
theorem memory_dyn_past_end :
    Checked.mIdxPG .dyn mdyn (mlit 1) =
      [(0x32, Checked.cmpU .lt rfl rfl (mlit 1) (.mlen mdyn rfl))] ∧
    Panic.Origin (.index σₘ.heap dynRef .dyn (u 1)) .bounds ∧
    (MPath.loc (.index .dyn mdyn (mlit 1))).mvalT σₘ = .error .revert ∧
    (panicStmt 0x32 (Checked.cmpU .lt rfl rfl (mlit 1) (.mlen mdyn rfl))).runR σₘ =
      .error (THalt.ofData (encodePanic 0x32)) :=
  memory_dyn_index_source σₘ mdyn (mlit 1) dynRef (u 1) rfl rfl
    ((memory_dyn_index_guard_eval σₘ mdyn (mlit 1) dynRef (u 1) rfl rfl).trans
      (congrArg Except.ok (by rw [Heap.len, MObj.elems_dyn]; rfl)))

/-- `f[2]` of a `uint[2] memory`. -/
theorem memory_fixed_past_end :
    Panic.Origin (.index σₘ.heap fixRef .fixed (u 2)) .bounds ∧
    (MPath.loc (.index .fixed mfix (mlit 2))).mvalT σₘ = .error .revert ∧
    (panicStmt 0x32 (Checked.cmpU .lt rfl rfl (mlit 2) (Checked.litU 2 (by decide)))).runR σₘ =
      .error (THalt.ofData (encodePanic 0x32)) :=
  (memory_fixed_index_source σₘ mfix (mlit 2) fixRef (u 2) (by decide) rfl rfl
    ((fixed_index_guard_eval σₘ (mlit 2) (u 2) 2 (by decide) rfl).trans (congrArg Except.ok (by rfl)))).2

/-- Control: the guard of `m[0]` read length one and passes. -/
example : (Val.mlen mdyn rfl).evalT σₘ = .ok (σₘ.heap.lenU dynRef) :=
  (memory_guard_length σₘ mdyn dynRef rfl).1

end Solidity.Examples.Panic.GuardsState
