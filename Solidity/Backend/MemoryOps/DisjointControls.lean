import Solidity.Backend.MemoryOps.DisjointOverwrite

/-! Actual reference-object writes, nested path observations and alias negatives. -/
namespace Solidity.Backend.MemoryOps.DisjointControls

private abbrev B : RefTy := .array (.prim .bool)
private abbrev P : RefTy := .fixed (.ref B) 2
private abbrev H : HTy := [B, B, P, P]
private def first : HRef H B := ⟨0, rfl⟩
private def second : HRef H B := ⟨1, rfl⟩
private def left : HRef H P := ⟨2, rfl⟩
private def right : HRef H P := ⟨3, rfl⟩
private def heap : Heap H := (⟨[true], by decide⟩, ⟨[false], by decide⟩,
  ⟨[first, second], rfl⟩, ⟨[first, second], rfl⟩, ())
private theorem capacity (hp : Heap H) (p : HRef H P) (offset : Nat) (v : HRef H B)
    (ho : offset ≤ 1) : offset + [v].length ≤ hp.len p .fixed := by
  simp only [Heap.len, MObj.elems_fixed]
  have hn := (hp.get p).property
  change (hp.get p).1.length = 2 at hn
  rw [hn]
  simp only [List.length_singleton]
  omega
private theorem hl : 0 + [second].length ≤ heap.len left .fixed := capacity heap left 0 second (by decide)
private theorem hr : 1 + [first].length ≤ heap.len right .fixed := capacity heap right 1 first (by decide)
private theorem separated : left.id ≠ right.id := by decide
private def out := overwriteTwo heap left .fixed 0 [second] hl right .fixed 1 [first] hr separated
private def rev := overwriteTwo heap right .fixed 1 [first] hr left .fixed 0 [second] hl separated.symm

/-- Both nonprimitive writes are inhabited and exact whole heaps commute. -/
theorem reference_commutation : out = rev :=
  overwriteTwo_comm heap left .fixed 0 [second] hl right .fixed 1 [first] hr separated

/-- The two parent slots really change, while both child objects retain contents. -/
theorem reference_effects :
    (MObj.elems .fixed (out.get left)).map HRef.id = [1, 1] ∧
    (MObj.elems .fixed (out.get right)).map HRef.id = [0, 0] ∧
    out.get first = heap.get first ∧ out.get second = heap.get second := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [out, overwriteTwo_first, overwriteSlice_elems]
    simp only [MObj.elems_fixed]
    rfl
  · rw [reference_commutation, rev, overwriteTwo_first, overwriteSlice_elems]
    simp only [MObj.elems_fixed]
    rfl
  · exact overwriteTwo_frame heap left .fixed 0 [second] hl right .fixed 1 [first] hr separated first (by decide) (by decide)
  · exact overwriteTwo_frame heap left .fixed 0 [second] hl right .fixed 1 [first] hr separated second (by decide) (by decide)

private abbrev Γ : Ctx := [.mem P, .mem P]
private def state : State StandardExample Γ :=
  {storage := Storage.init StandardExample, H := H, heap := heap, env := (some left, some right, ())}
private def zero : Val StandardExample Γ .uint := .simple (.lit 0 (by decide))
private def two : Val StandardExample Γ .uint := .simple (.lit 2 (by decide))
private def path : MPath StandardExample Γ (.prim .bool) :=
  .loc (.index .dyn (.loc (.index .fixed (.var .here rfl) zero)) zero)
private def badPath : MPath StandardExample Γ (.ref B) :=
  .loc (.index .fixed (.var .here rfl) two)

/-- Published nested typed path evaluation actually reads the redirected child. -/
theorem nested_path :
    path.mvalT {state with heap := out} = .ok false ∧
    path.mvalT {state with heap := rev} = .ok false := by
  constructor <;> simp only [path, MPath.mvalT, MLoc.addrT, Val.evalT,
    Simple.evalT, Heap.readAddr, Heap.index, MObj.elems_dyn, MObj.elems_fixed,
    TRes.ofOpt, state, TEnv.get, zero, PrimTy.ofLit,
    out, rev, overwriteTwo, overwriteSlice, withElems, heap, left, right, first, second,
    bind, pure, Except.bind, Except.pure, Heap.get, Heap.set, Objs.get, Objs.set, replaceSlice, List.take, List.drop, List.length,
    List.getElem?_cons_zero, Int.toNat, List.nil_append, List.cons_append]
    <;> decide +kernel

/-- The path-equality theorem applies to the concrete nested path. -/
theorem path_application :
    path.mvalT {state with heap := out} = path.mvalT {state with heap := rev} :=
  overwriteTwo_path state left .fixed 0 [second] hl right .fixed 1 [first] hr separated path

/-- Fixed-array bounds failure is preserved, rather than treated as success. -/
theorem path_bounds_failure :
    badPath.mvalT {state with heap := out} = .error .revert ∧
    badPath.mvalT {state with heap := rev} = .error .revert := by
  constructor <;> simp only [badPath, MPath.mvalT, MLoc.addrT, Val.evalT,
    Simple.evalT, Heap.readAddr, Heap.index, MObj.elems_dyn, MObj.elems_fixed,
    TRes.ofOpt, state, TEnv.get, two, PrimTy.ofLit,
    out, rev, overwriteTwo, overwriteSlice, withElems, heap, left, right, first, second,
    bind, pure, Except.bind, Except.pure, Heap.get, Heap.set, Objs.get, Objs.set, replaceSlice, List.take, List.drop, List.length,
    List.getElem?_cons_succ, List.getElem?_nil, Int.toNat, List.nil_append, List.cons_append]
    <;> decide +kernel

private def put (hp : Heap H) (v : HRef H B) : Heap H :=
  overwriteSlice hp left .fixed 0 [v] (capacity hp left 0 v (by decide))

/-- Removing separation would be false: two aliases to one slot do not commute. -/
theorem alias_negative : put (put heap second) first ≠ put (put heap first) second := by
  intro he
  have ho := congrArg (fun hp : Heap H => (MObj.elems .fixed (hp.get left)).map HRef.id) he
  simp only [put, overwriteSlice_elems, MObj.elems_fixed] at ho
  change [0, 1] = [1, 1] at ho
  cases ho

/-- info: 'Solidity.Backend.MemoryOps.DisjointControls.reference_commutation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reference_commutation
/-- info: 'Solidity.Backend.MemoryOps.DisjointControls.reference_effects' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reference_effects
/-- info: 'Solidity.Backend.MemoryOps.DisjointControls.nested_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nested_path
/-- info: 'Solidity.Backend.MemoryOps.DisjointControls.path_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms path_application
/-- info: 'Solidity.Backend.MemoryOps.DisjointControls.path_bounds_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms path_bounds_failure
/-- info: 'Solidity.Backend.MemoryOps.DisjointControls.alias_negative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms alias_negative

end Solidity.Backend.MemoryOps.DisjointControls
