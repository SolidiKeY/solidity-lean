import Solidity.Backend.MemoryOps.SourceCalldataBoolSlice

/-! Actual sliced Bool conversion composed with the existing paired Source/
intrinsic allocator and named-struct observer. No decoder, allocator, copy loop,
address-injectivity premise or emitted target program is introduced. -/
namespace Solidity.Backend.MemoryOps

/-- Bounds and payload come from INITIAL calldata operands and actual decode.
The only native size premise is validity of the computed selected window.
Reversed/end/decoder rejection executes no allocation suffix. -/
theorem SourceBoolStructAt.slice_bool_copy_native {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {addr : Nat} {hp : Heap H} {r : HRef H (.struct s)}
    {address : Nat → Nat} {layout : SourceBoolStructLayout E dn s tag child}
    (hr : SourceBoolStructAt y addr hp r address layout)
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (root : Source.Idx Γ (.array .calldata .bool none))
    (lo hi : Source.Idx Γ (.int .u256)) (off len : Nat)
    (start finish : PrimTy.uint.Denote) (toEnd : Bool)
    (hroot : y.1.get root=.cdRef rfl off len)
    (hlo : y.1.get lo=sourceUint start) (hhi : y.1.get hi=sourceUint finish)
    (capacity : (if toEnd then len else finish.1.toNat)-start.1.toNat<2^256)
    (SH : Source.HeapTy) (memOK : Source.MemOK E SH y) :
    let stop := if toEnd then len else finish.1.toNat
    if stop<start.1.toNat then
      (Source.evalE G F (fuel+3) (sourceBoolSliceCopy root lo hi toEnd)).run y=(.error (.revert []),y)
    else if len<stop then
      (Source.evalE G F (fuel+3) (sourceBoolSliceCopy root lo hi toEnd)).run y=(.error (.revert []),y)
    else match sourceCalldataBoolValues E F (off+32*start.1.toNat) ((if toEnd then len else finish.1.toNat)-start.1.toNat) with
    | .error e => (Source.evalE G F (fuel+3) (sourceBoolSliceCopy root lo hi toEnd)).run y=(.error e,y)
    | .ok vs => ∃ valid : (sourceBoolValuePayload vs).length<2^256,
      let o : MObj H (.array (.prim .bool)) := ⟨sourceBoolValuePayload vs,valid⟩
      let pair := hp.alloc o
      let e := List.prefix_append H [RefTy.array (.prim .bool)]
      let address' := allocatedSourceAddress address H.length y.2.heap.next
      let z : Source.EMState E Γ :=
        (y.1,{y.2 with heap := (y.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory (sourceBoolValuePayload vs)⟩).1})
      (Source.evalE G F (fuel+3) (sourceBoolSliceCopy root lo hi toEnd)).run y=(.ok (.val (.memRef rfl y.2.heap.next)),z) ∧
      Heap.Keeps e hp pair.1 ∧ SourceBoolStructAt z addr pair.1 (r.wk e) address' layout ∧
      SourceBoolMemoryAt z (address' pair.2.id) pair.1 pair.2 .dyn ∧ Source.MemOK E SH z ∧
      pair.2.id=H.length ∧ address' pair.2.id=y.2.heap.next ∧
      (∀ i,i<H.length → address' i=address i) ∧
      (∀ R (q : HRef H R),(q.wk e).id≠pair.2.id) ∧
      addr≠y.2.heap.next ∧ address (hp.field r layout.child_type).id≠y.2.heap.next ∧
      (∀ q : HRef H (.array (.prim .bool)),SourceBoolMemoryAt y (address q.id) hp q .dyn →
        SourceBoolMemoryAt z (address' (q.wk e).id) pair.1 (q.wk e) .dyn ∧ address q.id≠y.2.heap.next) ∧
      z.1=y.1 ∧ z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  first
  | solve | rfl | simp only [] | omega
  | dsimp only
    by_cases reversed : (if toEnd then len else finish.1.toNat)<start.1.toNat
    · rw [if_pos reversed,source_bool_slice_copy_eval G F fuel y root lo hi off len start finish toEnd hroot hlo hhi,
        if_pos reversed]
    · rw [if_neg reversed]
      by_cases over : len<(if toEnd then len else finish.1.toNat)
      · rw [if_pos over,source_bool_slice_copy_eval G F fuel y root lo hi off len start finish toEnd hroot hlo hhi,
          if_neg reversed,if_pos over]
      · rw [if_neg over]
        have window := source_bool_slice_copy_window G F fuel y root lo hi off len start finish toEnd
          hroot hlo hhi (Nat.le_of_not_gt reversed) (Nat.le_of_not_gt over)
        have paired := hr.cd_bool_copy F (off+32*start.1.toNat)
          ((if toEnd then len else finish.1.toNat)-start.1.toNat) capacity SH memOK
        cases decoded : sourceCalldataBoolValues E F (off+32*start.1.toNat)
            ((if toEnd then len else finish.1.toNat)-start.1.toNat) with
        | error error =>
          rw [decoded] at paired
          exact window.trans paired
        | ok values =>
          rw [decoded] at paired
          obtain ⟨valid,run,rest⟩ := paired
          exact ⟨valid,window.trans run,rest⟩

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.slice_bool_copy_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolStructAt.slice_bool_copy_native
end Solidity.Backend.MemoryOps
