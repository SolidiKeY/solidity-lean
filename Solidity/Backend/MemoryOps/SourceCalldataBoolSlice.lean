import Solidity.Backend.MemoryOps.SourceCalldataTransfer
import Solidity.Backend.MemoryOps.SourceSequence

/-! Actual resolved calldata slicing followed by the existing Boolean conversion.
The shifted raw input, slice rejection and decoder/allocation outcomes are
computed by the published Source operations. No target-copy or ABI-admission
certificate is inferred from this component. -/
namespace Solidity.Backend.MemoryOps

/-- The original calldata identity is retained; only its offset and length
change. Absent end uses the original length, not the supplied end operand. -/
theorem source_bool_slice_value {D : Source.Layout} (off len s e : Nat) (toEnd : Bool) :
    Source.sliceR (Source.Val.cdRef (D := D)
      (τ := .array .calldata .bool none) rfl off len) s e toEnd=
      let stop := if toEnd then len else e
      if stop<s then .error (.revert []) else if len<stop then .error (.revert [])
      else .ok (.cdRef rfl (off+32*s) (stop-s)) := by
  first | rfl | simp only [Source.sliceR]

/-- Use the existing typed slice constructor and conversion; no new copy or
slice operation is defined. Indices are evaluated after the array, in order. -/
def sourceBoolSliceCopy {E : Source.Env} {Γ : Source.RCtx}
    (root : Source.Idx Γ (.array .calldata .bool none))
    (start finish : Source.Idx Γ (.int .u256)) (toEnd : Bool) :
    Source.RExpr E Γ (.array .memory .bool none) :=
  .conv (.slice (.local root) (by decide) (.local start) rfl (.local finish) rfl toEnd) (.inl rfl)

/-- All three local operands are initial alignments. The outcome is the actual
slice computation, not a desired reached reference supplied as a premise. -/
theorem source_bool_slice_eval {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (y : Source.EMState E Γ)
    (root : Source.Idx Γ (.array .calldata .bool none))
    (start finish : Source.Idx Γ (.int .u256)) (off len : Nat)
    (s e : PrimTy.uint.Denote) (toEnd : Bool)
    (hr : y.1.get root=.cdRef rfl off len)
    (hs : y.1.get start=sourceUint s) (he : y.1.get finish=sourceUint e) :
    (Source.evalE G F (fuel+2)
      (.slice (.local root) (by decide) (.local start) rfl (.local finish) rfl toEnd)).run y=
      (match Source.sliceR (Source.Val.cdRef (D := E.layout)
        (τ := .array .calldata .bool none) rfl off len) s.1.toNat e.1.toNat toEnd with
        | .error error => .error error
        | .ok value => .ok (.val value),y) := by
  rw [Source.evalE,Source.Hoare.run_bind,source_local_value_run G F fuel y root _ hr]
  change ((Source.evalE G F (fuel+1) (.local start)) >>= fun sv =>
    Source.indexNat sv >>= fun si => (Source.evalE G F (fuel+1) (.local finish)) >>= fun ev =>
    Source.indexNat ev >>= fun ei => Source.EM.lift
      (Source.sliceR (Source.Val.cdRef (D := E.layout)
        (τ := .array .calldata .bool none) rfl off len) si ei toEnd) >>=
          fun value => pure (Source.RVal.val value)).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F fuel y start _ hs]
  change ((Source.evalE G F (fuel+1) (.local finish)) >>= fun ev =>
    Source.indexNat ev >>= fun ei => Source.EM.lift
      (Source.sliceR (Source.Val.cdRef (D := E.layout)
        (τ := .array .calldata .bool none) rfl off len) s.1.toNat ei toEnd) >>=
          fun value => pure (Source.RVal.val value)).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F fuel y finish _ he]
  change ((Source.EM.lift (Source.sliceR (Source.Val.cdRef (D := E.layout)
    (τ := .array .calldata .bool none) rfl off len) s.1.toNat e.1.toNat toEnd)) >>=
      fun value => pure (Source.RVal.val value)).run y=_
  rw [Source.Hoare.run_bind]
  cases result : Source.sliceR (Source.Val.cdRef (D := E.layout)
    (τ := .array .calldata .bool none) rfl off len) s.1.toNat e.1.toNat toEnd <;> rfl

/-- The actual conversion runs only after the actual slice has succeeded.
Slice bounds failure has no allocated suffix heap; decoder failure likewise
retains the input state as established by the existing copy law. -/
theorem source_bool_slice_copy_eval {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (y : Source.EMState E Γ)
    (root : Source.Idx Γ (.array .calldata .bool none))
    (start finish : Source.Idx Γ (.int .u256)) (off len : Nat)
    (s e : PrimTy.uint.Denote) (toEnd : Bool)
    (hr : y.1.get root=.cdRef rfl off len)
    (hs : y.1.get start=sourceUint s) (he : y.1.get finish=sourceUint e) :
    (Source.evalE G F (fuel+3) (sourceBoolSliceCopy root start finish toEnd)).run y=
      let stop := if toEnd then len else e.1.toNat
      if stop<s.1.toNat then (.error (.revert []),y)
      else if len<stop then (.error (.revert []),y)
      else match sourceCalldataBoolValues E F (off+32*s.1.toNat) (stop-s.1.toNat) with
      | .error error => (.error error,y)
      | .ok vs =>
        let xs := sourceBoolValuePayload vs
        (.ok (.val (.memRef rfl y.2.heap.next)),
          (y.1,{y.2 with heap := (y.2.heap.alloc
            ⟨.array .memory .bool none,sourceBoolMemory xs⟩).1})) := by
  rw [sourceBoolSliceCopy,Source.evalE,Source.Hoare.run_bind,
    source_bool_slice_eval G F fuel y root start finish off len s e toEnd hr hs he,
    source_bool_slice_value]
  by_cases reversed : (if toEnd then len else e.1.toNat)<s.1.toNat
  · simp only [if_pos reversed]
  · by_cases over : len<(if toEnd then len else e.1.toNat)
    · simp only [if_neg reversed,if_pos over]
    · simp only [if_neg reversed,if_neg over]
      change (Source.convRV F (fuel+2) (.array .memory .bool none)
        (.val (.cdRef rfl (off+32*s.1.toNat)
          ((if toEnd then len else e.1.toNat)-s.1.toNat)) :
            Source.RVal E.layout (.array .calldata .bool none))).run y=_
      unfold Source.convRV
      rw [dif_neg (show (Source.STy.array .calldata .bool none)≠
        .array .memory .bool none from by intro h;cases h)]
      exact source_cd_bool_run F _ _ y

/-- A valid actual slice feeds exactly its shifted window into the existing
copy producer. Bounds concern the original reference, not a decoder oracle. -/
theorem source_bool_slice_copy_window {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (y : Source.EMState E Γ)
    (root : Source.Idx Γ (.array .calldata .bool none))
    (start finish : Source.Idx Γ (.int .u256)) (off len : Nat)
    (s e : PrimTy.uint.Denote) (toEnd : Bool)
    (hr : y.1.get root=.cdRef rfl off len)
    (hs : y.1.get start=sourceUint s) (he : y.1.get finish=sourceUint e)
    (ordered : s.1.toNat≤(if toEnd then len else e.1.toNat))
    (bounded : (if toEnd then len else e.1.toNat)≤len) :
    (Source.evalE G F (fuel+3) (sourceBoolSliceCopy root start finish toEnd)).run y=
      (Source.cdToMem F (.array .memory .bool none)
        (off+32*s.1.toNat) ((if toEnd then len else e.1.toNat)-s.1.toNat)).run y := by
  first
  | rfl
  | simp only [source_bool_slice_copy_eval G F fuel y root start finish off len s e toEnd hr hs he,
      if_neg (Nat.not_lt.mpr ordered),if_neg (Nat.not_lt.mpr bounded),source_cd_bool_run]
    rfl

/-- info: 'Solidity.Backend.MemoryOps.source_bool_slice_value' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms source_bool_slice_value
/-- info: 'Solidity.Backend.MemoryOps.source_bool_slice_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_bool_slice_eval
/-- info: 'Solidity.Backend.MemoryOps.source_bool_slice_copy_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_bool_slice_copy_eval
/-- info: 'Solidity.Backend.MemoryOps.source_bool_slice_copy_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_bool_slice_copy_window
end Solidity.Backend.MemoryOps
