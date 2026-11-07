import Solidity.Backend.MemoryOps.SourceCalldataBoolSlice

/-! Actual indexing through a computed Source calldata slice. Only published
slice, index-location and read/decoder operations execute; no decoder, path
interpreter or target memory is introduced. Offsets are existing Source Nat
arithmetic, not a physical wrapping-address correspondence. -/
namespace Solidity.Backend.MemoryOps

/-- A one-word element is statically encoded in one word. -/
theorem oneWord_cdStaticWords {element : Source.STy} (single : element.oneWord=true) :
    element.cdStaticWords=1 := by
  unfold Source.STy.cdStaticWords; simp only [single,if_true]

/-- A one-word element has a one-word calldata head, so its dynamic array
admits range slicing. -/
theorem oneWord_sliceable {element : Source.STy} (single : element.oneWord=true) :
    (Source.STy.array .calldata element none).sliceable=true := by
  simp only [Source.STy.sliceable,oneWord_cdStaticWords single]; decide

/-- A one-word element's calldata stride is one word. -/
theorem oneWord_cdStride {element : Source.STy} (single : element.oneWord=true) :
    (Source.STy.array .calldata element none).cdStride=32 := by
  simp only [Source.STy.cdStride,Source.STy.cdHeadBytes,oneWord_cdStaticWords single]; decide

/-- The existing typed syntax for a one-word array slice followed by indexing. -/
def sourceSliceIndex {E : Source.Env} {Γ : Source.RCtx}
    (element : Source.STy) (single : element.oneWord=true)
    (root : Source.Idx Γ (.array .calldata element none))
    (start finish index : Source.Idx Γ (.int .u256)) (toEnd : Bool) :
    Source.RExpr E Γ element :=
  .indexArray (.slice (.local root) (oneWord_sliceable single) (.local start) rfl (.local finish) rfl toEnd)
    (.local index) rfl

/-- All three local operands are initial alignments. The outcome is the actual
slice computation, not a desired reached reference supplied as a premise. -/
theorem source_array_slice_eval {E : Source.Env} {Γ : Source.RCtx}
    (element : Source.STy) (single : element.oneWord=true)
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (y : Source.EMState E Γ)
    (root : Source.Idx Γ (.array .calldata element none))
    (start finish : Source.Idx Γ (.int .u256)) (off len : Nat)
    (s e : PrimTy.uint.Denote) (toEnd : Bool)
    (hr : y.1.get root=.cdRef rfl off len)
    (hs : y.1.get start=sourceUint s) (he : y.1.get finish=sourceUint e) :
    (Source.evalE G F (fuel+2)
      (.slice (.local root) (oneWord_sliceable single) (.local start) rfl (.local finish) rfl toEnd)).run y=
      (match Source.sliceR (Source.Val.cdRef (D := E.layout)
        (τ := .array .calldata element none) rfl off len) s.1.toNat e.1.toNat toEnd with
        | .error error => .error error
        | .ok value => .ok (.val value),y) := by
  rw [Source.evalE,Source.Hoare.run_bind,source_local_value_run G F fuel y root _ hr]
  change ((Source.evalE G F (fuel+1) (.local start)) >>= fun sv =>
    Source.indexNat sv >>= fun si => (Source.evalE G F (fuel+1) (.local finish)) >>= fun ev =>
    Source.indexNat ev >>= fun ei => Source.EM.lift
      (Source.sliceR (Source.Val.cdRef (D := E.layout)
        (τ := .array .calldata element none) rfl off len) si ei toEnd) >>=
          fun value => pure (Source.RVal.val value)).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F fuel y start _ hs]
  change ((Source.evalE G F (fuel+1) (.local finish)) >>= fun ev =>
    Source.indexNat ev >>= fun ei => Source.EM.lift
      (Source.sliceR (Source.Val.cdRef (D := E.layout)
        (τ := .array .calldata element none) rfl off len) s.1.toNat ei toEnd) >>=
          fun value => pure (Source.RVal.val value)).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F fuel y finish _ he]
  change ((Source.EM.lift (Source.sliceR (Source.Val.cdRef (D := E.layout)
    (τ := .array .calldata element none) rfl off len) s.1.toNat e.1.toNat toEnd)) >>=
      fun value => pure (Source.RVal.val value)).run y=_
  rw [Source.Hoare.run_bind]
  cases result : Source.sliceR (Source.Val.cdRef (D := E.layout)
    (τ := .array .calldata element none) rfl off len) s.1.toNat e.1.toNat toEnd <;> rfl

/-- Complete actual result of slice then indexed read. Slice bounds precede
index bounds; only an in-range selected word is decoded. Unselected malformed
words are not silently validated. All outcomes retain the actual input state. -/
theorem source_slice_index_eval {E : Source.Env} {Γ : Source.RCtx}
    (element : Source.STy) (single : element.oneWord=true)
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (y : Source.EMState E Γ)
    (root : Source.Idx Γ (.array .calldata element none))
    (start finish index : Source.Idx Γ (.int .u256)) (off len : Nat)
    (s e k : PrimTy.uint.Denote) (toEnd : Bool)
    (hr : y.1.get root=.cdRef rfl off len)
    (hs : y.1.get start=sourceUint s) (he : y.1.get finish=sourceUint e)
    (hk : y.1.get index=sourceUint k) :
    (Source.evalE G F (fuel+3) (sourceSliceIndex element single root start finish index toEnd)).run y=
      let stop := if toEnd then len else e.1.toNat
      if stop<s.1.toNat then (.error (.revert []),y)
      else if len<stop then (.error (.revert []),y)
      else if k.1.toNat<stop-s.1.toNat then
        (match Source.decodeWord E.layout (Source.cdWordAt F (off+32*(s.1.toNat+k.1.toNat))) element with
        | .error error => .error error
        | .ok value => .ok (.val value),y)
      else (.error (.revert (Source.panicData .index)),y) := by
  rw [sourceSliceIndex,Source.evalE,Source.Hoare.run_bind,
    source_array_slice_eval element single G F fuel y root start finish off len s e toEnd hr hs he]
  simp only [Source.sliceR,oneWord_cdStride single]
  by_cases reversed : (if toEnd then len else e.1.toNat)<s.1.toNat
  · simp only [if_pos reversed]
  · by_cases over : len<(if toEnd then len else e.1.toNat)
    · simp only [if_neg reversed,if_pos over]
    · simp only [if_neg reversed,if_neg over]
      change ((Source.evalE G F (fuel+2) (.local index)) >>= fun kv =>
        Source.indexNat kv >>= fun ki => Source.indexLoc F
          (Source.Val.cdRef (D := E.layout) (τ := .array .calldata element none)
            rfl (off+32*s.1.toNat) ((if toEnd then len else e.1.toNat)-s.1.toNat)) ki >>=
          fun loc => Source.readLoc F loc >>= fun value => pure (Source.RVal.val value)).run y=_
      rw [Source.Hoare.run_bind,source_local_value_run G F (fuel+1) y index _ hk]
      change ((Source.indexLoc F
        (Source.Val.cdRef (D := E.layout) (τ := .array .calldata element none)
          rfl (off+32*s.1.toNat) ((if toEnd then len else e.1.toNat)-s.1.toNat)) k.1.toNat) >>=
          fun loc => Source.readLoc F loc >>= fun value => pure (Source.RVal.val value)).run y=_
      have location : (Source.indexLoc (E := E) (Γ := Γ) F
          (Source.Val.cdRef (D := E.layout) (τ := .array .calldata element none)
            rfl (off+32*s.1.toNat) ((if toEnd then len else e.1.toNat)-s.1.toNat)) k.1.toNat).run y=
          if k.1.toNat<(if toEnd then len else e.1.toNat)-s.1.toNat then
            (.ok (.cd (off+32*s.1.toNat+32*k.1.toNat)),y)
          else (.error (.revert (Source.panicData .index)),y) := by
        by_cases inside : k.1.toNat<(if toEnd then len else e.1.toNat)-s.1.toNat <;>
          simp only [Source.indexLoc,Source.lengthOf,pure_bind,inside,Source.STy.isValueTy,single,↓reduceIte] <;> rfl
      rw [Source.Hoare.run_bind,location]
      by_cases inside : k.1.toNat<(if toEnd then len else e.1.toNat)-s.1.toNat
      · simp only [if_pos inside]
        change ((Source.EM.lift (Source.decodeWord E.layout
          (Source.cdWordAt F (off+32*s.1.toNat+32*k.1.toNat)) element)) >>=
            fun value => pure (Source.RVal.val value)).run y=_
        have address : off+32*s.1.toNat+32*k.1.toNat=off+32*(s.1.toNat+k.1.toNat) := by omega
        rw [address,Source.Hoare.run_bind]
        cases decoded : Source.decodeWord E.layout
          (Source.cdWordAt F (off+32*(s.1.toNat+k.1.toNat))) element <;> rfl
      · simp only [if_neg inside]

/-- info: 'Solidity.Backend.MemoryOps.source_array_slice_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_array_slice_eval
/-- info: 'Solidity.Backend.MemoryOps.source_slice_index_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_slice_index_eval
end Solidity.Backend.MemoryOps
