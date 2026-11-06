import Solidity.Source.Calldata

/-! Owned S02/G18.04 consumers of actual nested calldata operations. These
are Source execution/progress/layout facts; compiler/NEWBackend and EVM
correspondence are separate obligations. Dynamic-base range slices remain
refused, as pinned solc 0.8.38 error2148 requires. -/
namespace Solidity.Source
open EM

variable {E : Env} {Γ : RCtx}

theorem cdHeadBytes_positive (τ : STy) : 32 ≤ τ.cdHeadBytes := by
  exact Nat.le_trans (by decide : 32 ≤ 32*1)
    (Nat.mul_le_mul_left 32 (Nat.le_max_left 1 τ.cdStaticWords))

theorem cdHeadBytes_of_word {τ : STy} (word : τ.oneWord = true) : τ.cdHeadBytes = 32 := by
  cases τ <;> first | rfl | cases word

theorem cdNested_ok (F : Fr) (base index stride : Nat) : NotStuckR (cdNested F base index stride) := by
  intro message impossible
  unfold cdNested at impossible
  cases result : cdTail (F.cd.drop base) index stride with
  | error halt =>
    rw [result] at impossible
    cases impossible
    exact cdTail_ok (F.cd.drop base) index stride message result
  | ok pair =>
    rw [result] at impossible
    cases pair
    cases impossible

/-- The complete nested read retains the actual Source caller state on
success and error; no execution or preservation premise is supplied. -/
theorem readLoc_cdBytes_run (F : Fr) (base index : Nat) (before : EMState E Γ) :
    (readLoc F (.cdBytes base index)).run before =
      ((cdNested F base index 1).map fun pair => Val.cdRef rfl pair.1 pair.2,before) := by
  change ((lift (E := E) (Γ := Γ) (cdNested F base index 1)) >>= fun pair =>
    pure (Val.cdRef (D := E.layout) (τ := .bytes .calldata) rfl pair.1 pair.2)).run before = _
  cases cdNested F base index 1 with
  | error halt => rfl
  | ok pair => cases pair; rfl

theorem readLoc_cdString_run (F : Fr) (base index : Nat) (before : EMState E Γ) :
    (readLoc F (.cdString base index)).run before =
      ((cdNested F base index 1).map fun pair => Val.cdRef rfl pair.1 pair.2,before) := by
  change ((lift (E := E) (Γ := Γ) (cdNested F base index 1)) >>= fun pair =>
    pure (Val.cdRef (D := E.layout) (τ := .string .calldata) rfl pair.1 pair.2)).run before = _
  cases cdNested F base index 1 with
  | error halt => rfl
  | ok pair => cases pair; rfl

theorem readLoc_cdArray_run (F : Fr) (base index : Nat) (σ : STy) (before : EMState E Γ) :
    (readLoc F (.cdArray (σ := σ) base index)).run before =
      ((cdNested F base index σ.cdHeadBytes).map fun pair => Val.cdRef rfl pair.1 pair.2,before) := by
  change ((lift (E := E) (Γ := Γ) (cdNested F base index σ.cdHeadBytes)) >>= fun pair =>
    pure (Val.cdRef (D := E.layout) (τ := .array .calldata σ none) rfl pair.1 pair.2)).run before = _
  cases cdNested F base index σ.cdHeadBytes with
  | error halt => rfl
  | ok pair => cases pair; rfl

theorem readLoc_cdFixedArray_run (F : Fr) (offset length : Nat) (σ : STy) (before : EMState E Γ) :
    (readLoc F (.cdFixedArray (σ := σ) length offset)).run before =
      (.ok (.cdRef rfl offset length),before) := rfl

/-- Exact region and length facts follow from the actual successful producer;
the origin adjustment is derived, not assumed as a relocation oracle. -/
theorem cdNested_region (F : Fr) (base index stride : Nat) {offset length : Nat}
    (result : cdNested F base index stride = .ok (offset,length)) :
    ∃ relative, offset = base+relative+32 ∧ length < 2^64 ∧
      offset+stride*length ≤ F.cd.length := by
  unfold cdNested cdTail at result
  dsimp only at result
  split at result
  · cases result
  · split at result
    · cases result
    · rename_i small
      split at result
      · rename_i bounded
        cases result
        dsimp only at *
        refine ⟨wordAt (F.cd.drop base) index,?_,Nat.lt_of_not_ge small,?_⟩
        · omega
        · simp only [List.length_drop] at bounded
          omega
      · cases result

/-- This native refusal remains outside the admitted typed slice constructor. -/
theorem dynamic_array_base_slice_refused (σ : STy) :
    STy.sliceable (.array .calldata (.array .calldata σ none) none) = false := rfl

theorem dynamic_bytes_base_slice_refused :
    STy.sliceable (.array .calldata (.bytes .calldata) none) = false := rfl

theorem static_reference_slice_admitted :
    STy.sliceable (.array .calldata (.array .calldata (.int IntTy.u256) (some 2)) none) = true := rfl

theorem string_slice_admitted : STy.sliceable (.string .calldata) = true := rfl

theorem decodeArg_cdArray_run (data : Roadmap.Bytes) (index : Nat) (σ : STy)
    (supported : σ.cdElement = true) (before : EMState E Γ) :
    (decodeArg data index (.array .calldata σ none)).run before =
      (cdArg E.layout data index σ.cdHeadBytes rfl,before) := by
  simp only [decodeArg,if_pos supported]
  cases cdArg E.layout data index σ.cdHeadBytes (τ := .array .calldata σ none) rfl <;> rfl

/-- Execute the existing typed local-array index expression. The remaining
index/read program is actual Source code, with its real exceptions. -/
theorem eval_cdIndex_run {caller : RCtx} (G : Glob E) (F : Fr) (n : Nat) (σ : STy)
    (offset length index : Nat) (typed : IntTy.u256.lo ≤ (index : Int) ∧ (index : Int) ≤ IntTy.u256.hi)
    (tail : Locals E.layout caller) (state : St E) :
    let before : Locals E.layout (.array .calldata σ none :: .int IntTy.u256 :: caller) × St E :=
      (Locals.cons (Val.cdRef (τ := .array .calldata σ none) rfl offset length)
      (.cons (.int (t := IntTy.u256) index typed) tail),state)
    (evalE G F (n+2) (.indexArray (.local .here) (.local (.there .here)) rfl)).run before =
      (do let location ← indexLoc F (Val.cdRef (τ := .array .calldata σ none) rfl offset length) index
          return RVal.val (← readLoc F location)).run before := by
  simp only [evalE]
  rfl

theorem indexLoc_cdBytes_eq (F : Fr) (offset length index : Nat) (bound : index < length) :
    indexLoc (E := E) (Γ := Γ) F
      (Val.cdRef (τ := .array .calldata (.bytes .calldata) none) rfl offset length) index =
        pure (.cdBytes offset index) := by
  unfold indexLoc
  simp only [lengthOf,pure_bind,if_pos bound]
  rfl

theorem cdToMem_string_run (F : Fr) (offset length : Nat) (before : EMState E Γ) :
    (cdToMem F (.string .memory) offset length).run before =
      (.ok (.val (.memRef rfl before.2.heap.next)),
        (before.1,{before.2 with heap :=
          (before.2.heap.alloc ⟨.string .memory,.string ((F.cd.drop offset).take length)⟩).1})) := rfl

theorem indexLoc_cdArray_eq (F : Fr) (σ : STy) (offset length index : Nat) (bound : index < length) :
    indexLoc (E := E) (Γ := Γ) F
      (Val.cdRef (τ := .array .calldata (.array .calldata σ none) none) rfl offset length) index =
        pure (.cdArray offset index) := by
  unfold indexLoc
  simp only [lengthOf,pure_bind,if_pos bound]
  rfl

theorem eval_local_run {caller : RCtx} (G : Glob E) (F : Fr) (n : Nat) {τ : STy}
    (position : Idx caller τ) (before : EMState E caller) :
    (evalE G F (n+1) (.local position)).run before = (.ok (.val (before.1.get position)),before) := rfl

theorem eval_cdArrayIndex_run {caller : RCtx} (G : Glob E) (F : Fr) (n : Nat) (σ : STy)
    (offset length index : Nat) (bound : index < length)
    (typed : IntTy.u256.lo ≤ (index : Int) ∧ (index : Int) ≤ IntTy.u256.hi)
    (tail : Locals E.layout caller) (state : St E) :
    let before : Locals E.layout (.array .calldata (.array .calldata σ none) none :: .int IntTy.u256 :: caller) × St E :=
      (.cons (.cdRef rfl offset length) (.cons (.int index typed) tail),state)
    (evalE G F (n+2) (.indexArray (.local .here) (.local (.there .here)) rfl)).run before =
      ((cdNested F offset index σ.cdHeadBytes).map fun pair => RVal.val (Val.cdRef rfl pair.1 pair.2),before) := by
  refine Eq.trans (eval_cdIndex_run G F n (.array .calldata σ none) offset length index typed tail state) ?_
  rw [indexLoc_cdArray_eq F σ offset length index bound,pure_bind,Hoare.run_bind,readLoc_cdArray_run]
  cases cdNested F offset index σ.cdHeadBytes with
  | error halt => rfl
  | ok pair => cases pair; rfl

theorem em_pure_run {α : Type} (value : α) (before : EMState E Γ) :
    (pure value : EM E Γ α).run before = (.ok value,before) := rfl

theorem eval_cdIndex_out_run {caller : RCtx} (G : Glob E) (F : Fr) (n : Nat) (σ : STy)
    (offset length index : Nat) (outside : ¬ index < length)
    (typed : IntTy.u256.lo ≤ (index : Int) ∧ (index : Int) ≤ IntTy.u256.hi)
    (tail : Locals E.layout caller) (state : St E) :
    let before : Locals E.layout (.array .calldata σ none :: .int IntTy.u256 :: caller) × St E :=
      (.cons (.cdRef rfl offset length) (.cons (.int index typed) tail),state)
    (evalE G F (n+2) (.indexArray (.local .here) (.local (.there .here)) rfl)).run before =
      (.error (.revert (panicData .index)),before) := by
  refine Eq.trans (eval_cdIndex_run G F n σ offset length index typed tail state) ?_
  simp only [indexLoc,lengthOf,pure_bind,if_neg outside]
  rfl

theorem getV_val_eq {τ : STy} (value : Val E.layout τ) :
    getV (Γ := Γ) (.val value) = pure value := rfl

theorem indexNat_nat_eq (index : Nat)
    (typed : IntTy.u256.lo ≤ (index : Int) ∧ (index : Int) ≤ IntTy.u256.hi) :
    indexNat (E := E) (Γ := Γ) (.val (.int (t := IntTy.u256) index typed)) = pure index := rfl

theorem eval_cdDoubleIndex_run {caller : RCtx} (G : Glob E) (F : Fr) (n : Nat) (σ : STy)
    (offset length first second : Nat)
    (first_typed : IntTy.u256.lo ≤ (first : Int) ∧ (first : Int) ≤ IntTy.u256.hi)
    (second_typed : IntTy.u256.lo ≤ (second : Int) ∧ (second : Int) ≤ IntTy.u256.hi)
    (tail : Locals E.layout caller) (state : St E) :
    let before : Locals E.layout
        (.array .calldata (.array .calldata σ none) none :: .int IntTy.u256 :: .int IntTy.u256 :: caller) × St E :=
      (.cons (.cdRef rfl offset length) (.cons (.int first first_typed) (.cons (.int second second_typed) tail)),state)
    (evalE G F (n+3) (.indexArray (.indexArray (.local .here) (.local (.there .here)) rfl)
      (.local (.there (.there .here))) rfl)).run before =
      (do let location ← indexLoc F
            (Val.cdRef (τ := .array .calldata (.array .calldata σ none) none) rfl offset length) first
          let inner ← readLoc F location
          let element ← indexLoc F inner second
          return RVal.val (← readLoc F element)).run before := by
  rw [evalE]
  simp only [Hoare.run_bind]
  by_cases bound : first < length
  · rw [eval_cdArrayIndex_run G F n σ offset length first bound first_typed (.cons (.int second second_typed) tail) state]
    rw [indexLoc_cdArray_eq F σ offset length first bound]
    simp only [em_pure_run]
    rw [readLoc_cdArray_run]
    cases result : cdNested F offset first σ.cdHeadBytes with
    | error halt => rfl
    | ok pair =>
      cases pair
      simp only [Except.map,getV_val_eq,em_pure_run]
      rw [eval_local_run G F (n+1)]
      simp only [Locals.get,indexNat_nat_eq,em_pure_run]
  · rw [eval_cdIndex_out_run G F n (.array .calldata σ none) offset length first bound first_typed
      (.cons (.int second second_typed) tail) state]
    simp only [indexLoc,lengthOf,pure_bind,if_neg bound]
    rfl

end Solidity.Source
