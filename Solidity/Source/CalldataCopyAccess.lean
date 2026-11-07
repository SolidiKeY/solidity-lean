import Solidity.Source.CalldataCopy

/-! G18.05 extent and indexed-read transport through actual calldata copies.
No new evaluator or compiler simulation is introduced. -/
namespace Solidity.Source
open EM
variable {E : Env} {Γ : RCtx}

/-- Successful ordered validation derives the complete length and every
position's actual decoder equation; these are not extra copy premises. -/
theorem decode_traversal_shape {α β : Type} (decode : α → R β)
    (inputs : List α) {values : List β} (success : inputs.mapM decode = .ok values) :
    values.length = inputs.length ∧
      ∀ i (hi : i < inputs.length) (hv : i < values.length),
        decode inputs[i] = .ok values[i] := by
  induction inputs generalizing values with
  | nil =>
    cases success
    exact ⟨rfl,fun _ impossible => nomatch impossible⟩
  | cons head rest ih =>
    rw [List.mapM_cons] at success
    cases decoded : decode head with
    | error halt =>
      rw [decoded] at success
      cases success
    | ok value =>
      rw [decoded] at success
      change ((rest.mapM decode) >>= fun tail => pure (value :: tail)) = .ok values at success
      cases tail_decoded : rest.mapM decode with
      | error halt =>
        rw [tail_decoded] at success
        cases success
      | ok tail =>
        rw [tail_decoded] at success
        cases success
        obtain ⟨same_length,positions⟩ := ih tail_decoded
        refine ⟨congrArg Nat.succ same_length,?_⟩
        intro i hi hv
        cases i with
        | zero => exact decoded
        | succ i => exact positions i (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hv)

/-- The copied dynamic array has the requested extent, derived from the
actual decoder traversal rather than an assumed resource certificate. -/
theorem cdToMem_array_length (F : Fr) (σ : STy) (offset length : Nat)
    {values : List (Val E.layout σ)}
    (validation : (List.range length).mapM (fun j =>
      decodeWord E.layout (cdWordAt F (offset+32*j)) σ) = .ok values) :
    values.length = length := by
  have shape := (decode_traversal_shape _ _ validation).1
  exact shape.trans List.length_range

/-- The actual Source object accessor sees the just-installed object at
its real fresh address and retains the complete grown caller state. -/
theorem heapObj_alloc_run (before : EMState E Γ) (object : Σ τ, Data E.layout τ) :
    let after : EMState E Γ :=
      (before.1,{before.2 with heap := (before.2.heap.alloc object).1})
    (heapObj before.2.heap.next).run after = (.ok object,after) := by
  dsimp only
  unfold heapObj
  rw [Hoare.run_bind]
  change (match (before.2.heap.alloc object).1.get before.2.heap.next with
    | some value => (pure value : EM E Γ _)
    | none => halt (.stuck "dangling memory reference")).run _ = _
  have installed : (before.2.heap.alloc object).1.get before.2.heap.next = some object :=
    Heap.alloc_get before.2.heap object
  rw [installed]
  rfl

/-- Read the exact positional value from the actual freshly allocated typed
array, without a desired read/run premise. -/
theorem readLoc_alloc_array_run (F : Fr) (σ : STy) (values : List (Val E.layout σ))
    (before : EMState E Γ) (index : Fin values.length) :
    let after : EMState E Γ := (before.1,{before.2 with heap :=
      (before.2.heap.alloc ⟨.array .memory σ none,
        Data.array values.length (fun _ h => nomatch h) (fun k => .val (values.get k))⟩).1})
    (readLoc F (.mem (τ := σ) before.2.heap.next index.val)).run after =
      (.ok (values.get index),after) := by
  dsimp only
  simp only [readLoc,memElem]
  rw [Hoare.run_bind,heapObj_alloc_run]
  simp only [dif_pos index.isLt]
  rfl

/-- General actual copy-then-index transport. Requested extent and the
index's decoded value follow from validation. The read runs on the actual
grown heap, with the full copied caller state as its final state. -/
theorem cdToMem_array_read_run (F : Fr) (σ : STy) (offset length : Nat)
    (before : EMState E Γ) {values : List (Val E.layout σ)}
    (validation : (List.range length).mapM (fun j =>
      decodeWord E.layout (cdWordAt F (offset+32*j)) σ) = .ok values)
    (index : Fin length)
    (plain : ∀ e m, σ ≠ .array .memory e (some m) := by intro _ _ h; cases h) :
    ∃ bound : index.val < values.length,
      values.length = length ∧
      decodeWord E.layout (cdWordAt F (offset+32*index.val)) σ = .ok (values.get ⟨index.val,bound⟩) ∧
      ((do let _ ← cdToMem F (.array .memory σ none) offset length
           readLoc F (.mem (τ := σ) before.2.heap.next index.val)) : EM E Γ _).run before =
        (.ok (values.get ⟨index.val,bound⟩),
          ((cdToMem F (.array .memory σ none) offset length).run before).2) := by
  have size : values.length = length := cdToMem_array_length F σ offset length validation
  have bound : index.val < values.length := by rw [size]; exact index.isLt
  have input_bound : index.val < (List.range length).length := by
    rw [List.length_range]
    exact index.isLt
  have position := (decode_traversal_shape _ _ validation).2 index.val input_bound bound
  simp only [List.getElem_range] at position
  refine ⟨bound,size,position,?_⟩
  rw [Hoare.run_bind]
  simp only [cdToMem_array_run F σ offset length before plain,validation]
  exact readLoc_alloc_array_run F σ values before ⟨index.val,bound⟩

/-- Reading outside a successfully copied array panics on the grown heap;
it does not retroactively roll back the completed copy. -/
theorem readLoc_alloc_array_out_run (F : Fr) (σ : STy) (values : List (Val E.layout σ))
    (before : EMState E Γ) (index : Nat) (outside : values.length ≤ index) :
    let after : EMState E Γ := (before.1,{before.2 with heap :=
      (before.2.heap.alloc ⟨.array .memory σ none,
        Data.array values.length (fun _ h => nomatch h) (fun k => .val (values.get k))⟩).1})
    (readLoc F (.mem (τ := σ) before.2.heap.next index)).run after =
      (.error (.revert (panicData .index)),after) := by
  dsimp only
  simp only [readLoc,memElem]
  rw [Hoare.run_bind,heapObj_alloc_run]
  simp only [dif_neg (Nat.not_lt_of_ge outside)]
  rfl

/-- A failed copy bypasses its actual read continuation and retains the
original caller state, contrasting with a post-copy bounds failure. -/
theorem cdToMem_array_read_failure (F : Fr) (σ : STy) (offset length : Nat)
    (before : EMState E Γ) (index : Nat) (halt : Halt)
    (validation : (List.range length).mapM (fun j =>
      decodeWord E.layout (cdWordAt F (offset+32*j)) σ) = .error halt)
    (plain : ∀ e m, σ ≠ .array .memory e (some m) := by intro _ _ h; cases h) :
    ((do let _ ← cdToMem F (.array .memory σ none) offset length
         readLoc F (.mem (τ := σ) before.2.heap.next index)) : EM E Γ _).run before =
      (.error halt,before) := by
  rw [Hoare.run_bind,cdToMem_array_failure F σ offset length before halt validation plain]

/-- The requested length, derived from actual validation, determines the
post-copy bounds check. The copy remains installed on its original heap. -/
theorem cdToMem_array_read_out_run (F : Fr) (σ : STy) (offset length : Nat)
    (before : EMState E Γ) {values : List (Val E.layout σ)}
    (validation : (List.range length).mapM (fun j =>
      decodeWord E.layout (cdWordAt F (offset+32*j)) σ) = .ok values)
    (index : Nat) (outside : length ≤ index)
    (plain : ∀ e m, σ ≠ .array .memory e (some m) := by intro _ _ h; cases h) :
    ((do let _ ← cdToMem F (.array .memory σ none) offset length
         readLoc F (.mem (τ := σ) before.2.heap.next index)) : EM E Γ _).run before =
      (.error (.revert (panicData .index)),
        ((cdToMem F (.array .memory σ none) offset length).run before).2) := by
  have size : values.length = length := cdToMem_array_length F σ offset length validation
  rw [Hoare.run_bind]
  simp only [cdToMem_array_run F σ offset length before plain,validation]
  exact readLoc_alloc_array_out_run F σ values before index (size ▸ outside)

end Solidity.Source
