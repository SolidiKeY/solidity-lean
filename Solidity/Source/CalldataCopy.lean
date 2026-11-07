import Solidity.Source.CalldataAggregates

/-! G18.05 exact scalar-array calldata copy outcomes. Decoding precedes
allocation. These are actual Source interpreter equations, not compiler or
EVM execution correspondence. Recursive reference-element copying is open. -/
namespace Solidity.Source
open EM
variable {E : Env} {Γ : RCtx}

/-- A sequence of pure decoders retains the entire caller state, including
on a later error. The result is the actual ordered Except traversal. -/
theorem mapM_lift_run {α β : Type} (xs : List α) (decode : α → R β)
    (before : EMState E Γ) :
    (xs.mapM fun x => (lift (decode x) : EM E Γ β)).run before =
      (xs.mapM decode,before) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons,Hoare.run_bind,List.mapM_cons]
    cases result : decode x with
    | error halt => rfl
    | ok value =>
      change ((xs.mapM fun x => (lift (decode x) : EM E Γ β)) >>=
        fun values => pure (value :: values)).run before = _
      rw [Hoare.run_bind,ih]
      cases xs.mapM decode <;> rfl

/-- Total copy observation: validation returns the original exact error and
unchanged state, or one fresh typed array is installed after all elements
have decoded. No desired run or allocation is a premise. -/
theorem cdToMem_array_run (F : Fr) (σ : STy) (offset length : Nat)
    (before : EMState E Γ)
    (plain : ∀ e m, σ ≠ .array .memory e (some m) := by intro _ _ h; cases h) :
    (cdToMem F (.array .memory σ none) offset length).run before =
      match (List.range length).mapM (fun j =>
        decodeWord E.layout (cdWordAt F (offset+32*j)) σ) with
      | .error halt => (.error halt,before)
      | .ok values =>
        (.ok (.val (.memRef rfl before.2.heap.next)),
          (before.1,{before.2 with heap := (before.2.heap.alloc
            ⟨.array .memory σ none,
              Data.array values.length (fun _ h => nomatch h)
                (fun k => .val (values.get k))⟩).1})) := by
  have notcd : (some DataLoc.memory : Option DataLoc) ≠ some .calldata := by decide
  simp only [cdToMem,STy.loc?,dif_neg notcd]
  rw [Hoare.run_bind,mapM_lift_run]
  cases (List.range length).mapM (fun j =>
    decodeWord E.layout (cdWordAt F (offset+32*j)) σ) <;> rfl

/-- An actual failed validation never installs even a partial array. This
retains the original halt, locals, heap, world and execution observations. -/
theorem cdToMem_array_failure (F : Fr) (σ : STy) (offset length : Nat)
    (before : EMState E Γ) (halt : Halt)
    (validation : (List.range length).mapM (fun j =>
      decodeWord E.layout (cdWordAt F (offset+32*j)) σ) = .error halt)
    (plain : ∀ e m, σ ≠ .array .memory e (some m) := by intro _ _ h; cases h) :
    (cdToMem F (.array .memory σ none) offset length).run before =
      (.error halt,before) := by
  rw [cdToMem_array_run F σ offset length before plain,validation]

/-- Every protected old cell is retained on both validation outcomes. The
proof derives the allocated heap from the real run, without MemOK or an
assumed preservation certificate. -/
theorem cdToMem_array_old_cell (F : Fr) (σ : STy) (offset length : Nat)
    (before : EMState E Γ) (address : Nat)
    (old_address : address ≠ before.2.heap.next)
    (plain : ∀ e m, σ ≠ .array .memory e (some m) := by intro _ _ h; cases h) :
    ((cdToMem F (.array .memory σ none) offset length).run before).2.2.heap.get address =
      before.2.heap.get address := by
  rw [cdToMem_array_run F σ offset length before plain]
  cases (List.range length).mapM (fun j =>
    decodeWord E.layout (cdWordAt F (offset+32*j)) σ) with
  | error halt => rfl
  | ok values => exact Heap.alloc_other before.2.heap _ old_address

/-- The actual implicit conversion arm uses this copy, not a separate
snapshot conversion. Its array location change is genuinely nonidentity. -/
theorem convRV_cdArray (F : Fr) (n : Nat) (σ : STy) (offset length : Nat) :
    convRV (E := E) (Γ := Γ) F n (.array .memory σ none)
      (.val (.cdRef (τ := .array .calldata σ none) rfl offset length)) =
      cdToMem F (.array .memory σ none) offset length := by
  rfl

end Solidity.Source
