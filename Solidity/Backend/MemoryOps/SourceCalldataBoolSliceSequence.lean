import Solidity.Backend.MemoryOps.SourceCalldataBoolSlice

/-! A real two-statement Source program, with an actual sliced first copy and
a later malformed Boolean decoder. The first successful heap is retained by
this evaluator's error result. This is not a transaction rollback theorem. -/
namespace Solidity.Backend.MemoryOps

/-- Bounds and decoder failure concern immutable INITIAL calldata. The first
payload is computed; no intermediate Source heap, relation or run is a premise.
The second operation executes on the actual first allocation, with unchanged
locals proved by that operation rather than a desired suffix state. -/
theorem source_bool_slice_copy_late_error {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (y : Source.EMState E Γ)
    (root : Source.Idx Γ (.array .calldata .bool none))
    (start finish badStart badFinish : Source.Idx Γ (.int .u256))
    (off len : Nat) (s e bs be : PrimTy.uint.Denote) (toEnd badToEnd : Bool)
    (hr : y.1.get root=.cdRef rfl off len)
    (hs : y.1.get start=sourceUint s) (he : y.1.get finish=sourceUint e)
    (hbs : y.1.get badStart=sourceUint bs) (hbe : y.1.get badFinish=sourceUint be)
    (ordered : s.1.toNat≤(if toEnd then len else e.1.toNat))
    (bounded : (if toEnd then len else e.1.toNat)≤len)
    (badOrdered : bs.1.toNat≤(if badToEnd then len else be.1.toNat))
    (badBounded : (if badToEnd then len else be.1.toNat)≤len)
    (error : Source.Halt)
    (bad : sourceCalldataBoolValues E F (off+32*bs.1.toNat)
      ((if badToEnd then len else be.1.toNat)-bs.1.toNat)=.error error)
    (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    match sourceCalldataBoolValues E F (off+32*s.1.toNat)
      ((if toEnd then len else e.1.toNat)-s.1.toNat) with
    | .error firstError =>
      (Source.evalE G F (fuel+4) (sourceBoolSliceCopy root start finish toEnd)).run y=
        (.error firstError,y) ∧
      (Source.execItems G F (fuel+6) nps none
        (.stmt (.expr (sourceBoolSliceCopy root start finish toEnd))
          (.stmt (.expr (sourceBoolSliceCopy root badStart badFinish badToEnd)) .nil) :
            Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
              (.error firstError,(.nil,y.2))
    | .ok vs =>
      let middle : Source.EMState E Γ := (y.1,{y.2 with heap :=
        (y.2.heap.alloc ⟨.array .memory .bool none,sourceBoolMemory (sourceBoolValuePayload vs)⟩).1})
      (Source.evalE G F (fuel+4) (sourceBoolSliceCopy root start finish toEnd)).run y=
        (.ok (.val (.memRef rfl y.2.heap.next)),middle) ∧
      (Source.evalE G F (fuel+3) (sourceBoolSliceCopy root badStart badFinish badToEnd)).run middle=
        (.error error,middle) ∧
      (Source.execItems G F (fuel+6) nps none
        (.stmt (.expr (sourceBoolSliceCopy root start finish toEnd))
          (.stmt (.expr (sourceBoolSliceCopy root badStart badFinish badToEnd)) .nil) :
            Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
              (.error error,(.nil,middle.2)) ∧
      Source.MemOK E SH middle ∧
      (∀ b obj,y.2.heap.get b=some obj → middle.2.heap.get b=some obj ∧ b≠y.2.heap.next) ∧
      middle.1=y.1 ∧ middle.2.heap.next=y.2.heap.next+1 ∧
      middle.2.ex=y.2.ex ∧ middle.2.events=y.2.events ∧
      middle.2.logs=y.2.logs ∧ middle.2.fnLocals=y.2.fnLocals := by
  first
  | solve
    | rfl
    | simp only [Source.execItems]
    | omega
  | have first := source_bool_slice_copy_window G F (fuel+1) y root start finish off len s e toEnd hr hs he ordered bounded
    rw [source_cd_bool_run] at first
    cases decoded : sourceCalldataBoolValues E F (off+32*s.1.toNat)
        ((if toEnd then len else e.1.toNat)-s.1.toNat) with
    | error firstError =>
      rw [decoded] at first
      have statement := source_expr_statement_error G F (fuel+4) nps _ y y firstError first
      refine ⟨first,?_⟩
      rw [Source.execItems,Source.Hoare.run_bind,statement]
    | ok vs =>
      rw [decoded] at first
      dsimp only at first ⊢
      let middle : Source.EMState E Γ := (y.1,{y.2 with heap :=
        (y.2.heap.alloc ⟨.array .memory .bool none,sourceBoolMemory (sourceBoolValuePayload vs)⟩).1})
      have second : (Source.evalE G F (fuel+3)
          (sourceBoolSliceCopy root badStart badFinish badToEnd)).run middle=(.error error,middle) := by
        rw [source_bool_slice_copy_window G F fuel middle root badStart badFinish off len bs be badToEnd
          hr hbs hbe badOrdered badBounded,source_cd_bool_run,bad]
      have firstStatement := source_expr_statement_run G F (fuel+4) nps _ y middle
        (.val (.memRef rfl y.2.heap.next)) first
      have secondStatement := source_expr_statement_error G F (fuel+3) nps _ middle middle error second
      have mok := source_bool_alloc_memOK (E := E) (Γ := Γ) SH (sourceBoolValuePayload vs) y hm
      rw [source_bool_alloc] at mok
      refine ⟨first,second,source_items_pair_error G F fuel nps _ _ y middle middle error firstStatement secondStatement,
        mok.1,?_,rfl,rfl,rfl,rfl,rfl,rfl⟩
      intro b obj occupied
      have different : b≠y.2.heap.next := by
        intro same
        subst b
        have fresh := Source.Heap.alloc_fresh y.2.heap
          ⟨.array .memory .bool none,sourceBoolMemory (sourceBoolValuePayload vs)⟩
        change y.2.heap.get y.2.heap.next=none at fresh
        rw [fresh] at occupied
        cases occupied
      exact ⟨(Source.Heap.alloc_other y.2.heap _ different).trans occupied,different⟩

/-- info: 'Solidity.Backend.MemoryOps.source_bool_slice_copy_late_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_bool_slice_copy_late_error
end Solidity.Backend.MemoryOps
