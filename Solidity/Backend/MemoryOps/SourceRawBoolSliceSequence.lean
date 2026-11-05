import Solidity.Backend.MemoryOps.SourceRawBoolCopy
import Solidity.Backend.MemoryOps.SourceCalldataBoolSliceSequence

/-! Discharge the existing two-statement slice program's decoder premises from
actual raw words. Its first allocation, typed state and late error are derived,
not supplied as reached-state or decoder-run assumptions. -/
namespace Solidity.Backend.MemoryOps

theorem raw_bool_values_first_error (E : Source.Env) (F : Source.Fr) (off len : Nat)
    (acceptedIndices pending : List Nat) (i : Nat)
    (order : List.range len=acceptedIndices++i::pending)
    (canonical : ∀ j,j∈acceptedIndices → Source.cdWordAt F (off+32*j)=0 ∨ Source.cdWordAt F (off+32*j)=1)
    (invalid : 1<Source.cdWordAt F (off+32*i)) :
    sourceCalldataBoolValues E F off len=.error (.revert []) := by
  first
  | solve | simp only [] | omega
  | have bad : Source.decodeWord E.layout (Source.cdWordAt F (off+32*i)) .bool=.error (.revert []) := by
      simp only [Source.decodeWord,Source.decodeElemWord,if_neg (by omega : Source.cdWordAt F (off+32*i)≠0),
        if_neg (by omega : Source.cdWordAt F (off+32*i)≠1)]
    unfold sourceCalldataBoolValues
    rw [order,List.mapM_append,List.mapM_cons,raw_bool_indices E.layout F off acceptedIndices canonical]
    simp only [bad,bind,Except.bind]

/-- Original Source nps/horizons and slice bounds are preserved. Initial raw
words derive both decoder phases. The error exposes only the evaluator's real
retained globals, not transaction rollback or a target suffix machine. -/
theorem source_bool_slice_raw_late_error {E : Source.Env} {Γ : Source.RCtx}
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
    (canonical : ∀ j,j<((if toEnd then len else e.1.toNat)-s.1.toNat) →
      Source.cdWordAt F (off+32*s.1.toNat+32*j)=0 ∨ Source.cdWordAt F (off+32*s.1.toNat+32*j)=1)
    (acceptedIndices pending : List Nat) (i : Nat)
    (order : List.range ((if badToEnd then len else be.1.toNat)-bs.1.toNat)=acceptedIndices++i::pending)
    (accepted : ∀ j,j∈acceptedIndices → Source.cdWordAt F (off+32*bs.1.toNat+32*j)=0 ∨ Source.cdWordAt F (off+32*bs.1.toNat+32*j)=1)
    (invalid : 1<Source.cdWordAt F (off+32*bs.1.toNat+32*i))
    (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    let payload := rawBoolPayload F (off+32*s.1.toNat) ((if toEnd then len else e.1.toNat)-s.1.toNat)
    let middle : Source.EMState E Γ := (y.1,{y.2 with heap := (y.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory payload⟩).1})
    (Source.evalE G F (fuel+4) (sourceBoolSliceCopy root start finish toEnd)).run y=
      (.ok (.val (.memRef rfl y.2.heap.next)),middle) ∧
    (Source.evalE G F (fuel+3) (sourceBoolSliceCopy root badStart badFinish badToEnd)).run middle=
      (.error (.revert []),middle) ∧
    (Source.execItems G F (fuel+6) nps none
      (.stmt (.expr (sourceBoolSliceCopy root start finish toEnd))
        (.stmt (.expr (sourceBoolSliceCopy root badStart badFinish badToEnd)) .nil) : Source.RItems E [] false .body Γ Γ)
        y.1).run (.nil,y.2)=(.error (.revert []),(.nil,middle.2)) ∧
    Source.MemOK E SH middle ∧
    (∀ b obj,y.2.heap.get b=some obj → middle.2.heap.get b=some obj ∧ b≠y.2.heap.next) ∧
    middle.1=y.1 ∧ middle.2.heap.next=y.2.heap.next+1 ∧
    middle.2.ex=y.2.ex ∧ middle.2.events=y.2.events ∧ middle.2.logs=y.2.logs ∧ middle.2.fnLocals=y.2.fnLocals := by
  first
  | solve | simp only [] | omega
  | have first := raw_bool_indices E.layout F (off+32*s.1.toNat)
        (List.range ((if toEnd then len else e.1.toNat)-s.1.toNat))
        (fun j hj => canonical j (List.mem_range.mp hj))
    have bad := raw_bool_values_first_error E F (off+32*bs.1.toNat) _ acceptedIndices pending i order accepted invalid
    have sequence := source_bool_slice_copy_late_error G F fuel nps y root start finish badStart badFinish off len
      s e bs be toEnd badToEnd hr hs he hbs hbe ordered bounded badOrdered badBounded (.revert []) bad SH hm
    unfold sourceCalldataBoolValues at sequence
    rw [first] at sequence
    simpa only [sourceBoolValuePayload,rawBoolPayload,List.map_map,Function.comp_def,calldataBool] using sequence

/-- info: 'Solidity.Backend.MemoryOps.raw_bool_values_first_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_bool_values_first_error
/-- info: 'Solidity.Backend.MemoryOps.source_bool_slice_raw_late_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_bool_slice_raw_late_error
end Solidity.Backend.MemoryOps
