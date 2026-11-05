import Solidity.Backend.MemoryOps.SourceCalldataCopy

namespace Solidity.Backend.CalldataPackets.RawInt
open Solidity.Backend.MemoryOps

abbrev ArrayTy (t : Source.IntTy) : Source.STy := .array .memory (.int t) none

/-- Validation is computed from each raw word, before allocation. -/
def values (D : Source.Layout) (t : Source.IntTy) (F : Source.Fr) (off len : Nat) :
    Source.R (List (Source.Val D (.int t))) :=
  (List.range len).mapM fun j => Source.decodeWord D (Source.cdWordAt F (off+32*j)) (.int t)

def memory {D : Source.Layout} {t : Source.IntTy} (xs : List (Source.Val D (.int t))) :
    Source.Data D (ArrayTy t) :=
  .array xs.length (fun _ h => nomatch h) (fun k => .val (xs.get k))

/-- Exact range check on the signed 256-bit interpretation: dirty high bits revert. -/
theorem decode_range (D : Source.Layout) (t : Source.IntTy) (w : Nat) :
    Source.decodeWord D w (.int t) =
      if h : t.lo ≤ Source.wordInt t (Source.toWord w) ∧
          Source.wordInt t (Source.toWord w) ≤ t.hi then
        .ok (.int _ h) else .error (.revert []) := by
  by_cases h : t.lo ≤ Source.wordInt t (Source.toWord w) ∧ Source.wordInt t (Source.toWord w) ≤ t.hi
  · simp only [Source.decodeWord,Source.decodeElemWord,Source.readInt,if_pos h,Source.mkInt,dif_pos h]
    rfl
  · simp only [Source.decodeWord,Source.decodeElemWord,Source.readInt,if_neg h,dif_neg h]

/-- Arbitrary lengths: either all raw words decode and one object is allocated,
or validation fails and the entire initial state is preserved. -/
theorem copy_run {E : Source.Env} {Γ : Source.RCtx}
    (t : Source.IntTy) (F : Source.Fr) (off len : Nat) (y : Source.EMState E Γ) :
    (Source.cdToMem F (ArrayTy t) off len).run y =
      match values E.layout t F off len with
      | .error e => (.error e,y)
      | .ok xs => (.ok (.val (.memRef rfl y.2.heap.next)),
          (y.1,{y.2 with heap := (y.2.heap.alloc ⟨ArrayTy t,memory xs⟩).1})) := by
  simp only [Source.cdToMem,ArrayTy,Source.STy.loc?,Option.some.injEq,reduceCtorEq,dite_false]
  rw [Source.Hoare.run_bind,source_mapM_lift_run]
  unfold values
  cases (List.range len).mapM (fun j => Source.decodeWord E.layout (Source.cdWordAt F (off+32*j)) (.int t)) <;> rfl

end Solidity.Backend.CalldataPackets.RawInt
