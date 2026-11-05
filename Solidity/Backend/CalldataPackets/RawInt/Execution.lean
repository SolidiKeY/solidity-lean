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

/-- Exact range check on the declared integer interpretation: dirty high bits revert. -/
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

/-- Expose the actual sign-extension test for every declared signed width. -/
theorem signed_decode_range (D : Source.Layout) (t : Source.IntTy) (signed : t.signed=true) (w : Nat) :
    Source.decodeWord D w (.int t) =
      let v : Int := if 2^255 ≤ (Source.toWord w).val then
        ((Source.toWord w).val : Int)-2^256 else (Source.toWord w).val
      if h : t.lo ≤ v ∧ v ≤ t.hi then .ok (.int v h) else .error (.revert []) := by
  simpa only [Source.wordInt,signed,true_and] using decode_range D t w

/-- The existing resolved implicit conversion; no target execution assumed. -/
def copyExpr {E : Source.Env} {Γ : Source.RCtx} (t : Source.IntTy)
    (i : Source.Idx Γ (.array .calldata (.int t) none)) : Source.RExpr E Γ (ArrayTy t) :=
  .conv (.local i) (by
    apply Or.inl
    change (Source.STy.same (.int t) (.int t) && true && true)=true
    rw [Source.STy.same_refl]
    rfl)

theorem eval_copy {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (t : Source.IntTy) (y : Source.EMState E Γ)
    (i : Source.Idx Γ (.array .calldata (.int t) none)) (off len : Nat)
    (localRef : y.1.get i=.cdRef rfl off len) :
    (Source.evalE G F (n+2) (copyExpr t i)).run y=
      (Source.cdToMem F (ArrayTy t) off len).run y := by
  rw [copyExpr,Source.evalE,Source.Hoare.run_bind,source_local_value_run G F n y i _ localRef]
  change (Source.convRV F (n+1) (ArrayTy t)
    (.val (.cdRef rfl off len) : Source.RVal E.layout (.array .calldata (.int t) none))).run y=_
  unfold Source.convRV
  rw [dif_neg (show (Source.STy.array .calldata (.int t) none)≠ArrayTy t from by intro h;cases h)]
  rfl

/-- Entry rejection occurs before copying; admitted entries retain the exact
raw-word validation result, including dirty-input refusal. -/
theorem guarded_run {E : Source.Env} {Γ : Source.RCtx}
    (data : List UInt8) (i : Nat) (t : Source.IntTy) (F : Source.Fr) (y : Source.EMState E Γ) :
    ((Source.EM.lift (Source.cdTail data i 32)) >>= fun p =>
      Source.cdToMem F (ArrayTy t) p.1 p.2).run y=
      match Source.cdTail data i 32 with
      | .error e => (.error e,y)
      | .ok (off,len) => (Source.cdToMem F (ArrayTy t) off len).run y := by
  rw [Source.Hoare.run_bind]
  cases h : Source.cdTail data i 32 with
  | error e => simp only [Source.EM.lift];rfl
  | ok p => simp only [Source.EM.lift];rfl

/-- The complete state observation is derived from raw validation, including
rollback after a late dirty element and preservation of every address other than the allocation address. -/
theorem copy_observations {E : Source.Env} {Γ : Source.RCtx}
    (t : Source.IntTy) (F : Source.Fr) (off len : Nat) (y : Source.EMState E Γ) :
    let z := (Source.cdToMem F (ArrayTy t) off len).run y |>.2
    match values E.layout t F off len with
    | .error _ => z=y
    | .ok xs =>
      z.2.heap.get y.2.heap.next=some ⟨ArrayTy t,memory xs⟩ ∧
      z.2.heap.next=y.2.heap.next+1 ∧
      (∀ a,a≠y.2.heap.next → z.2.heap.get a=y.2.heap.get a) ∧
      z.1=y.1 ∧ {z.2 with heap := y.2.heap}=y.2 := by
  rw [copy_run]
  cases values E.layout t F off len with
  | error e => rfl
  | ok xs =>
    dsimp only
    refine ⟨Source.Heap.alloc_get _ _,rfl,?_,rfl,?_⟩
    · intro a different
      exact Source.Heap.alloc_other _ _ different
    · cases y.2
      rfl

end Solidity.Backend.CalldataPackets.RawInt
