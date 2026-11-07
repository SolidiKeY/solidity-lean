import Solidity.Backend.Aggregates.ByteParameters

/-! Exact execution of the published typed Source slice expression, followed
by intrinsic byte-value import. No new Source expression or evaluator, and
no source-to-fetched-EVM operation simulation is introduced. -/
namespace Solidity.Backend.Aggregates.ByteSlices
open Solidity
open ByteParameters

abbrev SliceCtx (caller : Source.RCtx) : Source.RCtx :=
  .bytes .calldata :: .int Source.IntTy.u256 :: .int Source.IntTy.u256 :: caller

def expr {E : Source.Env} {caller : Source.RCtx} :
    Source.RExpr E (SliceCtx caller) (.bytes .calldata) :=
  .slice (.local .here) rfl (.local (.there .here)) rfl
    (.local (.there (.there .here))) rfl false

def locals {D : Source.Layout} {caller : Source.RCtx} (tail : Source.Locals D caller)
    (offset length first last : Nat)
    (first_typed : Source.IntTy.u256.lo ≤ (first : Int) ∧ (first : Int) ≤ Source.IntTy.u256.hi)
    (last_typed : Source.IntTy.u256.lo ≤ (last : Int) ∧ (last : Int) ≤ Source.IntTy.u256.hi) :
    Source.Locals D (SliceCtx caller) :=
  .cons (.cdRef rfl offset length) (.cons (.int first first_typed) (.cons (.int last last_typed) tail))

/-- Actual evaluation retains the entire caller locals and Source state,
including heap, accounts, events and other ordered observations. -/
theorem eval_expr {E : Source.Env} {caller : Source.RCtx} (G : Source.Glob E)
    (frame : Source.Fr) (n : Nat) (tail : Source.Locals E.layout caller) (state : Source.St E)
    (offset length first last : Nat)
    (first_typed : Source.IntTy.u256.lo ≤ (first : Int) ∧ (first : Int) ≤ Source.IntTy.u256.hi)
    (last_typed : Source.IntTy.u256.lo ≤ (last : Int) ∧ (last : Int) ≤ Source.IntTy.u256.hi) :
    (Source.evalE G frame (n+2) expr).run
      (locals tail offset length first last first_typed last_typed,state) =
      ((Source.sliceR (Source.Val.cdRef (D := E.layout) (τ := .bytes .calldata) rfl offset length)
          first last false).map Source.RVal.val,
        (locals tail offset length first last first_typed last_typed,state)) := by
  simp only [expr,Source.evalE]
  change ((Source.EM.lift (E := E) (Γ := SliceCtx caller)
      (Source.sliceR (Source.Val.cdRef (D := E.layout) (τ := .bytes .calldata) rfl offset length)
        first last false)) >>= fun value => pure (Source.RVal.val value)).run
      (locals tail offset length first last first_typed last_typed,state) = _
  cases Source.sliceR
      (Source.Val.cdRef (D := E.layout) (τ := .bytes .calldata) rfl offset length) first last false <;>
    rfl

theorem slice_success (D : Source.Layout) (offset length first last : Nat)
    (ordered : first ≤ last) (bounded : last ≤ length) :
    Source.sliceR (Source.Val.cdRef (D := D) (τ := .bytes .calldata) rfl offset length)
      first last false = .ok (.cdRef rfl (offset+first) (last-first)) := by
  simp only [Source.sliceR, Source.STy.cdStride, Bool.false_eq_true, if_false, Nat.not_lt.mpr ordered,
    Nat.not_lt.mpr bounded, Nat.one_mul]
  rfl

theorem slice_capacity (frame : Source.Fr) {data : Roadmap.Bytes} {index offset length : Nat}
    (entry : Source.cdTail data index 1 = .ok (offset,length)) (first last : Nat)
    (bounded : last ≤ length) :
    (ByteParameters.payload frame (offset+first) (last-first)).length < 2^256 := by
  have count : last-first ≤ length := Nat.le_trans (Nat.sub_le last first) bounded
  exact Nat.lt_trans
    (Nat.lt_of_le_of_lt (Nat.le_trans (payload_length frame (offset+first) (last-first)) count)
      (entry_length entry)) (by decide)

theorem slice_extent (frame : Source.Fr) (selector data : Roadmap.Bytes)
    (selector_length : selector.length = 4) (input : frame.cd = selector ++ data)
    {index offset length : Nat} (entry : Source.cdTail data index 1 = .ok (offset,length))
    (first last : Nat) (ordered : first ≤ last) (bounded : last ≤ length) :
    (ByteParameters.payload frame (offset+first) (last-first)).length = last-first := by
  obtain ⟨relative,position,region⟩ := entry_region entry
  have size : offset+first+(last-first) ≤ frame.cd.length := by
    rw [input,List.length_append,selector_length,position]
    omega
  simp only [ByteParameters.payload,List.length_take,List.length_drop]
  omega

theorem index_typed {data : Roadmap.Bytes} {index offset length : Nat}
    (entry : Source.cdTail data index 1 = .ok (offset,length)) (j : Nat) (bounded : j ≤ length) :
    Source.IntTy.u256.lo ≤ (j : Int) ∧ (j : Int) ≤ Source.IntTy.u256.hi := by
  have small : j < 2^64 := Nat.lt_of_le_of_lt bounded (entry_length entry)
  have word : j < 2^256 := Nat.lt_trans small (by decide)
  change (0 : Int) ≤ (j : Int) ∧ (j : Int) ≤ ((2^256 : Nat) : Int)-1
  omega

/-- Compose actual typed Source evaluation and the runtime target value import.
All index representability and intrinsic object length bounds follow from the entry
and slice bounds. No Source execution/result is supplied as a premise. -/
theorem import_slice {E : Source.Env} {caller : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (frame : Source.Fr) (selector data : Roadmap.Bytes)
    (selector_length : selector.length = 4) (input : frame.cd = selector ++ data)
    {index offset length : Nat} (entry : Source.cdTail data index 1 = .ok (offset,length))
    (first last : Nat) (ordered : first ≤ last) (bounded : last ≤ length)
    (tail : Source.Locals E.layout caller) (state : Source.St E) (target : State C Γ) (n : Nat) :
    let first_typed := index_typed entry first (Nat.le_trans ordered bounded)
    let last_typed := index_typed entry last bounded
    let before := (locals tail offset length first last first_typed last_typed,state)
    let capacity := slice_capacity frame entry first last bounded
    (Source.evalE G frame (n+2) expr).run before =
        (.ok (.val (.cdRef rfl (offset+first) (last-first))),before) ∧
      RefRelated (D := E.layout) frame (.cdRef rfl (offset+first) (last-first))
        (lower target frame (offset+first) (last-first) capacity).heap
        (target.alloc (bytesObj target.H (ByteParameters.payload frame (offset+first) (last-first)) capacity)).2 ∧
      (ByteParameters.payload frame (offset+first) (last-first)).length = last-first := by
  refine ⟨?_,target_contents target frame (offset+first) (last-first) _,
    slice_extent frame selector data selector_length input entry first last ordered bounded⟩
  rw [eval_expr,slice_success E.layout offset length first last ordered bounded]
  rfl

end Solidity.Backend.Aggregates.ByteSlices
