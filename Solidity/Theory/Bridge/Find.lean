import Solidity.Theory.Abs

/-!
# Bridge: the interpreter's read is `findSt` on `abs`

A path the interpreter reads (`SVal.find`, `State.findStorage`) reads the same
value's `abs` in the Theory, as a literal equation: `find` walks the same
bindings `abs` lays out (`select_abs_fields`/`_array`/`_map`), and where it
halts nothing is claimed.  An array's length is its `length` member
(`abs_arrayLen`), which `abs` stores for a fixed-size array too, as
`arrayLen` answers for one.
-/

namespace Solidity
namespace Theory

open Semantics StValue

/-- A read the interpreter completes is the Theory's read of `abs`. -/
theorem _root_.Solidity.Semantics.SVal.abs_find {v w : SVal} {q : List Seg}
    (h : v.find q = .ok w) : v.abs.readAt q = w.abs := by
  induction q generalizing v with
  | nil =>
      simp only [SVal.find, Except.ok.injEq] at h
      subst h; rfl
  | cons a rest ih =>
      show readAt (selectSt (asStruct v.abs) a) rest = w.abs
      cases v with
      | prim p => cases a <;> simp only [SVal.find, reduceCtorEq] at h
      | struct fs =>
          cases a with
          | «at» i => simp only [SVal.find, reduceCtorEq] at h
          | field n =>
              simp only [SVal.find] at h
              show readAt (selectSt (SVal.abs.fields fs) (.field n)) rest = w.abs
              rw [SVal.select_abs_fields]
              split at h
              · next u hu => simp only [hu]; exact ih h
              · simp only [reduceCtorEq] at h
      | array es sh fx =>
          rw [SVal.select_abs_array]
          cases a with
          | «at» i =>
              simp only [SVal.find] at h
              split at h
              · next hi => simp only [dif_pos hi]; exact ih h
              · simp only [reduceCtorEq] at h
          | field n =>
              by_cases hn : n = "length"
              · subst hn
                cases fx <;> simp only [SVal.find, reduceCtorEq, if_true, if_false,
                  Bool.false_eq_true] at h ⊢
                exact ih h
              · simp only [SVal.find, reduceCtorEq] at h
      | map es d =>
          rw [SVal.select_abs_map]
          cases a with
          | field n => simp only [SVal.find, reduceCtorEq] at h
          | «at» i =>
              simp only [SVal.find] at h
              split at h
              · next u hu => simp only [hu]; exact ih h
              · next hu => simp only [hu]; exact ih h

/-- …at a state variable, from the storage node. -/
theorem _root_.Solidity.Semantics.State.abs_findStorage {σ : State} {r : Name} {segs : List Seg}
    {w : SVal} (h : σ.findStorage r segs = .ok w) : findSt σ.abs (rootPath r segs) = w.abs := by
  unfold State.findStorage at h
  rw [← readAt_st]
  show readAt (selectSt (SVal.abs.fields σ.storage) (.field r)) segs = w.abs
  rw [SVal.select_abs_fields]
  split at h
  · next v hv => simp only [hv]; exact SVal.abs_find h
  · simp only [reduceCtorEq] at h

/-- An array's `length` member, at a state variable: the one read the two
lemmas below share. -/
private theorem findSt_length_of_array {σ : State} {r : Name} {segs : List Seg}
    {es sh : List SVal} {fx : Bool} (h : σ.findStorage r segs = .ok (.array es sh fx)) :
    findSt σ.abs (rootPath r segs ++ [lengthSeg]) = .int es.length := by
  rw [find_append _ _ (List.cons_ne_nil _ _), State.abs_findStorage h]
  show selectSt (asStruct (SVal.array es sh fx).abs) lengthSeg = .int es.length
  rw [SVal.select_abs_array]
  rfl

/-- `values.length` is the `length` member. -/
theorem _root_.Solidity.Semantics.State.abs_arrayLen {σ : State} {r : Name} {segs : List Seg}
    {x : Value} (h : arrayLen σ r segs = .ok x) :
    findSt σ.abs (rootPath r segs ++ [lengthSeg]) = .prim x := by
  unfold arrayLen at h
  cases hf : σ.findStorage r segs with
  | error e => simp only [hf, bind, Except.bind, reduceCtorEq] at h
  | ok v =>
      simp only [hf, bind, Except.bind] at h
      cases v <;> simp only [reduceCtorEq, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact findSt_length_of_array hf

/-- The Theory's length of an array is its live length. -/
theorem _root_.Solidity.Semantics.State.abs_lenAt_of_array {σ : State} {r : Name}
    {segs : List Seg} {es sh : List SVal} {fx : Bool}
    (h : σ.findStorage r segs = .ok (.array es sh fx)) :
    lenAt σ.abs (rootPath r segs) = es.length := by
  unfold lenAt
  rw [findSt_length_of_array h]
  rfl

end Theory
end Solidity
