import Solidity.Yul.Compilation.ArgumentLowering
import Solidity.Yul.Compilation.NestedWrites

/-! Consume an already evaluated arity-indexed result vector into finite locals.
This is target compiler data, not a source AST or V12 function convention.
Ordering is explicit: top-first results are assigned head-first. Actual source
assignment ordering/alias admission remains a producer-binding obligation. -/
namespace Solidity.Yul.Compilation
open Backend Scalar

private theorem vector_cons_tail {α : Type} {arity : Nat} (v : Vector α (arity + 1)) :
    v.toList = v[0] :: v.tail.toList := by
  apply List.ext_getElem
  · simp only [Vector.length_toList, List.length_cons]
    omega
  · intro i hi hj
    cases i with
    | zero => simp only [Vector.getElem_toList, List.getElem_cons_zero]
    | succ i =>
      simp only [Vector.getElem_toList, List.getElem_cons_succ,
        Vector.tail_eq_cast_extract, Vector.getElem_cast, Vector.getElem_extract,
        Nat.add_comm]

/-- Every destination is intrinsically a local. Remaining result words and live
newer words determine actual SWAP depths; allocation offsets are not used. -/
def resultWritesCode {n : Nat} : (arity : Nat) → Vector (Fin n) arity → Nat → Option Program
  | 0, _, _ => some []
  | arity + 1, targets, depth =>
    if accessible : arity + depth + targets[0].val < 16 then
      (resultWritesCode arity targets.tail depth).map
        (fun rest => writeSlot ⟨arity + depth + targets[0].val, accessible⟩ ++ rest)
    else none

/-- All result values are supplied before the first local update. Repeated
destinations have the specified head-first/last-write result. -/
def assignResults {n : Nat} : (arity : Nat) → Vector (Fin n) arity → Vector Word arity →
    Vector Word n → Vector Word n
  | 0, _, _, locals => locals
  | arity + 1, targets, values, locals =>
    assignResults arity targets.tail values.tail
      (locals.set targets[0].val values[0] targets[0].isLt)

/-- Constructive exact contents from finite result/local bounds. No exchange
or desired-run result is assumed. The newer prefix and caller remain identical. -/
theorem resultWritesCode_run {n : Nat} (arity : Nat) (targets : Vector (Fin n) arity)
    (depth : Nat) (p : Program) (selected : resultWritesCode arity targets depth = some p)
    (values : Vector Word arity) (locals : Vector Word n)
    (newer : Vector Word depth) (tail : Stack) :
    run p (values.toList ++ (newer.toList ++ (locals.toList ++ tail))) =
      some (newer.toList ++ ((assignResults arity targets values locals).toList ++ tail)) := by
  induction arity generalizing locals p with
  | zero =>
    cases selected
    have empty : values.toList = [] := Vector.toList_eq_nil_iff.mpr rfl
    simp only [empty, List.nil_append, run, assignResults]
  | succ arity ih =>
    unfold resultWritesCode at selected
    split at selected
    next accessible =>
      cases hrest : resultWritesCode arity targets.tail depth with
      | none => simp only [hrest, Option.map_none, reduceCtorEq] at selected
      | some rest =>
        simp only [hrest, Option.map_some, Option.some.injEq] at selected
        subst p
        rw [vector_cons_tail values, List.cons_append]
        apply run_comp (t := values.tail.toList ++ (newer.toList ++
          ((locals.set targets[0].val values[0] targets[0].isLt).toList ++ tail)))
        · simpa only [Vector.toList_append, List.append_assoc] using
            write_under_prefix locals (values.tail ++ newer) targets[0] accessible values[0] tail
        · exact ih targets.tail rest hrest values.tail
            (locals.set targets[0].val values[0] targets[0].isLt)
    next inaccessible => cases selected

/-- Snapshot the complete RHS result vector before any destination write. The
interface specifies target head-first order, not unproved source alias rules. -/
def lowerResultAssign {n arity : Nat} {values : Vector Word n → Vector Word arity}
    (targets : Vector (Fin n) arity) (rhs : LoweredArgs n arity values) :
    LoweredStmt n (fun locals => assignResults arity targets (values locals) locals) where
  code := fun depth => (rhs.code depth).bind (fun p =>
    (resultWritesCode arity targets depth).map (fun q => p ++ q))
  correct := by
    intro depth p selected locals newer tail
    cases hr : rhs.code depth with
    | none => simp only [hr, Option.bind_none] at selected; cases selected
    | some code =>
      cases hw : resultWritesCode arity targets depth with
      | none => simp only [hr, hw, Option.bind_some, Option.map_none] at selected; cases selected
      | some writes =>
        simp only [hr, hw, Option.bind_some, Option.map_some, Option.some.injEq] at selected
        subst p
        exact run_comp (rhs.correct depth code hr locals newer tail)
          (resultWritesCode_run arity targets depth writes hw (values locals) locals newer tail)

private theorem writeSlot_bound_cons (i : Fin 16) (p : Program) (height : Int) :
    stackBound (writeSlot i ++ p) height =
      (safeHeight height && stackBound p (height - 1)) := by
  change (safeHeight height && (safeHeight (height + 0) && stackBound p ((height + 0) + -1))) = _
  simp only [Int.add_zero, Int.sub_eq_add_neg, ← Bool.and_assoc, Bool.and_self]

theorem resultWritesCode_bound_iff {n : Nat} (arity : Nat) (targets : Vector (Fin n) arity)
    (depth : Nat) (p : Program) (selected : resultWritesCode arity targets depth = some p)
    (height : Int) : stackBound p height = true ↔ (arity : Int) ≤ height ∧ height ≤ 1024 := by
  induction arity generalizing height p with
  | zero =>
    cases selected
    simp only [stackBound, heightTrace, List.all_cons, List.all_nil, Bool.and_true,
      safeHeight, decide_eq_true_eq, Int.natCast_zero]
  | succ arity ih =>
    unfold resultWritesCode at selected
    split at selected
    next accessible =>
      cases hrest : resultWritesCode arity targets.tail depth with
      | none => simp only [hrest, Option.map_none, reduceCtorEq] at selected
      | some rest =>
        simp only [hrest, Option.map_some, Option.some.injEq] at selected
        subst p
        rw [writeSlot_bound_cons, Bool.and_eq_true, ih targets.tail rest hrest]
        simp only [safeHeight, decide_eq_true_eq]
        omega
    next inaccessible => cases selected

theorem assignResults_other {n : Nat} (arity : Nat) (targets : Vector (Fin n) arity)
    (values : Vector Word arity) (locals : Vector Word n) (j : Fin n)
    (outside : j ∉ targets.toList) :
    (assignResults arity targets values locals)[j.val] = locals[j.val] := by
  induction arity generalizing locals with
  | zero => rfl
  | succ arity ih =>
    have remaining : j ∉ targets.tail.toList := by
      intro member
      apply outside
      rw [vector_cons_tail targets]
      exact List.mem_cons_of_mem _ member
    have different : targets[0].val ≠ j.val := by
      intro eqn
      apply outside
      rw [vector_cons_tail targets]
      exact List.mem_cons.mpr (Or.inl (Fin.ext eqn).symm)
    rw [assignResults, ih targets.tail values.tail _ remaining,
      Vector.getElem_set_ne targets[0].isLt j.isLt different]

#print axioms assignResults_other
#print axioms lowerResultAssign
#print axioms resultWritesCode_bound_iff
#print axioms resultWritesCode_run
#print axioms vector_cons_tail
end Solidity.Yul.Compilation
