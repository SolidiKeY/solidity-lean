import Solidity.Yul.Compilation.ArgumentLowering
import Solidity.Yul.Compilation.ScopeSemantics

/-! Target arity-frame cleanup. The input packet is explicitly result words,
then retired local words, then an arbitrary caller. This is an instruction
component, not a source function frame or V12 calling convention. -/
namespace Solidity.Yul.Compilation
open Backend Scalar

/-- SWAP1 through SWAPcount: move the word below the result front to its top,
without changing result order. The existing opcode indices are zero-based. -/
def resultSweep : (count : Nat) → count ≤ 16 → Program
  | 0, _ => []
  | count + 1, h => resultSweep count (by omega) ++ [.op (.SWAP ⟨count, by omega⟩)]

private theorem exchange_below (value old : Word) (front tail : Stack) :
    exchange value front.length (front ++ old :: tail) =
      some (old, front ++ value :: tail) := by
  induction front with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, List.cons_append, exchange, ih, Option.map_some]

theorem resultSweep_run (count : Nat) (bound : count ≤ 16)
    (results : Vector Word count) (retired : Word) (tail : Stack) :
    run (resultSweep count bound) (results.toList ++ retired :: tail) =
      some (retired :: (results.toList ++ tail)) := by
  induction count generalizing retired tail with
  | zero =>
    have empty : results.toList = [] := Vector.toList_eq_nil_iff.mpr rfl
    simp only [resultSweep, empty, List.nil_append, run]
  | succ count ih =>
    obtain ⟨front, last, eqn⟩ := Vector.exists_push (xs := results)
    subst results
    simp only [resultSweep, Vector.toList_push, List.append_assoc, List.cons_append,
      List.nil_append]
    apply run_comp (ih (by omega) front last (retired :: tail))
    have swap := exchange_below last retired front.toList tail
    rw [Vector.length_toList] at swap
    simp only [run, step, swap, Scalar.swap, Option.map_some, Option.bind_some]

/-- Repeatedly discard one word below the unchanged arity-indexed result front.
No temporary stack word is allocated, regardless of retired-local count. -/
def retireResultLocals (results : Fin 17) : Nat → Program
  | 0 => []
  | count + 1 => resultSweep results.val (by omega) ++
      (.op .POP :: retireResultLocals results count)

theorem retireResultLocals_run (arity : Fin 17) (results : Vector Word arity.val)
    (locals tail : Stack) :
    run (retireResultLocals arity locals.length) (results.toList ++ (locals ++ tail)) =
      some (results.toList ++ tail) := by
  induction locals with
  | nil => rfl
  | cons retired locals ih =>
    simp only [List.length_cons, retireResultLocals, List.cons_append]
    apply run_comp (resultSweep_run arity.val (by omega) results retired (locals ++ tail))
    change run (retireResultLocals arity locals.length)
      (results.toList ++ (locals ++ tail)) = _
    exact ih

/-- The finite retired vector derives all retired operands; no desired run premise. -/
theorem retireResultFrame_run {locals : Nat} (arity : Fin 17)
    (results : Vector Word arity.val) (frame : Vector Word locals) (tail : Stack) :
    run (retireResultLocals arity locals) (results.toList ++ (frame.toList ++ tail)) =
      some (results.toList ++ tail) := by
  simpa only [Vector.length_toList] using retireResultLocals_run arity results frame.toList tail

/-- Checked selection for consumers whose arity is a natural number. Arity17
is outside this SWAP-only component; this is not a source admission decision. -/
def retireResultCode (results locals : Nat) : Option Program :=
  if accessible : results ≤ 16 then
    some (retireResultLocals ⟨results, by omega⟩ locals) else none

theorem retireResultCode_run (results locals : Nat) (p : Program)
    (selected : retireResultCode results locals = some p)
    (values : Vector Word results) (frame : Vector Word locals) (tail : Stack) :
    run p (values.toList ++ (frame.toList ++ tail)) = some (values.toList ++ tail) := by
  unfold retireResultCode at selected
  split at selected
  next accessible =>
    cases selected
    exact retireResultFrame_run ⟨results, by omega⟩ values frame tail
  next inaccessible => cases selected

/-- Turn an accepted inline body over its input retired vector into a genuine
arity slice that consumes that vector. No CALL/return-address convention. -/
def closeInlineBody {locals : Nat} (arity : Fin 17)
    {output : Vector Word locals → Vector Word arity.val}
    (body : LoweredArgs locals arity.val output) : Option (AritySlice locals arity.val output) :=
  match selected : body.code 0 with
  | none => none
  | some p => some {
    code := p ++ retireResultLocals arity locals
    correct := by
      intro input tail
      apply run_comp
      · simpa only [Vector.toList_empty, List.nil_append] using
          body.correct 0 p selected input #v[] tail
      · exact retireResultFrame_run arity (output input) input tail }

private theorem safeHeight_entry (p : Program) (h : Int) :
    (safeHeight h && stackBound p h) = stackBound p h := by
  cases p with
  | nil => simp only [stackBound, heightTrace, List.all_cons, List.all_nil,
      Bool.and_true, Bool.and_self]
  | cons i p =>
    change (safeHeight h && (safeHeight h && _)) = _
    rw [← Bool.and_assoc, Bool.and_self]
    rfl

private theorem resultSweep_bound_suffix (count : Nat) (bound : count ≤ 16)
    (p : Program) (h : Int) :
    stackBound (resultSweep count bound ++ p) h = stackBound p h := by
  induction count generalizing p h with
  | zero => rfl
  | succ count ih =>
    rw [resultSweep, List.append_assoc, ih]
    change (safeHeight h && stackBound p (h + 0)) = _
    rw [Int.add_zero, safeHeight_entry]

/-- Height trace only: operand availability is the independent finite-vector
run theorem. In particular, a short stack can pass this capacity predicate. -/
theorem retireResultLocals_bound_iff (arity : Fin 17) (locals : Nat) (height : Int) :
    stackBound (retireResultLocals arity locals) height = true ↔
      (locals : Int) ≤ height ∧ height ≤ 1024 := by
  induction locals generalizing height with
  | zero =>
    simp only [retireResultLocals, stackBound, heightTrace, List.all_cons,
      List.all_nil, Bool.and_true, safeHeight, decide_eq_true_eq, Int.natCast_zero]
  | succ locals ih =>
    rw [retireResultLocals, resultSweep_bound_suffix]
    change (safeHeight height && stackBound (retireResultLocals arity locals)
      (height - 1)) = true ↔ _
    rw [Bool.and_eq_true, ih]
    simp only [safeHeight, decide_eq_true_eq]
    omega

#print axioms resultSweep_run
#print axioms retireResultFrame_run
#print axioms retireResultCode_run
#print axioms closeInlineBody
#print axioms retireResultLocals_bound_iff
end Solidity.Yul.Compilation
