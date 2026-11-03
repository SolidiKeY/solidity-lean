import Solidity.Yul.Compilation.ArgumentLowering
import Solidity.Yul.Compilation.ScopeSemantics

/-! Pure target lexical-scope compiler. Context extension is an intrinsic vector
prefix. This component selects only at empty temporary depth; actual source
statement boundary/source-context correspondence remains a separate obligation.
No source AST, source state or V12 function-entry convention is introduced. -/
namespace Solidity.Yul.Compilation
open Backend Scalar

/-- Remove exactly the fresh context prefix from the updated local vector. -/
def outerLocals {fresh n : Nat} (locals : Vector Word (fresh + n)) : Vector Word n :=
  (locals.extract fresh).cast (by omega)

theorem outerLocals_toList {fresh n : Nat} (locals : Vector Word (fresh + n)) :
    (outerLocals locals).toList = locals.toList.drop fresh := by
  simp only [outerLocals, Vector.toList_cast, Vector.toList_extract]
  have length : (locals.toList.drop fresh).length = fresh + n - fresh := by
    rw [List.length_drop, Vector.length_toList]
  rw [← length, List.take_length]

theorem popFresh_run {fresh n : Nat} (locals : Vector Word (fresh + n)) (tail : Stack) :
    run (popPrefix fresh) (locals.toList ++ tail) =
      some ((outerLocals locals).toList ++ tail) := by
  rw [outerLocals_toList]
  have length : (locals.toList.take fresh).length = fresh := by
    rw [List.length_take, Vector.length_toList]
    omega
  have split : locals.toList ++ tail =
      locals.toList.take fresh ++ (locals.toList.drop fresh ++ tail) := by
    rw [← List.append_assoc, List.take_append_drop]
  rw [split]
  simpa only [length] using popPrefix_run (locals.toList.take fresh) (locals.toList.drop fresh ++ tail)

/-- Compile initializer values, an extended-context body and exact prefix exit.
Only empty temporary depth is selected: fresh locals and outer locals must be
contiguous for the supplied body context. This is a target component domain,
not a source admission restriction or a V12 frame convention. -/
def lowerLocalScope {n fresh : Nat}
    {values : Vector Word n → Vector Word fresh}
    {update : Vector Word (fresh + n) → Vector Word (fresh + n)}
    (initializers : LoweredArgs n fresh values)
    (body : LoweredStmt (fresh + n) update) :
    LoweredStmt n (fun locals => outerLocals (update (values locals ++ locals))) where
  code := fun depth => if depth = 0 then
    (initializers.code 0).bind (fun p =>
      (body.code 0).map (fun q => p ++ q ++ popPrefix fresh)) else none
  correct := by
    intro depth p selected locals newer tail
    by_cases zero : depth = 0
    · subst depth
      have empty : newer.toList = [] := by
        exact Vector.toList_eq_nil_iff.mpr rfl
      cases hi : initializers.code 0 with
      | none => simp only [ite_true, hi, Option.bind_none] at selected; cases selected
      | some a =>
        cases hb : body.code 0 with
        | none =>
          simp only [ite_true, hi, hb, Option.bind_some, Option.map_none] at selected
          cases selected
        | some b =>
          simp only [ite_true, hi, hb, Option.bind_some, Option.map_some] at selected
          cases selected
          simp only [empty, List.nil_append]
          apply run_comp
          · apply run_comp
            · simpa only [Vector.toList_empty, List.nil_append] using
                initializers.correct 0 a hi locals #v[] tail
            · simpa only [Vector.toList_empty, Vector.toList_append,
                List.nil_append, List.append_assoc] using
                body.correct 0 b hb (values locals ++ locals) #v[] tail
          · exact popFresh_run (update (values locals ++ locals)) tail
    · simp only [zero, ite_false] at selected
      cases selected

#print axioms popFresh_run
#print axioms lowerLocalScope
end Solidity.Yul.Compilation
