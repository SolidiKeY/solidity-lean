import Solidity.Yul.Compilation.PureStatements
import Solidity.Yul.Compilation.LocalScopeLowering
/-! Actual producer let/zero binders to existing target prefix scopes.
Contexts/values stay intrinsic and existing source/target semantics are reused.
The current target factory selects only depth0; this is not source admission. -/
namespace Solidity.Yul.Compilation.ScopedStatements
open Backend Scalar
open Solidity.Yul.Closed ProducerExpressions ProducerStatements

theorem locals_append {a n : Nat} (front : Vector Scalar.Word a) (back : Vector Scalar.Word n) :
    sourceLocals (front ++ back) = extendValues (sourceLocals front) (sourceLocals back) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [sourceLocals,extendValues,Fin.addCases_left]
    exact congrArg BitVec.toFin (Vector.getElem_append_left j.isLt)
  · simp only [sourceLocals,extendValues,Fin.addCases_right]
    change (front ++ back)[a+j.val].toFin = back[j.val].toFin
    rw [Vector.getElem_append_right (by omega) (by omega)]
    simp only [Nat.add_sub_cancel_left]

theorem locals_outer {a n : Nat} (locals : Vector Scalar.Word (a+n)) :
    sourceLocals (outerLocals locals) = dropValues a (sourceLocals locals) := by
  funext i
  simp only [sourceLocals,outerLocals,Vector.getElem_cast,Vector.getElem_extract,dropValues]
  rfl

def oneArgument {n : Nat} {value : Vector Scalar.Word n → Scalar.Word}
    (rhs : LoweredExpr n value) : LoweredArgs n 1 (fun locals => #v[value locals]) where
  code := rhs.code
  correct := rhs.correct

def zeroArguments (n fresh : Nat) : LoweredArgs n fresh (fun _ => Vector.replicate fresh 0) where
  code := fun _ => some (pushPrefix (Vector.replicate fresh (0 : Scalar.Word)).toList)
  correct := by
    intro depth p selected locals newer tail
    cases selected
    exact pushPrefix_run _ _

def letOne {fuel c n} {rhs : Expr [] [] n 1} {body : Stmt [] [] c (1+n)}
    (initializer : ProducerExpressions.Compiled fuel rhs) (scope : ProducerStatements.Compiled fuel body) :
    ProducerStatements.Compiled (fuel+1) (.let_ 1 rhs body) where
  profile := ⟨initializer.profile,scope.profile⟩
  update := fun locals => outerLocals (scope.update (#v[initializer.value locals] ++ locals))
  lowered := lowerLocalScope (oneArgument initializer.lowered) scope.lowered
  source := by
    intro locals
    change (do
      let values ← evalExpr fuel .nil True.intro rhs initializer.profile (sourceLocals locals)
      let result ← evalStmt fuel .nil True.intro body scope.profile (extendValues values (sourceLocals locals))
      pure (⟨dropValues 1 result.vars,result.flow⟩ : Outcome c n)) = _
    rw [initializer.source]
    have initial : (fun _ : Fin 1 => (initializer.value locals).toFin) =
        sourceLocals #v[initializer.value locals] := by
      funext i
      have equal : i = 0 := by omega
      subst i
      rfl
    rw [initial]
    change (do
      let result ← evalStmt fuel .nil True.intro body scope.profile
        (extendValues (sourceLocals #v[initializer.value locals]) (sourceLocals locals))
      pure (⟨dropValues 1 result.vars,result.flow⟩ : Outcome c n)) = _
    rw [← locals_append,scope.source]
    change some (⟨dropValues 1 (sourceLocals _),.normal⟩ : Outcome c n) = _
    rw [← locals_outer]

def zero {fuel c n fresh} {body : Stmt [] [] c (fresh+n)}
    (scope : ProducerStatements.Compiled fuel body) :
    ProducerStatements.Compiled (fuel+1) (.zero fresh body) where
  profile := scope.profile
  update := fun locals => outerLocals (scope.update (Vector.replicate fresh 0 ++ locals))
  lowered := lowerLocalScope (zeroArguments n fresh) scope.lowered
  source := by
    intro locals
    change (do
      let result ← evalStmt fuel .nil True.intro body scope.profile
        (extendValues (fun _ : Fin fresh => word 0) (sourceLocals locals))
      pure (⟨dropValues fresh result.vars,result.flow⟩ : Outcome c n)) = _
    have initial : (fun _ : Fin fresh => word 0) = sourceLocals (Vector.replicate fresh (0 : Scalar.Word)) := by
      funext i
      simp only [sourceLocals,Vector.getElem_replicate]
      rfl
    rw [initial,← locals_append,scope.source]
    change some (⟨dropValues fresh (sourceLocals _),.normal⟩ : Outcome c n) = _
    rw [← locals_outer]

/-- Finite source horizon is preserved exactly through the real evaluator.
Other statement constructors refuse here, not at Solidity admission. -/
def compile {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) :
    Option (Compiled fuel stmt) :=
  match fuel with
  | 0 => none
  | fuel+1 => by
      apply Stmt.casesOn (motive_1 := fun F X c n stmt =>
        match F,X with
        | [],[] => Option (Compiled (fuel+1) stmt)
        | _,_ => Unit) stmt
      case skip =>
        intro F X c n
        cases F <;> cases X
        · exact some (skip fuel n)
        all_goals exact ()
      case seq =>
        intro F X c n a b
        cases F <;> cases X
        · exact do
            let first ← compile fuel a
            let second ← compile fuel b
            pure (seq first second)
        all_goals exact ()
      case assign =>
        intro F X c n r targets expr
        cases F <;> cases X
        · cases r with
          | zero => exact none
          | succ r =>
            cases r with
            | zero =>
              exact (PureExpressions.compile fuel expr).map (assignTargets targets)
            | succ _ => exact none
        all_goals exact ()
      case let_ =>
        intro F X c n r rhs body
        cases F <;> cases X
        · cases r with
          | zero => exact none
          | succ r =>
            cases r with
            | zero => exact do
                let initializer ← PureExpressions.compile fuel rhs
                let scope ← compile fuel body
                pure (letOne initializer scope)
            | succ _ => exact none
        all_goals exact ()
      case zero =>
        intro F X c n r body
        cases F <;> cases X
        · exact (compile fuel body).map ScopedStatements.zero
        all_goals exact ()
      all_goals intro F X; cases F <;> cases X <;> intros <;> first | exact none | exact ()
termination_by structural fuel


#print axioms compile
#print axioms locals_append
#print axioms locals_outer
#print axioms letOne
#print axioms zero
end Solidity.Yul.Compilation.ScopedStatements
