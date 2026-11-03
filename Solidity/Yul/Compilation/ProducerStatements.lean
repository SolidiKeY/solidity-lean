import Solidity.Yul.Compilation.ProducerExpressions
/-! Initial concrete statement visitor over VY1's actual Stmt/evalStmt.
Only normally completing skip, singleton local assignment and sequence are
implemented here. Function/control/physical/source-session/G24 adequacy remain
separate, as do admitted source syntax and actual target resource bounds. -/
namespace Solidity.Yul.Compilation.ProducerStatements
open Backend Scalar
open Solidity.Yul.Closed
open ProducerExpressions

structure Compiled (fuel : Nat) {c : Control} {n : Nat} (stmt : Stmt [] [] c n) where
  profile : StmtWordP stmt
  update : Vector Scalar.Word n → Vector Scalar.Word n
  lowered : LoweredStmt n update
  source : ∀ locals, evalStmt fuel .nil True.intro stmt profile (sourceLocals locals) =
    some ⟨sourceLocals (update locals),.normal⟩

def skip (fuel : Nat) {c : Control} (n : Nat) :
    Compiled (fuel+1) (Stmt.skip (c := c) (n := n)) :=
  ⟨True.intro, id, lowerSkip n, fun _ => rfl⟩

private theorem locals_set {n : Nat} (locals : Vector Scalar.Word n)
    (i : Fin n) (value : Scalar.Word) :
    sourceLocals (locals.set i.val value i.isLt) =
      writeTarget (.local i) value.toFin (sourceLocals locals) := by
  funext j
  simp only [sourceLocals, Vector.getElem_set, writeTarget]
  by_cases same : j = i
  · subst j; simp only [ite_true]
  · have ne : i.val ≠ j.val := fun h => same (Fin.ext h.symm)
    simp only [ne, same, ite_false]

def assign {fuel n : Nat} {c : Control} {expr : Expr [] [] n 1}
    (i : Fin n) (rhs : ProducerExpressions.Compiled fuel expr) :
    Compiled (fuel+1) (Stmt.assign (c := c) (fun _ : Fin 1 => .local i) expr) where
  profile := ⟨fun _ => True.intro, rhs.profile⟩
  update := fun locals => locals.set i.val (rhs.value locals) i.isLt
  lowered := lowerAssign i rhs.lowered
  source := by
    intro locals
    rw [evalStmt_assign, rhs.source]
    change some (⟨writeTarget (.local i) (rhs.value locals).toFin (sourceLocals locals),.normal⟩ : Outcome c n) = _
    rw [locals_set]

/-- Project an actual intrinsically closed target without transporting the
source AST through a function-extensional equality. -/
def localTarget {n : Nat} : Target [] n → Fin n
  | .local i => i
  | .external ref => nomatch ref.index

private theorem localTarget_eq {n : Nat} (target : Target [] n) :
    target = .local (localTarget target) := by
  cases target with
  | «local» i => rfl
  | external ref => cases ref.index

/-- Singleton targets may be a producer tabulation rather than definitionally
constant functions. Code/data retain the original AST index; equality is used
only in the proof of the actual write, never to cast the compiler result. -/
def assignTargets {fuel n : Nat} {c : Control} {expr : Expr [] [] n 1}
    (targets : Fin 1 → Target [] n) (rhs : ProducerExpressions.Compiled fuel expr) :
    Compiled (fuel+1) (Stmt.assign (c := c) targets expr) where
  profile := ⟨fun i => targetWordP_closed (targets i),rhs.profile⟩
  update := fun locals => locals.set (localTarget (targets 0)).val (rhs.value locals)
    (localTarget (targets 0)).isLt
  lowered := lowerAssign (localTarget (targets 0)) rhs.lowered
  source := by
    intro locals
    rw [evalStmt_assign,rhs.source]
    change some (⟨writeTarget (targets 0) (rhs.value locals).toFin (sourceLocals locals),.normal⟩ :
      Outcome c n) = _
    rw [localTarget_eq (targets 0),locals_set]
    rfl

def seq {fuel n : Nat} {c : Control} {a b : Stmt [] [] c n}
    (first : Compiled fuel a) (second : Compiled fuel b) :
    Compiled (fuel+1) (.seq a b) where
  profile := ⟨first.profile,second.profile⟩
  update := fun locals => second.update (first.update locals)
  lowered := lowerSeq first.lowered second.lowered
  source := by
    intro locals
    change (do
      let result ← evalStmt fuel .nil True.intro a first.profile (sourceLocals locals)
      match result.flow with
      | .normal => evalStmt fuel .nil True.intro b second.profile result.vars
      | _ => pure result) = _
    rw [first.source]
    exact second.source (first.update locals)

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
              exact (ProducerExpressions.compile fuel expr).map (assignTargets targets)
            | succ _ => exact none
        all_goals exact ()
      all_goals intro F X; cases F <;> cases X <;> intros <;> first | exact none | exact ()
termination_by structural fuel

theorem executes {fuel n : Nat} {c : Control} {stmt : Stmt [] [] c n}
    (compiled : Compiled fuel stmt) (depth : Nat) (code : Program)
    (emitted : compiled.lowered.code depth = some code) (locals : Vector Scalar.Word n)
    (newer : Vector Scalar.Word depth) (caller : Stack) :
    evalStmt fuel .nil True.intro stmt compiled.profile (sourceLocals locals) =
      some ⟨sourceLocals (compiled.update locals),.normal⟩ ∧
    run code (newer.toList ++ (locals.toList ++ caller)) =
      some (newer.toList ++ ((compiled.update locals).toList ++ caller)) :=
  ⟨compiled.source locals, compiled.lowered.correct depth code emitted locals newer caller⟩
#print axioms assignTargets
#print axioms compile
#print axioms executes
end Solidity.Yul.Compilation.ProducerStatements
