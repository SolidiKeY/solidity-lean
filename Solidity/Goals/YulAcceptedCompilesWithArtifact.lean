import Solidity.Tools.Goal
import Solidity.Yul.Compilation.Artifact
import Solidity.Yul.Compilation.ProducerStatements
import Solidity.Yul.Compilation.WordMachine

/-! The plan goal `yulAcceptedCompilesWithArtifact` (`y1-yul-artifact-producers`), one module per goal. -/

namespace Solidity.Goals

open Solidity.Goal

/-! Accepted Yul language for the producer Artifact obligation (plan step
y1-yul-artifact-producers). Three separate layers:

* `YulArtifact.Accepted`: syntax only. Closed statements (`Stmt [] []`, any
  control `c`, any local count `n`) built from `skip`, `seq` and single-target
  assignment whose right side is built from literals, locals and
  `add`/`sub`/`mul`. Nesting and composition are arbitrary. These are exactly the
  constructors `ProducerStatements.compile` and `ProducerExpressions.compile`
  visit; any other constructor (`discard`, `let`, `zero`, `if`, `switch`, `for`,
  multi-target assignment, other builtins, early control, function groups) is
  outside this language, not a certificate failure. Calls and externals cannot
  occur in a closed statement.
* `YulArtifact.Fits depth`: the representation limit of the emitted code. Local
  reads use DUP and writes use SWAP, whose Backend index is `Fin 16`; a read at
  stack height `h` above the locals (counting the `depth` newer words) needs `h + i < 16`, and a
  write needs `depth + i < 16` (`lowerLocal`, `lowerAssign`, `lowerBinary`).
  Syntactic: computed from the program and the depth, never from success.
* The goal: the producer must succeed on every accepted program, its emission at
  every fitting depth must select into `Evm.Instr` through the existing word
  selector (stack, `ADD`, `SUB`, `MUL` and more), and exactly that code must
  carry an `Artifact` for the same statement, with both directions as defined. -/
namespace YulArtifact

open Solidity.Yul

/-- The binary operators the expression producer visits. -/
def Binary (op : Yul.Pure 2) : Prop := op = .add ∨ op = .sub ∨ op = .mul

/-- Accepted right-hand sides: literals, locals and arbitrarily nested binaries. -/
inductive AcceptedExpr {n : Nat} : Yul.Expr [] [] n 1 → Prop
  | literal (w : Yul.Word) : AcceptedExpr (.literal w)
  | «local» (i : Fin n) : AcceptedExpr (.local i)
  | binary {op : Yul.Pure 2} {args : Fin 2 → Yul.Expr [] [] n 1} (selected : Binary op)
      (left : AcceptedExpr (args 0)) (right : AcceptedExpr (args 1)) :
      AcceptedExpr (.builtin (.pure op) args)

/-- Accepted statements. In a closed program every target is a local. -/
inductive Accepted {c : Yul.Control} {n : Nat} : Yul.Stmt [] [] c n → Prop
  | skip : Accepted .skip
  | seq {a b : Yul.Stmt [] [] c n} (first : Accepted a) (second : Accepted b) :
      Accepted (.seq a b)
  | assign (targets : Fin 1 → Yul.Target [] n) {expr : Yul.Expr [] [] n 1}
      (value : AcceptedExpr expr) : Accepted (.assign targets expr)

/-- DUP reach of an expression evaluated `height` words above the locals. The
right operand runs first; the left one runs one word deeper. -/
inductive ExprFits {n : Nat} : Nat → Yul.Expr [] [] n 1 → Prop
  | literal (height : Nat) (w : Yul.Word) : ExprFits height (.literal w)
  | «local» {height : Nat} (i : Fin n) (reach : height + i.val < 16) :
      ExprFits height (.local i)
  | builtin {height : Nat} {b : Yul.Builtin 2 1} {args : Fin 2 → Yul.Expr [] [] n 1}
      (right : ExprFits height (args 1)) (left : ExprFits (1 + height) (args 0)) :
      ExprFits height (.builtin b args)

/-- DUP/SWAP reach of a statement run under `depth` newer words. -/
inductive Fits {c : Yul.Control} {n : Nat} : Nat → Yul.Stmt [] [] c n → Prop
  | skip (depth : Nat) : Fits depth .skip
  | seq {depth : Nat} {a b : Yul.Stmt [] [] c n} (first : Fits depth a) (second : Fits depth b) :
      Fits depth (.seq a b)
  | assign {depth : Nat} (targets : Fin 1 → Yul.Target [] n) {expr : Yul.Expr [] [] n 1}
      (reach : ∀ i : Fin n, targets 0 = .local i → depth + i.val < 16)
      (value : ExprFits depth expr) : Fits depth (.assign targets expr)

end YulArtifact

/-- Every accepted program compiles: the producer succeeds at some fuel. For every
successful compilation and every fitting newer-prefix depth, the lowered program
is emitted, the word selector translates it, and an `Artifact` for the same
statement has exactly that code. The `Artifact` fields keep every source horizon
forward, an existential horizon backward, arbitrary machine and caller frames,
the newer prefix and exact final machine and skip observations. -/
@[goal Solidity.Yul.accepted_compiles_with_artifact "y1-yul-artifact-producers"]
def yulAcceptedCompilesWithArtifact : Prop :=
  ∀ {c : Yul.Control} {n : Nat} (stmt : Yul.Stmt [] [] c n), YulArtifact.Accepted stmt →
    (∃ fuel, (Yul.Compilation.ProducerStatements.compile fuel stmt).isSome) ∧
    ∀ (fuel : Nat) (compiled : Yul.Compilation.ProducerStatements.Compiled fuel stmt),
      Yul.Compilation.ProducerStatements.compile fuel stmt = some compiled →
      ∀ depth : Nat, YulArtifact.Fits depth stmt →
      ∃ (p : Backend.Program) (code : List Evm.Instr),
        compiled.lowered.code depth = some p ∧
        Yul.Compilation.WordMachine.selectCode p = some code ∧
        ∃ artifact : Yul.Compilation.Artifact depth stmt, artifact.code = code

end Solidity.Goals
