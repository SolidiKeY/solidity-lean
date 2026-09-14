import Solidity.Semantics

/-!
# Monadic view of the executable semantics

`Semantics.execStmt : State -> Stmt -> Except Halt State` is already a
state-and-exception computation written out by hand. This module names that
shape — `SolM := StateT State (ExceptT Halt Id)` — and gives the two
modalities of `SolidityJudgment.check` one weakest precondition each over it,
*without touching the interpreter*: the wrappers below are definitional
repackagings, and every wp fact is proved against the original
`execStmt`/`execBlock`.

The two modalities differ only in what they make of a halt:

* box (`[ ]`): a `Halt.revert` validates the judgment vacuously — `wpB`'s
  error arm is `h = Halt.revert`;
* diamond (`< >`): any halt refutes the judgment — `wpD`'s error arm is
  `False`.

`Halt.stuck` is rejected by both, matching `check`.
-/

namespace Solidity
namespace Wp

open Semantics

/-- The interpreter's monad, named: state threaded, halts as exceptions. -/
abbrev SolM (α : Type) : Type := StateT State (ExceptT Halt Id) α

/-- `execStmt` as a `SolM` program. Definitional repackaging only. -/
def execStmtM (stmt : Stmt) : SolM Unit :=
  fun s => (execStmt s stmt).map (fun s' => ((), s'))

/-- `execBlock` as a `SolM` program. Definitional repackaging only. -/
def execBlockM (b : Block) : SolM Unit :=
  fun s => (execBlock s b).map (fun s' => ((), s'))

/-- Running a `SolM` bind: sequence in the underlying `Except`. -/
theorem SolM.bind_run {α β : Type} (x : SolM α) (f : α -> SolM β) (s : State) :
    (x >>= f) s = (x s : Except Halt (α × State)).bind (fun p => f p.1 p.2) :=
  rfl

@[simp] theorem execBlockM_nil : execBlockM [] = (pure () : SolM Unit) := rfl

@[simp] theorem execBlockM_cons (stmt : Stmt) (rest : Block) :
    execBlockM (stmt :: rest)
      = (execStmtM stmt >>= fun _ => execBlockM rest : SolM Unit) := by
  funext s
  rw [SolM.bind_run]
  unfold execBlockM execStmtM
  cases h : execStmt s stmt <;>
    simp [execBlock, h, Except.map, Except.bind, Bind.bind,
      ExceptT.bind, ExceptT.bindCont, ExceptT.mk, Id.pure_eq]

/-- The run of a `SolM` computation, exposing the underlying `Except`. -/
@[simp] theorem execStmtM_run (stmt : Stmt) (s : State) :
    execStmtM stmt s = (execStmt s stmt).map (fun s' => ((), s')) := rfl

@[simp] theorem execBlockM_run (b : Block) (s : State) :
    execBlockM b s = (execBlock s b).map (fun s' => ((), s')) := rfl

/-! ## Box modality: `Halt.revert` is vacuous success -/

namespace Box

/-- Box weakest precondition for `SolM`: the interpreter's result read
directly, with `Halt.revert` as vacuous success. -/
def wpB {α : Type} (c : SolM α) (Q : α -> State -> Prop) : State -> Prop :=
  fun s =>
    match (c s : Except Halt (α × State)) with
    | .ok (a, s') => Q a s'
    | .error h => h = Halt.revert

/-- Closed form: box wp inspects the interpreter's result directly. -/
theorem wpB_run {α : Type} (c : SolM α) (Q : α -> State -> Prop) (s : State) :
    wpB c Q s =
      match (c s : Except Halt (α × State)) with
      | .ok (a, s') => Q a s'
      | .error h => h = Halt.revert := rfl

end Box

/-! ## Diamond modality: every halt is failure -/

namespace Dia

/-- Diamond weakest precondition for `SolM`: every halt is failure. -/
def wpD {α : Type} (c : SolM α) (Q : α -> State -> Prop) : State -> Prop :=
  fun s =>
    match (c s : Except Halt (α × State)) with
    | .ok (a, s') => Q a s'
    | .error _ => False

/-- Closed form: diamond wp demands normal termination. -/
theorem wpD_run {α : Type} (c : SolM α) (Q : α -> State -> Prop) (s : State) :
    wpD c Q s =
      match (c s : Except Halt (α × State)) with
      | .ok (a, s') => Q a s'
      | .error _ => False := rfl

end Dia

end Wp
end Solidity
