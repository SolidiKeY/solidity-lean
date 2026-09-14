import Solidity.Wp.Judgment

/-!
# Generic wp step lemmas

Peeling one statement off a block under `wpB`/`wpD`, given the interpreter's
verdict on that statement. Together with the per-rule `_update` equations
(`Wp/Terminal/Update*.lean`), these turn a wp goal over `stmt :: rest` into a wp goal
over `rest` in the updated state — the state-carrying step the rewrite layer's
empty residuals cannot express.
-/

namespace Solidity
namespace Wp

open Semantics

namespace Box

theorem wpB_cons_ok {stmt : Stmt} {rest : Block} {s s' : State}
    {Q : Unit -> State -> Prop} (hexec : execStmt s stmt = .ok s') :
    wpB (execBlockM (stmt :: rest)) Q s ↔ wpB (execBlockM rest) Q s' := by
  rw [execBlockM_cons, wpB_run, wpB_run, SolM.bind_run]
  rw [show execStmtM stmt s
      = (execStmt s stmt).map (fun t => ((), t)) from rfl]
  rw [hexec]
  rfl

/-- Box: a reverting head statement validates the block vacuously. -/
theorem wpB_cons_revert {stmt : Stmt} {rest : Block} {s : State}
    {Q : Unit -> State -> Prop}
    (hexec : execStmt s stmt = .error Halt.revert) :
    wpB (execBlockM (stmt :: rest)) Q s := by
  rw [execBlockM_cons, wpB_run, SolM.bind_run]
  rw [show execStmtM stmt s
      = (execStmt s stmt).map (fun t => ((), t)) from rfl]
  rw [hexec]
  rfl

theorem wpB_nil {s : State} {Q : Unit -> State -> Prop} :
    wpB (execBlockM []) Q s ↔ Q () s := by
  rw [wpB_run]
  exact Iff.rfl

end Box

namespace Dia

theorem wpD_cons_ok {stmt : Stmt} {rest : Block} {s s' : State}
    {Q : Unit -> State -> Prop} (hexec : execStmt s stmt = .ok s') :
    wpD (execBlockM (stmt :: rest)) Q s ↔ wpD (execBlockM rest) Q s' := by
  rw [execBlockM_cons, wpD_run, wpD_run, SolM.bind_run]
  rw [show execStmtM stmt s
      = (execStmt s stmt).map (fun t => ((), t)) from rfl]
  rw [hexec]
  rfl

/-- Diamond: a halting head statement refutes the block. -/
theorem not_wpD_cons_halt {stmt : Stmt} {rest : Block} {s : State}
    {Q : Unit -> State -> Prop} {h : Halt}
    (hexec : execStmt s stmt = .error h) :
    ¬ wpD (execBlockM (stmt :: rest)) Q s := by
  rw [execBlockM_cons, wpD_run, SolM.bind_run]
  rw [show execStmtM stmt s
      = (execStmt s stmt).map (fun t => ((), t)) from rfl]
  rw [hexec]
  exact fun hf => hf

theorem wpD_nil {s : State} {Q : Unit -> State -> Prop} :
    wpD (execBlockM []) Q s ↔ Q () s := by
  rw [wpD_run]
  exact Iff.rfl

end Dia

end Wp
end Solidity
