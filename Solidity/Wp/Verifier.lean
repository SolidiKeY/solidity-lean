import Solidity.EvalBattery
import Solidity.Wp.Step
import Solidity.Wp.StepSoundness

/-!
# The wp verifier: `sol_wp`

The final stage of the wp pipeline: a push-button tactic proving
`(sol!{…}).Holds` goals by *kernel-checked symbolic execution* — no
`native_decide` anywhere.

The WF-recursive interpreter does not kernel-reduce, so `decide` on a raw
`Holds`/`execStmt` term fails. Instead:

1. `sol_exec_eval` computes a single concrete interpreter verdict
   (`execStmt s stmt = .ok ?s'` / `= .error ?h`) by `simp` with the
   interpreter's equation lemmas plus the `SoliditySyntax` smart
   constructors, then `rfl` to assign the result metavariable.
2. `sol_wp_step` peels one statement off the wp goal through the *total*
   step lemmas `Dia.wpD_cons_eval` / `Box.wpB_cons_eval` (thin wrappers
   over `Step.lean`'s `cons_ok`/`cons_revert`/`not_cons_halt`), each fed
   the interpreter verdict computed by `sol_exec_eval`. (`rw` postpones
   the `by`-blocks until after the lemma's implicit `s`/`stmt` are fixed
   by unification with the goal, so the verdicts are computed on
   *concrete* states — and the verdict hypothesis `execStmt s stmt = ?r`
   succeeds whatever the outcome, keeping the `first` dispatch sound.)
3. `sol_wp` glues it together: `Holds_dia_iff`/`Holds_box_iff` turns the
   judgment into a wp goal, the step is repeated to exhaustion, and the
   residual `postCond` goal is evaluated by the same battery — after
   simp-normalization everything is WF-free, so the kernel checks it.

The axiom profile of every proof produced this way is
`[propext, Classical.choice, Quot.sound]`.
-/

namespace Solidity
namespace Wp

open Semantics

set_option maxHeartbeats 8000000

/-! ## Total step lemmas

`Step.lean`'s `cons_ok`/`cons_revert` lemmas each *presuppose* a verdict
shape, but a tactic cannot cheaply predict which one holds: a `by`-block
that fails inside a `rw` argument is postponed past the `first`
combinator's backtracking. The `cons_eval` lemmas below are total — their
hypothesis `execStmt s stmt = r` is established for *whatever* `r` the
interpreter computes, and the continuation `wpNext` dispatches on `r`
afterwards, by mere iota reduction. -/

namespace Box

/-- The box continuation after one step: proceed on `.ok`, vacuous success
exactly on `.revert`. -/
def wpNext (rest : Block) (Q : Unit -> State -> Prop) : Res State -> Prop
  | .ok s' => wpB (execBlockM rest) Q s'
  | .error h => h = Halt.revert

/-- Total box step: peel the head statement given its interpreter verdict,
whatever it is. -/
theorem wpB_cons_eval {stmt : Stmt} {rest : Block} {s : State}
    {Q : Unit -> State -> Prop} {r : Res State}
    (hexec : execStmt s stmt = r) :
    wpB (execBlockM (stmt :: rest)) Q s ↔ wpNext rest Q r := by
  cases r with
  | ok s' => exact wpB_cons_ok hexec
  | error h =>
      show _ ↔ h = Halt.revert
      rw [execBlockM_cons, wpB_run, SolM.bind_run]
      rw [show execStmtM stmt s
          = (execStmt s stmt).map (fun t => ((), t)) from rfl]
      rw [hexec]
      exact Iff.rfl

end Box

namespace Dia

/-- The diamond continuation after one step: proceed on `.ok`, refuted by
any halt. -/
def wpNext (rest : Block) (Q : Unit -> State -> Prop) : Res State -> Prop
  | .ok s' => wpD (execBlockM rest) Q s'
  | .error _ => False

/-- Total diamond step: peel the head statement given its interpreter
verdict, whatever it is. -/
theorem wpD_cons_eval {stmt : Stmt} {rest : Block} {s : State}
    {Q : Unit -> State -> Prop} {r : Res State}
    (hexec : execStmt s stmt = r) :
    wpD (execBlockM (stmt :: rest)) Q s ↔ wpNext rest Q r := by
  cases r with
  | ok s' => exact wpD_cons_ok hexec
  | error h =>
      show _ ↔ False
      exact iff_false_intro (not_wpD_cons_halt hexec)

end Dia

/-! ## The evaluation battery

`sol_eval_battery` and `sol_exec_eval` live in
`Solidity/EvalBattery.lean`: they depend on the interpreter alone, with no
reference to the wp algebra below. -/

/-- Peel one statement off a wp-over-block goal via the total `cons_eval`
lemmas: the modality is dispatched by unification (`Dia.wpD` and
`Box.wpB` are distinct constants, so at most one of the two `rw`
patterns has a matching head), the interpreter verdict is
computed by `sol_exec_eval` — which always succeeds, whatever the verdict —
and `wpNext` is reduced away on the now-concrete verdict. A revert under
box leaves `Halt.revert = Halt.revert`, closed by the trailing `rfl`. -/
macro "sol_wp_step" : tactic =>
  `(tactic|
    ((first
        | rw [Dia.wpD_cons_eval (by sol_exec_eval)]
        | rw [Box.wpB_cons_eval (by sol_exec_eval)]);
     simp only [Dia.wpNext, Box.wpNext];
     try rfl))

/-- Discharge the residual goal of a fully peeled block: `wpD_nil`/`wpB_nil`
exposes `postCond post () s`, whose `evalValue` is computed by the same
battery; the leftover ground literal falls to `simp`'s closing rules (with
kernel `decide` as a fallback — everything is WF-free by now). -/
macro "sol_wp_post" : tactic =>
  `(tactic|
    ((try (first
        | rw [Dia.wpD_nil]
        | rw [Box.wpB_nil]));
     simp only [postCond];
     sol_eval_battery;
     try decide))

/-- The wp verifier: proves `(sol!{…}).Holds` goals (default initial state)
by turning the judgment into a wp goal (`Holds_dia_iff`/`Holds_box_iff`),
peeling statements to exhaustion with interpreter-computed verdicts, and
evaluating the residual postcondition. Kernel-checked throughout — no
`native_decide`. -/
macro "sol_wp" : tactic =>
  `(tactic|
    ((first
        | rw [Holds_dia_iff]
        | rw [Holds_box_iff]);
     repeat sol_wp_step;
     all_goals sol_wp_post))

end Wp
end Solidity
