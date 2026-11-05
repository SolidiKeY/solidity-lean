import Solidity.Backend.StructuredFlow.WhileContinueCompiler
import Solidity.Lowering.G19.AssignmentWhileContinueControls

namespace Solidity.Backend.StructuredFlow.WhileContinueCompiler.Controls
open Solidity.Evm Solidity.Lowering.V07 Solidity.Lowering.G19
open Source.SemanticsExamples (E0 G0 F0)
open MappedCondition.Controls (C mapping caller)
open ConditionalSourceCompiler.Controls (Rel)
open AssignmentWhileReset.Controls (source machine core entry initial)
open AssignmentWhileContinue.Controls (tail)

theorem joined (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag : Bool) :
    (Source.execS (G0 pipeline) F0 (fuel+8) 0 none (R := []) (M := false)
      (AssignmentWhileContinue.statement (l := false) .here (.there .here) tail) (source flag).1).run
      (.nil,(source flag).2) =
      (.ok (Source.Out.normal (AssignmentWhileReset.sourceAfter (source flag).1 .here (.there .here) flag)),
        (.nil,(source flag).2)) ∧
    StmtOut C 1 0 (Frag.init [.val .bool,.val .bool]) false false false
      (core.run (caller flag)) (run (emit (C := C) 0 mapping .here (.there .here) rfl rfl) (machine flag))
      (machine flag) := by
  rcases correct (G0 pipeline) F0 fuel 0 none (returns := []) (M := false) (l := false) (u := false)
    (source flag) (caller flag) mapping Rel (initial flag) (fun _ _ h => h) rfl
    .here (.there .here) rfl rfl rfl rfl tail (entry flag) rfl (by decide) with
    ⟨src,_,_,_,compiled⟩
  exact ⟨src,compiled⟩

def wrongCore : Prog C [.val .bool,.val .bool] [.val .bool,.val .bool] :=
  .cons (.block (AssignmentWhileBreak.code mapping .here (.there .here) rfl rfl))
    (.cons (.loop .auto (.simple (.bool false))
      (AssignmentWhileReset.body mapping .here (.there .here) rfl rfl)) .nil)

def wrongEmit : List Instr := compileProg 0 wrongCore

theorem wrong_run (flag : Bool) : wrongCore.run (caller flag) =
    .ok ⟨AssignmentWhileBreak.reached mapping .here (.there .here) rfl rfl (caller flag),
      List.prefix_refl _⟩ := by
  exact false_guard_run mapping .here (.there .here) rfl rfl (caller flag)

theorem wrong_checked (flag : Bool) : StmtOut C 1 0 (Frag.init [.val .bool,.val .bool]) false false false
    (wrongCore.run (caller flag)) (run wrongEmit (machine flag)) (machine flag) := by
  exact prog_sim wrongCore (entry flag) rfl (by decide)

theorem wrong_observed : ∃ final, run wrongEmit (machine true) = .ok final 0 ∧
    final.mem 1 = .val (bword true) := by
  rcases wrong_checked true with ⟨o,final,sourceRun,targetRun,_,_,repr⟩ |
    ⟨sourceRun,_⟩ | ⟨assertion,_⟩ | ⟨payment,_⟩ | ⟨sourceRun,_⟩
  · rw [wrong_run] at sourceRun
    cases sourceRun
    exact ⟨final,targetRun,repr.vals .here⟩
  · rw [wrong_run] at sourceRun
    cases sourceRun
  · cases assertion
  · cases payment
  · rw [wrong_run] at sourceRun
    cases sourceRun

theorem guard_change_refused : run wrongEmit (machine true) ≠
    run (emit (C := C) 0 mapping .here (.there .here) rfl rfl) (machine true) := by
  rcases AssignmentWhileReset.Controls.observed true with ⟨good,goodRun,_,goodValue,_⟩
  rcases wrong_observed with ⟨bad,badRun,badValue⟩
  intro same
  change run wrongEmit (machine true) = run AssignmentWhileReset.Controls.emitted (machine true) at same
  rw [badRun,goodRun] at same
  have wordSame : bad.mem 1 = good.mem 1 := congrArg (fun out : Solidity.Evm.Out =>
    match out with | .ok post _ => post.mem 1 | _ => w[0]) same
  rw [badValue,goodValue] at wordSame
  have different : Word.val (bword true) ≠ Word.val (bword false) := by decide
  exact different wordSame

theorem scalar_dead_accepted :
    (inFragP (⟨[.ok,.dead]⟩ : Frag [.val .bool,.val .bool]) core).isSome = true := by decide

theorem wrong_entry_refused :
    ¬ Sim C 1 0 (⟨[.ok,.dead]⟩ : Frag [.val .bool,.val .bool]) (caller true) (machine false) := by
  intro h
  have bad : (w[0] : Word) = w[1] := h.vals (.there .here)
  have different : (w[0] : Word) ≠ w[1] := by decide
  exact different bad

end Solidity.Backend.StructuredFlow.WhileContinueCompiler.Controls
