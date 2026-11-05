import Solidity.Lowering.G19.AssignmentWhileReset
import Solidity.Backend.StructuredFlow.ConditionalSourceCompilerControls

namespace Solidity.Lowering.G19.AssignmentWhileReset.Controls
open Solidity.Evm Solidity.Lowering.V07
open Source.SemanticsExamples (E0 G0 F0 s0)
open Solidity.Backend.StructuredFlow.MappedCondition.Controls (C mapping caller loaded represented)
open Solidity.Backend.StructuredFlow.ConditionalSourceCompiler.Controls (Rel)

def source (flag : Bool) : Source.EMState E0 [.bool,.bool] :=
  (.cons (.bool (!flag)) (.cons (.bool flag) .nil),s0)
def core : Prog C [.val .bool,.val .bool] [.val .bool,.val .bool] :=
  code mapping .here (.there .here) rfl rfl
def emitted : List Instr := compileProg 0 core
def machine (flag : Bool) : Machine := {loaded flag with mem := upd (loaded flag).mem 3 w[99]}

theorem initial (flag : Bool) : mapping.Related Rel (source flag).1 (caller flag).env := by
  intro τ i
  cases i with
  | here => rfl
  | there i => cases i with
    | here => rfl
    | there i => nomatch i

theorem entry (flag : Bool) : Sim C 1 0 (Frag.init [.val .bool,.val .bool]) (caller flag) (machine flag) := by
  apply SimL.congrMem (represented flag)
  intro level low high
  apply upd_other
  change level ≠ 3
  change level < 2 at high
  omega

theorem joined (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag : Bool) :
    (Source.execS (G0 pipeline) F0 (fuel+4) 0 none (R := []) (M := false)
      (.whileLoop (l := false) (u := false) (.assign (.local .here) (.local (.there .here)))
        (.expr (.assign (.local (.there .here)) (.bool false)))) (source flag).1).run (.nil,(source flag).2) =
      (.ok (Source.Out.normal (sourceAfter (source flag).1 .here (.there .here) flag)),(.nil,(source flag).2)) ∧
    core.run (caller flag) = .ok ⟨targetAfter mapping .here (.there .here) rfl rfl (caller flag),List.prefix_refl _⟩ ∧
    mapping.Related Rel (sourceAfter (source flag).1 .here (.there .here) flag)
      (targetAfter mapping .here (.there .here) rfl rfl (caller flag)).env ∧
    (targetAfter mapping .here (.there .here) rfl rfl (caller flag)).glob = (caller flag).glob := by
  exact correct (G0 pipeline) F0 fuel 0 none (returns := []) (M := false) (l := false) (u := false)
    (source flag) (caller flag) mapping Rel (initial flag) (fun _ _ h => h) rfl
    .here (.there .here) rfl rfl rfl rfl

theorem checked (flag : Bool) : StmtOut C 1 0 (Frag.init [.val .bool,.val .bool]) false false false
    (core.run (caller flag)) (run emitted (machine flag)) (machine flag) := by
  exact prog_sim core (entry flag) rfl (by decide)

theorem observed (flag : Bool) : ∃ final, run emitted (machine flag) = .ok final 0 ∧
    final.mem 0 = .val (bword false) ∧ final.mem 1 = .val (bword false) ∧
    final.mem 3 = w[99] ∧ final.stack = [w[77]] := by
  have typed : core.run (caller flag) =
      .ok ⟨targetAfter mapping .here (.there .here) rfl rfl (caller flag),List.prefix_refl _⟩ :=
    (joined .legacy 0 flag).2.1
  rcases checked flag with ⟨o,final,sourceRun,targetRun,stack,_,repr⟩ |
    ⟨sourceRun,_⟩ | ⟨assertion,_⟩ | ⟨payment,_⟩ | ⟨sourceRun,_⟩
  · rw [typed] at sourceRun
    cases sourceRun
    refine ⟨final,targetRun,?_,?_,?_,stack⟩
    · cases flag <;> exact repr.vals (.there .here)
    · cases flag <;> exact repr.vals .here
    · exact exec_mem (by decide : codeStoresCell 3 emitted = false) targetRun
  · rw [typed] at sourceRun
    cases sourceRun
  · cases assertion
  · cases payment
  · rw [typed] at sourceRun
    cases sourceRun

def omitted : List Instr := compileProg 0
  (AssignmentWhileBreak.code mapping .here (.there .here) rfl rfl : Prog C [.val .bool,.val .bool] [.val .bool,.val .bool])

theorem omitted_checked : StmtOut C 1 0 (Frag.init [.val .bool,.val .bool]) false false false
    ((AssignmentWhileBreak.code mapping .here (.there .here) rfl rfl : Prog C _ _).run (caller true))
    (run omitted (machine true)) (machine true) := by
  exact prog_sim (AssignmentWhileBreak.code mapping .here (.there .here) rfl rfl :
    Prog C [.val .bool,.val .bool] [.val .bool,.val .bool]) (entry true) rfl (by decide)

theorem omitted_observed : ∃ final, run omitted (machine true) = .ok final 0 ∧
    final.mem 1 = .val (bword true) := by
  have typed : (AssignmentWhileBreak.code mapping .here (.there .here) rfl rfl :
      Prog C [.val .bool,.val .bool] [.val .bool,.val .bool]).run (caller true) =
      .ok ⟨AssignmentWhileBreak.reached mapping .here (.there .here) rfl rfl (caller true),List.prefix_refl _⟩ :=
    AssignmentWhileBreak.target_run mapping .here (.there .here) rfl rfl (caller true)
  rcases omitted_checked with ⟨o,final,sourceRun,targetRun,_,_,repr⟩ |
    ⟨sourceRun,_⟩ | ⟨assertion,_⟩ | ⟨payment,_⟩ | ⟨sourceRun,_⟩
  · rw [typed] at sourceRun
    cases sourceRun
    exact ⟨final,targetRun,repr.vals .here⟩
  · rw [typed] at sourceRun
    cases sourceRun
  · cases assertion
  · cases payment
  · rw [typed] at sourceRun
    cases sourceRun

theorem omitted_loop_refused : run omitted (machine true) ≠ run emitted (machine true) := by
  rcases observed true with ⟨good,goodRun,_,goodValue,_⟩
  rcases omitted_observed with ⟨bad,badRun,badValue⟩
  intro same
  rw [badRun,goodRun] at same
  have wordSame : bad.mem 1 = good.mem 1 := congrArg (fun out : Solidity.Evm.Out =>
    match out with | .ok post _ => post.mem 1 | _ => w[0]) same
  rw [badValue,goodValue] at wordSame
  have different : Word.val (bword true) ≠ Word.val (bword false) := by decide
  exact different wordSame

theorem self_alias (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag : Bool) :
    (Source.execS (G0 pipeline) F0 (fuel+4) 0 none (R := []) (M := false)
      (.whileLoop (l := false) (u := false) (.assign (.local .here) (.local .here))
        (.expr (.assign (.local .here) (.bool false)))) (source flag).1).run (.nil,(source flag).2) =
      (.ok (Source.Out.normal ((source flag).1.set .here (.bool false))),(.nil,(source flag).2)) ∧
    (code mapping .here .here rfl rfl : Prog C _ _).run (caller flag) =
      .ok ⟨(caller flag).setLocal .here false,List.prefix_refl _⟩ := by
  rw [source_run (G0 pipeline) F0 fuel 0 none (source flag).1 (source flag).2 .here .here (!flag) rfl,
    target_run mapping .here .here rfl rfl (caller flag)]
  cases flag <;> exact ⟨rfl,rfl⟩

end Solidity.Lowering.G19.AssignmentWhileReset.Controls
