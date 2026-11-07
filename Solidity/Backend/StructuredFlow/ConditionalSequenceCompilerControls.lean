import Solidity.Backend.StructuredFlow.ConditionalSequenceCompiler
import Solidity.Backend.StructuredFlow.ConditionalSourceCompilerControls

namespace Solidity.Backend.StructuredFlow.ConditionalSequenceCompiler.Controls
open Solidity.Evm Solidity.Lowering.V07 Solidity.Lowering.G19
open Source.SemanticsExamples (G0 F0)
open MappedCondition.Controls (C)
open ConditionalSourceCompiler.Controls
  (SourceCtx TargetCtx source caller mapping Rel sci sca tci tca machine initial entry)

def core : Prog C TargetCtx TargetCtx := ConditionalSequence.code tci tca tci .here tca tci tca tci
def emitted : List Instr := emit (C := C) 0 tci tca tci .here tca tci tca tci
def post (flag : Bool) : State C TargetCtx :=
  ConditionalSequence.targetAfter (caller flag) tci flag tci .here tca tci tca tci

theorem joined (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag : Bool) :
    (Source.execS (G0 pipeline) F0 (fuel+6) 0 none (R := []) (M := false)
      (ConditionalSequence.statement (k := ⟨false,false⟩) sci sca sci .here sca sci sca sci)
      (source flag).1).run (.nil,(source flag).2) =
      (.ok (Source.Out.normal (ConditionalSequence.sourceAfter (source flag) sci flag sci .here sca sci sca sci).1),
        (.nil,(source flag).2)) ∧
    core.run (caller flag) = .ok ⟨post flag,List.prefix_refl _⟩ ∧
    mapping.Related Rel (ConditionalSequence.sourceAfter (source flag) sci flag sci .here sca sci sca sci).1
      (post flag).env ∧
    (post flag).glob = (caller flag).glob ∧
    StmtOut C 1 0 (Frag.init TargetCtx) false false false
      (core.run (caller flag)) (run emitted (machine flag)) (machine flag) := by
  exact correct (G0 pipeline) F0 fuel 0 none (returns := []) (M := false) (k := ⟨false,false⟩)
    (source flag) (caller flag) mapping Rel (initial flag) (fun _ _ h => h)
    sci sca sci .here sca sci sca sci tci tca tci .here tca tci tca tci
    rfl rfl rfl rfl rfl rfl rfl rfl (entry flag) rfl (by decide)

theorem typed_run (flag : Bool) : core.run (caller flag) = .ok ⟨post flag,List.prefix_refl _⟩ :=
  (joined .legacy 0 flag).2.1

theorem checked (flag : Bool) :
    StmtOut C 1 0 (Frag.init TargetCtx) false false false
      (core.run (caller flag)) (run emitted (machine flag)) (machine flag) :=
  (joined .legacy 0 flag).2.2.2.2

theorem no_canary_store : codeStoresCell 5 emitted = false := by decide

theorem observed (flag : Bool) :
    ∃ final, run emitted (machine flag) = .ok final 0 ∧
      final.mem 0 = .val (bword false) ∧ final.mem 1 = .val (bword false) ∧
      final.mem 2 = .val (bword false) ∧ final.mem 5 = w[99] ∧ final.stack = [w[77]] := by
  rcases checked flag with ⟨o,final,sourceRun,targetRun,stack,_,repr⟩ |
    ⟨sourceRun,_⟩ | ⟨assertion,_⟩ | ⟨payment,_⟩ | ⟨sourceRun,_⟩
  · rw [typed_run flag] at sourceRun
    cases sourceRun
    refine ⟨final,targetRun,?_,?_,?_,?_,stack⟩
    · cases flag <;> exact repr.vals (.there (.there .here))
    · cases flag <;> exact repr.vals (.there .here)
    · cases flag <;> exact repr.vals .here
    · exact exec_mem no_canary_store targetRun
  · rw [typed_run flag] at sourceRun
    cases sourceRun
  · cases assertion
  · cases payment
  · rw [typed_run flag] at sourceRun
    cases sourceRun

def badCore : Prog C TargetCtx TargetCtx := ConditionalSequence.code tci tca tci .here tca tci tca tca
def badEmitted : List Instr := emit (C := C) 0 tci tca tci .here tca tci tca tca

theorem checked_bad : StmtOut C 1 0 (Frag.init TargetCtx) false false false
    (badCore.run (caller true)) (run badEmitted (machine true)) (machine true) := by
  exact prog_sim badCore (entry true) rfl (by decide)

theorem typed_bad : badCore.run (caller true) =
    .ok ⟨ConditionalSequence.targetAfter (caller true) tci true tci .here tca tci tca tca,List.prefix_refl _⟩ :=
  ConditionalSequence.target_run (caller true) tci tca true tci .here tca tci tca tca rfl

theorem observed_bad : ∃ final, run badEmitted (machine true) = .ok final 0 ∧
    final.mem 0 = .val (bword true) := by
  rcases checked_bad with ⟨o,final,sourceRun,targetRun,_,_,repr⟩ |
    ⟨sourceRun,_⟩ | ⟨assertion,_⟩ | ⟨payment,_⟩ | ⟨sourceRun,_⟩
  · rw [typed_bad] at sourceRun
    cases sourceRun
    exact ⟨final,targetRun,repr.vals (.there (.there .here))⟩
  · rw [typed_bad] at sourceRun
    cases sourceRun
  · cases assertion
  · cases payment
  · rw [typed_bad] at sourceRun
    cases sourceRun

theorem wrong_tail_slot_refused : run badEmitted (machine true) ≠ run emitted (machine true) := by
  rcases observed true with ⟨good,goodRun,goodValue,_⟩
  rcases observed_bad with ⟨bad,badRun,badValue⟩
  intro same
  rw [badRun,goodRun] at same
  have wordSame : bad.mem 0 = good.mem 0 := congrArg (fun out : Solidity.Evm.Out =>
    match out with | .ok post _ => post.mem 0 | _ => w[0]) same
  rw [badValue,goodValue] at wordSame
  have different : Word.val (bword true) ≠ Word.val (bword false) := by decide
  exact different wordSame

theorem source_zero (pipeline : Roadmap.Pipeline) (flag : Bool) :
    Source.execS (G0 pipeline) F0 0 0 none (R := []) (M := false)
      (ConditionalSequence.statement (k := ⟨false,false⟩) sci sca sci .here sca sci sca sci)
      (source flag).1 = Source.EM.halt .timeout := by rfl

end Solidity.Backend.StructuredFlow.ConditionalSequenceCompiler.Controls
