import Solidity.Backend.StructuredFlow.ScopedMappedSequence
import Solidity.Backend.StructuredFlow.MappedBranchControls

namespace Solidity.Backend.StructuredFlow.ScopedMappedSequence.Controls
open Solidity.Evm Solidity.Lowering.V07
open MappedCondition.Controls (C mapping caller loaded represented)
open MappedBranch.Controls (left right)

def tail : Prog C [.val .bool,.val .bool] [.val .bool,.val .bool,.val .bool] :=
  .cons (.declLocal .bool (.user "after_branch") (some (.simple (.local .here)))) .nil

def badTail : Prog C [.val .bool,.val .bool] [.val .bool,.val .bool,.val .bool] :=
  .cons (.declLocal .bool (.user "after_branch") (some (.simple (.local (.there .here))))) .nil

def core : Prog C [.val .bool,.val .bool] [.val .bool,.val .bool,.val .bool] :=
  program mapping .here (.there .here) rfl rfl left right tail

def badCore : Prog C [.val .bool,.val .bool] [.val .bool,.val .bool,.val .bool] :=
  program mapping .here (.there .here) rfl rfl left right badTail

def emitted : List Instr := emit 0 mapping .here (.there .here) rfl rfl left right tail
def badEmitted : List Instr := emit 0 mapping .here (.there .here) rfl rfl left right badTail

def loadedCanary (flag : Bool) : Machine := {loaded flag with mem := upd (loaded flag).mem 3 w[99]}
def outState (flag : Bool) : State C [.val .bool,.val .bool,.val .bool] :=
  (caller flag).push (t := .val .bool) (!flag)

theorem entry (flag : Bool) :
    Sim C 1 0 (Frag.init [.val .bool,.val .bool]) (caller flag) (loadedCanary flag) := by
  apply SimL.congrMem (represented flag)
  intro level low high
  apply upd_other
  change level ≠ 3
  change level < 2 at high
  omega

theorem checked_good (flag : Bool) :
    StmtOut C 1 0 (Frag.init [.val .bool,.val .bool,.val .bool]) false false false
      (core.run (caller flag)) (run emitted (loadedCanary flag)) (loadedCanary flag) := by
  apply correct (F₁ := Frag.init [.val .bool,.val .bool,.val .bool])
    (F₂ := Frag.init [.val .bool,.val .bool,.val .bool])
    mapping .here (.there .here) rfl rfl left right tail (entry flag) rfl rfl rfl
  change 1 ≤ Lmax
  exact (entry flag).bound

theorem checked_bad (flag : Bool) :
    StmtOut C 1 0 (Frag.init [.val .bool,.val .bool,.val .bool]) false false false
      (badCore.run (caller flag)) (run badEmitted (loadedCanary flag)) (loadedCanary flag) := by
  apply correct (F₁ := Frag.init [.val .bool,.val .bool,.val .bool])
    (F₂ := Frag.init [.val .bool,.val .bool,.val .bool])
    mapping .here (.there .here) rfl rfl left right badTail (entry flag) rfl rfl rfl
  change 1 ≤ Lmax
  exact (entry flag).bound

theorem typed_runs (flag : Bool) :
    core.run (caller flag) = .ok ⟨outState flag,List.prefix_refl _⟩ ∧
    badCore.run (caller flag) = .ok ⟨(caller flag).push (t := .val .bool) flag,List.prefix_refl _⟩ := by
  constructor <;> cases flag <;> (change Prog.runR _ _ = _; rw [Prog.runR_eq]; rfl)

theorem no_canary_store : codeStoresCell 3 emitted = false ∧ codeStoresCell 3 badEmitted = false := by decide

theorem observed_good (flag : Bool) :
    ∃ final, run emitted (loadedCanary flag) = .ok final 0 ∧
      final.mem 0 = .val (bword flag) ∧ final.mem 1 = .val (bword (!flag)) ∧
      final.mem 2 = .val (bword (!flag)) ∧ final.mem 3 = w[99] ∧ final.stack = [w[77]] := by
  rcases checked_good flag with ⟨o,final,sourceRun,targetRun,stack,_,post⟩ |
    ⟨sourceRun,_⟩ | ⟨assertion,_⟩ | ⟨payment,_⟩ | ⟨sourceRun,_⟩
  · rw [(typed_runs flag).1] at sourceRun
    cases sourceRun
    refine ⟨final,targetRun,?_,?_,?_,?_,stack⟩
    · exact post.vals (.there (.there .here))
    · exact post.vals (.there .here)
    · exact post.vals .here
    · exact exec_mem no_canary_store.1 targetRun
  · rw [(typed_runs flag).1] at sourceRun
    cases sourceRun
  · cases assertion
  · cases payment
  · rw [(typed_runs flag).1] at sourceRun
    cases sourceRun

theorem observed_bad (flag : Bool) :
    ∃ final, run badEmitted (loadedCanary flag) = .ok final 0 ∧
      final.mem 0 = .val (bword flag) ∧ final.mem 1 = .val (bword (!flag)) ∧
      final.mem 2 = .val (bword flag) ∧ final.mem 3 = w[99] ∧ final.stack = [w[77]] := by
  rcases checked_bad flag with ⟨o,final,sourceRun,targetRun,stack,_,post⟩ |
    ⟨sourceRun,_⟩ | ⟨assertion,_⟩ | ⟨payment,_⟩ | ⟨sourceRun,_⟩
  · rw [(typed_runs flag).2] at sourceRun
    cases sourceRun
    refine ⟨final,targetRun,?_,?_,?_,?_,stack⟩
    · exact post.vals (.there (.there .here))
    · exact post.vals (.there .here)
    · exact post.vals .here
    · exact exec_mem no_canary_store.2 targetRun
  · rw [(typed_runs flag).2] at sourceRun
    cases sourceRun
  · cases assertion
  · cases payment
  · rw [(typed_runs flag).2] at sourceRun
    cases sourceRun

theorem wrong_index_refused (flag : Bool) :
    run badEmitted (loadedCanary flag) ≠ run emitted (loadedCanary flag) := by
  rcases observed_good flag with ⟨good,goodRun,_,_,goodValue,_,_⟩
  rcases observed_bad flag with ⟨bad,badRun,_,_,badValue,_,_⟩
  intro same
  rw [badRun,goodRun] at same
  have wordSame : bad.mem 2 = good.mem 2 := congrArg (fun out : Solidity.Evm.Out =>
    match out with | .ok post _ => post.mem 2 | _ => w[0]) same
  rw [badValue,goodValue] at wordSame
  have different : Word.val (bword flag) ≠ Word.val (bword (!flag)) := by cases flag <;> decide
  exact different wordSame

end Solidity.Backend.StructuredFlow.ScopedMappedSequence.Controls
