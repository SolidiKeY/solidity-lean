import Solidity.Backend.StructuredFlow.ConditionalReturnCompiler
import Solidity.Lowering.G19.ConditionalReturnControls
import Solidity.Backend.StructuredFlow.ReturnTailCompilerControls

namespace Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.Controls
open Solidity.Evm Solidity.Lowering.V07 Solidity.Lowering.G19
open Source.SemanticsExamples (G0 F0)
open MappedCondition.Controls (C)
open ConditionalSourceCompiler.Controls (TargetCtx mapping Rel sci sca tci tca)
open ReturnTailCompiler.Controls (source caller machine initial entry)
open ConditionalReturn (statement code reached)

def core : Prog C TargetCtx (.val .bool :: TargetCtx) := code tci tca .here tci tca .here
def emitted : List Instr := emit (C := C) 0 tci tca .here tci tca .here
/-- Caller cells, true return capture, retained selected-value temporary,
canary, then the entire stack. -/
def snapshot (out : Evm.Out) : Option (List Word) :=
  match out with
  | .ok post 0 => some ([post.mem 0,post.mem 1,post.mem 2,post.mem 3,post.mem 4,post.mem 5] ++ post.stack)
  | _ => none

theorem joined (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag checked : Bool) :
    (Source.execS (G0 pipeline) {F0 with checked := checked} (fuel+6) 0 none (M := false)
      (statement (k := ⟨false,false⟩) sci sca .here sci sca .here) (source flag).1).run
      (.nil,(source flag).2) =
      (.ok (Source.Out.ret (ConditionalAssignments.sourceAfter (source flag) sci flag .here sci sca .here).1),
        (.nil,(source flag).2)) ∧
    StmtOut C 1 0 (Frag.init (.val .bool :: TargetCtx)) false false false
      (core.run (caller flag)) (run emitted (machine flag)) (machine flag) := by
  rcases correct (G0 pipeline) {F0 with checked := checked} fuel 0 none
    (M := false) (k := ⟨false,false⟩) (source flag) (caller flag) mapping Rel
    (initial flag) (fun _ _ h => h) sci sca .here sci sca .here
    tci tca .here tci tca .here rfl rfl rfl rfl rfl rfl (entry flag) rfl (by decide) with
    ⟨src,_,_,_,_,compiled⟩
  exact ⟨src,compiled⟩

theorem prefix_typed (flag : Bool) : (ConditionalAssignments.code (C := C) tci tca .here tci tca .here).run (caller flag) =
    .ok ⟨((ConditionalAssignments.targetAfter (caller flag) tci flag .here tci tca .here).push
      (t := .val .bool) flag).push (t := .val .bool) true,List.prefix_refl _⟩ := by
  have typed : (ConditionalAssignments.code (C := C) tci tca .here tci tca .here).run (caller flag) =
      .ok ⟨((ConditionalAssignments.targetAfter (caller flag) tci flag .here tci tca .here).push
        (t := .val .bool) flag).push
        (TEnv.get (if flag then tci else .here) (TEnv.set tci flag (caller flag).env)),List.prefix_refl _⟩ :=
    ConditionalAssignments.prefix_run (caller flag) tci tca flag .here tci tca .here rfl
  cases flag <;> exact typed

theorem prefix_observed (flag : Bool) :
    ∃ prefixState, run (compileProg 0 (ConditionalAssignments.code (C := C) tci tca .here tci tca .here))
      (machine flag) = .ok prefixState 0 ∧
      prefixState.mem 0 = w[1] ∧ prefixState.mem 1 = .val (bword flag) ∧
      prefixState.mem 2 = w[1] ∧ prefixState.mem 4 = w[1] ∧
      prefixState.mem 5 = w[99] ∧ prefixState.stack = [w[77]] := by
  have compiled : StmtOut C 1 0 (Frag.init (.val .bool :: .val .bool :: TargetCtx)) false false false
      ((ConditionalAssignments.code (C := C) tci tca .here tci tca .here).run (caller flag))
      (run (compileProg 0 (ConditionalAssignments.code (C := C) tci tca .here tci tca .here))
        (machine flag)) (machine flag) :=
    prog_sim (ConditionalAssignments.code (C := C) tci tca .here tci tca .here) (entry flag) rfl (by decide)
  rw [prefix_typed flag] at compiled
  rcases ReturnTailCompiler.normal_of_ok compiled with ⟨prefixState,prefixRun,stack,repr⟩
  have m0 : prefixState.mem 0 = w[1] := by
    cases flag <;> exact repr.vals (.there (.there (.there (.there .here))))
  have m1 : prefixState.mem 1 = .val (bword flag) := by
    cases flag <;> exact repr.vals (.there (.there (.there .here)))
  have m2 : prefixState.mem 2 = w[1] := by
    cases flag <;> exact repr.vals (.there (.there .here))
  have m4 : prefixState.mem 4 = w[1] := repr.vals .here
  have noCanary : codeStoresCell 5 (compileProg 0 (ConditionalAssignments.code (C := C) tci tca .here tci tca .here)) = false := by decide
  have m5 : prefixState.mem 5 = w[99] := exec_mem noCanary prefixRun
  exact ⟨prefixState,prefixRun,m0,m1,m2,m4,m5,stack⟩

theorem emitted_split : emitted =
    compileProg 0 (ConditionalAssignments.code (C := C) tci tca .here tci tca .here) ++
      [.push w[1],.mstore 3] := by rfl

/-- Only the two-instruction capture suffix; every input cell fact is supplied
by the independently proved actual prefix execution. -/
theorem capture_snapshot (before : Machine) (flag : Bool)
    (m0 : before.mem 0 = w[1]) (m1 : before.mem 1 = .val (bword flag))
    (m2 : before.mem 2 = w[1]) (m4 : before.mem 4 = w[1])
    (m5 : before.mem 5 = w[99]) (stack : before.stack = [w[77]]) :
    snapshot (run [.push w[1],.mstore 3] before) =
      some [w[1],.val (bword flag),w[1],w[1],w[1],w[99],w[77]] := by
  change some ([before.mem 0,before.mem 1,before.mem 2,w[1],before.mem 4,before.mem 5] ++ before.stack) = _
  rw [m0,m1,m2,m4,m5,stack]
  rfl

theorem observed (flag : Bool) : snapshot (run emitted (machine flag)) =
    some [w[1],.val (bword flag),w[1],w[1],w[1],w[99],w[77]] := by
  rcases prefix_observed flag with ⟨before,hr,m0,m1,m2,m4,m5,stack⟩
  have composed : run emitted (machine flag) = run [.push w[1],.mstore 3] before :=
    (congrArg (fun program : List Instr => run program (machine flag)) emitted_split).trans
      (run_append_ok hr)
  exact (congrArg snapshot composed).trans (capture_snapshot before flag m0 m1 m2 m4 m5 stack)

theorem wrong_donor_refused :
    snapshot (run (emit (C := C) 0 tci tca .here .here tca .here) (machine true)) ≠
      snapshot (run emitted (machine true)) := by
  have typed : (code (C := C) tci tca .here .here tca .here).run (caller true) =
      .ok ⟨reached (caller true) tci true .here .here tca .here,List.prefix_refl _⟩ :=
    ConditionalReturn.target_run (caller true) tci tca true .here .here tca .here rfl
  have compiled : StmtOut C 1 0 (Frag.init (.val .bool :: TargetCtx)) false false false
      ((code (C := C) tci tca .here .here tca .here).run (caller true))
      (run (emit (C := C) 0 tci tca .here .here tca .here) (machine true)) (machine true) :=
    prog_sim (code (C := C) tci tca .here .here tca .here) (entry true) rfl (by decide)
  rw [typed] at compiled
  rcases ReturnTailCompiler.normal_of_ok compiled with ⟨bad,hr,_,repr⟩
  intro same
  rw [hr,observed] at same
  have selected : some (bad.mem 2) = some w[1] := congrArg
    (fun out : Option (List Word) => match out with | some (_ :: _ :: x :: _) => some x | _ => none) same
  have one : bad.mem 2 = w[1] := Option.some.inj selected
  have zero : bad.mem 2 = w[0] := repr.vals (.there .here)
  exact (by decide : (w[0] : Word) ≠ w[1]) (zero.symm.trans one)

theorem wrong_flag_refused :
    snapshot (run (compileProg 0 ConditionalReturn.Controls.wrongFlag) (machine false)) ≠
      snapshot (run emitted (machine false)) := by
  have typed : ConditionalReturn.Controls.wrongFlag.run (caller false) =
      .ok ⟨(ConditionalAssignments.targetAfter (caller false) tci false .here tci tca .here).push
        (t := .val .bool) false,List.prefix_refl _⟩ := by
    have prefixRun : (ConditionalStatement.code (C := C) tci tca .here tci tca .here).run (caller false) =
        .ok ⟨ConditionalAssignments.targetAfter (caller false) tci false .here tci tca .here,List.prefix_refl _⟩ :=
      ConditionalStatement.target_run (caller false) tci tca false .here tci tca .here rfl
    unfold Prog.run at prefixRun
    rw [ConditionalReturn.Controls.wrongFlag,DeferredSource.join_run]
    unfold TRun.seq
    rw [prefixRun]
    rfl
  have compiled : StmtOut C 1 0 (Frag.init (.val .bool :: TargetCtx)) false false false
      (ConditionalReturn.Controls.wrongFlag.run (caller false))
      (run (compileProg 0 ConditionalReturn.Controls.wrongFlag) (machine false)) (machine false) :=
    prog_sim ConditionalReturn.Controls.wrongFlag (entry false) rfl (by decide)
  rw [typed] at compiled
  rcases ReturnTailCompiler.normal_of_ok compiled with ⟨bad,hr,_,repr⟩
  intro same
  rw [hr,observed] at same
  have selected : some (bad.mem 3) = some w[1] := congrArg
    (fun out : Option (List Word) => match out with | some (_ :: _ :: _ :: x :: _) => some x | _ => none) same
  have one : bad.mem 3 = w[1] := Option.some.inj selected
  have zero : bad.mem 3 = w[0] := repr.vals .here
  exact (by decide : (w[0] : Word) ≠ w[1]) (zero.symm.trans one)

end Solidity.Backend.StructuredFlow.ConditionalReturnCompiler.Controls
