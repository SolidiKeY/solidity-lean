import Solidity.Backend.StructuredFlow.ConditionalContinuationCompiler
import Solidity.Lowering.G19.ConditionalReturnContinuationControls
import Solidity.Backend.StructuredFlow.ConditionalReturnCompilerControls

namespace Solidity.Backend.StructuredFlow.ConditionalContinuationCompiler.Controls
open Solidity.Evm Solidity.Lowering.V07 Solidity.Lowering.G19
open Source.SemanticsExamples (G0 F0)
open MappedCondition.Controls (C)
open ConditionalSourceCompiler.Controls (TargetCtx mapping Rel sci sca tci tca)
open ReturnTailCompiler.Controls (source caller machine initial entry)
open ConditionalReturnContinuation (statement code suffix)
open ConditionalReturnContinuation.Controls (sourceTail targetTail eager)
open ConditionalReturnCompiler.Controls (snapshot prefix_observed)

def core : Prog C TargetCtx (.val .bool :: TargetCtx) := code tci tca .here tci tca .here targetTail
def emitted : List Instr := emit (C := C) 0 tci tca .here tci tca .here targetTail
def eagerEmitted : List Instr := compileProg 0 eager

theorem joined (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag checked : Bool) :
    (Source.execS (G0 pipeline) {F0 with checked := checked} (fuel+8) 0 none (M := false)
      (statement (k := ⟨false,false⟩) sci sca .here sci sca .here sourceTail) (source flag).1).run
      (.nil,(source flag).2) =
      (.ok (Source.Out.ret (ConditionalAssignments.sourceAfter (source flag) sci flag .here sci sca .here).1),
        (.nil,(source flag).2)) ∧
    StmtOut C 1 0 (Frag.init (.val .bool :: TargetCtx)) false false false
      (core.run (caller flag)) (run emitted (machine flag)) (machine flag) := by
  rcases correct (G0 pipeline) {F0 with checked := checked} fuel 0 none
    (M := false) (k := ⟨false,false⟩) (source flag) (caller flag) mapping Rel
    (initial flag) (fun _ _ h => h) sci sca .here sci sca .here
    tci tca .here tci tca .here rfl rfl rfl rfl rfl rfl sourceTail targetTail (entry flag) rfl (by decide) with
    ⟨src,_,_,_,_,compiled⟩
  exact ⟨src,compiled⟩

theorem emitted_split : emitted =
    compileProg 0 (ConditionalAssignments.code (C := C) tci tca .here tci tca .here) ++
      ([.push w[1],.mstore 3] ++ compileProg 0 (suffix targetTail)) := by rfl

theorem capture_guard_snapshot (before : Machine) (flag : Bool)
    (m0 : before.mem 0 = w[1]) (m1 : before.mem 1 = .val (bword flag))
    (m2 : before.mem 2 = w[1]) (m4 : before.mem 4 = w[1])
    (m5 : before.mem 5 = w[99]) (stack : before.stack = [w[77]]) :
    snapshot (run ([.push w[1],.mstore 3] ++ compileProg 0 (suffix targetTail)) before) =
      some [w[1],.val (bword flag),w[1],w[1],w[1],w[99],w[77]] := by
  change some ([before.mem 0,before.mem 1,before.mem 2,w[1],before.mem 4,before.mem 5] ++ before.stack) = _
  rw [m0,m1,m2,m4,m5,stack]
  rfl

theorem observed (flag : Bool) : snapshot (run emitted (machine flag)) =
    some [w[1],.val (bword flag),w[1],w[1],w[1],w[99],w[77]] := by
  rcases prefix_observed flag with ⟨before,hr,m0,m1,m2,m4,m5,stack⟩
  have composed : run emitted (machine flag) =
      run ([.push w[1],.mstore 3] ++ compileProg 0 (suffix targetTail)) before :=
    (congrArg (fun program : List Instr => run program (machine flag)) emitted_split).trans (run_append_ok hr)
  exact (congrArg snapshot composed).trans (capture_guard_snapshot before flag m0 m1 m2 m4 m5 stack)

theorem eager_split : eagerEmitted =
    compileProg 0 (ConditionalAssignments.code (C := C) tci tca .here tci tca .here) ++
      [.push w[1],.mstore 3,.push w[0],.mstore 2] := by rfl

theorem capture_eager_snapshot (before : Machine) (flag : Bool)
    (m0 : before.mem 0 = w[1]) (m1 : before.mem 1 = .val (bword flag))
    (m4 : before.mem 4 = w[1]) (m5 : before.mem 5 = w[99]) (stack : before.stack = [w[77]]) :
    snapshot (run [.push w[1],.mstore 3,.push w[0],.mstore 2] before) =
      some [w[1],.val (bword flag),w[0],w[1],w[1],w[99],w[77]] := by
  change some ([before.mem 0,before.mem 1,w[0],w[1],before.mem 4,before.mem 5] ++ before.stack) = _
  rw [m0,m1,m4,m5,stack]
  rfl

theorem eager_observed (flag : Bool) : snapshot (run eagerEmitted (machine flag)) =
    some [w[1],.val (bword flag),w[0],w[1],w[1],w[99],w[77]] := by
  rcases prefix_observed flag with ⟨before,hr,m0,m1,_,m4,m5,stack⟩
  have composed : run eagerEmitted (machine flag) = run [.push w[1],.mstore 3,.push w[0],.mstore 2] before :=
    (congrArg (fun program : List Instr => run program (machine flag)) eager_split).trans (run_append_ok hr)
  exact (congrArg snapshot composed).trans (capture_eager_snapshot before flag m0 m1 m4 m5 stack)

theorem eager_refused (flag : Bool) :
    snapshot (run eagerEmitted (machine flag)) ≠ snapshot (run emitted (machine flag)) := by
  rw [eager_observed,observed]
  cases flag <;> decide

end Solidity.Backend.StructuredFlow.ConditionalContinuationCompiler.Controls
