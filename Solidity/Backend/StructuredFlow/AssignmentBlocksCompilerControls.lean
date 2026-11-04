import Solidity.Backend.StructuredFlow.AssignmentBlocksCompiler
import Solidity.Backend.StructuredFlow.ReturnTailCompilerControls

namespace Solidity.Backend.StructuredFlow.AssignmentBlocksCompiler.Controls
open Solidity.Evm Solidity.Lowering.V07 Solidity.Lowering.G19
open Source.SemanticsExamples (G0 F0)
open MappedCondition.Controls (C)
open ConditionalSourceCompiler.Controls (SourceCtx TargetCtx mapping Rel)
open ReturnTailCompiler.Controls (source caller machine initial entry)
open AssignmentBlocks (statement code sourceAfter targetAfter)

def index : Source.Idx SourceCtx .bool → Idx TargetCtx (.val .bool)
  | .here => .here
  | .there .here => .there .here
  | .there (.there .here) => .there (.there .here)

theorem maps : ∀ i, mapping.slot i = ⟨.val .bool,index i⟩ := by
  intro i
  cases i with
  | here => rfl
  | there i => cases i with
    | here => rfl
    | there i => cases i with
      | here => rfl
      | there i => nomatch i

def steps : List (Source.Idx SourceCtx .bool × Source.Idx SourceCtx .bool) :=
  [(.here,.there (.there .here)),(.there (.there .here),.here)]
def emitted : List Instr := emit (C := C) 0 index steps
def snapshot (out : Evm.Out) : Option (List Word) :=
  match out with
  | .ok post 0 => some ([post.mem 0,post.mem 1,post.mem 2,post.mem 3,post.mem 4,post.mem 5] ++ post.stack)
  | _ => none

theorem joined (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag checked : Bool) :
    (Source.execS (G0 pipeline) {F0 with checked := checked} (fuel+steps.length+4) 0 none
      (R := []) (M := false) (k := ⟨false,false⟩) (statement steps) (source flag).1).run (.nil,(source flag).2) =
      (.ok (Source.Out.normal (sourceAfter steps (source flag).1)),(.nil,(source flag).2)) ∧
    StmtOut C 1 0 (Frag.init TargetCtx) false false false
      ((code index steps).run (caller flag)) (run emitted (machine flag)) (machine flag) := by
  rcases correct (G0 pipeline) {F0 with checked := checked} fuel 0 none (returns := []) (M := false)
    (k := ⟨false,false⟩) steps (source flag) (caller flag) mapping Rel index maps (initial flag)
    (entry flag) rfl (by decide) with ⟨src,_,_,_,compiled⟩
  exact ⟨src,compiled⟩

theorem observed (flag : Bool) : snapshot (run emitted (machine flag)) =
    some [.val (bword flag),.val (bword (!flag)),.val (bword flag),w[0],w[0],w[99],w[77]] := by
  cases flag <;> rfl

theorem emitted_code : emitted = [.mload 0,.mstore 2,.mload 2,.mstore 0] := by rfl

theorem emitted_run (before : Machine) : run emitted before =
    .ok {before with mem := upd (upd before.mem 2 (before.mem 0)) 0 (before.mem 0)} 0 := by
  rw [emitted_code]
  rfl

theorem repeated_code : emit (C := C) 0 index (steps ++ steps) = emitted ++ emitted := by rfl

theorem repeated_observed (flag : Bool) :
    snapshot (run (emit (C := C) 0 index (steps ++ steps)) (machine flag)) =
      some [.val (bword flag),.val (bword (!flag)),.val (bword flag),w[0],w[0],w[99],w[77]] := by
  rw [repeated_code,run_append_ok (emitted_run (machine flag)),emitted_run]
  cases flag <;> rfl

theorem reversed_observed (flag : Bool) :
    snapshot (run (emit (C := C) 0 index steps.reverse) (machine flag)) =
      some [.val (bword (!flag)),.val (bword (!flag)),.val (bword (!flag)),w[0],w[0],w[99],w[77]] := by
  cases flag <;> rfl

theorem reverse_refused (flag : Bool) :
    snapshot (run (emit (C := C) 0 index steps.reverse) (machine flag)) ≠ snapshot (run emitted (machine flag)) := by
  rw [reversed_observed,observed]
  cases flag <;> decide

theorem self_alias_observed (flag : Bool) :
    snapshot (run (emit (C := C) 0 index [(.here,.here)]) (machine flag)) =
      some [.val (bword flag),.val (bword (!flag)),.val (bword (!flag)),w[0],w[0],w[99],w[77]] := by
  cases flag <;> rfl

end Solidity.Backend.StructuredFlow.AssignmentBlocksCompiler.Controls
