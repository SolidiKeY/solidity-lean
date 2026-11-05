import Solidity.Backend.StructuredFlow.MappedCondition

namespace Solidity.Backend.StructuredFlow.MappedCondition.Controls
open Solidity.Evm Solidity.Lowering.V07
open Solidity.Lowering.G19.AssignmentReturnFlag

def C : Contract := default

def mapping : ContextMap [.bool,.bool] [.val .bool,.val .bool] :=
  (ContextMap.empty.cons .bool (.val .bool)).cons .bool (.val .bool)

def initial : State C [] := freshT C 0 W_pos ⟨0,W_pos⟩
def machine : Machine := {Machine.init (fun _ => 0) ⟨0,W_pos⟩ with stack := [w[77]]}
def caller (flag : Bool) : State C [.val .bool,.val .bool] :=
  (initial.push (t := .val .bool) flag).push (t := .val .bool) (!flag)
def loaded (flag : Bool) : Machine :=
  let written := upd machine.mem 0 (.val (bword flag))
  {machine with mem := upd written 1 (.val (bword (!flag)))}

def snapshot (base : Nat) : Solidity.Evm.Out → Option (List Word)
  | .ok m skip => if skip = 0 then
      some ([m.mem base,m.mem (base+1),m.mem (base+2),m.mem (base+3)] ++ m.stack) else none
  | _ => none

def frame (base : Nat) (flag : Bool) : Machine :=
  let first := upd machine.mem base (.val (bword flag))
  let second := upd first (base+1) (.val (bword (!flag)))
  {machine with mem := upd second (base+3) w[99]}

def wrongCapture : List Instr := [.mload 1,.mload 0,.mstore 1,.mstore 2]

theorem represented (flag : Bool) :
    Sim C 1 0 (Frag.init [.val .bool,.val .bool]) (caller flag) (loaded flag) := by
  exact Sim.pushVal
    (Sim.pushVal ((Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl).stack [w[77]])
      (p := .bool) (v := flag) (w := .val (bword flag)) rfl)
    (p := .bool) (v := !flag) (w := .val (bword (!flag))) rfl

theorem checked (flag : Bool) :
    StmtOut C 1 0 (Frag.init [.val .bool,.val .bool,.val .bool]) false false false
      ((code mapping .here (.there .here) rfl rfl : Prog C _ _).run (caller flag))
      (run (emit 0 mapping .here (.there .here) rfl rfl) (loaded flag)) (loaded flag) :=
  correct mapping .here (.there .here) rfl rfl (represented flag)

theorem post_representation (flag : Bool) :
    Sim C 1 0 (Frag.init [.val .bool,.val .bool,.val .bool])
      (reached mapping .here (.there .here) rfl rfl (caller flag))
      (after 0 mapping .here (.there .here) rfl rfl (loaded flag)) :=
  postSim mapping .here (.there .here) rfl rfl (represented flag)

theorem nonzero_frame (flag : Bool) :
    snapshot 128 (run (emit 128 mapping .here (.there .here) rfl rfl) (frame 128 flag)) =
      some [.val (bword flag),.val (bword flag),.val (bword flag),w[99],w[77]] := by rfl

theorem self_alias (flag : Bool) :
    snapshot 0 (run (emit 0 mapping .here .here rfl rfl) (loaded flag)) =
      some [.val (bword flag),.val (bword (!flag)),.val (bword (!flag)),w[0],w[77]] := by rfl

theorem stale_capture_refused :
    snapshot 0 (run wrongCapture (loaded true)) ≠
      snapshot 0 (run (emit 0 mapping .here (.there .here) rfl rfl) (loaded true)) := by decide

theorem wrong_base_refused :
    snapshot 128 (run (emit 0 mapping .here (.there .here) rfl rfl) (frame 128 true)) ≠
      snapshot 128 (run (emit 128 mapping .here (.there .here) rfl rfl) (frame 128 true)) := by decide

end Solidity.Backend.StructuredFlow.MappedCondition.Controls
