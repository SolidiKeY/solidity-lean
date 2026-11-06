import Solidity.Backend.StructuredFlow.MappedBranch
import Solidity.Backend.StructuredFlow.MappedConditionControls

namespace Solidity.Backend.StructuredFlow.MappedBranch.Controls
open Solidity.Evm Solidity.Lowering.V07
open MappedCondition.Controls (C mapping caller loaded frame snapshot represented)

def left : Prog C [.val .bool,.val .bool,.val .bool] [.val .bool,.val .bool,.val .bool] :=
  .cons (.assignLocal (.there .here) (.simple (.bool false))) .nil

def right : Prog C [.val .bool,.val .bool,.val .bool] [.val .bool,.val .bool,.val .bool] :=
  .cons (.assignLocal (.there .here) (.simple (.bool true))) .nil

def core : Prog C [.val .bool,.val .bool] [.val .bool,.val .bool,.val .bool] :=
  program mapping .here (.there .here) rfl rfl left right

def emitted (base : Nat) : List Instr :=
  emit base mapping .here (.there .here) rfl rfl (compileProg base left) (compileProg base right)

def bad_emitted : List Instr :=
  Branch.emit (MappedCondition.Controls.wrongCapture ++ [.mload 2])
    (compileProg 0 left) (compileProg 0 right)

def exitObservation : Solidity.Evm.Out → Option (Nat × List Word)
  | .ok m skip => some (skip,[m.mem 0,m.mem 1,m.mem 2,m.mem 3] ++ m.stack)
  | _ => none

theorem condition_code (base : Nat) :
    condition base mapping .here (.there .here) rfl rfl =
      [.mload base,.mstore (base+1),.mload (base+1),.mstore (base+2),.mload (base+2)] := rfl

theorem arm_codes (base : Nat) :
    compileProg base left = [.push (.val (bword false)),.mstore (base+1)] ∧
    compileProg base right = [.push (.val (bword true)),.mstore (base+1)] := ⟨rfl,rfl⟩

theorem emitted_code (base : Nat) :
    emitted base = [.mload base,.mstore (base+1),.mload (base+1),.mstore (base+2),.mload (base+2),
      .iszero,.jumpi 3,.push (.val (bword false)),.mstore (base+1),.jump 2,
      .push (.val (bword true)),.mstore (base+1)] := by
  rw [emitted,emit,condition_code,(arm_codes base).1,(arm_codes base).2]
  rfl

theorem checked (flag : Bool) :
    StmtOut C 1 0 (Frag.init [.val .bool,.val .bool,.val .bool]) false false false
      (core.run (caller flag)) (run (emitted 0) (loaded flag)) (loaded flag) := by
  apply correct (F₁ := Frag.init [.val .bool,.val .bool,.val .bool])
    (F₂ := Frag.init [.val .bool,.val .bool,.val .bool])
    mapping .here (.there .here) rfl rfl left right (represented flag) rfl rfl
  change 1 ≤ Lmax
  exact (represented flag).bound

theorem typed_run (flag : Bool) :
    core.run (caller flag) = .ok ⟨(caller flag).push (t := .val .bool) flag,List.prefix_refl _⟩ := by
  cases flag <;> (change Prog.runR core (caller _) = _; rw [Prog.runR_eq]; rfl)

theorem frame_observation (flag : Bool) :
    snapshot 128 (run (emitted 128) (frame 128 flag)) =
      some [.val (bword flag),.val (bword (!flag)),.val (bword flag),w[99],w[77]] := by
  cases flag
  · have test : run (condition 128 mapping .here (.there .here) rfl rfl) (frame 128 false) =
        .ok ((MappedCondition.after 128 mapping .here (.there .here) rfl rfl (frame 128 false)).push
          (.val (bword false))) 0 := condition_run 128 mapping .here (.there .here) rfl rfl _
    have selected : run (emitted 128) (frame 128 false) =
        run (compileProg 128 right)
          (MappedCondition.after 128 mapping .here (.there .here) rfl rfl (frame 128 false)) :=
      Branch.false_run (left := compileProg 128 left) test
    rw [selected,(arm_codes 128).2]
    rfl
  · have test : run (condition 128 mapping .here (.there .here) rfl rfl) (frame 128 true) =
        .ok ((MappedCondition.after 128 mapping .here (.there .here) rfl rfl (frame 128 true)).push
          (.val (bword true))) 0 := condition_run 128 mapping .here (.there .here) rfl rfl _
    have body : run (compileProg 128 left)
        (MappedCondition.after 128 mapping .here (.there .here) rfl rfl (frame 128 true)) =
        .ok {MappedCondition.after 128 mapping .here (.there .here) rfl rfl (frame 128 true) with
          mem := upd (MappedCondition.after 128 mapping .here (.there .here) rfl rfl (frame 128 true)).mem
            129 (.val (bword false))} 0 := by
      rw [(arm_codes 128).1]
      rfl
    have selected : run (emitted 128) (frame 128 true) =
        .ok {MappedCondition.after 128 mapping .here (.there .here) rfl rfl (frame 128 true) with
          mem := upd (MappedCondition.after 128 mapping .here (.there .here) rfl rfl (frame 128 true)).mem
            129 (.val (bword false))} 0 := Branch.true_success test body
    rw [selected]
    rfl

theorem wrong_capture_refused :
    snapshot 0 (run bad_emitted (loaded true)) ≠ snapshot 0 (run (emitted 0) (loaded true)) := by
  let badPost : Machine := {loaded true with
    mem := upd (upd (loaded true).mem 1 (.val (bword true))) 2 (.val (bword false))}
  have badTest : run (MappedCondition.Controls.wrongCapture ++ [.mload 2]) (loaded true) =
      .ok (badPost.push (.val (bword false))) 0 := by rfl
  have bad : run bad_emitted (loaded true) = run (compileProg 0 right) badPost :=
    Branch.false_run (left := compileProg 0 left) badTest
  have goodTest : run (condition 0 mapping .here (.there .here) rfl rfl) (loaded true) =
      .ok ((MappedCondition.after 0 mapping .here (.there .here) rfl rfl (loaded true)).push
        (.val (bword true))) 0 := condition_represented mapping .here (.there .here) rfl rfl (represented true)
  have goodBody : run (compileProg 0 left)
      (MappedCondition.after 0 mapping .here (.there .here) rfl rfl (loaded true)) =
      .ok {MappedCondition.after 0 mapping .here (.there .here) rfl rfl (loaded true) with
        mem := upd (MappedCondition.after 0 mapping .here (.there .here) rfl rfl (loaded true)).mem
          1 (.val (bword false))} 0 := by
    rw [(arm_codes 0).1]
    rfl
  have good : run (emitted 0) (loaded true) =
      .ok {MappedCondition.after 0 mapping .here (.there .here) rfl rfl (loaded true) with
        mem := upd (MappedCondition.after 0 mapping .here (.there .here) rfl rfl (loaded true)).mem
          1 (.val (bword false))} 0 := Branch.true_success goodTest goodBody
  rw [bad,good,(arm_codes 0).2]
  decide

theorem pending_exit_exact :
    run (emit 0 mapping .here (.there .here) rfl rfl [.jump 4] [.push w[9],.mstore 3]) (loaded true) =
      .ok (MappedCondition.after 0 mapping .here (.there .here) rfl rfl (loaded true)) 1 := by
  have selected : run (emit 0 mapping .here (.there .here) rfl rfl
      [.jump 4] [.push w[9],.mstore 3]) (loaded true) =
      exec [.push w[9],.mstore 3] 3
        (MappedCondition.after 0 mapping .here (.there .here) rfl rfl (loaded true)) :=
    true_pending_skip (skip := 3) mapping .here (.there .here) rfl rfl (represented true) rfl
      [.jump 4] [.push w[9],.mstore 3] rfl
  exact selected

theorem short_exit_refused :
    exitObservation (run (emit 0 mapping .here (.there .here) rfl rfl
      [.jump 2] [.push w[9],.mstore 3]) (loaded true)) ≠
    exitObservation (run (emit 0 mapping .here (.there .here) rfl rfl
      [.jump 4] [.push w[9],.mstore 3]) (loaded true)) := by
  have short : run (emit 0 mapping .here (.there .here) rfl rfl
      [.jump 2] [.push w[9],.mstore 3]) (loaded true) =
      exec [.push w[9],.mstore 3] 1
        (MappedCondition.after 0 mapping .here (.there .here) rfl rfl (loaded true)) :=
    true_pending_skip (skip := 1) mapping .here (.there .here) rfl rfl (represented true) rfl
      [.jump 2] [.push w[9],.mstore 3] rfl
  rw [short,pending_exit_exact]
  decide

theorem unsupported_refused :
    inFragP (Frag.init [.val .bool,.val .bool])
      (program mapping .here (.there .here) rfl rfl
        (.cons .assumeFalse .nil : Prog C [.val .bool,.val .bool,.val .bool]
          [.val .bool,.val .bool,.val .bool]) right) = none := rfl

end Solidity.Backend.StructuredFlow.MappedBranch.Controls
