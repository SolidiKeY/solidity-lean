import Solidity.Backend.StructuredFlow.BranchSelector

/-! Inhabited exact-machine selector controls. These are target semantics,
not an unproved source/compiler agreement or a physical-memory ownership proof. -/
namespace Solidity.Backend.StructuredFlow.BranchControls
open Solidity.Evm

def initial : Machine :=
  { Machine.init with stack := [w[77]], mem := fun a =>
      if a = 0 then w[132] else if a = 1 ∨ a = 2 then w[128]
      else if a = 128 then w[2] else if a = 129 then w[4]
      else if a = 9 then w[99] else w[0] }

def condition (value : Bool) : List Instr := [.push (.val (bword value))]
def write (value : Fin W) : List Instr := [.push (.val value), .mstore 5]
def stored (value : Fin W) : Machine :=
  {initial with mem := upd initial.mem 5 (.val value)}

theorem true_writes (value : Fin W) :
    run (Branch.emit (condition true) (write value) [.revert]) initial =
      .ok (stored value) 0 :=
  Branch.true_success rfl rfl

theorem false_writes (value : Fin W) :
    run (Branch.emit (condition false) [.revert] (write value)) initial =
      .ok (stored value) 0 := by
  rw [Branch.false_run (post := initial) rfl]
  rfl

/-- Fixed memory cells of a hand-built machine (no `StateRepr`) all
survive the selected body's one real local write. -/
theorem frame_fields (value : Fin W) :
    (stored value).stack = [w[77]] ∧ (stored value).mem 0 = w[132] ∧
    (stored value).mem 1 = w[128] ∧ (stored value).mem 2 = w[128] ∧
    (stored value).mem 9 = w[99] ∧ (stored value).mem 129 = w[4] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem selected_revert :
    run (Branch.emit (condition true) [.revert] (write ⟨7, by decide⟩)) initial = .revert :=
  Branch.true_revert (post := initial) rfl rfl

theorem selected_fault :
    run (Branch.emit (condition false) (write ⟨7, by decide⟩) [.pop, .pop]) initial = .fault := by
  rw [Branch.false_run (post := initial) rfl]
  rfl

/-- Condition effects belong to the actual post-condition machine, not an
invented unchanged initial state. -/
theorem condition_effect :
    run (Branch.emit [.push w[11], .mstore 6, .push w[1]]
      (write ⟨3, by decide⟩) [.revert]) initial =
      .ok {initial with mem := upd (upd initial.mem 6 w[11]) 5 w[3]} 0 :=
  Branch.true_success (post := {initial with mem := upd initial.mem 6 w[11]}) rfl rfl

/-- Dropping a pending body skip would incorrectly hide the reached else. -/
theorem pending_skip_reaches_else :
    run (Branch.emit (condition true) [.jump 1] (write ⟨3, by decide⟩)) initial =
      .ok (stored ⟨3, by decide⟩) 0 := by
  rw [Branch.true_pending_skip (post := initial) (skip := 0) rfl rfl]
  rfl

theorem pending_skip_is_not_return :
    run (Branch.emit (condition true) [.jump 1] [.revert]) initial ≠ .ok initial 0 := by
  rw [Branch.true_pending_skip (post := initial) (skip := 0) rfl rfl]
  intro impossible
  cases impossible

/-- An actual fault while computing the guard executes neither arm. -/
theorem condition_failure :
    run (Branch.emit [.pop, .pop] (write ⟨3, by decide⟩) (write ⟨7, by decide⟩)) initial = .fault :=
  Branch.condition_fault rfl

private def observation : Out → String
  | .ok machine skip =>
      let saved := match machine.stack with | [word] => toString word | _ => "bad-stack"
      toString skip ++ ":" ++ saved ++ ":" ++ toString (machine.mem 5) ++
        ":" ++ toString (machine.mem 9) ++ ":" ++ toString (machine.mem 1) ++ ":" ++ toString (machine.mem 2)
  | .revert => "revert"
  | .fault => "fault"

/-- info: ["0:77:3:99:128:128", "0:77:7:99:128:128"] -/
#guard_msgs in
#eval [true, false].map fun choose => observation
  (run (Branch.emit (condition choose) (write ⟨3, by decide⟩) (write ⟨7, by decide⟩)) initial)

/-- info: "revert" -/
#guard_msgs in
#eval observation (run (Branch.emit (condition true) [.jump 1] [.revert]) initial)

end Solidity.Backend.StructuredFlow.BranchControls
