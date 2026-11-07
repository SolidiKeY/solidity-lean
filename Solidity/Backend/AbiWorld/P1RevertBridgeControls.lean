import Solidity.Backend.AbiWorld.P1RevertBridge
import Solidity.Evm.Correct

/-! Controls for `P1RevertBridge`. One statement, `require(total != 0)`,
compiled by the public compiler from a fresh frame. An admitted input from the
published fresh contract (`Sim.init`) reverts on both sides (a reverting admitted input, not an
`InterfaceV2.RevertingEntry`), with the target revert derived from the
bridge's `Local` and cross-checked by an independent kernel run. `require(total == 0)` succeeds on both sides at
the same input. `assert(false)` shows why the context excludes `assert`: the
source observes `revert(Panic(0x01))`, the compiled core code reverts without
data. -/
namespace Solidity.Backend.AbiWorld.P1RevertBridgeControls
open Solidity.Evm Solidity.Backend.AbiWorld.PublicCompilerTotal
open Solidity.Backend.AbiWorld.P1RevertBridge
open Solidity.Backend.InternalFlow.RuntimeFrame.P1LangV2
open Solidity.Roadmap (Outcome Prefix)

def C : Contract := { vars := [("total", .prim .uint)] }

abbrev Γ₀ : Ctx := []

def total : Solidity.Val C Γ₀ .uint := .read (.root "total" rfl)

def zero : Solidity.Val C Γ₀ .uint := .simple (.lit 0 (by decide))

/-- `require(total != 0);` -/
def guardNe : Solidity.Stmt C Γ₀ Γ₀ := .require (.binop .neB rfl rfl total zero)

/-- `require(total == 0);` -/
def guardEq : Solidity.Stmt C Γ₀ Γ₀ := .require (.binop .eqB rfl rfl total zero)

theorem guardNe_ok : StmtOk [] guardNe [] := .require (.binop _ _ _ (.read (.root _ _)) (.lit _ _))
theorem guardEq_ok : StmtOk [] guardEq [] := .require (.binop _ _ _ (.read (.root _ _)) (.lit _ _))

/-- The fresh contract as a version-2 P1 input. -/
def fresh : Input C Γ₀ :=
  ⟨1, 0, freshT C 0 W_pos ⟨0, W_pos⟩, fun _ => ⟨0, W_pos⟩,
    MachineV2.ofBase (Machine.init (fun _ => 0) ⟨0, W_pos⟩), 0⟩

theorem fresh_admitted : admitted 0 (Frag.init Γ₀) fresh :=
  ⟨Sim.init C 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl, by unfold Lmax; decide⟩

/-- The bridge for `require(total != 0)`. -/
noncomputable def bridgeNe :=
  p1_revert_bridge (C := C) 0 (Matches.init Γ₀) guardNe_ok rfl

theorem guardNe_source_halt : (guardNe.run fresh.caller).halt? = some .revert := by
  decide +kernel

/-- The source reverts (bare) at the admitted fresh input. -/
theorem guardNe_reverts : guardNe.run fresh.caller = .error .revert := by
  have h := guardNe_source_halt
  revert h
  cases guardNe.run fresh.caller with
  | ok _ => intro h; cases h
  | error e => intro h; cases h; rfl

/-- **Reverting entry**: the compiled code reverts there with empty data and
the caller's journal, by the bridge's own `Local`. -/
theorem guardNe_target_reverts :
    runV2 (lift (code 0 (Frag.init Γ₀) guardNe)) fresh.machine = .revert fresh.machine.calls [] :=
  (bridgeNe.local fresh fresh_admitted).1 guardNe_reverts

theorem guardEq_source_halt : (guardEq.run fresh.caller).halt? = none := by
  decide +kernel

/-- The opposite guard succeeds on both sides at the same input. -/
theorem guardEq_target_success :
    targetSem (lift (code 0 (Frag.init Γ₀) guardEq)) fresh = ⟨[], some (.success [])⟩ := by
  rw [agree (Matches.init Γ₀) guardEq_ok rfl fresh fresh_admitted]
  have h := guardEq_source_halt
  revert h
  cases guardEq.run fresh.caller with
  | ok _ => intro _; rfl
  | error e => intro h; cases h

/-- Independent kernel runs of the frozen compiled code at the same machine. -/
theorem guardNe_run_revert :
    (match run (code 0 (Frag.init Γ₀) guardNe) fresh.machine.base with
      | .revert => true | _ => false) = true := by
  decide +kernel

theorem guardEq_run_ok :
    (match run (code 0 (Frag.init Γ₀) guardEq) fresh.machine.base with
      | .ok _ 0 => true | _ => false) = true := by
  decide +kernel

/-! ## Why `assert` is excluded -/

/-- `assert(false);` -/
def assertFalse : Solidity.Stmt C Γ₀ Γ₀ := .assert (.simple (.bool false))

theorem assertFalse_ok : StmtOk [] assertFalse [] := .assert (.bool _)

/-- The source observes `revert(Panic(0x01))`. -/
theorem assertFalse_source :
    sourcePrefix (assertFalse.run fresh.caller) =
      ⟨[], some (.revert (Semantics.encodePanic 1))⟩ := rfl

/-- The compiled core code reverts without data. -/
theorem assertFalse_target_bare :
    (match run (code 0 (Frag.init Γ₀) assertFalse) fresh.machine.base with
      | .revert => true | _ => false) = true := by
  decide +kernel

/-- info: 'Solidity.Backend.AbiWorld.P1RevertBridge.p1_revert_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms p1_revert_bridge

/-- info: 'Solidity.Backend.AbiWorld.P1RevertBridgeControls.guardNe_target_reverts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms guardNe_target_reverts

end Solidity.Backend.AbiWorld.P1RevertBridgeControls
