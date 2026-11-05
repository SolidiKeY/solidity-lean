import Solidity.Assurance.NonVacuityH28.Locals

/-! Joint nonzero transaction fields and an actual compiled environment read. -/
namespace Solidity.Assurance.NonVacuityH28
open Solidity Semantics
variable (C : Contract)

def environmentSource : State C [] :=
  { Evm.freshT C 0 (by decide) ⟨7, by decide⟩ with
    tx := {
      msgSender := ⟨11, rfl⟩
      msgValue := ⟨22, rfl⟩
      timestamp := ⟨33, rfl⟩
      selfAddress := ⟨7, rfl⟩ } }

def environmentMachine : Evm.Machine :=
  { Evm.Machine.init (fun _ => 0) ⟨7, by decide⟩ with
    caller := ⟨11, by decide⟩, callvalue := ⟨22, by decide⟩, timestamp := ⟨33, by decide⟩ }

theorem environment_simulation :
    Evm.Sim C 1 0 (Evm.Frag.init []) (environmentSource C) environmentMachine := by
  have h : Evm.Sim C 1 0 (Evm.Frag.init [])
      (Evm.freshT C 0 (by decide) ⟨7, by decide⟩)
      (Evm.Machine.init (fun _ => 0) ⟨7, by decide⟩) :=
    Evm.Sim.init C 0 (by decide) (fun _ => 0) ⟨7, by decide⟩ rfl
  exact ⟨h.store, h.vals, h.aliases, h.net, h.netSelf, h.bound, h.fragile,
    ⟨rfl, rfl, rfl, rfl⟩, h.funds, h.oracle⟩

theorem mismatched_timestamp :
    ¬ Evm.Sim C 1 0 (Evm.Frag.init []) (environmentSource C)
      { environmentMachine with timestamp := ⟨34, by decide⟩ } := by
  intro h
  have heq : (33 : Int) = 34 := h.env.2.2.1
  omega

def senderProgram : Prog C [] [.val .uint] :=
  .cons (.declLocal .uint (.user "sender") (some (.simple (.env .msgSender rfl)))) .nil

def senderSource : State C [.val .uint] :=
  (environmentSource C).push (⟨11, rfl⟩ : PrimTy.uint.Denote)
def senderMachine : Evm.Machine :=
  { environmentMachine with
    mem := Evm.upd environmentMachine.mem 0 (.val ⟨11, by decide⟩) }

theorem sender_source : Prog.run (environmentSource C) (senderProgram C) =
    .ok ⟨senderSource C, List.prefix_refl _⟩ := rfl

theorem sender_target : Evm.run (Evm.compileProg 0 (senderProgram C)) environmentMachine =
    .ok senderMachine 0 := rfl

theorem sender_fragment : Evm.inFragP (Evm.Frag.init []) (senderProgram C) =
    some (Evm.Frag.init [.val .uint]) := rfl

theorem sender_representation :
    Evm.Sim C 1 0 (Evm.Frag.init [.val .uint]) (senderSource C) senderMachine :=
  represented_success (sender_fragment C) (environment_simulation C)
    (by change 1 ≤ Evm.Lmax; decide) (sender_source C) (sender_target C)

end Solidity.Assurance.NonVacuityH28
