import Solidity.Assurance.NonVacuityH28.Locals

/-! Explicit states rejected by alias/fragment and memory-pointer premises. -/
namespace Solidity.Assurance.NonVacuityH28
open Solidity Semantics

def unsetAliasSource : State aliasContract [.alias (.array (.prim .uint))] :=
  (localSource aliasContract).push (none : Option (SRef aliasContract (.ref (.array (.prim .uint)))))
def deadAliasLayout : Evm.Frag [.alias (.array (.prim .uint))] := ⟨[.dead]⟩

theorem unset_alias_not_ok (L b : Nat) (mc : Evm.Machine) :
    ¬ Evm.Sim aliasContract L b (Evm.Frag.init [.alias (.array (.prim .uint))]) unsetAliasSource mc := by
  intro h
  obtain ⟨r, _, heq, _⟩ := h.aliases .here rfl
  change (none : Option (SRef aliasContract (.ref (.array (.prim .uint))))) = some r at heq
  cases heq

theorem dead_alias_simulation :
    Evm.Sim aliasContract 1 0 deadAliasLayout unsetAliasSource localMachine := by
  have h : Evm.Sim aliasContract 1 0 (Evm.Frag.init []) (localSource aliasContract) localMachine :=
    closed_simulation aliasContract
  refine ⟨h.store, (fun i => nomatch i), ?_, h.net, h.netSelf, h.bound, ?_, h.env, h.funds, h.oracle⟩
  · intro R i hi
    cases i with
    | here => cases hi
    | there i => nomatch i
  · intro R i hi
    cases i with
    | here => cases hi
    | there i => nomatch i

def deadAliasRead : Prog aliasContract [.alias (.array (.prim .uint))]
    [.val .uint, .alias (.array (.prim .uint))] :=
  .cons (.declLocal .uint (.user "n") (some (.len (.alias .here) rfl))) .nil

theorem dead_alias_fragment_rejected : Evm.inFragP deadAliasLayout deadAliasRead = none := rfl

theorem dead_alias_source_reverts : Prog.run unsetAliasSource deadAliasRead = .error .revert := rfl

theorem dead_alias_target_faults : Evm.run (Evm.compileProg 0 deadAliasRead) localMachine = .fault := rfl

variable (C : Contract)

def unsetMemorySource (R : RefTy) : State C [.mem R] :=
  (localSource C).push (none : Option (HRef [] R))

theorem unset_memory_core_simulation (R : RefTy) :
    Evm.Sim C 1 0 (Evm.Frag.init [.mem R]) (unsetMemorySource C R) localMachine := by
  have h : Evm.Sim C 1 0 (Evm.Frag.init []) (localSource C) localMachine := closed_simulation C
  exact ⟨h.store, (fun i => nomatch i), (fun i => nomatch i), h.net, h.netSelf, h.bound,
    (fun i => nomatch i), h.env, h.funds, h.oracle⟩

/-- Core Sim is inhabited, but does not supply a live memory pointer. -/
theorem unset_memory_pointer_rejected (R : RefTy) (L b frame : Nat)
    (F : Evm.Frag [.mem R]) (base : Nat → Fin Evm.W) (mc : Evm.Machine) :
    ¬ Evm.Memory.StateRepr L b frame F (unsetMemorySource C R) base mc := by
  intro h
  obtain ⟨r, heq, _⟩ := h.pointers (.here : Idx [.mem R] (.mem R))
  change (none : Option (HRef [] R)) = some r at heq
  cases heq

end Solidity.Assurance.NonVacuityH28
