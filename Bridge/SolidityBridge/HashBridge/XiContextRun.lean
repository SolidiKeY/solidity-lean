import SolidityBridge.HashBridge.XiContextSetup

/-! Actual public Xi success for arbitrary invocation world/context with the
fixed one-query code and gas34. Extra fuel is quantified, not a raised check
budget. No successful state/reply, account layout or source judgment is input. -/
namespace Solidity.HashBridge.XiContext
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof Solidity.Evm.External

def query (i : Inputs) : List Nat :=
  byteQuery (machineQuery (ready i).toMachineState (.ofNat 0) (.ofNat 0))

theorem completed_driver (fuel : Nat) (dest : Array UInt256) (i : Inputs)
    (code : i.environment.code = program) :
    ∃ next, CheckedHashEdge (fuel+1) dest (ready i) (.ofNat 0) (.ofNat 0) [] next ∧
      DriverQueryReceipt (fuel+5) dest (initial i) [query i]
        (.ok (.success (Assembly.stopAfter next 0) .empty)) ∧
      next.gasAvailable = .ofNat 0 ∧ next.pc = .ofNat 3 ∧
      next.toState = (initial i).toState ∧ next.execLength = 3 := by
  obtain ⟨next,edge⟩ := checked_hash_edge (fuel+1) dest (ready i) (.ofNat 0) (.ofNat 0) []
    (fetches i code).2.2 rfl (hash_ready i)
  have context : next.executionEnv = i.environment :=
    congrArg (fun s : EvmYul.State .EVM => s.executionEnv) edge.world
  have pc : next.pc = .ofNat 3 := edge.pc
  have hf : fetched next = (.STOP,none) := by
    unfold fetched
    rw [context,pc,code]
    rfl
  have room : next.stack.length ≤ 1024 := by rw [edge.stack]; change 1 ≤ 1024; decide
  have stop : DriverQueryReceipt (fuel+2) dest next [] (.ok (.success (Assembly.stopAfter next 0) .empty)) :=
    (stop_query_success fuel dest next hf room).1
  have hash : DriverQueryReceipt (fuel+3) dest (ready i) [query i]
      (.ok (.success (Assembly.stopAfter next 0) .empty)) := by
    have joined : DriverQueryReceipt (fuel+3) dest (ready i)
        (directQueries (fetched (ready i)).1 (hashMemoryCharged (ready i)) ++ [])
        (.ok (.success (Assembly.stopAfter next 0) .empty)) :=
      query_receipt_prepend (fuel+1) (hashOpcodeCost (ready i)) dest (ready i)
        (hashMemoryCharged (ready i)) next [] _ edge.checked
        (by simpa only [(fetches i code).2.2] using edge.evaluated)
        (by rw [(fetches i code).2.2]; rfl) stop
    have direct : directQueries (fetched (ready i)).1 (hashMemoryCharged (ready i)) = [query i] := by
      rw [(fetches i code).2.2]
      rfl
    simpa only [direct,List.append_nil] using joined
  have second : DriverQueryReceipt (fuel+4) dest (pushed i) [query i]
      (.ok (.success (Assembly.stopAfter next 0) .empty)) := by
    have joined : DriverQueryReceipt (fuel+4) dest (pushed i)
        (directQueries (fetched (pushed i)).1 (pushed i) ++ [query i])
        (.ok (.success (Assembly.stopAfter next 0) .empty)) :=
      query_receipt_prepend (fuel+2) 2 dest _ _ _ [query i] _ (push_checks dest i code).2
        (push_steps (fuel+2) i code).2 (by rw [(fetches i code).2.1]; rfl) hash
    simpa only [(fetches i code).2.1,directQueries,Bool.false_eq_true,if_false,List.nil_append] using joined
  have full : DriverQueryReceipt (fuel+5) dest (initial i) [query i]
      (.ok (.success (Assembly.stopAfter next 0) .empty)) := by
    have joined : DriverQueryReceipt (fuel+5) dest (initial i)
        (directQueries (fetched (initial i)).1 (initial i) ++ [query i])
        (.ok (.success (Assembly.stopAfter next 0) .empty)) :=
      query_receipt_prepend (fuel+3) 2 dest _ _ _ [query i] _ (push_checks dest i code).1
        (push_steps (fuel+3) i code).1 (by rw [(fetches i code).1]; rfl) second
    simpa only [(fetches i code).1,directQueries,Bool.false_eq_true,if_false,List.nil_append] using joined
  have gas : next.gasAvailable = .ofNat 0 := by
    rw [edge.gas]
    obtain ⟨hm,hc⟩ := PairControls.zero_size_costs (ready i) (.ofNat 0) rfl rfl
    simp only [hashMemoryCharged,hm,hc]
    change (UInt256.ofNat 30 - UInt256.ofNat 0) - UInt256.ofNat 30 = UInt256.ofNat 0
    decide
  exact ⟨next,edge,full,gas,pc,edge.world,edge.execLength⟩

/-- All public world/context arguments are used in the real constructor.
Only code identity is required; calldata, owner/source/value/depth, permission,
header/blobs, accounts, created set, substate and snapshot are arbitrary. -/
theorem completed_invocation (fuel : Nat) (i : Inputs) (code : i.environment.code = program) :
    XiQueryReceipt (fuel+6) i.created i.genesis i.blocks i.world i.snapshot (.ofNat 34)
      i.accrued i.environment [query i] (.ok (.success (i.created,i.world,.ofNat 0,i.accrued) .empty)) ∧
      Ξ (fuel+6) i.created i.genesis i.blocks i.world i.snapshot (.ofNat 34) i.accrued i.environment =
      .ok (.success (i.created,i.world,.ofNat 0,i.accrued) .empty) := by
  obtain ⟨next,edge,receipt,gas,pc,world,exec⟩ :=
    completed_driver fuel (D_J i.environment.code (.ofNat 0)) i code
  have invoked : XiQueryReceipt (fuel+6) i.created i.genesis i.blocks i.world i.snapshot (.ofNat 34)
      i.accrued i.environment [query i] (.ok (.success (i.created,i.world,.ofNat 0,i.accrued) .empty)) := by
    refine ⟨.ok (.success (Assembly.stopAfter next 0) .empty),receipt,?_⟩
    have created : next.createdAccounts = (initial i).createdAccounts :=
      congrArg (fun s : EvmYul.State .EVM => s.createdAccounts) world
    have accounts : next.accountMap = (initial i).accountMap :=
      congrArg (fun s : EvmYul.State .EVM => s.accountMap) world
    have accrued : next.substate = (initial i).substate :=
      congrArg (fun s : EvmYul.State .EVM => s.substate) world
    simp only [Bind.bind,Except.bind,Assembly.stopAfter,Assembly.chargedPrepare,
      gas,word_sub_zero,created,accounts,accrued,initial]
  exact ⟨invoked,invoked.sound⟩
end Solidity.HashBridge.XiContext
