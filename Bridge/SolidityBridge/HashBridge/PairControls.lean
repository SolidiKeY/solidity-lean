import SolidityBridge.HashBridge.TwoHashCuts
import SolidityBridge.HashBridge.ChargedControls
/-! Constructed kernel control: two actual charged hash instructions followed
by the real remaining-fuel error. Digest and padding bytes stay symbolic.
This is not a native test or an original Solidity-source execution witness. -/
namespace Solidity.HashBridge.PairControls
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof
def input : EVM.State :=
  { ChargedControls.input 64 [.ofNat 0,.ofNat 0,.ofNat 0] with
    executionEnv := {(ChargedControls.input 64 []).executionEnv with code := ⟨#[0x20,0x20]⟩} }
theorem zero_size_costs (s : EVM.State) (offset : UInt256)
    (hs : s.stack = [offset,.ofNat 0]) (ha : s.activeWords = .ofNat 0) :
    memoryExpansionCost s .KECCAK256 = 0 ∧ hashOpcodeCost s = 30 := by
  have hm : memoryExpansionCost s .KECCAK256 = 0 := by
    change Cₘ (.ofNat (MachineState.M s.activeWords.toNat s.stack[0]!.toNat
      s.stack[1]!.toNat)) - Cₘ s.activeWords = 0
    rw [hs,ha]
    simp only [List.getElem!_cons_succ,List.getElem!_cons_zero]
    have hz : (UInt256.ofNat 0).toNat = 0 := rfl
    rw [hz]
    simp only [MachineState.M,Nat.sub_self]
  have hc : hashOpcodeCost s = 30 := by
    rw [hash_opcode_cost,hs]
    simp only [List.getElem!_cons_succ,List.getElem!_cons_zero]
    rfl
  exact ⟨hm,hc⟩

theorem zero_size_guard (s : EVM.State) (offset : UInt256)
    (hs : s.stack = [offset,.ofNat 0]) (ha : s.activeWords = .ofNat 0)
    (hg : s.gasAvailable = .ofNat 34) : hashGuard s = .ok () := by
  obtain ⟨hm,hc⟩ := zero_size_costs s offset hs ha
  unfold hashGuard
  rw [hm,hc]
  simp only [hashMemoryCharged,hm,hg,hs]
  rfl

theorem actual_pair (dest : Array UInt256) :
    ∃ middle last,
      CheckedHashEdge 1 dest input (.ofNat 0) (.ofNat 0) [.ofNat 0] middle ∧
      CheckedHashEdge 0 dest middle
        (actualDigest (machineQuery input.toMachineState (.ofNat 0) (.ofNat 0)))
        (.ofNat 0) [] last ∧
      fetched middle = (.KECCAK256,none) ∧
      middle.gasAvailable = .ofNat 34 ∧ last.gasAvailable = .ofNat 4 ∧ last.pc = .ofNat 2 := by
  obtain ⟨middle,first⟩ := checked_hash_edge 1 dest input (.ofNat 0) (.ofNat 0)
    [.ofNat 0] rfl rfl (by rfl)
  have henv : middle.executionEnv = input.executionEnv :=
    congrArg (fun t : EvmYul.State .EVM => t.executionEnv) first.world
  have hf : fetched middle = (.KECCAK256,none) := by
    unfold fetched
    rw [henv,first.pc]
    rfl
  have hg : middle.gasAvailable = .ofNat 34 := first.gas
  have ha : middle.activeWords = .ofNat 0 := first.activeWords
  have guard : hashGuard middle = .ok () := zero_size_guard middle _ first.stack ha hg
  obtain ⟨last,second⟩ := checked_hash_edge 0 dest middle
    (actualDigest (machineQuery input.toMachineState (.ofNat 0) (.ofNat 0)))
    (.ofNat 0) [] hf first.stack guard
  have hlast : last.gasAvailable = .ofNat 4 := by
    rw [second.gas]
    unfold hashMemoryCharged
    obtain ⟨hm,hc⟩ := zero_size_costs middle _ first.stack ha
    rw [hm,hc,hg]
    change (UInt256.ofNat 34 - UInt256.ofNat 0) - UInt256.ofNat 30 = UInt256.ofNat 4
    decide
  have hpc : last.pc = .ofNat 2 := by
    rw [second.pc,first.pc]
    rfl
  exact ⟨middle,last,first,second,hf,hg,hlast,hpc⟩

/-- Discharges BOTH edge premises of the compositional client from the fixed
input. The cut cursor is internal evidence, not a public error poststate. -/
theorem actual_pair_error_cut (dest : Array UInt256) :
    ∃ (middle last : EVM.State) (e : ExecutionException),
      DriverQueryCut 3 dest input
        [byteQuery (machineQuery input.toMachineState (.ofNat 0) (.ofNat 0)),
         byteQuery (machineQuery middle.toMachineState
           (actualDigest (machineQuery input.toMachineState (.ofNat 0) (.ofNat 0))) (.ofNat 0))]
        (.error e) 1 last
        [byteQuery (machineQuery input.toMachineState (.ofNat 0) (.ofNat 0)),
         byteQuery (machineQuery middle.toMachineState
           (actualDigest (machineQuery input.toMachineState (.ofNat 0) (.ofNat 0))) (.ofNat 0))] [] ∧
      middle.gasAvailable = .ofNat 34 ∧ last.gasAvailable = .ofNat 4 ∧ last.pc = .ofNat 2 ∧
      X 3 dest input = .error e := by
  obtain ⟨middle,last,first,second,hf,hgas,hlast,hpc⟩ := actual_pair dest
  obtain ⟨queries,path⟩ := two_hash_query_cut 0 dest input middle last
    (.ofNat 0) (.ofNat 0)
    (actualDigest (machineQuery input.toMachineState (.ofNat 0) (.ofNat 0)))
    (.ofNat 0) [.ofNat 0] [] first second rfl rfl hf first.stack
  have hnil : queries = [] := query_receipt_unique 1 dest last queries []
    (X 3 dest input) (X 1 dest last) path.sound.2.2 (driver_one_queries dest last)
  subst queries
  obtain ⟨e,he⟩ := driver_one_error dest last
  have full : X 3 dest input = .error e :=
    first.continues.trans (second.continues.trans he)
  rw [full] at path
  exact ⟨middle,last,e,path,hgas,hlast,hpc,full⟩

end Solidity.HashBridge.PairControls
