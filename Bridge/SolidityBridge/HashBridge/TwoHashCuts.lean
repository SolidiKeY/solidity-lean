import SolidityBridge.HashBridge.CutComposition
import SolidityBridge.HashBridge.HashCuts

/-! A client over two actual checked hash edges. These are conditional local
components, not a claim that a source invocation reaches either instruction.
The final query receipt and outcome come from the existing X computation. -/
namespace Solidity.HashBridge
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof

theorem two_hash_query_cut (fuel : Nat) (dest : Array UInt256)
    (s middle last : EVM.State) (offset size offset' size' : UInt256)
    (tail tail' : List UInt256)
    (first : CheckedHashEdge (fuel+1) dest s offset size tail middle)
    (second : CheckedHashEdge fuel dest middle offset' size' tail' last)
    (hf : fetched s = (.KECCAK256,none)) (hs : s.stack = offset :: size :: tail)
    (hf' : fetched middle = (.KECCAK256,none))
    (hs' : middle.stack = offset' :: size' :: tail') :
    ∃ queries, DriverQueryCut (fuel+3) dest s
      (byteQuery (machineQuery s.toMachineState offset size) ::
       byteQuery (machineQuery middle.toMachineState offset' size') :: queries)
      (X (fuel+3) dest s) (fuel+1) last
      [byteQuery (machineQuery s.toMachineState offset size),
       byteQuery (machineQuery middle.toMachineState offset' size')] queries := by
  obtain ⟨queries,rest⟩ := driver_queries (fuel+1) dest last
  have later : DriverQueryCut (fuel+2) dest middle
      (byteQuery (machineQuery middle.toMachineState offset' size') :: queries)
      (X (fuel+2) dest middle) (fuel+1) last
      [byteQuery (machineQuery middle.toMachineState offset' size')] queries :=
    second.query_cut hf' hs' rest
  have earlier : DriverQueryCut (fuel+3) dest s
      (byteQuery (machineQuery s.toMachineState offset size) ::
       byteQuery (machineQuery middle.toMachineState offset' size') :: queries)
      (X (fuel+3) dest s) (fuel+2) middle
      [byteQuery (machineQuery s.toMachineState offset size)]
      (byteQuery (machineQuery middle.toMachineState offset' size') :: queries) :=
    first.query_cut hf hs (by
    obtain ⟨cut,receipt,path⟩ := later
    exact ⟨cut,receipt⟩)
  have aligned : DriverQueryCut (fuel+2) dest middle
      (byteQuery (machineQuery middle.toMachineState offset' size') :: queries)
      (X (fuel+3) dest s) (fuel+1) last
      [byteQuery (machineQuery middle.toMachineState offset' size')] queries := by
    rw [first.continues]
    exact later
  exact ⟨queries,earlier.compose aligned⟩

end Solidity.HashBridge
