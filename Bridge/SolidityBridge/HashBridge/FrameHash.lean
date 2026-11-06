import SolidityBridge.HashBridge.FrameSound

/-! Import the actual checked KECCAK edge into a complete direct-frame query
receipt. Remaining queries are derived from the SAME residual X, never an
independent desired terminal certificate or selected successful child reply. -/
namespace Solidity.HashBridge
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof

/-- Component transport over an actual effectful checked edge. The public
all-fuel producer below supplies both this edge and its tail receipt itself. -/
theorem CheckedHashEdge.prepend_queries {fuel : Nat} {dest : Array UInt256}
    {s next : EVM.State} {offset size : UInt256} {tail : List UInt256}
    (edge : CheckedHashEdge fuel dest s offset size tail next)
    (hf : fetched s = (.KECCAK256,none)) (hs : s.stack = offset :: size :: tail)
    {queries : List (List Nat)}
    (rest : DriverQueryReceipt (fuel+1) dest next queries (X (fuel+1) dest next)) :
    DriverQueryReceipt (fuel+2) dest s
      (byteQuery (machineQuery s.toMachineState offset size) :: queries) (X (fuel+2) dest s) := by
  obtain ⟨cut,hq⟩ := rest
  have he : step (fuel+1) (hashOpcodeCost s) (some (fetched s)) (hashMemoryCharged s) =
      .ok next := by simpa only [hf] using edge.evaluated
  have hh : terminalData next (fetched s).1 = none := by rw [hf]; rfl
  let first : Classifies (fuel+2) dest s (X (fuel+1) dest next) :=
    .tail (fuel+1) dest s (hashMemoryCharged s) (hashOpcodeCost s) next edge.checked he hh
  have hfirst : ClassifiedQueries first
      (directQueries (fetched s).1 (hashMemoryCharged s) ++ queries) :=
    .tail (fuel+1) dest s (hashMemoryCharged s) (hashOpcodeCost s) next edge.checked he hh hq
  have hstack : (hashMemoryCharged s).stack = offset :: size :: tail := hs
  rw [edge.continues]
  refine ⟨first,?_⟩
  simpa only [hf, directQueries, hstack, beq_self_eq_true, if_pos rfl,
    hash_charged_input, List.cons_append, List.nil_append] using hfirst

/-- All-fuel account with actual first hash query plus SAME residual-frame
queries when the real guard passes. No successful check or future receipt is
an input to this proposition's producer. Low/check-failure arms remain empty. -/
def HashFrameAccount (fuel : Nat) (dest : Array UInt256) (s : EVM.State)
    (offset size : UInt256) (tail : List UInt256) : Prop :=
  match fuel with
  | 0 | 1 => DriverQueryReceipt fuel dest s [] (X fuel dest s)
  | n+2 => match hashGuard s with
    | .error _ => DriverQueryReceipt (n+2) dest s [] (X (n+2) dest s)
    | .ok () => ∃ next queries, CheckedHashEdge n dest s offset size tail next ∧
        DriverQueryReceipt (n+2) dest s
          (byteQuery (machineQuery s.toMachineState offset size) :: queries) (X (n+2) dest s) ∧
        DriverQueryReceipt (n+1) dest next queries (X (n+1) dest next)

/-- Concrete fetched-X consumer, no passed checks, chosen reply/state/result,
independent reached tail, sufficient fuel/gas, or destination membership premise. -/
theorem hash_frame_queries (fuel : Nat) (dest : Array UInt256) (s : EVM.State)
    (offset size : UInt256) (tail : List UInt256)
    (hf : fetched s = (.KECCAK256,none)) (hs : s.stack = offset :: size :: tail) :
    HashFrameAccount fuel dest s offset size tail := by
  cases fuel with
  | zero => exact ⟨.zero dest s,.zero dest s⟩
  | succ f =>
    cases f with
    | zero => exact driver_one_queries dest s
    | succ n =>
      change (match hashGuard s with
        | .error _ => DriverQueryReceipt (n+2) dest s [] (X (n+2) dest s)
        | .ok () => ∃ next queries, CheckedHashEdge n dest s offset size tail next ∧
          DriverQueryReceipt (n+2) dest s
            (byteQuery (machineQuery s.toMachineState offset size) :: queries) (X (n+2) dest s) ∧
          DriverQueryReceipt (n+1) dest next queries (X (n+1) dest next))
      cases hg : hashGuard s with
      | error e =>
        have hc : checks dest s = .error e := by rw [hash_checks dest s hf,hg]; rfl
        rw [check_failure (n+1) dest s e hc]
        exact ⟨.guard (n+1) dest s e hc,.guard (n+1) dest s e hc⟩
      | ok ticket =>
        cases ticket
        obtain ⟨next,edge⟩ := checked_hash_edge n dest s offset size tail hf hs hg
        obtain ⟨queries,rest⟩ := driver_queries (n+1) dest next
        exact ⟨next,queries,edge,edge.prepend_queries hf hs rest,rest⟩

end Solidity.HashBridge
