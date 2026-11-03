import SolidityBridge.HashBridge.CutSound
import SolidityBridge.HashBridge.FrameHash

/-! Concrete all-fuel cuts of the SAME checked KECCAK computation. The first
cursor and remaining query receipt are derived, not supplied as desired states
or terminal certificates. No new execution or source model is introduced. -/
namespace Solidity.HashBridge
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof

theorem CheckedHashEdge.query_cut {fuel : Nat} {dest : Array UInt256}
    {s next : EVM.State} {offset size : UInt256} {tail : List UInt256}
    (edge : CheckedHashEdge fuel dest s offset size tail next)
    (hf : fetched s = (.KECCAK256,none)) (hs : s.stack = offset :: size :: tail)
    {queries : List (List Nat)}
    (rest : DriverQueryReceipt (fuel+1) dest next queries (X (fuel+1) dest next)) :
    DriverQueryCut (fuel+2) dest s
      (byteQuery (machineQuery s.toMachineState offset size) :: queries) (X (fuel+2) dest s)
      (fuel+1) next [byteQuery (machineQuery s.toMachineState offset size)] queries := by
  have he : step (fuel+1) (hashOpcodeCost s) (some (fetched s)) (hashMemoryCharged s) =
      .ok next := by simpa only [hf] using edge.evaluated
  have hh : terminalData next (fetched s).1 = none := by rw [hf]; rfl
  have hstack : (hashMemoryCharged s).stack = offset :: size :: tail := hs
  have h : DriverQueryCut (fuel+2) dest s
      (directQueries (fetched s).1 (hashMemoryCharged s) ++ queries) (X (fuel+2) dest s)
      (fuel+1) next (directQueries (fetched s).1 (hashMemoryCharged s)) queries :=
    tail_query_cut (fuel+1) dest s (hashMemoryCharged s) next (hashOpcodeCost s)
      edge.checked he hh queries rest
  simpa only [hf, directQueries, hstack, beq_self_eq_true, if_pos rfl,
    hash_charged_input, List.cons_append, List.nil_append] using h

/-- Low/check-failure arms cut at the actual initial state; the successful
head arm cuts only after its real checked evaluator step. -/
def HashCutAccount (fuel : Nat) (dest : Array UInt256) (s : EVM.State)
    (offset size : UInt256) (tail : List UInt256) : Prop :=
  match fuel with
  | 0 | 1 => DriverQueryCut fuel dest s [] (X fuel dest s) fuel s [] []
  | n+2 => match hashGuard s with
    | .error _ => DriverQueryCut (n+2) dest s [] (X (n+2) dest s) (n+2) s [] []
    | .ok () => ∃ next queries, CheckedHashEdge n dest s offset size tail next ∧
        DriverQueryCut (n+2) dest s
          (byteQuery (machineQuery s.toMachineState offset size) :: queries) (X (n+2) dest s)
          (n+1) next [byteQuery (machineQuery s.toMachineState offset size)] queries

/-- Public producer: no passed check, desired cursor/reply/world, tail receipt,
sufficient resource or destination-table membership premise. -/
theorem hash_frame_cut (fuel : Nat) (dest : Array UInt256) (s : EVM.State)
    (offset size : UInt256) (tail : List UInt256)
    (hf : fetched s = (.KECCAK256,none)) (hs : s.stack = offset :: size :: tail) :
    HashCutAccount fuel dest s offset size tail := by
  have account : HashFrameAccount fuel dest s offset size tail :=
    hash_frame_queries fuel dest s offset size tail hf hs
  cases fuel with
  | zero => exact account.here_cut
  | succ f =>
    cases f with
    | zero => exact account.here_cut
    | succ n =>
      change (match hashGuard s with
        | .error _ => DriverQueryCut (n+2) dest s [] (X (n+2) dest s) (n+2) s [] []
        | .ok () => ∃ next queries, CheckedHashEdge n dest s offset size tail next ∧
          DriverQueryCut (n+2) dest s
            (byteQuery (machineQuery s.toMachineState offset size) :: queries) (X (n+2) dest s)
            (n+1) next [byteQuery (machineQuery s.toMachineState offset size)] queries)
      cases hg : hashGuard s with
      | error e =>
        simp only [HashFrameAccount,hg] at account
        exact account.here_cut
      | ok ticket =>
        cases ticket
        simp only [HashFrameAccount,hg] at account
        obtain ⟨next,queries,edge,_,rest⟩ := account
        exact ⟨next,queries,edge,edge.query_cut hf hs rest⟩

end Solidity.HashBridge
