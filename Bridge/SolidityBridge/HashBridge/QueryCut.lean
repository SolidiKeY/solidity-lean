import SolidityBridge.HashBridge.QueryUnique

/-! Cursor cuts within ONE existing direct-query receipt. Only existing
ClassifiedQueries.tail evidence can advance a cursor. This is an indexed
proof view, not another execution relation, evaluator or fuel-monotonicity rule.
No runtime erasure of the indexed Prop is introduced (G0). -/
namespace Solidity.HashBridge
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof

inductive ReceiptCut : {fuel : Nat} → {dest : Array UInt256} → {s : EVM.State} →
    {result : Except ExecutionException (ExecutionResult EVM.State)} →
    {cut : Classifies fuel dest s result} → {queries : List (List Nat)} →
    ClassifiedQueries cut queries → Nat → EVM.State → List (List Nat) → List (List Nat) → Prop where
  | here {fuel : Nat} {dest : Array UInt256} {s : EVM.State}
      {result : Except ExecutionException (ExecutionResult EVM.State)}
      {cut : Classifies fuel dest s result} {queries : List (List Nat)}
      (receipt : ClassifiedQueries cut queries) : ReceiptCut receipt fuel s [] queries
  | next (fuel : Nat) (dest : Array UInt256) (s charged : EVM.State)
      (cost : Nat) (next : EVM.State) (hc : checks dest s = .ok (charged,cost))
      (he : step fuel cost (some (fetched s)) charged = .ok next)
      (hh : terminalData next (fetched s).1 = none) {queries : List (List Nat)}
      {restCut : Classifies fuel dest next (X fuel dest next)}
      (rest : ClassifiedQueries restCut queries)
      {remaining : Nat} {last : EVM.State} {before after : List (List Nat)}
      (path : ReceiptCut rest remaining last before after) :
      ReceiptCut (.tail fuel dest s charged cost next hc he hh rest) remaining last
        (directQueries (fetched s).1 charged ++ before) after

/-- Existentially package only proofs of the existing full receipt and its
cut. Cursor states must come from real tail constructors, not a desired state. -/
def DriverQueryCut (fuel : Nat) (dest : Array UInt256) (s : EVM.State)
    (queries : List (List Nat)) (result : Except ExecutionException (ExecutionResult EVM.State))
    (remaining : Nat) (cursor : EVM.State) (before after : List (List Nat)) : Prop :=
  ∃ cut : Classifies fuel dest s result, ∃ receipt : ClassifiedQueries cut queries,
    ReceiptCut receipt remaining cursor before after

end Solidity.HashBridge
