import SolidityBridge.HashBridge.CutSound
namespace Solidity.HashBridge
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof
theorem ReceiptCut.compose {fuel : Nat} {dest : Array UInt256} {s : EVM.State}
    {result : Except ExecutionException (ExecutionResult EVM.State)}
    {cut : Classifies fuel dest s result} {queries : List (List Nat)}
    {receipt : ClassifiedQueries cut queries} {remaining : Nat} {cursor : EVM.State}
    {before after : List (List Nat)} (path : ReceiptCut receipt remaining cursor before after)
    {remaining' : Nat} {cursor' : EVM.State} {middle suffix : List (List Nat)}
    (later : DriverQueryCut remaining dest cursor after result remaining' cursor' middle suffix) :
    DriverQueryCut fuel dest s queries result remaining' cursor' (before ++ middle) suffix := by
  induction path with
  | here receipt =>
    simpa only [List.nil_append] using later
  | @next fuel dest s charged cost next hc he hh queries restCut rest remaining last before after path ih =>
    obtain ⟨laterCut,laterReceipt,laterPath⟩ := ih later
    refine ⟨.tail fuel dest s charged cost next hc he hh,
      .tail fuel dest s charged cost next hc he hh rest, ?_⟩
    simpa only [List.append_assoc] using
      ReceiptCut.next fuel dest s charged cost next hc he hh rest laterPath

/-- Compose only a later cut of the actual cursor computation. Matching result
indices do not license an arbitrary unrelated cursor or a new fuel run. -/
theorem DriverQueryCut.compose {fuel : Nat} {dest : Array UInt256} {s : EVM.State}
    {queries : List (List Nat)} {result : Except ExecutionException (ExecutionResult EVM.State)}
    {remaining : Nat} {cursor : EVM.State} {before after : List (List Nat)}
    (first : DriverQueryCut fuel dest s queries result remaining cursor before after)
    {remaining' : Nat} {cursor' : EVM.State} {middle suffix : List (List Nat)}
    (later : DriverQueryCut remaining dest cursor after result remaining' cursor' middle suffix) :
    DriverQueryCut fuel dest s queries result remaining' cursor' (before ++ middle) suffix := by
  obtain ⟨cut,receipt,path⟩ := first
  exact path.compose later

end Solidity.HashBridge
