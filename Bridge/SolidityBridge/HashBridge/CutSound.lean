import SolidityBridge.HashBridge.QueryCut

/-! Sound cuts preserve the SAME ultimate X result while exposing the actual
cursor and query split. No equality of whole machine/world states across an
effectful step, arbitrary shorter-fuel run, or native correspondence is used. -/
namespace Solidity.HashBridge
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof

/-- A cursor splits full queries in order, preserves operational continuation,
and carries a remaining receipt with the ORIGINAL public result index. -/
theorem ReceiptCut.sound {fuel : Nat} {dest : Array UInt256} {s : EVM.State}
    {result : Except ExecutionException (ExecutionResult EVM.State)}
    {cut : Classifies fuel dest s result} {queries : List (List Nat)}
    {receipt : ClassifiedQueries cut queries} {remaining : Nat} {cursor : EVM.State}
    {before after : List (List Nat)} (path : ReceiptCut receipt remaining cursor before after) :
    queries = before ++ after ∧ X fuel dest s = X remaining dest cursor ∧
      DriverQueryReceipt remaining dest cursor after result := by
  induction path with
  | @here fuel dest s result cut queries receipt =>
    exact ⟨rfl,rfl,cut,receipt⟩
  | @next fuel dest s charged cost next hc he hh queries restCut rest remaining last before after path ih =>
    refine ⟨?_,(X_continue fuel dest s charged next cost hc he hh).trans ih.2.1,ih.2.2⟩
    rw [ih.1,List.append_assoc]

theorem DriverQueryCut.sound {fuel : Nat} {dest : Array UInt256} {s : EVM.State}
    {queries : List (List Nat)} {result : Except ExecutionException (ExecutionResult EVM.State)}
    {remaining : Nat} {cursor : EVM.State} {before after : List (List Nat)}
    (h : DriverQueryCut fuel dest s queries result remaining cursor before after) :
    queries = before ++ after ∧ X fuel dest s = X remaining dest cursor ∧
      DriverQueryReceipt remaining dest cursor after result := by
  obtain ⟨cut,receipt,path⟩ := h
  exact path.sound

/-- Here is a cut of the actual receipt, not a freely chosen reached state. -/
theorem DriverQueryReceipt.here_cut {fuel : Nat} {dest : Array UInt256} {s : EVM.State}
    {queries : List (List Nat)} {result : Except ExecutionException (ExecutionResult EVM.State)}
    (h : DriverQueryReceipt fuel dest s queries result) :
    DriverQueryCut fuel dest s queries result fuel s [] queries := by
  obtain ⟨cut,receipt⟩ := h
  exact ⟨cut,receipt,.here receipt⟩

/-- Import one EXISTING checked nonterminal edge and its actual remaining
receipt. This component never claims that supplied edge premises have run. -/
theorem tail_query_cut (fuel : Nat) (dest : Array UInt256) (s charged next : EVM.State)
    (cost : Nat) (hc : checks dest s = .ok (charged,cost))
    (he : step fuel cost (some (fetched s)) charged = .ok next)
    (hh : terminalData next (fetched s).1 = none) (queries : List (List Nat))
    (rest : DriverQueryReceipt fuel dest next queries (X fuel dest next)) :
    DriverQueryCut (fuel+1) dest s (directQueries (fetched s).1 charged ++ queries)
      (X (fuel+1) dest s) fuel next (directQueries (fetched s).1 charged) queries := by
  obtain ⟨cut,receipt⟩ := rest
  rw [X_continue fuel dest s charged next cost hc he hh]
  refine ⟨.tail fuel dest s charged cost next hc he hh,
    .tail fuel dest s charged cost next hc he hh receipt,?_⟩
  simpa only [List.append_nil] using
    ReceiptCut.next fuel dest s charged cost next hc he hh receipt (.here receipt)

end Solidity.HashBridge
