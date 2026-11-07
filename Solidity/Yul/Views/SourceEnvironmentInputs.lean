import Solidity.Yul.Views.Inputs
import Solidity.Source.Eval

namespace Solidity.Yul.Views

/-- Exact zero extension, justified by the actual160bit Address bound. -/
def addressInputWord (a : Roadmap.Address) : Roadmap.Word :=
  ⟨a.val,Nat.lt_trans a.isLt (by decide)⟩

theorem sourceAddress_input_word (D : Source.Layout) (a : Roadmap.Address) :
    (Source.Val.address (D := D) (p := false) a).word=some (addressInputWord a) := by
  apply congrArg some
  apply Fin.ext
  exact Nat.mod_eq_of_lt (addressInputWord a).isLt

/-- Bind only actual transaction inputs. All other universally supplied
Osaka inputs stay unchanged. Glob does not contain tx.origin. -/
def Environment.bindTransaction (environment : Environment) (tx : Source.TxConfig) : Environment :=
  { environment with timestamp := tx.request.timestamp, origin := tx.origin }

theorem transaction_timestamp (environment : Environment) (tx : Source.TxConfig) :
    (environment.bindTransaction tx).read .timestamp=tx.request.timestamp := rfl

theorem transaction_origin (environment : Environment) (tx : Source.TxConfig) :
    (environment.bindTransaction tx).read .origin=addressInputWord tx.origin := rfl

theorem transaction_other_input (environment : Environment) (tx : Source.TxConfig) (read : EnvRead)
    (notTimestamp : read≠.timestamp) (notOrigin : read≠.origin) :
    (environment.bindTransaction tx).read read=environment.read read := by
  cases read <;> first | rfl | contradiction

theorem transaction_hash_inputs (environment : Environment) (tx : Source.TxConfig) :
    (environment.bindTransaction tx).historicalHash=environment.historicalHash ∧
    (environment.bindTransaction tx).blobHashes=environment.blobHashes := ⟨rfl,rfl⟩

theorem transaction_blockhash (environment : Environment) (tx : Source.TxConfig) (query : Roadmap.Word) :
    blockhash (environment.bindTransaction tx) query=blockhash environment query := rfl

/-- Binding actual Source transaction metadata preserves the eligible-block
hash result for every supplied environment and transaction. -/
theorem transaction_blockhash_in_window (environment : Environment) (tx : Source.TxConfig)
    (query : Roadmap.Word) (past : query.val < environment.number.val)
    (recent : environment.number.val - query.val ≤ 256) :
    blockhash (environment.bindTransaction tx) query = environment.historicalHash query :=
  (transaction_blockhash environment tx query).trans
    (blockhash_in_window environment query past recent)

/-- Regression boundary: transaction binding cannot turn a current/future or
too-old query into an eligible historical lookup. No Source admission is added. -/
theorem transaction_blockhash_outside_window (environment : Environment) (tx : Source.TxConfig)
    (query : Roadmap.Word)
    (outside : ¬ (query.val < environment.number.val ∧ environment.number.val - query.val ≤ 256)) :
    blockhash (environment.bindTransaction tx) query = 0 :=
  (transaction_blockhash environment tx query).trans
    (blockhash_outside_window environment query outside)

theorem transaction_blobhash (environment : Environment) (tx : Source.TxConfig) (index : Roadmap.Word) :
    blobhash (environment.bindTransaction tx) index=blobhash environment index := rfl

/-- Actual Source transaction binding preserves an eligible supplied blob
lookup, including the same list entry and dependent index-bound proof. -/
theorem transaction_blobhash_in_bounds (environment : Environment) (tx : Source.TxConfig)
    (index : Roadmap.Word) (inside : index.val < environment.blobHashes.length) :
    blobhash (environment.bindTransaction tx) index = environment.blobHashes[index.val]'inside :=
  (transaction_blobhash environment tx index).trans
    (blobhash_in_bounds environment index inside)

/-- Binding actual transaction metadata does not make an out-of-range blob
index valid. This is a data-binding law, not program or fork admission. -/
theorem transaction_blobhash_outside_bounds (environment : Environment) (tx : Source.TxConfig)
    (index : Roadmap.Word) (outside : environment.blobHashes.length ≤ index.val) :
    blobhash (environment.bindTransaction tx) index = 0 :=
  (transaction_blobhash environment tx index).trans
    (blobhash_outside_bounds environment index outside)

theorem transaction_last (environment : Environment) (first last : Source.TxConfig) :
    (environment.bindTransaction first).bindTransaction last=environment.bindTransaction last := rfl

/-- Actual source frame record, not a second frame/state semantics.
Contract identity, checked mode and depth are explicit execution inputs. -/
def sourceFrameOfCall (frame : Source.CallFrame) (contract : String) (checked : Bool) (depth : Nat) : Source.Fr :=
  { this := frame.this, sender := frame.caller, value := frame.value,
    static := frame.static, contract := contract, checked := checked, depth := depth, cd := frame.input }

theorem sourceFrameOfCall_fields (frame : Source.CallFrame) (contract : String) (checked : Bool) (depth : Nat) :
    let source := sourceFrameOfCall frame contract checked depth
    source.this=frame.this ∧ source.sender=frame.caller ∧ source.value=frame.value ∧
    source.static=frame.static ∧ source.contract=contract ∧ source.checked=checked ∧ source.depth=depth :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- The actual per-call input is preserved, independently of all other
frame fields. The older seven-field projection theorem remains unchanged. -/
theorem sourceFrameOfCall_cd (frame : Source.CallFrame) (contract : String)
    (checked : Bool) (depth : Nat) :
    (sourceFrameOfCall frame contract checked depth).cd=frame.input := by
  rfl

/-- Actual owner byte-reference reads consume the same per-call input and
preserve the complete source state. This is not a reference-formation,
callee-admission or whole-call adequacy theorem. -/
theorem sourceFrameOfCall_bytes {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.CallFrame) (contract : String) (checked : Bool)
    (depth horizon off len : Nat) (s : Source.Locals E.layout Γ × Source.St E) :
    (Source.bytesOfRV (sourceFrameOfCall frame contract checked depth) horizon
      (τ:=.bytes .calldata) (.val (.cdRef rfl off len))).run s=
      (.ok ((frame.input.drop off).take len),s) := by
  rfl

end Solidity.Yul.Views
