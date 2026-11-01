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

theorem transaction_blobhash (environment : Environment) (tx : Source.TxConfig) (index : Roadmap.Word) :
    blobhash (environment.bindTransaction tx) index=blobhash environment index := rfl

theorem transaction_last (environment : Environment) (first last : Source.TxConfig) :
    (environment.bindTransaction first).bindTransaction last=environment.bindTransaction last := rfl

/-- Actual source frame record, not a second frame/state semantics.
Contract identity, checked mode and depth are explicit execution inputs. -/
def sourceFrameOfCall (frame : Source.CallFrame) (contract : String) (checked : Bool) (depth : Nat) : Source.Fr :=
  { this := frame.this, sender := frame.caller, value := frame.value,
    static := frame.static, contract := contract, checked := checked, depth := depth }

theorem sourceFrameOfCall_fields (frame : Source.CallFrame) (contract : String) (checked : Bool) (depth : Nat) :
    let source := sourceFrameOfCall frame contract checked depth
    source.this=frame.this ∧ source.sender=frame.caller ∧ source.value=frame.value ∧
    source.static=frame.static ∧ source.contract=contract ∧ source.checked=checked ∧ source.depth=depth :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end Solidity.Yul.Views
