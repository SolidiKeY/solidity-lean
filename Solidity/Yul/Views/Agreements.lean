import Solidity.Yul.Views.MemoryLayout
import Solidity.Yul.Views.Inputs
import Solidity.Yul.Views.StorageContract
import Solidity.Storage.HashedKeccak

/-! Explicit owner input agreements. These are extension obligations, not
instances of V10/V11 compilers or a second source environment/state. -/
namespace Solidity.Yul.Views

/-- G27/V10 must use the approved shared Fixed hash over the existing
HashedKeccak preimage encoding. This requires no collision axiom. -/
def HashInputAgreement (fixed : Roadmap.Evm.Fixed) (hash : Storage.Pre → Nat) : Prop :=
  ∀ p, hash p = fixed.keccak ((Storage.encode p).map UInt8.ofNat)

theorem HashInputAgreement.bounded {fixed : Roadmap.Evm.Fixed} {hash : Storage.Pre → Nat}
    (h : HashInputAgreement fixed hash) (p : Storage.Pre) : hash p < 2 ^ 256 := by
  rw [h p]
  exact fixed.keccak_lt _

/-- Existing source timestamp, transaction origin, frame input and Fixed must
be shared. Other block/tx fields need the authorized source extension before
its resolver rows can reopen; they are not synthesized from these premises. -/
structure InputAgreement {E : Source.Env} (g : Source.Glob E) (tx : Source.TxConfig)
    (frame : Source.CallFrame) (input : Roadmap.Bytes) (fixed : Roadmap.Evm.Fixed)
    (environment : Environment) : Prop where
  fixed_shared : fixed = g.fixed.evm
  calldata_shared : input = frame.input
  origin_shared : environment.origin = tx.origin
  timestamp_shared : environment.timestamp = g.timestamp

theorem InputAgreement.timestamp {E : Source.Env} {g : Source.Glob E} {tx : Source.TxConfig}
    {frame : Source.CallFrame} {input : Roadmap.Bytes} {fixed : Roadmap.Evm.Fixed} {e : Environment}
    (h : InputAgreement g tx frame input fixed e) : e.read .timestamp = g.timestamp :=
  h.timestamp_shared

theorem InputAgreement.hash {E : Source.Env} {g : Source.Glob E} {tx : Source.TxConfig}
    {frame : Source.CallFrame} {input : Roadmap.Bytes} {fixed : Roadmap.Evm.Fixed} {e : Environment}
    (h : InputAgreement g tx frame input fixed e) (m : ByteView) (a n : Nat) :
    keccak256 fixed m a n = keccak256 g.fixed.evm m a n := by
  rw [h.fixed_shared]

theorem InputAgreement.calldata {E : Source.Env} {g : Source.Glob E} {tx : Source.TxConfig}
    {frame : Source.CallFrame} {input : Roadmap.Bytes} {fixed : Roadmap.Evm.Fixed} {e : Environment}
    (h : InputAgreement g tx frame input fixed e) (a : Nat) :
    calldataloadWord input a = calldataloadWord frame.input a := by
  rw [h.calldata_shared]

end Solidity.Yul.Views
