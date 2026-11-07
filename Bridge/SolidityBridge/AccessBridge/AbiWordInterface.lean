import SolidityBridge.AccessBridge.Interface
import Solidity.Backend.AbiEntry.CalldataWordInterface
import Solidity.Backend.AbiEntry.WordValidation

/-! Native input-word and existing numeric-validator agreement with the actual
indexed semantic decoder. This is not a fetched native validator sequence or
an entry span-check certificate. All charged-load failures remain inherited. -/
namespace SolidityBridge.AccessBridge
open Solidity Solidity.Backend EvmYul
structure AbiWordCertificate : Prop extends CalldataLoadCertificate where
  semantic : ∀ (native : EvmYul.State .EVM) (frame : Source.Fr) (offset : UInt256),
    native.executionEnv.calldata.data.toList=frame.cd →
    (EvmYul.State.calldataload native offset).toNat=Solidity.AbiEntry.load frame.cd offset.toNat
  validation : ∀ (native : EvmYul.State .EVM) (frame : Source.Fr) (offset : UInt256),
    native.executionEnv.calldata.data.toList=frame.cd →
    ∀ (kind : Solidity.AbiEntry.Kind) (tail : Scalar.Stack),
    Scalar.run (Backend.AbiEntry.WordValidation.validator kind).code
      (BitVec.ofNat 256 (EvmYul.State.calldataload native offset).toNat::tail)=
      some (Scalar.flag (kind.valid (Solidity.AbiEntry.load frame.cd offset.toNat))::tail)
  rejected : ∀ (native : EvmYul.State .EVM) (frame : Source.Fr) (offset : UInt256),
    native.executionEnv.calldata.data.toList=frame.cd →
    ∀ (kind : Solidity.AbiEntry.Kind) (tail : Scalar.Stack) (fuel length free : Nat),
    Solidity.AbiEntry.cval {data := frame.cd,free := free} (fuel+1) (.word kind) offset.toNat length=.error .revert ↔
      Scalar.run (Backend.AbiEntry.WordValidation.validator kind).code
        (BitVec.ofNat 256 (EvmYul.State.calldataload native offset).toNat::tail)=
        some (Scalar.flag false::tail)
end SolidityBridge.AccessBridge
