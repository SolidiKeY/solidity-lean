import Solidity.Backend.AbiEntry.TailGuardInterface

/-! Raw-byte operands for the existing numeric tail guard, not another decoder.
Metadata is wrapped exactly as the semantic arithmetic wraps it. -/
namespace Solidity.Backend.AbiEntry.Interface
open Solidity.AbiEntry

def rawTailOperands (input : Input) (shape : Shape) (base pointer : Nat) : Scalar.Stack :=
  let relative := load input.data pointer
  let address := wrap (base+relative)
  [BitVec.ofNat 256 shape.tailSize,BitVec.ofNat 256 input.size,BitVec.ofNat 256 base,
   BitVec.ofNat 256 relative,BitVec.ofNat 256 (load input.data address),
   BitVec.ofNat 256 shape.stride,BitVec.ofNat 256 input.size,BitVec.ofNat 256 address]

def rawTailCondition (input : Input) (shape : Shape) (base pointer : Nat) : Bool :=
  let relative := load input.data pointer
  let address := wrap (base+relative)
  tailFits input.size base relative shape.tailSize && decide (load input.data address≤lim) &&
    regionFits input.size address (load input.data address) shape.stride

structure RawTailGuardCertificate (code : Program) : Prop extends TailGuardCertificate code where
  raw : ∀ (input : Input) (shape : Shape) (base pointer : Nat) (suffix : Scalar.Stack),
    Scalar.run code (rawTailOperands input shape base pointer++suffix)=
      some (Scalar.flag (rawTailCondition input shape base pointer)::suffix)
  reference : ∀ (input : Input) (shape : Shape) (base pointer : Nat), shape.lengthPrefixed=true →
    tailRef input shape base pointer=
      if rawTailCondition input shape base pointer=true then
        .ok (wrap (wrap (base+load input.data pointer)+32),
          load input.data (wrap (base+load input.data pointer))) else .error .revert
end Solidity.Backend.AbiEntry.Interface
