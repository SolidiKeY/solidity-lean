import Solidity.Source.Value
import Solidity.Evm.Machine

/-! G42.05 value boundary. The backend word convention uses the low 192 bits;
this is not an assertion about ABI alignment or solc storage packing.
The source type retains parameters, returns and mutability. -/
namespace Solidity.Backend.FunctionValues
open Solidity.Source Solidity.Roadmap

/-- Runtime components of an external function value at its full source type. -/
structure ExternalValue (D : Layout) (ps rs : List STy) (m : Option Source.Mutability) where
  address : Address
  selector : List UInt8
  selector_length : selector.length = 4

def ExternalValue.source (v : ExternalValue D ps rs m) : Source.Val D (.fn true ps rs m) :=
  .externalFn v.address v.selector v.selector_length

/-- Numeric identity used by Source.Val.key, before any ABI/storage layout. -/
def ExternalValue.number (v : ExternalValue D ps rs m) : Nat :=
  v.address.val * 2 ^ 32 + bytesNat v.selector

/-- Exact source-to-word relation. No truncation is permitted by this relation. -/
def Represents (source : Source.Val D (.fn true ps rs m)) (word : Fin Evm.W) : Prop :=
  ∃ v : ExternalValue D ps rs m, source = v.source ∧ word.val = v.number

end Solidity.Backend.FunctionValues
