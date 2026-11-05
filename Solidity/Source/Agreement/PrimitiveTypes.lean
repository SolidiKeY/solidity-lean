import Solidity.Source.State
import Solidity.Semantics.Run

/-!
# Primitive source/model correspondence types

The first value-level clause of source-soundness item 3. This relates the
published independent source values to the existing elaborated model's
primitive values. It does not identify their heaps, executions, environments,
calldata, or compiler outputs. In particular this is not an execution oracle.
The source producers are imported unchanged from the recorded master input.
-/

namespace Solidity.Source.Agreement

/-- Exactly the three primitive types supported by the elaborated model. -/
def sourceTy : PrimTy → STy
  | .bool => .bool
  | .uint => .int IntTy.u256
  | .int => .int { IntTy.u256 with signed := true }

/-- A typed correspondence, keeping each side's actual range evidence.
No unsupported source type is erased or assigned a model value. -/
inductive PrimitiveRel (D : Layout) :
    (p : PrimTy) → Source.Val D (sourceTy p) → p.Denote → Prop where
  | bool (b : Bool) : PrimitiveRel D .bool (.bool b) b
  | uint (v : PrimTy.uint.Denote)
      (h : IntTy.u256.lo ≤ v.1 ∧ v.1 ≤ IntTy.u256.hi) :
      PrimitiveRel D .uint (.int v.1 h) v
  | int (v : PrimTy.int.Denote)
      (h : ({ IntTy.u256 with signed := true } : IntTy).lo ≤ v.1 ∧
        v.1 ≤ ({ IntTy.u256 with signed := true } : IntTy).hi) :
      PrimitiveRel D .int (.int v.1 h) v

end Solidity.Source.Agreement
