import Solidity.Signature
import SolidityBridge.Arith.Division

namespace Solidity.Bridge.Arith

/-- Every typed binary symbol uses the very evaluator audited in this family. -/
theorem signature_binary {C : Contract} (g : State C []) {p : PrimTy}
    (op : BinOp) (h : op.accepts p = true) (x y : p.Denote) :
    Op2.eval g (.binop op h) (some x) (some y) = op.evalT h x y := by
  change binopT op h x (some y) = _
  exact binopT_some op h x y

theorem signature_unary {C : Contract} (g : State C []) {p : PrimTy}
    (op : UnOp) (h : op.accepts p = true) (x : p.Denote) :
    Op1.eval g (.unop op h) (some x) = op.evalT h x := rfl

/-- Signature.toInt widens to KeY's unbounded integer sort; it is not a signed cast. -/
theorem signature_uint_to_kint {C : Contract} (g : State C []) (x : PrimTy.uint.Denote) :
    Op1.eval g .toInt (some x) = some ((BitVec.ofInt 256 x.val).toNat : Int) := by
  change some x.val = _
  rw [uint_decode]

end Solidity.Bridge.Arith

#print axioms Solidity.Bridge.Arith.signature_binary
#print axioms Solidity.Bridge.Arith.signature_unary
#print axioms Solidity.Bridge.Arith.signature_uint_to_kint
