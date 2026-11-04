import SolidityBridge.RoadmapV15.P10.BitwiseConsumer
import Solidity.Backend.PrimitivePackets.Bitwise.Source

/-! Published clean unsigned Source leaves and actual fetched bitwise bodies.
Native operands are constructed; no physical input-load or compiler-origin claim. -/
namespace SolidityBridge.RoadmapV15.P10.PublishedBitwise
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open Solidity.Backend.PrimitivePackets.Bitwise

def opcode : Source.BinOp → Backend.Op
  | .bitAnd => .AND | .bitOr => .OR | .bitXor => .XOR | _ => .AND

theorem clean_word (w : Fin 32) (x : Nat) (hx : x<2^(unsigned w).bits) :
    (BitVec.ofNat 256 x).toNat=x := by
  change x % 2^256=x
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hx
    (Nat.pow_le_pow_right (by decide) (unsigned w).valid.2.2))

theorem value_word (op : Source.BinOp) (hop : Supported op) (x y : Nat) :
    (match op with
    | .bitAnd => (BitVec.ofNat 256 x &&& BitVec.ofNat 256 y)
    | .bitOr => (BitVec.ofNat 256 x ||| BitVec.ofNat 256 y)
    | .bitXor => (BitVec.ofNat 256 x ^^^ BitVec.ofNat 256 y)
    | _ => 0) = BitVec.ofNat 256 (value op x y) := by
  rcases hop with rfl | rfl | rfl
  · exact BitVec.ofNat_and.symm
  · exact BitVec.ofNat_or.symm
  · exact BitVec.ofNat_xor.symm

theorem fetched {E : Source.Env} (G : Source.Glob E) (F : Source.Fr)
    (sfuel : Nat) (s : Source.St E) (w : Fin 32) (op : Source.BinOp) (hop : Supported op)
    (x y : Nat) (hx : x < 2^(unsigned w).bits) (hy : y < 2^(unsigned w).bits)
    (site : Site (opcode op)) (tail : Scalar.Stack) (room : tail.length+2≤1024)
    (gas : 3≤site.seed.gasAvailable.toNat) (nfuel : Nat) :
    let ls := Source.Locals.cons (operand (D := E.layout) w x hx) (.cons (operand w y hy) .nil)
    let input := (modularSite site (BitVec.ofNat 256 x::BitVec.ofNat 256 y::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((BitVec.ofNat 256 (value op x y)::tail).map (fun z=>UInt256.mk z.toFin))
    (Source.evalE G F (sfuel+3) (sourceExpr E w op)).run (ls,s)=
      (.ok (.val (operand w (value op x y) (value_lt op hop _ _ _ hx hy))),(ls,s)) ∧
    Assembly.driverSteps 1 (nfuel+2) #[] input=.ok next ∧
    EVM.X (nfuel+2) #[] input=EVM.X (nfuel+1) #[] next ∧
    next.toState=input.toState ∧ next.memory=input.memory ∧
    next.returnData=input.returnData ∧ next.H_return=input.H_return := by
  have src := evalE_operand G F sfuel w op hop x y hx hy s
  have native : let input := (modularSite site (BitVec.ofNat 256 x::BitVec.ofNat 256 y::tail)).state
      let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
        ((BitVec.ofNat 256 (value op x y)::tail).map (fun z=>UInt256.mk z.toFin))
      Assembly.driverSteps 1 (nfuel+2) #[] input=.ok next ∧
      EVM.X (nfuel+2) #[] input=EVM.X (nfuel+1) #[] next := by
    rcases hop with rfl | rfl | rfl
    · simpa only [value,BitVec.ofNat_and] using (bitwise_and_agreement site (BitVec.ofNat 256 x) (BitVec.ofNat 256 y) tail room gas nfuel).2
    · simpa only [value,BitVec.ofNat_or] using (bitwise_or_agreement site (BitVec.ofNat 256 x) (BitVec.ofNat 256 y) tail room gas nfuel).2
    · simpa only [value,BitVec.ofNat_xor] using (bitwise_xor_agreement site (BitVec.ofNat 256 x) (BitVec.ofNat 256 y) tail room gas nfuel).2
  exact ⟨src,native.1,native.2,rfl,rfl,rfl,rfl⟩

#print axioms clean_word
#print axioms value_word
#print axioms fetched
end SolidityBridge.RoadmapV15.P10.PublishedBitwise
