import Solidity.Backend.PrimitivePackets.Comparisons.LocalReads
import Solidity.Evm.MemoryCompile

/-! Public checked selection of the local relational family. The source reads
are related to initial intrinsic locals, and StateRepr is the existing physical
layout relation. No successful compiled run or CompiledVal is an input. -/
namespace Solidity.Backend.PrimitivePackets.Comparisons
open Lowering.V07 Evm Evm.Memory
variable {C : Contract} {Γ : Ctx}

def value (o : Order) (signed : Bool) (a b : Idx Γ (.val (prim signed))) : Val C Γ .bool :=
  .binop (targetOp o) (accepts o signed) (returns o signed) (.simple (.local a)) (.simple (.local b))

def selected (base : Nat) (F : Frag Γ) (o : Order) (signed : Bool)
    (a b : Idx Γ (.val (prim signed))) : CompiledVal base F (value (C:=C) o signed a b) :=
by
  cases o <;> cases signed <;>
    exact ⟨_,.binary _ rfl rfl _ _ _ _ (.core _ rfl) (.core _ rfl)⟩

theorem public_selection (base : Nat) (F : Frag Γ) (o : Order) (signed : Bool)
    (a b : Idx Γ (.val (prim signed))) :
    compileVal base F (value (C:=C) o signed a b) = some (selected base F o signed a b) := by
  cases o <;> cases signed <;> rfl

theorem exact_code (base : Nat) (F : Frag Γ) (o : Order) (signed : Bool)
    (a b : Idx Γ (.val (prim signed))) :
    (selected (C:=C) base F o signed a b).code =
      [.mload (cellOf base a),.mload (cellOf base b)] ++
      (match signed,o with
       | false,.lt => [.gt] | false,.le => [.lt,.iszero]
       | false,.gt => [.lt] | false,.ge => [.gt,.iszero]
       | true,.lt => [.sgt] | true,.le => [.slt,.iszero]
       | true,.gt => [.slt] | true,.ge => [.sgt,.iszero]) := by
  cases o <;> cases signed <;> rfl

theorem intrinsic_run (state : State C Γ) (o : Order) (signed : Bool)
    (a b : Idx Γ (.val (prim signed))) (x y : Int)
    (hx : (ty signed).lo≤x ∧ x≤(ty signed).hi) (hy : (ty signed).lo≤y ∧ y≤(ty signed).hi)
    (left : TEnv.get a state.env = integerValue (ty signed) x hx)
    (right : TEnv.get b state.env = integerValue (ty signed) y hy) :
    (value o signed a b).evalT state = .ok (result o x y) := by
  cases o <;> cases signed <;>
    simp only [value,targetOp,Val.evalT,Simple.evalT,left,right,ty,integerValue,
      integerPrim,BinOp.shortT,BinOp.evalT,BinOp.evalNum,
      bind,Except.bind,TRes.ofOpt,result] <;> rfl

#print axioms public_selection
#print axioms exact_code
#print axioms intrinsic_run
end Solidity.Backend.PrimitivePackets.Comparisons
