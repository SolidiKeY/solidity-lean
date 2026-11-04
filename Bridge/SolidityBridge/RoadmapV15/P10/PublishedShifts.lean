import SolidityBridge.RoadmapV15.P10.LogicalShiftExecution
import Solidity.Backend.PrimitivePackets.Shifts.General

/-! Published unchecked Source shift leaves and actual emitted SWAP1/SHL-or-SHR
bodies. Fin-word/BitVec transport preserves all counts, not a count cutoff. -/
namespace SolidityBridge.RoadmapV15.P10.PublishedShifts
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open Solidity.Backend.PrimitivePackets.Shifts
namespace Src
export Solidity.Backend.PrimitivePackets.Shifts.General (expression source_execution)
end Src

theorem shl_word (x k : Fin Solidity.Evm.W) :
    (if k.val<256 then BitVec.ofFin x <<< k.val else 0)=BitVec.ofFin (resultWord true x k) := by
  by_cases h : k.val<256
  · simp only [resultWord,h,if_true]
    apply BitVec.eq_of_toNat_eq
    change (x.val <<< k.val) % 2^256=(x.val*2^k.val)%2^256
    rw [Nat.shiftLeft_eq]
  · simp only [resultWord,h,if_true,if_false]
    rfl

theorem shr_word (x k : Fin Solidity.Evm.W) :
    (if k.val<256 then BitVec.ofFin x >>> k.val else 0)=BitVec.ofFin (resultWord false x k) := by
  by_cases h : k.val<256
  · simp only [resultWord,h,Bool.false_eq_true,if_true,if_false]
    apply BitVec.eq_of_toNat_eq
    change (BitVec.ofFin x >>> k.val).toNat=x.val/2^k.val
    rw [BitVec.toNat_ushiftRight,BitVec.toNat_ofFin,Nat.shiftRight_eq_div_pow]
  · simp only [resultWord,h,Bool.false_eq_true,if_false]
    rfl

theorem shl_fetched {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (sfuel : Nat) (ls : Source.Locals E.layout Γ) (s : Source.St E)
    (i j : Source.Idx Γ (.int Source.IntTy.u256)) (x k : Fin Solidity.Evm.W)
    (readValue : ls.get i=.int (x.val:Int) (word_range x))
    (readCount : ls.get j=.int (k.val:Int) (word_range k))
    (seed : EVM.State) (before after : Backend.Program) (tail : Scalar.Stack)
    (fits : (Backend.encode (before++[.op (.SWAP 0)])).length<UInt256.size)
    (room : tail.length+2≤1024) (gas : 6≤seed.gasAvailable.toNat) (nfuel : Nat) :
    let input := logicalShiftInput seed before after .SHL (BitVec.ofFin x::BitVec.ofFin k::tail)
    let swapped := logicalShiftSwapped seed before after .SHL (BitVec.ofFin x) (BitVec.ofFin k) tail
    let next := (Assembly.chargedPrepare swapped 3).replaceStackAndIncrPC
      ((BitVec.ofFin (resultWord true x k)::tail).map (fun z=>UInt256.mk z.toFin))
    (Source.evalE G {F with checked:=false} (sfuel+3) (Src.expression true i j)).run (ls,s)=
      (.ok (.val (.int ((resultWord true x k).val:Int) (word_range (resultWord true x k)))),(ls,s)) ∧
    Scalar.run Scalar.uintShl.code (BitVec.ofFin x::BitVec.ofFin k::tail)=some (BitVec.ofFin (resultWord true x k)::tail) ∧
    Assembly.driverSteps 2 (nfuel+3) #[] input=.ok next ∧
    EVM.X (nfuel+3) #[] input=EVM.X (nfuel+1) #[] next ∧
    next.toState=input.toState ∧ next.memory=input.memory ∧
    next.returnData=input.returnData ∧ next.H_return=input.H_return := by
  have src := Src.source_execution G F sfuel true i j ls s x k readValue readCount
  have native := logical_shl_execution seed before after (BitVec.ofFin x) (BitVec.ofFin k) tail fits room gas nfuel
  dsimp only at native
  rw [BitVec.toNat_ofFin,shl_word] at native
  exact ⟨src,native.1,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

theorem shr_fetched {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (sfuel : Nat) (ls : Source.Locals E.layout Γ) (s : Source.St E)
    (i j : Source.Idx Γ (.int Source.IntTy.u256)) (x k : Fin Solidity.Evm.W)
    (readValue : ls.get i=.int (x.val:Int) (word_range x))
    (readCount : ls.get j=.int (k.val:Int) (word_range k))
    (seed : EVM.State) (before after : Backend.Program) (tail : Scalar.Stack)
    (fits : (Backend.encode (before++[.op (.SWAP 0)])).length<UInt256.size)
    (room : tail.length+2≤1024) (gas : 6≤seed.gasAvailable.toNat) (nfuel : Nat) :
    let input := logicalShiftInput seed before after .SHR (BitVec.ofFin x::BitVec.ofFin k::tail)
    let swapped := logicalShiftSwapped seed before after .SHR (BitVec.ofFin x) (BitVec.ofFin k) tail
    let next := (Assembly.chargedPrepare swapped 3).replaceStackAndIncrPC
      ((BitVec.ofFin (resultWord false x k)::tail).map (fun z=>UInt256.mk z.toFin))
    (Source.evalE G {F with checked:=false} (sfuel+3) (Src.expression false i j)).run (ls,s)=
      (.ok (.val (.int ((resultWord false x k).val:Int) (word_range (resultWord false x k)))),(ls,s)) ∧
    Scalar.run Scalar.uintShr.code (BitVec.ofFin x::BitVec.ofFin k::tail)=some (BitVec.ofFin (resultWord false x k)::tail) ∧
    Assembly.driverSteps 2 (nfuel+3) #[] input=.ok next ∧
    EVM.X (nfuel+3) #[] input=EVM.X (nfuel+1) #[] next ∧
    next.toState=input.toState ∧ next.memory=input.memory ∧
    next.returnData=input.returnData ∧ next.H_return=input.H_return := by
  have src := Src.source_execution G F sfuel false i j ls s x k readValue readCount
  have native := logical_shr_execution seed before after (BitVec.ofFin x) (BitVec.ofFin k) tail fits room gas nfuel
  dsimp only at native
  rw [BitVec.toNat_ofFin,shr_word] at native
  exact ⟨src,native.1,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

#print axioms shl_word
#print axioms shr_word
#print axioms shl_fetched
#print axioms shr_fetched
end SolidityBridge.RoadmapV15.P10.PublishedShifts
