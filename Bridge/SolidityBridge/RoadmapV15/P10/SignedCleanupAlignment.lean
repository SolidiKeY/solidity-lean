import SolidityBridge.RoadmapV15.P10.SignedCleanupTail
import SolidityBridge.RoadmapV15.P10.WordPushConsumer

/-! Concrete native arithmetic and state alignment for emitted signed cleanup.
No execution relation is replaced; these are consequences of the actual updates. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

theorem signed_push_gas : ∀ g : UInt256, 8 ≤ g.toNat → 5 ≤ (g - UInt256.ofNat 3).toNat := by
  intro g h
  change 5 ≤ (g.val - (3 : Fin UInt256.size)).val
  rw [Fin.sub_val_of_le (by change 3 ≤ g.toNat; omega)]
  change 5 ≤ g.toNat - 3
  omega

theorem signed_push_pc : ∀ n : Nat,
    UInt256.ofNat n + UInt256.ofNat 33 = UInt256.ofNat (n+33) := by
  intro n
  apply congrArg UInt256.mk
  apply Fin.ext
  exact (Nat.add_mod n 33 UInt256.size).symm

def signedPushInput (seed : EVM.State) (before after : Backend.Program)
    (w : Fin 32) (x : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  wordPushInput seed before (.op .SIGNEXTEND::after) (signedCleanupIndex w) (x::tail)
def signedPushResult (seed : EVM.State) (before after : Backend.Program)
    (w : Fin 32) (x : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (signedPushInput seed before after w x tail) 3).replaceStackAndIncrPC
    ((signedCleanupIndex w::x::tail).map (fun y => UInt256.mk y.toFin)) 33

/-- Complete actual PUSH output is exactly the represented fetched tail entry. -/
theorem signed_push_tail_alignment :
∀ (seed : EvmYul.EVM.State) (before after : Solidity.Backend.Program) (w : Fin 32)
 (x : Solidity.Backend.Scalar.Word) (tail : Solidity.Backend.Scalar.Stack)
 (fits : (Solidity.Backend.encode (before ++ [Solidity.Backend.Scalar.pushWord (SolidityBridge.RoadmapV15.P10.signedCleanupIndex w)])).length < EvmYul.UInt256.size),
 (SolidityBridge.RoadmapV15.P10.modularSite
  (SolidityBridge.RoadmapV15.P10.signedCleanupSite
   (SolidityBridge.RoadmapV15.P10.signedPushResult seed before after w x tail) before after w fits)
  (SolidityBridge.RoadmapV15.P10.signedCleanupIndex w::x::tail)).state =
 SolidityBridge.RoadmapV15.P10.signedPushResult seed before after w x tail
 := by
  intro seed before after w x tail fits
  simp only [signedCleanupSite,modularSite,Site.state,signedPushResult,signedPushInput,
    wordPushInput,Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,
    List.map_cons,List.append_assoc,List.cons_append,List.nil_append,Backend.encode_append,
    Backend.encode_cons,Backend.encode_nil,List.length_append,List.length_cons,List.length_nil,
    Scalar.encode_pushWord,Vector.length_toList,signed_push_pc]

#print axioms signed_push_tail_alignment
#print axioms signed_push_gas
#print axioms signed_push_pc
end SolidityBridge.RoadmapV15.P10
