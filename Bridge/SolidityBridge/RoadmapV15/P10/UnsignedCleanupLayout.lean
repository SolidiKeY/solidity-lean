import SolidityBridge.RoadmapV15.P10.BitwiseConsumer
import SolidityBridge.RoadmapV15.P10.SignedCleanupAlignment

/-! Actual unsignedCode emitter layout and resource transport. Existing width
correctness is consumed read-only; no arithmetic/profile definition is replaced. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

def unsignedCleanupMask (w : Fin 32) : Scalar.Word :=
  BitVec.ofNat 256 (2 ^ Scalar.widthBits w - 1)

/-- Extract the mask result from the published intrinsic emitter theorem. -/
theorem unsigned_mask_result (w : Fin 32) (x : Scalar.Word) :
    unsignedCleanupMask w &&& x = Scalar.unsignedClean w x := by
  have h := Scalar.unsigned_correct w x []
  rw [Scalar.unsignedCode,Scalar.run,Scalar.step_pushWord] at h
  change some ((unsignedCleanupMask w &&& x)::[]) = some (Scalar.unsignedClean w x::[]) at h
  exact (List.cons.inj (Option.some.inj h)).1

/-- Adequate natural costs do not wrap when encoded and debited by the reference. -/
theorem reference_gas_debit : ∀ (g : UInt256) (cost : Nat), cost ≤ g.toNat →
    (g - UInt256.ofNat cost).toNat = g.toNat - cost := by
  intro g cost enough
  have fits : cost < UInt256.size := Nat.lt_of_le_of_lt enough g.val.isLt
  change (g.val - (UInt256.ofNat cost).val).val = g.toNat-cost
  rw [Fin.sub_val_of_le (by change cost % UInt256.size ≤ g.toNat; rw [Nat.mod_eq_of_lt fits]; exact enough)]
  change g.toNat - cost % UInt256.size = g.toNat - cost
  rw [Nat.mod_eq_of_lt fits]

def unsignedPushInput (seed : EVM.State) (before after : Backend.Program)
    (w : Fin 32) (words : Scalar.Stack) : EVM.State :=
  wordPushInput seed before (.op .AND::after) (unsignedCleanupMask w) words
def unsignedPushResult (seed : EVM.State) (before after : Backend.Program)
    (w : Fin 32) (words : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (unsignedPushInput seed before after w words) 3).replaceStackAndIncrPC
    ((unsignedCleanupMask w::words).map (fun y => UInt256.mk y.toFin)) 33

def unsignedCleanupSite (seed : EVM.State) (before after : Backend.Program) (w : Fin 32)
    (fits : (Backend.encode (before ++ [Scalar.pushWord (unsignedCleanupMask w)])).length < UInt256.size) :
    Site .AND := ⟨seed,before ++ [Scalar.pushWord (unsignedCleanupMask w)],after,fits⟩

/-- The complete code image is exactly the existing unsignedCode emitter. -/
theorem unsigned_cleanup_code :
∀ (seed : EvmYul.EVM.State) (before after : Solidity.Backend.Program) (w : Fin 32) (words : Solidity.Backend.Scalar.Stack),
 (SolidityBridge.RoadmapV15.P10.unsignedPushInput seed before after w words).executionEnv.code.data.toList =
 Solidity.Backend.encode (before ++ Solidity.Backend.Scalar.unsignedCode w ++ after)
 := by
  intro seed before after w words
  simp only [unsignedPushInput,wordPushInput,Scalar.unsignedCode,unsignedCleanupMask,
    List.append_assoc,List.cons_append,List.nil_append,List.toList_toArray]

/-- Complete actual PUSH output matches the represented AND tail entry. -/
theorem unsigned_push_tail_alignment :
∀ (seed : EvmYul.EVM.State) (before after : Solidity.Backend.Program) (w : Fin 32) (words : Solidity.Backend.Scalar.Stack)
 (fits : (Solidity.Backend.encode (before ++ [Solidity.Backend.Scalar.pushWord (SolidityBridge.RoadmapV15.P10.unsignedCleanupMask w)])).length < EvmYul.UInt256.size),
 (SolidityBridge.RoadmapV15.P10.modularSite
  (SolidityBridge.RoadmapV15.P10.unsignedCleanupSite (SolidityBridge.RoadmapV15.P10.unsignedPushResult seed before after w words) before after w fits)
  (SolidityBridge.RoadmapV15.P10.unsignedCleanupMask w::words)).state =
 SolidityBridge.RoadmapV15.P10.unsignedPushResult seed before after w words
 := by
  intro seed before after w words fits
  simp only [unsignedCleanupSite,modularSite,Site.state,unsignedPushResult,unsignedPushInput,
    wordPushInput,Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,
    List.map_cons,List.append_assoc,List.cons_append,List.nil_append,Backend.encode_append,
    Backend.encode_cons,Backend.encode_nil,List.length_append,List.length_cons,List.length_nil,
    Scalar.encode_pushWord,Vector.length_toList,signed_push_pc]

#print axioms unsigned_cleanup_code
#print axioms unsigned_push_tail_alignment
#print axioms unsigned_mask_result
#print axioms reference_gas_debit
end SolidityBridge.RoadmapV15.P10
