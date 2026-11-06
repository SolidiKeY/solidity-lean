import SolidityBridge.RoadmapV15.P10.SignExtensionPositive

/-! Actual signedCode tail sites. The seed is an explicit tail-entry state;
no preceding PUSH execution, source origin or whole-program adequacy is assumed. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

def signedCleanupIndex (w : Fin 32) : Scalar.Word := BitVec.ofNat 256 w.val

def signedCleanupSite (seed : EVM.State) (before after : Backend.Program) (w : Fin 32)
    (fits : (Backend.encode (before ++ [Scalar.pushWord (signedCleanupIndex w)])).length < UInt256.size) :
    Site .SIGNEXTEND :=
  ⟨seed,before ++ [Scalar.pushWord (signedCleanupIndex w)],after,fits⟩

/-- The exact index emitted by signedCode, at every admitted width and value. -/
theorem signed_cleanup_index_word : ∀ (w : Fin 32) (x : Scalar.Word),
    UInt256.signextend (UInt256.mk (signedCleanupIndex w).toFin) (UInt256.mk x.toFin) =
      UInt256.mk (Scalar.signedClean w x).toFin :=
  signextend_width_word

#print axioms signed_cleanup_index_word
end SolidityBridge.RoadmapV15.P10
