import SolidityBridge.RoadmapV15.P10.SignedLePrimitive
import SolidityBridge.RoadmapV15.P10.BooleanNotConsumer
import SolidityBridge.RoadmapV15.P10.LogicalShiftLayout

/-! Exact selected intLe code and full SGT-output/ISZERO-entry State alignment.
No source frame or desired execution relation is introduced. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

def signedLeInput (seed : EVM.State) (before after : Backend.Program) (words : Scalar.Stack) : EVM.State :=
  {seed with
    pc := .ofNat (Backend.encode before).length
    stack := words.map (fun w => UInt256.mk w.toFin)
    executionEnv := {seed.executionEnv with code :=
      ⟨(Backend.encode (before ++ .op .SGT :: .op .ISZERO :: after)).toArray⟩}}
def signedLeCompared (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (signedLeInput seed before after (a::b::tail)) 3).replaceStackAndIncrPC
    ((Scalar.flag (decide (b.toInt < a.toInt))::tail).map (fun w => UInt256.mk w.toFin))
def signedLeTailSite (seed : EVM.State) (before after : Backend.Program)
    (fits : (Backend.encode (before ++ [.op .SGT])).length < UInt256.size) : Site .ISZERO :=
  ⟨seed,before ++ [.op .SGT],after,fits⟩

theorem signed_le_prefix_length (before : Backend.Program) :
    (Backend.encode (before ++ [.op .SGT])).length = (Backend.encode before).length+1 := by
  simp only [Backend.encode_append,Backend.encode_cons,Backend.encode_nil,
    Instr.encode,List.length_append,List.length_cons,List.length_nil]

theorem signed_le_tail_alignment (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack)
    (fits : (Backend.encode (before ++ [.op .SGT])).length < UInt256.size) :
    (modularSite (signedLeTailSite (signedLeCompared seed before after a b tail) before after fits)
      (Scalar.flag (decide (b.toInt < a.toInt))::tail)).state = signedLeCompared seed before after a b tail := by
  simp only [signedLeTailSite,modularSite,Site.state,signedLeCompared,signedLeInput,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,
    List.map_cons,List.append_assoc,List.cons_append,List.nil_append,Backend.encode_append,
    Backend.encode_cons,Backend.encode_nil,Instr.encode,List.length_append,List.length_cons,
    List.length_nil,logical_shift_pc_increment]

theorem signed_le_code (seed : EVM.State) (before after : Backend.Program) (words : Scalar.Stack) :
    (signedLeInput seed before after words).executionEnv.code.data.toList =
      Backend.encode (before ++ Scalar.intLe.code ++ after) := by
  simp only [signedLeInput,Scalar.intLe,List.append_assoc,List.cons_append,
    List.nil_append,List.toList_toArray]

theorem signed_le_selection : Scalar.selectBinary .le .int rfl = some Scalar.intLe := by
  rfl


#print axioms signed_le_prefix_length
#print axioms signed_le_tail_alignment
#print axioms signed_le_code
#print axioms signed_le_selection
end SolidityBridge.RoadmapV15.P10
