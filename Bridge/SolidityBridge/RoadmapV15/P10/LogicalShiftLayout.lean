import SolidityBridge.RoadmapV15.P10.LogicalShiftConsumer
import SolidityBridge.RoadmapV15.P10.StackFamilyConsumer
import SolidityBridge.RoadmapV15.P10.UnsignedCleanupLayout

/-! Exact selected SWAP1+shift code and complete intermediate-State alignment.
No physical allocation or source/frame-origin relation is introduced. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

def logicalShiftInput (seed : EVM.State) (before after : Backend.Program)
    (op : Backend.Op) (words : Scalar.Stack) : EVM.State :=
  {seed with
    pc := .ofNat (Backend.encode before).length
    stack := words.map (fun w => UInt256.mk w.toFin)
    executionEnv := {seed.executionEnv with code :=
      ⟨(Backend.encode (before ++ .op (.SWAP 0) :: .op op :: after)).toArray⟩}}
def logicalShiftSwapped (seed : EVM.State) (before after : Backend.Program)
    (op : Backend.Op) (value count : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (logicalShiftInput seed before after op (value::count::tail)) 3).replaceStackAndIncrPC
    ((count::value::tail).map (fun w => UInt256.mk w.toFin))
def logicalShiftTailSite (seed : EVM.State) (before after : Backend.Program) (op : Backend.Op)
    (fits : (Backend.encode (before ++ [.op (.SWAP 0)])).length < UInt256.size) : Site op :=
  ⟨seed,before ++ [.op (.SWAP 0)],after,fits⟩

theorem logical_shift_pc_increment (n : Nat) :
    UInt256.ofNat n + UInt256.ofNat 1 = UInt256.ofNat (n+1) := by
  apply congrArg UInt256.mk
  apply Fin.ext
  exact (Nat.add_mod n 1 UInt256.size).symm

theorem logical_shift_prefix_length (before : Backend.Program) :
    (Backend.encode (before ++ [.op (.SWAP 0)])).length = (Backend.encode before).length+1 := by
  simp only [Backend.encode_append,Backend.encode_cons,Backend.encode_nil,
    Instr.encode,List.length_append,List.length_cons,List.length_nil]

theorem logical_shift_tail_alignment (seed : EVM.State) (before after : Backend.Program)
    (op : Backend.Op) (value count : Scalar.Word) (tail : Scalar.Stack)
    (fits : (Backend.encode (before ++ [.op (.SWAP 0)])).length < UInt256.size) :
    (modularSite (logicalShiftTailSite (logicalShiftSwapped seed before after op value count tail)
      before after op fits) (count::value::tail)).state =
      logicalShiftSwapped seed before after op value count tail := by
  simp only [logicalShiftTailSite,modularSite,Site.state,logicalShiftSwapped,logicalShiftInput,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,
    List.map_cons,List.append_assoc,List.cons_append,List.nil_append,Backend.encode_append,
    Backend.encode_cons,Backend.encode_nil,Instr.encode,List.length_append,List.length_cons,
    List.length_nil,logical_shift_pc_increment]

theorem logical_shl_code (seed : EVM.State) (before after : Backend.Program) (words : Scalar.Stack) :
    (logicalShiftInput seed before after .SHL words).executionEnv.code.data.toList =
      Backend.encode (before ++ Scalar.uintShl.code ++ after) := by
  have zeroIndex : (0 : Fin 16) = ⟨0,by decide⟩ := by decide
  simp only [logicalShiftInput,Scalar.uintShl,List.append_assoc,List.cons_append,
    List.nil_append,List.toList_toArray,zeroIndex]

theorem logical_shr_code (seed : EVM.State) (before after : Backend.Program) (words : Scalar.Stack) :
    (logicalShiftInput seed before after .SHR words).executionEnv.code.data.toList =
      Backend.encode (before ++ Scalar.uintShr.code ++ after) := by
  have zeroIndex : (0 : Fin 16) = ⟨0,by decide⟩ := by decide
  simp only [logicalShiftInput,Scalar.uintShr,List.append_assoc,List.cons_append,
    List.nil_append,List.toList_toArray,zeroIndex]

theorem logical_shift_selection :
    Scalar.selectBinary .shl .uint rfl = some Scalar.uintShl ∧
    Scalar.selectBinary .shr .uint rfl = some Scalar.uintShr := by
  exact ⟨rfl,rfl⟩


#print axioms logical_shift_selection
#print axioms logical_shift_pc_increment
#print axioms logical_shift_prefix_length
#print axioms logical_shift_tail_alignment
#print axioms logical_shl_code
#print axioms logical_shr_code
end SolidityBridge.RoadmapV15.P10
