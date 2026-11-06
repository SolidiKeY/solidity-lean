import SolidityBridge.RoadmapV15.P10.MetadataPushConsumer

/-! Arbitrary intrinsic payload/Scalar-tail transport through the existing
all-width charged metadata PUSH theorem. Exact bytes, including leading zeroes,
are recovered rather than postulated; no new machine or resource gate is defined. -/
namespace SolidityBridge.RoadmapV15.P10.PushFamily
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

abbrev cost := metadataPushCost

def value (n : Fin 33) (payload : Vector UInt8 n.val) : Fin (256^n.val) :=
  ⟨ofBytesBE payload.toList,by simpa only [Vector.length_toList] using bytes_value_bound payload.toList⟩

theorem exact_payload (n : Fin 33) (payload : Vector UInt8 n.val) :
    toBytesBE n.val (value n payload).val=payload := by
  apply Vector.toList_inj.mp
  have h := bytes_encoding_roundtrip payload.toList
  rw [Vector.length_toList (xs:=payload)] at h
  exact h

theorem reader (n : Fin 33) (payload : Vector UInt8 n.val) :
    uInt256OfByteArray ⟨payload.toArray⟩=UInt256.mk (Scalar.immediate payload.toList).toFin := by
  have h := congrArg UInt256.ofNat (reference_big_reader payload.toList)
  simpa only [uInt256OfByteArray,fromByteArrayBigEndian,Vector.toList,List.toList_toArray,
    Scalar.immediate] using h

theorem arity : ∀ n : Fin 33, EVM.δ (DecoderAgreement.pushOp n)=some 0 := by decide

def typedWord (w : Scalar.Word) : Backend.Environment.Word := lenU w.toNat w.isLt

theorem typed_word (w : Scalar.Word) : Scalar.encodeValue .uint (typedWord w)=w := by
  apply BitVec.eq_of_toNat_eq
  rw [Scalar.encode_uint_toNat]
  rfl

def input (seed : EVM.State) (before after : Backend.Program) (n : Fin 33)
    (payload : Vector UInt8 n.val) (words : Scalar.Stack) : EVM.State :=
  {seed with
    pc := UInt256.ofNat (Backend.encode before).length
    stack := words.map (fun w=>UInt256.mk w.toFin)
    executionEnv := {seed.executionEnv with
      code := ⟨(Backend.encode (before++ .push n payload::after)).toArray⟩}}

theorem metadata_input (seed : EVM.State) (before after : Backend.Program) (n : Fin 33)
    (payload : Vector UInt8 n.val) (words : Scalar.Stack) :
    metadataPushInput seed before after n (value n payload) (words.map typedWord)=
      input seed before after n payload words := by
  simp only [metadataPushInput,input,Backend.Environment.constant,exact_payload,List.map_map,
    Function.comp_def,typed_word]

theorem agreement (seed : EVM.State) (before after : Backend.Program) (n : Fin 33)
    (payload : Vector UInt8 n.val) (words : Scalar.Stack)
    (fits : (Backend.encode before).length<UInt256.size)
    (gas : cost n≤seed.gasAvailable.toNat) (room : words.length+1≤1024) (fuel : Nat) :
    let s := input seed before after n payload words
    let next := (Assembly.chargedPrepare s (cost n)).replaceStackAndIncrPC
      ((Scalar.immediate payload.toList::words).map (fun w=>UInt256.mk w.toFin)) (n.val+1)
    Scalar.step (.push n payload) words=some (Scalar.immediate payload.toList::words) ∧
    Assembly.driverSteps 1 (fuel+2) #[] s=.ok next ∧
    EVM.X (fuel+2) #[] s=EVM.X (fuel+1) #[] next := by
  dsimp only
  have h := metadata_constant_execution #[] seed before after n (value n payload) (words.map typedWord)
    fits gas (by simpa only [List.length_map] using room) fuel
  dsimp only at h
  rw [metadata_input] at h
  have word : UInt256.ofNat (value n payload).val=UInt256.mk (Scalar.immediate payload.toList).toFin := rfl
  rw [word] at h
  exact ⟨rfl,h.2.1,h.2.2.1⟩

#print axioms exact_payload
#print axioms reader
#print axioms arity
#print axioms typed_word
#print axioms metadata_input
#print axioms agreement
end SolidityBridge.RoadmapV15.P10.PushFamily
