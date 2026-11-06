import SolidityBridge.RoadmapV15.EncodingUniqueness
import SolidityBridge.RoadmapV15.P10.PublishedMultiply
import SolidityBridge.RoadmapV15.P10.WordPushConsumer

/-! Actual Source word bytes through backend and pinned pure reference readers.
Exact ordered32bytes and typed readback do not establish memory padding or origin. -/
namespace SolidityBridge.RoadmapV15.P10.SourceWordBytes
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

theorem word_bytes (w : Solidity.Roadmap.Word) :
    Source.wordBytes w=(toBytesBE 32 w.val).toList := by
  exact bytes_canonical 32 w.val (Source.wordBytes w) (Source.wordBytes_length w) (Source.wordBytes_value w)

theorem integer_bytes (v : Int) :
    Source.wordBytes (Source.intWord v)=(toBytesBE 32 (BitVec.ofInt 256 v).toNat).toList := by
  have h := congrArg BitVec.toNat (PublishedMultiply.int_word v)
  change (Source.intWord v).val=(BitVec.ofInt 256 v).toNat at h
  rw [word_bytes,h]

theorem word_immediate (w : Solidity.Roadmap.Word) :
    Scalar.immediate (Source.wordBytes w)=BitVec.ofFin w := by
  rw [word_bytes]
  exact word32_immediate (BitVec.ofFin w)

theorem native_reader (w : Solidity.Roadmap.Word) :
    uInt256OfByteArray ⟨(Source.wordBytes w).toArray⟩=UInt256.mk w := by
  rw [word_bytes]
  simp only [Vector.toList,Array.toArray_toList]
  simpa only [BitVec.toNat_ofFin] using push_word_value (BitVec.ofFin w)

theorem typed_roundtrip {D : Source.Layout} (t : Source.IntTy) (v : Int)
    (range : t.lo≤v ∧ v≤t.hi) :
    ((Source.Val.int (D:=D) (t:=t) v range).word.map
      (fun w => (Scalar.immediate (Source.wordBytes w)).toFin)).bind (Source.readInt t)=some v := by
  simp only [Source.Val.word,Option.map_some,word_immediate]
  exact Source.Val.word_int (D:=D) v range

theorem bytes_injective (a b : Solidity.Roadmap.Word)
    (same : Source.wordBytes a=Source.wordBytes b) : a=b := by
  apply Fin.ext
  have h := congrArg Source.beValue same
  rw [Source.wordBytes_value,Source.wordBytes_value] at h
  exact h

theorem push_payload (w : Solidity.Roadmap.Word) :
    Backend.encode [Scalar.pushWord (BitVec.ofFin w)]=0x7f::Source.wordBytes w := by
  rw [word_bytes]
  simp only [Backend.encode_cons,Backend.encode_nil,Scalar.pushWord,Instr.encode,List.append_nil,BitVec.toNat_ofFin]
  rfl

theorem fetched_push (seed : EVM.State) (before after : Backend.Program)
    (w : Solidity.Roadmap.Word) (tail : Scalar.Stack)
    (fits : (Backend.encode before).length<UInt256.size)
    (gas : 3≤seed.gasAvailable.toNat) (room : tail.length+1≤1024) (fuel : Nat) :
    let input := wordPushInput seed before after (BitVec.ofFin w) tail
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((BitVec.ofFin w::tail).map (fun x=>UInt256.mk x.toFin)) 33
    (Source.wordBytes w).length=32 ∧
    uInt256OfByteArray ⟨(Source.wordBytes w).toArray⟩=UInt256.mk w ∧
    Assembly.driverSteps 1 (fuel+2) #[] input=.ok next ∧
    EVM.X (fuel+2) #[] input=EVM.X (fuel+1) #[] next ∧
    next.toState=input.toState ∧ next.memory=input.memory ∧
    next.returnData=input.returnData ∧ next.H_return=input.H_return := by
  have native := word_push_agreement seed before after (BitVec.ofFin w) tail fits gas room fuel
  exact ⟨Source.wordBytes_length w,native_reader w,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

#print axioms word_bytes
#print axioms integer_bytes
#print axioms word_immediate
#print axioms native_reader
#print axioms typed_roundtrip
#print axioms bytes_injective
#print axioms push_payload
#print axioms fetched_push
end SolidityBridge.RoadmapV15.P10.SourceWordBytes
