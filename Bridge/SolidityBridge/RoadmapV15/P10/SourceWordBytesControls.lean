import SolidityBridge.RoadmapV15.P10.SourceWordBytes
import SolidityBridge.RoadmapV15.P10.WordPushFixtures
import Solidity.Backend.PrimitivePackets.SignedMod.Controls

/-! Full Source32byte observations, typed narrow readback and actual fetched
PUSH32 clients. Numeric reader equality alone is not an exact-length witness. -/
namespace SolidityBridge.RoadmapV15.P10.SourceWordBytesControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open SourceWordBytes
open WordPushFixtures (seed before after spill u accounts)
namespace Fixture
export Solidity.Backend.PrimitivePackets.SignedMod.Controls (E)
end Fixture

def i8 : Source.IntTy := ⟨true,8,by decide⟩
def u8 : Source.IntTy := ⟨false,8,by decide⟩

theorem positive_reader :
    Source.wordBytes (Source.toWord 66051)=List.replicate 29 0++[1,2,3] ∧
    (Source.wordBytes (Source.toWord 66051)).length=32 ∧
    uInt256OfByteArray ⟨(Source.wordBytes (Source.toWord 66051)).toArray⟩=u 66051 := by
  have bytes : Source.wordBytes (Source.toWord 66051)=List.replicate 29 0++[1,2,3] := by decide
  exact ⟨bytes,Source.wordBytes_length _,native_reader _⟩

private theorem integer_word_value (t : Source.IntTy) (v : Int) (range : t.lo≤v ∧ v≤t.hi) :
    Source.wordInt t (Source.intWord v)=v := by
  have h := Source.Val.word_int (D:=Fixture.E.layout) (t:=t) v range
  simp only [Source.Val.word,Option.bind_some] at h
  unfold Source.readInt at h
  dsimp only at h
  split at h
  · exact Option.some.inj h
  · cases h

theorem narrow_signed :
    ((Source.Val.int (D:=Fixture.E.layout) (t:=i8) (-2) (by decide)).word.map
      (fun w => (Scalar.immediate (Source.wordBytes w)).toFin)).bind (Source.readInt i8)=some (-2) ∧
    ((Source.Val.int (D:=Fixture.E.layout) (t:=u8) 255 (by decide)).word.map
      (fun w => (Scalar.immediate (Source.wordBytes w)).toFin)).bind (Source.readInt u8)=some 255 ∧
    Source.readInt u8 (Source.intWord 256)=none ∧
    Source.readInt i8 (Source.intWord (-129))=none ∧
    Source.wordBytes (Source.intWord (-2))=List.replicate 31 0xff++[0xfe] := by
  have reject : Source.readInt i8 (Source.intWord (-129))=none := by
    let wide : Source.IntTy := ⟨true,16,by decide⟩
    have value := integer_word_value wide (-129) (by decide)
    have same (w : Solidity.Roadmap.Word) : Source.wordInt i8 w=Source.wordInt wide w := by rfl
    rw [Source.readInt,same,value]
    decide
  have bytes : Source.wordBytes (Source.intWord (-2))=List.replicate 31 0xff++[0xfe] := by
    rw [integer_bytes]
    simp only [BitVec.toNat_ofInt,Nat.reducePow]
    decide
  exact ⟨typed_roundtrip i8 (-2) (by decide),typed_roundtrip u8 255 (by decide),by decide,reject,bytes⟩

theorem length_endian :
    let bytes := Source.wordBytes (Source.toWord 66051)
    bytes≠bytes.reverse ∧ bytes≠bytes.drop 1 ∧
    (bytes.drop 1).length=31 ∧ Source.beValue (bytes.drop 1)=66051 ∧
    Scalar.immediate (bytes.drop 1)=Scalar.immediate bytes := by
  rw [positive_reader.1]
  decide

private theorem shape (w : Solidity.Roadmap.Word) (perm : Bool) :
    (Assembly.chargedPrepare (WordPushFixtures.input 10 perm (BitVec.ofFin w) spill) 3).replaceStackAndIncrPC
      ((BitVec.ofFin w::spill).map (fun z=>UInt256.mk z.toFin)) 33=
      WordPushFixtures.expected perm (BitVec.ofFin w) spill := by
  change ({WordPushFixtures.input 10 perm (BitVec.ofFin w) spill with
    pc:=u 3+u 33,gasAvailable:=u 10-u 3,execLength:=42,
    stack:=(BitVec.ofFin w::spill).map (fun z=>UInt256.mk z.toFin)} : EVM.State)=_
  have pc : u 3+u 33=u 36 := by rfl
  have gas : u 10-u 3=u 7 := by rfl
  rw [pc,gas]
  rfl

theorem push_client (w : Solidity.Roadmap.Word) (perm : Bool) :
    uInt256OfByteArray ⟨(Source.wordBytes w).toArray⟩=UInt256.mk w ∧
    Backend.encode [Scalar.pushWord (BitVec.ofFin w)]=0x7f::Source.wordBytes w ∧
    Assembly.driverSteps 1 2 #[] (WordPushFixtures.input 10 perm (BitVec.ofFin w) spill)=
      .ok (WordPushFixtures.expected perm (BitVec.ofFin w) spill) ∧
    EVM.X 2 #[] (WordPushFixtures.input 10 perm (BitVec.ofFin w) spill)=
      EVM.X 1 #[] (WordPushFixtures.expected perm (BitVec.ofFin w) spill) := by
  have h := fetched_push (seed 10 perm) before after w spill (by decide) (by change 3≤10;decide) (by decide) 0
  dsimp only at h
  have hs := shape w perm
  simp only [WordPushFixtures.input] at hs
  rw [hs] at h
  exact ⟨h.2.1,push_payload w,h.2.2.1,h.2.2.2.1⟩

theorem complete_observation (perm : Bool) :
    let next := WordPushFixtures.expected perm (BitVec.ofFin (Source.toWord 66051)) spill
    next.stack=[u 66051,u 258,u 513] ∧ next.stack≠[u 197121,u 258,u 513] ∧ next.stack≠[u 66051,u 513,u 258] ∧
    next.executionEnv.code.data.toList=[0x60,0x7f,0x50,0x7f]++List.replicate 29 0++[1,2,3,0] ∧
    next.pc=u 36 ∧ next.gasAvailable=u 7 ∧ next.execLength=42 ∧
    next.memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    next.returnData.data.toList=[0xcc,0xdd] ∧ next.H_return.data.toList=[0xee,0xff] ∧
    next.executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧ next.accountMap=accounts ∧ next.σ₀=accounts := by
  refine ⟨rfl,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change [u 66051,u 258,u 513]≠[u 197121,u 258,u 513];decide
  · change [u 66051,u 258,u 513]≠[u 66051,u 513,u 258];decide

#print axioms positive_reader
#print axioms narrow_signed
#print axioms length_endian
#print axioms push_client
#print axioms complete_observation
end SolidityBridge.RoadmapV15.P10.SourceWordBytesControls
