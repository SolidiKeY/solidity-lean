import Solidity.Yul.Adapters.P6Inputs
import Solidity.Source.Semantics

namespace Solidity.Yul.Adapters.P6Inputs.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
private def C : Contract := {vars:=[]}
private def F : Source.Fr := {this:=1,sender:=2,value:=0,static:=true,contract:="Inputs",cd:=[1,2,255]}
private def image (p : Pipeline) : FrameMem C [] :=
  {st:=State.init C,key:=⟨7,1,p,2,lenU 1 (by decide),lenU 2 (by decide),lenU 0 (by decide)⟩
   scalar:=by intro R i;cases i
   capacity:=160,aligned:=⟨5,rfl⟩,data:=fun i=>if i.val=127 then 170 else 0
   highWaterWords:=5,resident:=by decide,zeroAbove:=by intro i high;have bound:=i.isLt;omega}
private def four (p : Pipeline) : ByteSpan (image p).capacity :=
  ⟨lenU 31 (by decide),lenU 4 (by decide),Or.inr (by change 31+4≤160;decide)⟩
private def word (p : Pipeline) : ByteSpan (image p).capacity :=
  ⟨lenU 31 (by decide),lenU 32 (by decide),Or.inr (by change 31+32≤160;decide)⟩
private def inputOffset : Environment.Word := lenU 1 (by decide)
private def copied (p : Pipeline) := copyCalldata (image p) F inputOffset (four p)

theorem padded (p : Pipeline) : Environment.readMemory (frameBytes (copied p)) 31 4=[2,255,0,0] :=
  copy_readback (image p) F inputOffset (four p)

theorem actual_word (p : Pipeline) : Source.beValue (Environment.readMemory
    (frameBytes (copyCalldata (image p) F inputOffset (word p))) 31 32)=Source.cdWordAt F 1 :=
  copied_source_word _ _ _ _ rfl

private def E : Source.Env := ⟨[]⟩
private def y : Source.EMState E [] := (.nil,Source.St.init E)

/-- All actual typed decoder results, including errors and the full source
state, are retained rather than replaced by a successful numeric observation. -/
theorem actual_read (p : Pipeline) (τ : Source.STy) :
    (Source.readLoc (E:=E) (Γ:=[]) F (τ:=τ) (.cd 1)).run y=
      (Source.decodeWord E.layout (Source.beValue (Environment.readMemory
        (frameBytes (copyCalldata (image p) F inputOffset (word p))) 31 32)) τ,y) :=
  copied_source_read (E:=E) (Ξ:=[]) (image p) F inputOffset (word p) rfl τ y

theorem exterior (p : Pipeline) : frameBytes (copied p) 127=170 := by
  change frameBytes (copyCalldata (image p) F inputOffset (four p)) 127=170
  rw [copy_outside _ _ _ _ 127 (Or.inr (by change 31+4≤127;decide))]
  rfl

theorem beyond_end : callBytes F 100 4=[0,0,0,0] := rfl

theorem largest_offset : callBytes F (2^256-1) 4=[0,0,0,0] := rfl

private def emptySpan (p : Pipeline) : ByteSpan (image p).capacity :=
  ⟨lenU (2^256-1) (by decide),lenU 0 (by decide),Or.inl rfl⟩
theorem empty_copy (p : Pipeline) : copyCalldata (image p) F (lenU (2^256-1) (by decide)) (emptySpan p)=image p :=
  copy_empty _ _ _ _ rfl

/-- The actual hash slice consumes the copied/padded4bytes and preserves
its complete memory and caller stack tail. -/
theorem actual_hash (p : Pipeline) :
    Environment.cryptoStep (.op .KECCAK256)
      ⟨(four p).offset::(four p).length::[lenU 77 (by decide)],frameBytes (copied p)⟩=
      some ⟨Environment.digest [2,255,0,0]::[lenU 77 (by decide)],frameBytes (copied p)⟩ :=
  hash_after_copy _ _ _ _ _

private def readUint : Option Nat :=
  ((Source.readLoc (E:=E) (Γ:=[]) F (τ:=.int .u256) (.cd 1)).run y).1.toOption.bind fun v=>v.word.map Fin.val
private def rejectedBool : Bool :=
  match ((Source.readLoc (E:=E) (Γ:=[]) F (τ:=.bool) (.cd 1)).run y).1 with
  | .error (.revert [])=>true
  | _=>false
private def digestObserved (p : Pipeline) : Option Nat :=
  (Environment.cryptoStep (.op .KECCAK256)
    ⟨(four p).offset::(four p).length::[],frameBytes (copied p)⟩).bind fun s=>
      s.stack.head?.map fun w=>w.val.toNat

/-- info: ([2, 255, 0, 0], [0, 0, 0, 0], 170, true, true, true) -/
#guard_msgs in
#eval (Environment.readMemory (frameBytes (copied .legacy)) 31 4,
  callBytes F 100 4,frameBytes (copied .viaIR) 127,
  readUint==some ((2*256+255)*256^30),rejectedBool,
  digestObserved .viaIR==some (Roadmap.Evm.keccakWord [2,255,0,0]))

/- Wrong source offset/padding/endian, erased sentinel and stale/wrong-preimage
hashes are discriminated by complete selected byte or256bit observations. -/
/-- info: (false, false, false, false, false) -/
#guard_msgs in
#eval (Environment.readMemory (frameBytes (copied .legacy)) 31 4==([1,2,255,0] : List UInt8),
  Environment.readMemory (frameBytes (copied .viaIR)) 31 4==([0,0,2,255] : List UInt8),
  frameBytes (copied .legacy) 127==0,
  digestObserved .legacy==some (Roadmap.Evm.keccakWord [1,2,255,0]),
  digestObserved .viaIR==some (Roadmap.Evm.keccakWord [0,0,2,255]))

end Solidity.Yul.Adapters.P6Inputs.Controls
