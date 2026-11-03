import Solidity.Backend.InternalFlow.RuntimeFrameBytes
import Solidity.Semantics.AbiEntry

namespace Solidity.Backend.AbiWorld.CallerWordBytes
open Solidity Evm Evm.Memory

def word (saved : Fin Evm.W) : AbiEntry.Word (.uint 256) :=
 ⟨saved.val,by rw [AbiEntry.W_eq]; exact saved.isLt,
  by change decide (saved.val < 2^256) = true; exact decide_eq_true saved.isLt⟩
def values (saved : Fin Evm.W) : AbiEntry.Vals [.word (.uint 256)] := .cons (.word (word saved)) .nil

theorem word_encoding (saved : Fin Evm.W) :
 Semantics.wordBytes saved.val = AbiEntry.encodeArgs (values saved) := by
 simp only [values,AbiEntry.encodeArgs,AbiEntry.Vals.parts,AbiEntry.assemble,
  AbiEntry.Shape.dynamic,AbiEntry.Val.enc,word,AbiEntry.assemble.go,List.foldl_cons,
  List.foldl_nil,Bool.false_eq_true,↓reduceIte,List.append_nil]
 unfold Semantics.wordBytes AbiEntry.wordBytes
 apply List.map_congr_left
 intro index member
 exact UInt8.ofNat_mod_size

theorem recovered {m : Machine} {bytes : Environment.Memory} {live : Nat → Prop}
 (image : MemoryOps.Physical.WordFrame m bytes live) (cell temporary saved : Fin W)
 (selected : live cell.val) (tail : List Evm.Word) (byteTail : List Environment.Word)
 (top : m.stack = .val saved :: tail) (same : m.mem cell.val = .val saved) :
 Evm.run (InternalFlow.RuntimeFrame.Restore.consumeCode cell.val (.val temporary)) m = .ok {m with stack := tail} 0 ∧
 Environment.runCrypto (InternalFlow.RuntimeFrame.Bytes.code cell (image.fits cell.val selected) temporary)
  ⟨lenU saved.val saved.isLt :: byteTail,bytes⟩ =
   some ⟨byteTail,InternalFlow.RuntimeFrame.Bytes.afterBytes bytes cell temporary saved⟩ ∧
 MemoryOps.Physical.WordFrame {m with stack := tail}
  (InternalFlow.RuntimeFrame.Bytes.afterBytes bytes cell temporary saved) live ∧
 Environment.readMemory (InternalFlow.RuntimeFrame.Bytes.afterBytes bytes cell temporary saved)
  (32*cell.val) 32 = AbiEntry.encodeArgs (values saved) := by
 obtain ⟨numeric,physical,frame,observed⟩ :=
  InternalFlow.RuntimeFrame.Bytes.consume_frame image cell temporary saved selected tail byteTail top same
 exact ⟨numeric,physical,frame,observed.trans (word_encoding saved)⟩

theorem raw_revert (bytes : Environment.Memory) (cell temporary saved : Fin W)
 (fits : 32*cell.val+32≤2^256) (tail : List Roadmap.Word) (suffix : Backend.Program) :
 Backend.Failure.Slice.run (.op .REVERT :: suffix)
  ⟨(⟨32*cell.val,by change 32*cell.val<2^256;omega⟩ : Roadmap.Word)::
   (⟨32,by decide⟩ : Roadmap.Word)::tail,InternalFlow.RuntimeFrame.Bytes.afterBytes bytes cell temporary saved⟩ =
 some (⟨tail,InternalFlow.RuntimeFrame.Bytes.afterBytes bytes cell temporary saved⟩,
  some (.revert (AbiEntry.encodeArgs (values saved)))) := by
 rw [← word_encoding]
 exact InternalFlow.RuntimeFrame.Bytes.revert_saved bytes cell temporary saved fits tail suffix

theorem typed {C : Contract} {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
 {source : State C Γ} {base : Nat → Fin W} {machine : Machine}
 (represented : StateRepr L b frame F source base machine) (index : Idx Γ (.val .uint))
 (cell temporary saved : Fin W) (address : cell.val = cellOf b index)
 (bytes : Environment.Memory) (live : Nat → Prop) (image : MemoryOps.Physical.WordFrame machine bytes live)
 (selected : live cell.val) (tail : List Evm.Word) (byteTail : List Environment.Word)
 (top : machine.stack = .val saved :: tail)
 (captured : ReprV .uint (TEnv.get index source.env) (.val saved)) :
 Evm.run (InternalFlow.RuntimeFrame.Restore.consumeCode cell.val (.val temporary)) machine = .ok {machine with stack := tail} 0 ∧
 StateRepr L b frame F source base {machine with stack := tail} ∧
 Environment.runCrypto (InternalFlow.RuntimeFrame.Bytes.code cell (image.fits cell.val selected) temporary)
  ⟨lenU saved.val saved.isLt :: byteTail,bytes⟩ =
   some ⟨byteTail,InternalFlow.RuntimeFrame.Bytes.afterBytes bytes cell temporary saved⟩ ∧
 MemoryOps.Physical.WordFrame {machine with stack := tail}
  (InternalFlow.RuntimeFrame.Bytes.afterBytes bytes cell temporary saved) live ∧
 Environment.readMemory (InternalFlow.RuntimeFrame.Bytes.afterBytes bytes cell temporary saved)
  (32*cell.val) 32 = AbiEntry.encodeArgs (values saved) := by
 obtain ⟨numeric,repr,physical,frame⟩ := InternalFlow.RuntimeFrame.Bytes.scalar
  represented index cell temporary saved address bytes live image selected tail byteTail top captured
 refine ⟨numeric,repr,physical,frame,?_⟩
 rw [InternalFlow.RuntimeFrame.Bytes.afterBytes,← word_encoding]
 simpa only [MemoryOps.Physical.word_bytes_length] using
  Environment.read_written (Semantics.wordBytes saved.val) (32*cell.val)
   (Environment.writeBytes bytes (32*cell.val) (Semantics.wordBytes temporary.val))

theorem outside_byte (bytes : Environment.Memory) (cell temporary saved : Fin W) (probe : Nat)
 (outside : probe < 32*cell.val ∨ 32*cell.val+32≤probe) :
 InternalFlow.RuntimeFrame.Bytes.afterBytes bytes cell temporary saved probe = bytes probe := by
 unfold InternalFlow.RuntimeFrame.Bytes.afterBytes
 rw [Environment.writeBytes_frame (Semantics.wordBytes saved.val) (32*cell.val) probe _
  (by simpa only [MemoryOps.Physical.word_bytes_length] using outside)]
 exact Environment.writeBytes_frame (Semantics.wordBytes temporary.val) (32*cell.val) probe bytes
  (by simpa only [MemoryOps.Physical.word_bytes_length] using outside)

end Solidity.Backend.AbiWorld.CallerWordBytes
