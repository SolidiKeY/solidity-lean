import Solidity.Yul.Adapters.P6CalldataHash
import Solidity.Source.Semantics

/-! Concrete Fixed and both pipeline witnesses link actual Source allocation
to the published P6 copy/target opcode. Oversized typed-reference controls are
API states, not claims about ABI reachability or complete allocation refinement. -/
namespace Solidity.Yul.Adapters.P6CalldataHash.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Views
private def E : Source.Env := ⟨[]⟩
private def C : Contract := {vars:=[]}
private def F : Source.Fr := {this:=1,sender:=2,value:=0,static:=false,contract:="CopyHash",cd:=[17,255,0,128]}
private def fixed : Roadmap.Fixed := ⟨Roadmap.Evm.withKeccak,fun bal _ a=>bal a,1,0⟩
private def G (p : Pipeline) : Source.Glob E :=
  ⟨{body:=fun _=>none,consts:=fun _=>none,inits:=fun _=>[],ctor:=fun _=>none,
    ctorLocals:=fun _=>[],baseArgs:=fun _=>[],contracts:=[]},(match p with | .legacy=>.legacy | .viaIR=>.viaIR),fixed,
    fun _=>⟨0,by decide⟩,fun _ _=>true,fun _=>.answer (.success []),⟨0,by decide⟩⟩
private def state : Source.EMState E [.bytes .calldata] := (.cons (.cdRef rfl 1 5) .nil,Source.St.init E)
private def after := objectAllocatedState state (Source.Data.bytes (l:=.memory) [255,0,128])
private def image (p : Pipeline) : FrameMem C [] :=
  {st:=State.init C,key:=⟨8,1,p,2,lenU 1 (by decide),lenU 2 (by decide),lenU 0 (by decide)⟩
   scalar:=by intro R i;cases i
   capacity:=192,aligned:=⟨6,rfl⟩,data:=fun i=>if i.val=131 then 99 else if i.val=132 then 77 else if i.val=191 then 170 else 42
   highWaterWords:=6,resident:=by decide,zeroAbove:=by intro i high;have bound:=i.isLt;omega}
private def destination (p : Pipeline) : ByteSpan (image p).capacity :=
  ⟨lenU 128 (by decide),lenU 3 (by decide),Or.inr (by change 128+3≤192;decide)⟩
private def source : Environment.Word := lenU 1 (by decide)
private def copied (p : Pipeline) := P6Inputs.copyCalldata (image p) F source (destination p)

theorem actual_pipeline (p : Pipeline) (n : Nat) :
    (Source.evalE (G p) F (n+4) (sourceCalldataHashExpr Source.Idx.here)).run state=
      (.ok (.val (Source.mkBytes (n:=32) (h:=by decide) (Source.wordBytes ((G p).fixed.hash [255,0,128])))),after) ∧
    Environment.cryptoStep (.op .KECCAK256)
      ⟨(destination p).offset::(destination p).length::[lenU 77 (by decide)],frameBytes (copied p)⟩=
      some ⟨Environment.digest [255,0,128]::[lenU 77 (by decide)],frameBytes (copied p)⟩ ∧
    (Environment.digest [255,0,128]).val.toNat=((G p).fixed.hash [255,0,128]).val := by
  have run := source_target_clipped_hash (G p) F n state .here source 5 rfl (image p) (destination p)
    [lenU 77 (by decide)] rfl rfl
  exact ⟨run.1,run.2.1,run.2.2.2.1⟩

theorem source_allocation_retained : after.2.heap.next=1 ∧
    after.2.heap.get 0=some ⟨.bytes .memory,Source.Data.bytes [255,0,128]⟩ := ⟨rfl,rfl⟩

theorem source_invariant : Source.MemOK E state.2.heap.ty state :=
  ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,⟨trivial,trivial⟩⟩,
    Source.HeapShaped.empty,Source.HeapInner.empty⟩

theorem allocated_invariant : Source.MemOK E state.2.heap.ty after :=
  (objectAllocRef_MemOK _ state (Source.Data.bytes (l:=.memory) [255,0,128]) rfl trivial trivial (.bytes _) source_invariant).1

private def observed (p : Pipeline) : List Nat :=
  Environment.readMemory (frameBytes (copied p)) 128 3 |>.map UInt8.toNat |>.append
    [(frameBytes (copied p) 131).toNat,(frameBytes (copied p) 132).toNat,(frameBytes (copied p) 191).toNat,
     ((Source.evalE (G p) F 4 (sourceCalldataHashExpr Source.Idx.here)).run state).2.2.heap.next]
/-- info: [255, 0, 128, 99, 77, 170, 1] -/
#guard_msgs in #eval observed .legacy
/-- info: [255, 0, 128, 99, 77, 170, 1] -/
#guard_msgs in #eval observed .viaIR

private def emptySpan (p : Pipeline) : ByteSpan (image p).capacity :=
  ⟨lenU (2^256-1) (by decide),lenU 0 (by decide),Or.inl rfl⟩

theorem empty_copy (p : Pipeline) : P6Inputs.copyCalldata (image p) F source (emptySpan p)=image p :=
  P6Inputs.copy_empty _ _ _ _ rfl

theorem empty_hash (p : Pipeline) :
    Environment.cryptoStep (.op .KECCAK256)
      ⟨(emptySpan p).offset::(emptySpan p).length::[lenU 77 (by decide)],frameBytes (image p)⟩=
      some ⟨Environment.digest []::[lenU 77 (by decide)],frameBytes (image p)⟩ := by
  have target := P6Inputs.hash_after_copy (image p) F source (emptySpan p) [lenU 77 (by decide)]
  rw [empty_copy] at target
  exact target

private def wrongSpan (p : Pipeline) : ByteSpan (image p).capacity :=
  ⟨lenU 128 (by decide),lenU 5 (by decide),Or.inr (by change 128+5≤192;decide)⟩
/-- info: (0, 0, false) -/
#guard_msgs in #eval
  ((frameBytes (P6Inputs.copyCalldata (image .legacy) F source (wrongSpan .legacy)) 131).toNat,
   (frameBytes (P6Inputs.copyCalldata (image .legacy) F source (wrongSpan .legacy)) 132).toNat,
   Roadmap.Evm.keccakWord [255,0,128]==Roadmap.Evm.keccakWord [255,0,128,0,0])
end Solidity.Yul.Adapters.P6CalldataHash.Controls
