import Solidity.Yul.Adapters.SourceSliceFrame
import Solidity.Source.Semantics

namespace Solidity.Yul.Adapters.SourceSliceFrame.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
private def C : Contract := {vars:=[]}
private def E : Source.Env := ⟨[]⟩
private abbrev Γ : Source.RCtx := [.bytes .calldata,.bytes .calldata]
private def F : Source.Fr := {this:=1,sender:=2,value:=0,static:=true,contract:="Slice",cd:=[9,10,20,30,40,99]}
private def y : Source.EMState E Γ :=
  (.cons (.cdRef rfl 1 4) (.cons (.cdRef rfl 1 4) .nil),Source.St.init E)
private def image (p : Pipeline) : FrameMem C [] :=
  {st:=State.init C,key:=⟨9,1,p,3,lenU 1 (by decide),lenU 2 (by decide),lenU 0 (by decide)⟩
   scalar:=by intro R i;cases i
   capacity:=128,aligned:=⟨4,rfl⟩,data:=fun i=>if i.val=127 then 170 else 0
   highWaterWords:=4,resident:=by decide,zeroAbove:=by intro i high;have bound:=i.isLt;omega}
private def span (p : Pipeline) (n : Nat) (hn : n<2^256) (fit : 31+n≤128) : ByteSpan (image p).capacity :=
  ⟨lenU 31 (by decide),lenU n hn,Or.inr (by simpa only [lenU,Int.toNat_natCast] using fit)⟩
private def two (p : Pipeline) := span p 2 (by decide) (by decide)
private def three (p : Pipeline) := span p 3 (by decide) (by decide)
private def a : Source.Idx Γ (.bytes .calldata) := .here
private def b : Source.Idx Γ (.bytes .calldata) := .there .here

theorem aliases (p : Pipeline) :
    (consumeLocal (image p) (two p) F 4 a 1 3 false).run y=
      (consumeLocal (image p) (two p) F 4 b 1 3 false).run y := by
  rw [local_run _ _ _ _ _ _ _ _ _ 1 4 rfl,local_run _ _ _ _ _ _ _ _ _ 1 4 rfl]

theorem actual_image (p : Pipeline) :
    ∃ next : FrameMem C [],
      (consumeLocal (image p) (two p) F 4 a 1 3 false).run y=(.ok ([20,30],some next),y) ∧
      frameBytes next=Environment.writeBytes (frameBytes (image p)) 31 [20,30] ∧
      Environment.readMemory (frameBytes next) 31 2=[20,30] ∧ next.st=(image p).st ∧ next.key=(image p).key := by
  rw [local_run _ _ _ _ _ _ _ _ _ 1 4 rfl]
  exact consume_image _ _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) rfl

/-- Exact Source error, including full original caller locals/store. -/
theorem reversed_halts (p : Pipeline) :
    (consumeLocal (image p) (two p) F 4 a 3 1 false).run y=(.error (.revert []),y) := by
  rw [local_run _ _ _ _ _ _ _ _ _ 1 4 rfl]
  exact consume_halt _ _ _ _ _ _ _ _ _ _ _ rfl

/-- A destination-length mismatch is Source SUCCESS plus preparation None. -/
theorem size_mismatch (p : Pipeline) :
    (consumeLocal (image p) (three p) F 4 a 1 3 false).run y=(.ok ([20,30],none),y) := by
  rw [local_run _ _ _ _ _ _ _ _ _ 1 4 rfl]
  rw [consume_success _ _ _ _ _ _ _ _ _ _ (by decide) (by decide)]
  rfl

/-- Synthetic malformed-reference boundary: Source bytes truncate; a matching
logical slice length does not silently erase missing bytes or zero-pad them. -/
theorem truncated_boundary (p : Pipeline) :
    (consume (E:=E) (Γ:=Γ) (image p) (two p) F 4 5 20 0 2 false).run y=(.ok ([99],none),y) := by
  rw [consume_success _ _ _ _ _ _ _ _ _ _ (by decide) (by decide)]
  rfl

private def emptySpan (p : Pipeline) : ByteSpan (image p).capacity :=
  ⟨lenU (2^256-1) (by decide),lenU 0 (by decide),Or.inl rfl⟩

/-- Successful empty source slice preserves the WHOLE prepared image, including
access metadata, even at the maximum destination offset. -/
theorem empty_identity (p : Pipeline) :
    (consumeLocal (image p) (emptySpan p) F 4 a 4 4 false).run y=(.ok ([],some (image p)),y) := by
  rw [local_run _ _ _ _ _ _ _ _ _ 1 4 rfl]
  rw [consume_success _ _ _ _ _ _ _ _ _ _ (by decide) (by decide)]
  rfl

theorem past_length_halts (p : Pipeline) :
    (consumeLocal (image p) (two p) F 4 a 0 5 false).run y=(.error (.revert []),y) := by
  rw [local_run _ _ _ _ _ _ _ _ _ 1 4 rfl]
  exact consume_halt _ _ _ _ _ _ _ _ _ _ _ rfl

private def observation (r : Except Source.Halt (Roadmap.Bytes × Option (FrameMem C []))) :
    Nat × List Nat × List Nat :=
  match r with
  | .error (.revert bs)=>(0,bs.map UInt8.toNat,[])
  | .error _=>(3,[],[])
  | .ok (bs,none)=>(1,bs.map UInt8.toNat,[])
  | .ok (bs,some m)=>(2,bs.map UInt8.toNat,[frameBytes m 31,frameBytes m 32,frameBytes m 127].map UInt8.toNat)

/-- info: ((2, [20, 30], [20, 30, 170]), (2, [20, 30], [20, 30, 170]), (1, [20, 30], []), (0, [], []), (2, [20, 30, 40], [20, 30, 170]), 1, [99], []) -/
#guard_msgs (whitespace := lax) in
#eval (observation ((consumeLocal (image .legacy) (two .legacy) F 4 a 1 3 false).run y).1,
  observation ((consumeLocal (image .viaIR) (two .viaIR) F 4 b 1 3 false).run y).1,
  observation ((consumeLocal (image .legacy) (three .legacy) F 4 a 1 3 false).run y).1,
  observation ((consumeLocal (image .legacy) (two .legacy) F 4 a 3 1 false).run y).1,
  observation ((consumeLocal (image .viaIR) (three .viaIR) F 4 a 1 0 true).run y).1,
  observation ((consume (E:=E) (Γ:=Γ) (image .legacy) (two .legacy) F 4 5 20 0 2 false).run y).1)

/- Wrong preparation/source-error classification, lost toEnd bytes and invented
zero-padding of the truncated source payload are discriminated. -/
/-- info: (false, false, false, false) -/
#guard_msgs in
#eval (observation ((consumeLocal (image .legacy) (two .legacy) F 4 a 1 3 false).run y).1==(1,[20,30],[]),
  observation ((consumeLocal (image .legacy) (three .legacy) F 4 a 1 3 false).run y).1==(0,[],[]),
  observation ((consumeLocal (image .viaIR) (three .viaIR) F 4 a 1 0 true).run y).1==(2,[20,30],[20,30,170]),
  observation ((consume (E:=E) (Γ:=Γ) (image .legacy) (two .legacy) F 4 5 20 0 2 false).run y).1==(2,[99,0],[99,0,170]))

end Solidity.Yul.Adapters.SourceSliceFrame.Controls
