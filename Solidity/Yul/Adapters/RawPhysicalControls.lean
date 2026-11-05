import Solidity.Yul.Adapters.RawPhysical
import Solidity.Source.Semantics

/-! Inhabited raw LOCAL physical-byte controls. Dirty words stay raw until the
existing explicit return boundary is called. Overlay administration is observed
separately from view equality; these are not compiler/EVM observations. -/
namespace Solidity.Yul.Adapters.RawPhysical.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
private def E : Source.Env := ⟨[]⟩
private def boolCtx : Source.Ctx := {env:=E,scope:=none,locals:=[("flag",.bool)]}
private def boolCell : WordCell (localExternalTypes boolCtx) := .scalar ⟨.boolean,.here⟩
private def initial : RawFrame.State boolCtx :=
  RawFrame.ofClean (.cons (.bool false) .nil) (Source.St.init E)
private def dirty : RawFrame.State boolCtx := RawFrame.write initial boolCell (word 2)
private def C : Contract := {vars:=[]}
private def image (p : Pipeline) : FrameMem C [] :=
  {st:=State.init C,key:=⟨9,1,p,3,lenU 1 (by decide),lenU 2 (by decide),lenU 0 (by decide)⟩
   scalar:=by intro R i;cases i
   capacity:=96,aligned:=⟨3,rfl⟩,data:=fun i=>if i.val=95 then 170 else 0
   highWaterWords:=3,resident:=by decide,zeroAbove:=by intro i h;have hi:=i.isLt;omega}
private def area (p : Pipeline) : WordSpan (image p).capacity :=
  ⟨lenU 33 (by decide),by change 33+32≤96;decide⟩
private def restored (p : Pipeline) : RawFrame.State boolCtx :=
  load (store (image p) (area p) dirty boolCell) 33 initial boolCell

theorem dirty_roundtrip (p : Pipeline) : RawFrame.view (restored p) boolCell=word 2 := by
  rw [restored,load_view]
  change readWord (store (image p) (area p) dirty boolCell) (area p).offset.val.toNat=word 2
  rw [read_store]
  exact RawFrame.read_write _ _ _

theorem clean_preserved (p : Pipeline) : (restored p).clean=initial.clean := rfl

theorem explicit_bool (pipeline : RawFrame.Pipeline) (p : Pipeline) :
    RawFrame.returnBool pipeline (restored p) .here=.bool true := by
  cases pipeline <;> cases p <;> rfl

private def u8Ctx : Source.Ctx := {env:=E,scope:=none,locals:=[("x",.int Source.IntTy.u8)]}
private def u8Cell : WordCell (localExternalTypes u8Ctx) := .scalar ⟨.unsigned 0,.here⟩
private def u8Initial : RawFrame.State u8Ctx :=
  RawFrame.ofClean (.cons (.int 0 (by decide)) .nil) (Source.St.init E)
private def u8Dirty : RawFrame.State u8Ctx := RawFrame.write u8Initial u8Cell (word 257)
private def u8Restored (p : Pipeline) : RawFrame.State u8Ctx :=
  load (store (image p) (area p) u8Dirty u8Cell) 33 u8Initial u8Cell

theorem explicit_u8 (pipeline : RawFrame.Pipeline) (p : Pipeline) :
    RawFrame.returnU8 pipeline (u8Restored p) .here=.int 1 (by decide) := by
  cases pipeline <;> cases p <;> rfl

/-- info: (2, some 0, some 2, 170) -/
#guard_msgs in #eval
  ((RawFrame.view (restored .legacy) boolCell).val,
   ((restored .legacy).clean.get .here).word.map Fin.val,
   (restored .legacy).raw boolCell |>.map Fin.val,
   (frameBytes (store (image .legacy) (area .legacy) dirty boolCell) 95).toNat)
/-- info: (none, some 0) -/
#guard_msgs in #eval
  (initial.raw boolCell |>.map Fin.val,
   (load (store (image .viaIR) (area .viaIR) initial boolCell) 33 initial boolCell).raw boolCell |>.map Fin.val)
/-- info: true -/
#guard_msgs in #eval
  (readWord (store (image .viaIR) (area .viaIR)
    (RawFrame.write initial boolCell (word (2^256-1))) boolCell) 33).val==2^256-1
/-- info: (false, false) -/
#guard_msgs in #eval
  ((RawFrame.view (restored .viaIR) boolCell).val==1,
   (RawFrame.view (u8Restored .legacy) u8Cell).val==1)
/-- Actual target MSTORE retains the dirty bool word2 and complete stack tail. -/
theorem raw_target (p : Pipeline) (tail : List Environment.Word) :
    Environment.cryptoStep (.op .MSTORE)
      ⟨(area p).offset::lenU 2 (by decide)::tail,frameBytes (image p)⟩=
      some ⟨tail,frameBytes (store (image p) (area p) dirty boolCell)⟩ :=
  store_target (image p) (area p) dirty boolCell tail

private def targetObserved (p : Pipeline) (reverse : Bool) : List Nat :=
  let offset := (area p).offset
  let value := lenU 2 (by decide)
  let operands := if reverse then [value,offset,lenU 77 (by decide)]
    else [offset,value,lenU 77 (by decide)]
  match Environment.cryptoStep (.op .MSTORE) ⟨operands,frameBytes (image p)⟩ with
  | some reached => reached.stack.map (fun w=>w.val.toNat) ++
      [Source.beValue (Environment.readMemory reached.memory 33 32),(reached.memory 95).toNat]
  | none => []
/-- info: [77, 2, 170] -/
#guard_msgs in #eval targetObserved .legacy false
/-- info: [77, 2, 170] -/
#guard_msgs in #eval targetObserved .viaIR false
/-- info: false -/
#guard_msgs in #eval targetObserved .legacy true==[77,2,170]
/-- info: ([1, 2], false) -/
#guard_msgs in #eval
  ((Source.wordBytes (word 258)).drop 30 |>.map UInt8.toNat,
   (Source.wordBytes (word 258)).drop 30==[2,1])

private def cellArea (p : Pipeline) : WordSpan (image p).capacity :=
  ⟨lenU 32 (by decide),by change 32+32≤96;decide⟩
private def cellImage (p : Pipeline) : FrameMem C [] := store (image p) (cellArea p) dirty boolCell
private def cellMachine : Evm.Machine := Evm.Memory.writeMachine Evm.Machine.init 1 (.val (word 2))
private theorem cellFrame (p : Pipeline) : WordFrame cellMachine (frameBytes (cellImage p)) (fun c=>c=1) := by
  refine ⟨?_,?_⟩
  · intro c hc
    subst c
    decide
  · intro c hc
    subst c
    rw [cellImage,store_image,source_backend_wordBytes]
    exact cell_write_same Evm.Machine.init (frameBytes (image p)) 1 (word 2)

/-- An actual numeric cell, raw-local overlay and core load all observe word2;
word index1 is explicitly placed at byte32, not byte1. -/
theorem raw_load_target (p : Pipeline) : ∃ a : WordSpan (cellImage p).capacity,
    a.offset.val.toNat=32 ∧
    (Evm.Instr.mload 1).step cellMachine=.ok {cellMachine with stack:=[.val (word 2)]} 0 ∧
    RawFrame.view (load (cellImage p) a.offset.val.toNat initial boolCell) boolCell=word 2 ∧
    (load (cellImage p) a.offset.val.toNat initial boolCell).clean=initial.clean := by
  have room : 32*1+32≤(cellImage p).capacity := by
    simp only [cellImage,store,P6ByteMemory.write_capacity]
    change 64≤96
    decide
  obtain ⟨a,offset,w,step,view,raw,clean,world,frame⟩ :=
    load_frame (cellImage p) cellMachine (fun c=>c=1) (cellFrame p) 1 rfl room initial boolCell
  have value : RawFrame.view (load (cellImage p) a.offset.val.toNat initial boolCell) boolCell=word 2 := by
    rw [offset,load_view]
    change readWord (store (image p) (cellArea p) dirty boolCell) (cellArea p).offset.val.toNat=word 2
    rw [read_store]
    exact RawFrame.read_write _ _ _
  have same : w=word 2 := view.symm.trans value
  rw [same] at step view
  exact ⟨a,offset,step,view,clean⟩

/-- info: (2, 2, 170) -/
#guard_msgs in #eval
  let loaded := match (Evm.Instr.mload 1).step cellMachine with
    | .ok next _ => match next.stack with | .val w::_=>w.val | _=>999
    | _ => 999
  (loaded,(RawFrame.view (load (cellImage .legacy) 32 initial boolCell) boolCell).val,
    (frameBytes (cellImage .legacy) 95).toNat)
/-- info: false -/
#guard_msgs in #eval (RawFrame.view (load (cellImage .viaIR) 1 initial boolCell) boolCell).val==2

end Solidity.Yul.Adapters.RawPhysical.Controls
