import Solidity.Yul.Adapters.RawPhysicalProducer
import Solidity.Source.Semantics

/-! Four actual raw cells include both fields of an external function. Dirty
bool/u8/function words survive a nonaligned finite physical snapshot. Clean
Source values remain separate; absent overlays are not administratively equal
to capture. These are seeded kernel controls, not compiler layout observations. -/
namespace Solidity.Yul.Adapters.RawPhysicalInventory.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage

def E : Source.Env := ⟨[]⟩
def fnTy : Source.STy := .fn true [.bool] [.int Source.IntTy.u8] (some .view)
def ctx : Source.Ctx := {env:=E,scope:=none,locals:=[("flag",.bool),("small",.int Source.IntTy.u8),("fn",fnTy)]}
def flag : WordCell (localExternalTypes ctx) := .scalar ⟨.boolean,.here⟩
def small : WordCell (localExternalTypes ctx) := .scalar ⟨.unsigned 0,.there .here⟩
def address : WordCell (localExternalTypes ctx) := .address (.there (.there .here))
def selector : WordCell (localExternalTypes ctx) := .selector (.there (.there .here))
def clean : RawFrame.State ctx := RawFrame.ofClean
  (.cons (.bool false) (.cons (.int 0 (by decide))
    (.cons (.externalFn ⟨4660,by decide⟩ [137,171,205,239] rfl) .nil))) (Source.St.init E)
def dirty := RawFrame.write (RawFrame.write (RawFrame.write (RawFrame.write clean flag (word 2)) small (word 257))
  address (word (2^256-1))) selector (word (2^255+85))
def C : Contract := {vars:=[]}
def image (pipeline : Pipeline) : FrameMem C [] :=
  {st:=State.init C,key:=⟨9,1,pipeline,3,lenU 1 (by decide),lenU 2 (by decide),lenU 0 (by decide)⟩
   scalar:=by intro R i;cases i
   capacity:=192,aligned:=⟨6,rfl⟩,data:=fun _=>0xa5,highWaterWords:=6,
   resident:=by decide,zeroAbove:=by intro i high;have small:=i.isLt;omega}
theorem room (pipeline : Pipeline) : 33+32*wordCellCount (localExternalTypes ctx)≤(image pipeline).highWaterWords*32 := by
  change 33+32*4≤6*32
  decide

def stored (pipeline : Pipeline) := frameOf 33 dirty (image pipeline) (room pipeline)
def restored (pipeline : Pipeline) := decode 33 clean (frameBytes (stored pipeline))

theorem all_four (pipeline : Pipeline) :
    RawFrame.view (restored pipeline) flag=word 2 ∧ RawFrame.view (restored pipeline) small=word 257 ∧
    RawFrame.view (restored pipeline) address=word (2^256-1) ∧
    RawFrame.view (restored pipeline) selector=word (2^255+85) := by
  first | (simp only;done) | decide | omega | rfl | skip
  have views := (frame_roundtrip 33 dirty (image pipeline) (room pipeline)).1
  change RawFrame.view (decode 33 dirty (frameBytes (stored pipeline)))=RawFrame.view dirty at views
  have same : RawFrame.view (restored pipeline)=RawFrame.view dirty := views
  rw [same]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem restored_capture (pipeline : Pipeline) : restored pipeline=RawFrame.capture clean (RawFrame.view dirty) := by
  first | omega | decide | skip
  have views := (frame_roundtrip 33 dirty (image pipeline) (room pipeline)).1
  exact congrArg (RawFrame.capture clean) views

theorem source_and_readback (pipeline : Pipeline) (boundary : RawFrame.Pipeline) :
    (restored pipeline).clean=clean.clean ∧ (restored pipeline).world=clean.world ∧
    RawFrame.returnBool boundary (restored pipeline) .here=.bool true ∧
    RawFrame.returnU8 boundary (restored pipeline) (.there .here)=.int 1 (by decide) := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [restored_capture]
  refine ⟨rfl,rfl,?_,?_⟩
  · cases boundary <;> rfl
  · cases boundary <;> rfl

theorem nonaligned_and_padding (pipeline : Pipeline) :
    offset 33 flag=33 ∧ offset 33 small=65 ∧ offset 33 address=97 ∧ offset 33 selector=129 ∧
    frameBytes (stored pipeline) 32=0xa5 ∧ frameBytes (stored pipeline) 161=0xa5 ∧
    frameBytes (stored pipeline) 191=0xa5 ∧ frameBytes (stored pipeline) 192=0 := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only [stored]
  rw [frame_bytes]
  cases pipeline <;> decide

theorem dirty_not_cleaned (pipeline : Pipeline) : RawCoherent.coherent (restored pipeline)=false := by
  first | omega | decide | skip
  rw [restored_capture]
  decide

/-- A clean view roundtrip still installs actual Some overlays. -/
theorem absent_overlay_not_identity :
    (decode 33 clean (encode 33 clean (fun _=>0))).raw flag≠clean.raw flag := by
  first | (simp only;done) | decide | omega | rfl

def emptyCtx : Source.Ctx := {env:=E,scope:=none,locals:=[]}
def empty : RawFrame.State emptyCtx := RawFrame.ofClean .nil (Source.St.init E)
theorem empty_inventory (memory : Views.ByteView) : encode 33 empty memory=memory := rfl

def skipProducer : RawSourceAdapter.Adapter ctx [] false false (.skip) :=
  RawSourceAdapter.body RawLoopBody.Supported.skip

/-- A real published producer instance supplies Source execution; the physical
consumer retains the actual success/timeout result at every fuel. -/
theorem skip_transport (glob : Source.Glob E) (frame : Source.Fr) (fuel nps : Nat)
    (ph : Option (Source.Ph E)) (pipeline : Pipeline) :
    let reached := skipProducer.run fuel clean
    let loaded := decode 33 reached.2 (frameBytes (frameOf 33 reached.2 (image pipeline) (room pipeline)))
    RawCoherent.coherent loaded=true ∧ RawFrame.view loaded=RawFrame.view reached.2 ∧
      (Source.execS glob frame fuel nps ph (.skip : Source.RStmt E [] false ⟨true,false⟩ ctx.tys ctx.tys)
        clean.clean).run (Source.L0 E,clean.world)=RawLoopBody.represented (reached.1,loaded) := by
  first | (simp only;done) | decide | omega | rfl | skip
  have result := RawPhysicalProducer.transport skipProducer glob frame fuel nps ph clean
    (RawCoherent.coherent_ofClean _ _) 33 (image pipeline) (room pipeline)
  exact ⟨result.1,result.2.1,result.2.2.2.2⟩

end Solidity.Yul.Adapters.RawPhysicalInventory.Controls
