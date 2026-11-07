import Solidity.Yul.Interfaces.P16
import Solidity.Yul.Adapters.RawPhysicalInventory

/-! Consumer of the actual published bounded P16 Source adapter. Its correct
field remains a producer obligation for the exact indexed Source statement.
Physical all-cell capture preserves the represented result and coherence;
this supplies no adapter for arbitrary assembly or target compiler theorem. -/
namespace Solidity.Yul.Adapters.RawPhysicalProducer
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open RawPhysicalInventory

/-- Actual Source execution, exact raw-local physical snapshot and unchanged
representation carriers share the producer's reached result, on every horizon. -/
theorem transport {ctx : Source.Ctx} {returns : List Source.STy} {modifier u : Bool}
    {stmt : Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys}
    {C : Contract} {Γ : Ctx}
    (producer : RawSourceAdapter.Adapter ctx returns modifier u stmt)
    (glob : Source.Glob ctx.env) (frame : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph ctx.env))
    (state : RawFrame.State ctx) (coherent : RawCoherent.coherent state=true)
    (base : Nat) (image : FrameMem C Γ)
    (room : base+32*wordCellCount (localExternalTypes ctx)≤image.highWaterWords*32) :
    let reached := producer.run fuel state
    let physical := frameOf base reached.2 image room
    let loaded := decode base reached.2 (frameBytes physical)
    RawCoherent.coherent loaded=true ∧ RawFrame.view loaded=RawFrame.view reached.2 ∧
    loaded.clean=reached.2.clean ∧ loaded.world=reached.2.world ∧
    (Source.execS glob frame fuel nps ph stmt state.clean).run (Source.L0 ctx.env,state.world)=
      RawLoopBody.represented (reached.1,loaded) := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  have sourceRun := producer.correct glob frame fuel nps ph state coherent
  have raw := frame_bytes base (producer.run fuel state).2 image room
  have snapshot := view_roundtrip base (producer.run fuel state).2 (frameBytes image)
  refine ⟨?_,?_,rfl,rfl,?_⟩
  · rw [raw,coherence_roundtrip]
    exact sourceRun.1
  · rw [raw]
    exact snapshot
  · exact sourceRun.2
end Solidity.Yul.Adapters.RawPhysicalProducer
