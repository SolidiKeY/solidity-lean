import Solidity.Yul.Adapters.RawPhysicalCallFrame
import Solidity.Yul.Adapters.RawPhysicalCallOutputControls
import Solidity.Yul.World.WorldChecks

/-! Full adapter execution with a synthetic, explicitly supplied answer.
Real Source journal operations change caller storage on success and roll back
on revert, retaining the caller prefix. Revert bytes still reach caller memory.
This is not a source CALL producer or compiler invocation adequacy witness. -/
namespace Solidity.Yul.Adapters.RawPhysicalCallFrame.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Source.StateExamples
open RawPhysicalInventory RawPhysicalInventory.Controls

def entry : World.ObservedEffects D₀ LW LW :=
  ⟨World.Checks.callerEntry,[.log World.Checks.l0],rfl⟩
def parent : Source.CallFrame := entry.effects.execution.enter (addr 1) (addr 2) (Source.toWord 0) [] false
def input (pipeline : Pipeline) : ByteSpan (stored pipeline).capacity :=
  ⟨lenU 32 (by decide),lenU 1 (by decide),Or.inr (by change 32+1≤192;decide)⟩
def output := RawPhysicalCallOutput.Controls.area

def answer (outcome : Solidity.Roadmap.Outcome) : World.FrameAnswer D₀ LW LW :=
  ⟨World.Checks.havoc,[.log World.Checks.l4],outcome⟩
def invoke (outcome : Solidity.Roadmap.Outcome) : World.WorldPort D₀ LW LW :=
  fun _ _ _ _ _ _ => some (answer outcome)
def run (pipeline : Pipeline) (outcome : Solidity.Roadmap.Outcome) :=
  World.callAdapter World.TargetMemory.port (invoke outcome) entry (frameBytes (stored pipeline)) parent .call
    (addr 3) (Source.toWord 100) (Source.toWord 0)
    (P6ByteMemory.wireWord (input pipeline).offset) (P6ByteMemory.wireWord (input pipeline).length)
    (P6ByteMemory.wireWord (output pipeline).offset) (P6ByteMemory.wireWord (output pipeline).length)
def frame (pipeline : Pipeline) := World.childContext entry.effects.execution parent .call (addr 3)
  (Source.toWord 0) (snapshot (stored pipeline) (input pipeline))

theorem full_run (pipeline : Pipeline) (outcome : Solidity.Roadmap.Outcome) :
    run pipeline outcome=some (completed (stored pipeline) (output pipeline) entry (frame pipeline) (answer outcome)) :=
  execute_eq (stored pipeline) (input pipeline) (output pipeline) (invoke outcome) entry parent .call
    (addr 3) (Source.toWord 100) (Source.toWord 0) (answer outcome) rfl
    (by change 32+1≤2^256;decide) (by change decide (161+16≤2^256)=true;decide) rfl

/-- Actual adapter return: caller storage eight and prior log survive havoc;
revert data replaces stale data and its short output is copied without padding. -/
theorem revert_run (pipeline : Pipeline) :
    (run pipeline (.revert [17,255])).map (fun result =>
      ((result.observed.effects.execution.world.accounts (addr 1)).storage.read countPath,
       result.observed.effects.logs,result.observed.effects.returndata,result.observed.trace,
       result.copiedMemory.map (fun memory => (memory 161,memory 162,memory 163))))=
      some (some eight,[World.Checks.l0],[17,255],[.log World.Checks.l0],some (17,255,0xa5)) := by
  rw [full_run]
  have fields := revert_fields (stored pipeline) (output pipeline) entry (frame pipeline)
    World.Checks.havoc [.log World.Checks.l4] [17,255]
  dsimp only [answer,Option.map_some] at fields ⊢
  rw [fields.1,fields.2.1,fields.2.2.1,fields.2.2.2.1,fields.2.2.2.2,Option.map_some]
  have bytes := RawPhysicalCallOutput.Controls.prefix_tail pipeline
  dsimp only [RawPhysicalCallOutput.Controls.reached] at bytes
  dsimp only [output]
  rw [bytes.1,bytes.2.1,bytes.2.2.1]
  rfl

/-- Actual success executes the supplied havoc and retains both ordered logs. -/
theorem success_run (pipeline : Pipeline) :
    (run pipeline (.success [17,255])).map (fun result =>
      ((result.observed.effects.execution.world.accounts (addr 1)).storage.read countPath,
        result.observed.effects.logs,result.observed.effects.returndata,result.observed.trace))=
      some (some seven,[World.Checks.l0,World.Checks.l4],[17,255],
        [.log World.Checks.l0,.log World.Checks.l4]) := by
  rw [full_run]
  rfl

/-- The actual preflight rejects a value-bearing call under a static parent. -/
theorem static_refusal (pipeline : Pipeline) :
    World.callAdapter World.TargetMemory.port (invoke (.success [17,255])) entry
      (frameBytes (stored pipeline)) {parent with static:=true} .call (addr 3)
      (Source.toWord 100) (Source.toWord 1)
      (P6ByteMemory.wireWord (input pipeline).offset) (P6ByteMemory.wireWord (input pipeline).length)
      (P6ByteMemory.wireWord (output pipeline).offset) (P6ByteMemory.wireWord (output pipeline).length)=none :=
  World.callAdapter_static_value_refusal _ _ _ _ _ _ _ _ _ _ _ _ rfl (by decide)

theorem rollback_not_success : (some eight : Option (Source.Val D₀ (.int Source.IntTy.u256)))≠some seven := by
  intro same
  injection same with values
  injection values with integers
  omega
end Solidity.Yul.Adapters.RawPhysicalCallFrame.Controls
