import Solidity.Yul.Views.RetainedLocalAlias
import Solidity.Yul.Views.RetainedTupleControls

/-! Overwriting a dormant incoming alias retains its old path in capture even
though both final locals and the return name a different child. No successful
historical index event or current ancestor bound is fabricated. -/
namespace Solidity.Yul.Views.Controls
open Solidity.Backend.MemoryOps
open RetainedLocalAlias

def raGlobals (pipeline : Roadmap.Pipeline) : Source.Glob agEnv :=
  ⟨{body:=fun _=>none,consts:=fun _=>none,inits:=fun _=>[],ctor:=fun _=>none,
    ctorLocals:=fun _=>[],baseArgs:=fun _=>[],contracts:=[]},
    (match pipeline with | .legacy=>.legacy | .viaIR=>.viaIR),
    ⟨Roadmap.Evm.withKeccak,fun bal _ a=>bal a,1,0⟩,
    fun _=>⟨0,by decide⟩,fun _ _=>true,fun _=>.answer (.success []),⟨0,by decide⟩⟩

def raState : Source.EMState agEnv [agAliasTy,agAliasTy] :=
  (.cons (.storRef (by rfl) (agInner 1)) (.cons (.storRef (by rfl) (agInner 0)) .nil),agShrink.2.2)
def raAfter : Source.EMState agEnv [agAliasTy,agAliasTy] :=
  (raState.1.set .here (raState.1.get (.there .here)),raState.2)
def raCaptured (pipeline : Roadmap.Pipeline) := captureEvaluatedValue (raGlobals pipeline) packedStepFrame 2
  (sourceLocalAlias .here (.there .here)) [] raState

theorem ra_actual (pipeline : Roadmap.Pipeline) :
    (raCaptured pipeline).1=(.ok (Source.Val.storRef (τ:=agAliasTy) (by rfl) (agInner 0)),raAfter) := by
  rw [raCaptured,RetainedLocalAlias.captured]
  rfl

/-- Scope multiplicity remains visible; the finite visit union is duplicate-safe. -/
theorem ra_scopes (pipeline : Roadmap.Pipeline) : scopedEntryIndices rhLayout (raCaptured pipeline).2=[1,0,0,0,0] := by
  rw [raCaptured,RetainedLocalAlias.captured]
  rfl

theorem ra_visits (pipeline : Roadmap.Pipeline) : capturedVisitIndices rhLayout [] (raCaptured pipeline).2 0=[1,0] := by
  rw [capturedVisitIndices,ra_scopes]
  rfl

/-- Scanning only final locals loses the overwritten child1 alias. -/
theorem ra_final_only : capturedVisitIndices rhLayout [] [entryLocalScope packedStepFrame raAfter.1] 0=[0] := rfl

theorem ra_loss (pipeline : Roadmap.Pipeline) :
    capturedVisitIndices rhLayout [] [entryLocalScope packedStepFrame raAfter.1] 0≠
      capturedVisitIndices rhLayout [] (raCaptured pipeline).2 0 := by
  rw [ra_final_only,ra_visits]
  decide

theorem ra_outer_zero : (Source.readLen packedStepFrame agPath).run raState=(.ok 0,raState) := rfl

/-- RefOK is static path typing, not evidence of a successful runtime index. -/
theorem ra_initial_safe : Source.MemOK agEnv agState.2.heap.ty raState := by
  refine ⟨⟨⟨ag_alias_MemOK.1.1.heap,ag_alias_MemOK.1.1.le⟩,?_⟩,ag_alias_MemOK.2⟩
  exact ⟨rfl,rfl,trivial⟩

theorem ra_typed (pipeline : Roadmap.Pipeline) : agEnv.pathTy (agInner 0)=some agAliasTy ∧
    raAfter.1.get .here=Source.Val.storRef (τ:=agAliasTy) (by rfl) (agInner 0) ∧
    ⟨packedStepFrame.this,[agInner 0]⟩ ∈ (raCaptured pipeline).2 :=
  typed_return (raGlobals pipeline) packedStepFrame 0 raState .here (.there .here) [] _ ra_initial_safe rfl (agInner 0) rfl

theorem ra_store_identity : raAfter.2=raState.2 := rfl

/-- Late halt keeps the actual assignment and both pre-overwrite observations. -/
theorem ra_late_halt (pipeline : Roadmap.Pipeline) :
    let out := captureValueBindRun packedStepFrame [] (value (raGlobals pipeline) packedStepFrame 0 .here (.there .here))
      (fun _ => Source.EM.halt (.revert [0xde,0xad]) : Source.Val agEnv.layout agAliasTy → Source.EM agEnv [agAliasTy,agAliasTy] (Source.Val agEnv.layout agAliasTy)) raState
    out.1=(.error (.revert [0xde,0xad]),raAfter) ∧
      ⟨packedStepFrame.this,[agInner 0]⟩ ∈ out.2 ∧ entryLocalScope packedStepFrame raState.1 ∈ out.2 :=
  late_halt (raGlobals pipeline) packedStepFrame 0 raState .here (.there .here) [] (.revert [0xde,0xad])

/-- Account tags prevent reinterpreting captured aliases in another account. -/
theorem ra_wrong_account (pipeline : Roadmap.Pipeline) :
    capturedVisitIndices rhLayout []
      (captureEvaluatedValue (raGlobals pipeline) {packedStepFrame with this:=2} 2
        (sourceLocalAlias .here (.there .here)) [] raState).2 0=[] := by
  rw [RetainedLocalAlias.captured]
  rfl
end Solidity.Yul.Views.Controls
