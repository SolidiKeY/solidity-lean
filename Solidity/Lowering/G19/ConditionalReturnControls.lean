import Solidity.Lowering.G19.ConditionalReturn
import Solidity.Backend.StructuredFlow.ReturnTailCompilerControls

namespace Solidity.Lowering.G19.ConditionalReturn.Controls
open Solidity.Lowering.V07
open Source.SemanticsExamples (G0 F0)
open Solidity.Backend.StructuredFlow.MappedCondition.Controls (C)
open Solidity.Backend.StructuredFlow.ConditionalSourceCompiler.Controls
  (TargetCtx mapping Rel sci sca tci tca)
open Solidity.Backend.StructuredFlow.ReturnTailCompiler.Controls (source caller initial)

theorem joined (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag checked : Bool) :
    (Source.execS (G0 pipeline) {F0 with checked := checked} (fuel+6) 0 none (M := false)
      (statement (k := ⟨false,false⟩) sci sca .here sci sca .here) (source flag).1).run
      (.nil,(source flag).2) =
      (.ok (Source.Out.ret (ConditionalAssignments.sourceAfter (source flag) sci flag .here sci sca .here).1),
        (.nil,(source flag).2)) ∧
    (code (C := C) tci tca .here tci tca .here).run (caller flag) =
      .ok ⟨reached (caller flag) tci flag .here tci tca .here,List.prefix_refl _⟩ ∧
    (mapping.wk (Thin.drop (t := .val .bool) .refl)).Related Rel
      (ConditionalAssignments.sourceAfter (source flag) sci flag .here sci sca .here).1
      (reached (caller flag) tci flag .here tci tca .here).env := by
  rcases correct (G0 pipeline) {F0 with checked := checked} fuel 0 none
    (M := false) (k := ⟨false,false⟩) (source flag) (caller flag) mapping Rel
    (initial flag) (fun _ _ h => h) sci sca .here sci sca .here
    tci tca .here tci tca .here rfl rfl rfl rfl rfl rfl with ⟨src,typed,related,_,_⟩
  exact ⟨src,typed,related⟩

def observe (program : Prog C TargetCtx (.val .bool :: TargetCtx)) (flag : Bool) : Option (List Bool) :=
  match program.run (caller flag) with
  | .ok out => some [TEnv.get .here out.st.env,TEnv.get (.there .here) out.st.env,
      TEnv.get (.there tci) out.st.env,TEnv.get (.there tca) out.st.env]
  | _ => none

theorem observed (flag : Bool) :
    observe (code (C := C) tci tca .here tci tca .here) flag = some [true,true,flag,true] := by
  unfold observe
  rw [target_run (caller flag) tci tca flag .here tci tca .here rfl]
  cases flag <;> rfl

theorem wrong_donor_refused :
    observe (code (C := C) tci tca .here .here tca .here) true ≠
      observe (code (C := C) tci tca .here tci tca .here) true := by
  rw [observed]
  unfold observe
  rw [target_run (caller true) tci tca true .here .here tca .here rfl]
  change some [true,false,true,true] ≠ (some [true,true,true,true] : Option (List Bool))
  decide

def wrongFlag : Prog C TargetCtx (.val .bool :: TargetCtx) :=
  (ConditionalStatement.code tci tca .here tci tca .here).join
    (.cons (.declLocal .bool (.user "bad_return") (some (.simple (.local tci)))) .nil)

theorem wrong_flag_refused :
    observe wrongFlag false ≠ observe (code (C := C) tci tca .here tci tca .here) false := by
  have typed : wrongFlag.run (caller false) =
      .ok ⟨(ConditionalAssignments.targetAfter (caller false) tci false .here tci tca .here).push
        (t := .val .bool) false,List.prefix_refl _⟩ := by
    have prefixRun : (ConditionalStatement.code (C := C) tci tca .here tci tca .here).run (caller false) =
        .ok ⟨ConditionalAssignments.targetAfter (caller false) tci false .here tci tca .here,List.prefix_refl _⟩ :=
      ConditionalStatement.target_run (caller false) tci tca false .here tci tca .here rfl
    unfold Prog.run at prefixRun
    rw [wrongFlag,DeferredSource.join_run]
    unfold TRun.seq
    rw [prefixRun]
    rfl
  rw [observed]
  unfold observe
  rw [typed]
  change some [false,true,false,true] ≠ (some [true,true,false,true] : Option (List Bool))
  decide

theorem return_not_normal (flag : Bool) :
    (Source.execS (G0 .legacy) F0 6 0 none (M := false)
      (statement (k := ⟨false,false⟩) sci sca .here sci sca .here) (source flag).1).run
      (.nil,(source flag).2) ≠
      (.ok (Source.Out.normal (ConditionalAssignments.sourceAfter (source flag) sci flag .here sci sca .here).1),
        (.nil,(source flag).2)) := by
  rw [source_run (G0 .legacy) F0 0 0 none (source flag) sci sca flag .here sci sca .here rfl]
  intro same
  cases same

end Solidity.Lowering.G19.ConditionalReturn.Controls
