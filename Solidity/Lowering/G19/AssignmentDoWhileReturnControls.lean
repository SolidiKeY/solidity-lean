import Solidity.Lowering.G19.AssignmentDoWhileReturn
import Solidity.Backend.StructuredFlow.ReturnTailCompilerControls

namespace Solidity.Lowering.G19.AssignmentDoWhileReturn.Controls
open Solidity.Lowering.V07
open Source.SemanticsExamples (G0 F0 E0)
open Solidity.Backend.StructuredFlow.MappedCondition.Controls (C)
open Solidity.Backend.StructuredFlow.ConditionalSourceCompiler.Controls
  (SourceCtx TargetCtx mapping Rel sci sca tci tca)
open Solidity.Backend.StructuredFlow.ReturnTailCompiler.Controls (source caller initial)

theorem joined (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag checked : Bool)
    (condition : Source.RExpr E0 SourceCtx .bool) :
    (Source.execS (G0 pipeline) {F0 with checked := checked} (fuel+6) 0 none (M := false)
      (.doWhile (l := false) (u := false) (body sci sca) condition) (source flag).1).run
      (.nil,(source flag).2) =
      (.ok (Source.Out.ret ((source flag).1.set sci (.bool flag))),(.nil,(source flag).2)) ∧
    (code mapping sci sca rfl rfl : Prog C TargetCtx (.val .bool :: TargetCtx)).run (caller flag) =
      .ok ⟨reached mapping sci sca rfl rfl (caller flag),List.prefix_refl _⟩ ∧
    (mapping.wk (Thin.drop (t := .val .bool) .refl)).Related Rel
      ((source flag).1.set sci (.bool flag)) (reached mapping sci sca rfl rfl (caller flag)).env := by
  rcases correct (G0 pipeline) {F0 with checked := checked} fuel 0 none
    (M := false) (l := false) (u := false) (source flag) (caller flag) mapping Rel
    (initial flag) (fun _ _ h => h) sci sca rfl rfl rfl rfl condition with
    ⟨src,typed,related,_,_⟩
  exact ⟨src,typed,related⟩

def observe (program : Prog C TargetCtx (.val .bool :: TargetCtx)) (flag : Bool) : Option (List Bool) :=
  match program.run (caller flag) with
  | .ok out => some [TEnv.get .here out.st.env,TEnv.get (.there tci) out.st.env,
      TEnv.get (.there tca) out.st.env,TEnv.get (.there .here) out.st.env]
  | _ => none

theorem observed (flag : Bool) :
    observe (code mapping sci sca rfl rfl) flag = some [true,flag,flag,!flag] := by
  unfold observe
  rw [target_run]
  cases flag <;> rfl

/-- Using the body's assigned value as the return flag would lose false-valued returns. -/
theorem wrong_return_flag_refused :
    observe (AssignmentReturnFlag.code mapping sci sca rfl rfl) false ≠
      observe (code mapping sci sca rfl rfl) false := by
  rw [observed]
  change some [false,false,false,true] ≠ (some [true,false,false,true] : Option (List Bool))
  decide

theorem trailing_condition_writes :
    Source.evalE (G0 .legacy) F0 2 (.assign (.local sci) (.bool false)) (plan := none)
      ((source true).1.set sci (.bool true),(source true).2) =
      (.ok (.val (.bool false)),((source true).1.set sci (.bool false),(source true).2)) := by rfl

theorem trailing_write_refused :
    (Source.execS (G0 .legacy) F0 6 0 none (M := false)
      (.doWhile (l := false) (u := false) (body sci sca)
        (.assign (.local sci) (.bool false))) (source true).1).run (.nil,(source true).2) ≠
      (.ok (Source.Out.ret ((source true).1.set sci (.bool false))),(.nil,(source true).2)) := by
  rw [source_run (G0 .legacy) F0 0 0 none (source true).1 (source true).2 sci sca true rfl]
  intro same
  cases same

theorem return_not_normal (flag : Bool) :
    (Source.execS (G0 .legacy) F0 6 0 none (M := false)
      (.doWhile (l := false) (u := false) (body sci sca) (.bool true))
      (source flag).1).run (.nil,(source flag).2) ≠
      (.ok (Source.Out.normal ((source flag).1.set sci (.bool flag))),(.nil,(source flag).2)) := by
  rw [source_run (G0 .legacy) F0 0 0 none (source flag).1 (source flag).2 sci sca flag rfl]
  intro same
  cases same

theorem same_slot (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag checked : Bool)
    (condition : Source.RExpr E0 SourceCtx .bool) :
    (Source.execS (G0 pipeline) {F0 with checked := checked} (fuel+6) 0 none (M := false)
      (.doWhile (l := false) (u := false) (body sca sca) condition) (source flag).1).run
      (.nil,(source flag).2) = (.ok (Source.Out.ret (source flag).1),(.nil,(source flag).2)) ∧
    (code mapping sca sca rfl rfl : Prog C TargetCtx (.val .bool :: TargetCtx)).run (caller flag) =
      .ok ⟨(caller flag).push (t := .val .bool) true,List.prefix_refl _⟩ := by
  have src : (Source.execS (G0 pipeline) {F0 with checked := checked} (fuel+6) 0 none (M := false)
      (.doWhile (l := false) (u := false) (body sca sca) condition) (source flag).1).run (.nil,(source flag).2) =
      (.ok (Source.Out.ret ((source flag).1.set sca (.bool flag))),(.nil,(source flag).2)) := source_run (G0 pipeline) {F0 with checked := checked} fuel 0 none
    (M := false) (l := false) (u := false) (source flag).1 (source flag).2 sca sca flag rfl condition
  have typed : (code mapping sca sca rfl rfl : Prog C TargetCtx (.val .bool :: TargetCtx)).run (caller flag) =
      .ok ⟨reached mapping sca sca rfl rfl (caller flag),List.prefix_refl _⟩ := target_run (C := C) mapping sca sca rfl rfl (caller flag)
  cases flag <;> exact ⟨src,typed⟩

end Solidity.Lowering.G19.AssignmentDoWhileReturn.Controls
