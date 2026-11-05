import Solidity.Lowering.G19.ReturnPair
import Solidity.Backend.StructuredFlow.ReturnTailCompilerControls

namespace Solidity.Lowering.G19.ReturnPair.Controls
open Solidity.Lowering.V07
open Solidity.Source.SemanticsExamples (G0 F0)
open Solidity.Backend.StructuredFlow.MappedCondition.Controls (C)
open Solidity.Backend.StructuredFlow.ConditionalSourceCompiler.Controls (TargetCtx mapping Rel sci sca tci tca)
open Solidity.Backend.StructuredFlow.ReturnTailCompiler.Controls (source caller initial)

theorem joined (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag : Bool) :
    (Source.execS (G0 pipeline) F0 (fuel+8) 0 none (M := false)
      (statement (k := ⟨false,false⟩) sci sca sci .here sca sci) (source flag).1).run
      (.nil,(source flag).2) =
      (.ok (if flag then Source.Out.ret (sourceAfter (source flag) sci flag sci .here sca sci).1
        else Source.Out.normal (sourceAfter (source flag) sci flag sci .here sca sci).1),(.nil,(source flag).2)) ∧
    (code (C := C) tci tca tci .here tca tci).run (caller flag) =
      .ok ⟨reached (caller flag) tci flag tci .here tca tci,List.prefix_refl _⟩ ∧
    (mapping.wk (Thin.drop (t := .val .bool) .refl)).Related Rel
      (sourceAfter (source flag) sci flag sci .here sca sci).1
      (reached (caller flag) tci flag tci .here tca tci).env := by
  rcases correct (G0 pipeline) F0 fuel 0 none (M := false) (k := ⟨false,false⟩)
    (source flag) (caller flag) mapping Rel (initial flag) (fun _ _ h => h)
    sci sca sci .here sca sci tci tca tci .here tca tci rfl rfl rfl rfl rfl rfl with
    ⟨src,typed,related,_,_⟩
  exact ⟨src,typed,related⟩

def observe (program : Prog C TargetCtx (.val .bool :: TargetCtx)) (flag : Bool) : Option (List Bool) :=
  match program.run (caller flag) with
  | .ok out => some [TEnv.get .here out.st.env,TEnv.get (.there .here) out.st.env,
      TEnv.get (.there (.there .here)) out.st.env,TEnv.get (.there (.there (.there .here))) out.st.env]
  | _ => none

theorem observed (flag : Bool) :
    observe (code (C := C) tci tca tci .here tca tci) flag = some [flag,!flag,true,true] := by
  unfold observe
  rw [(joined .legacy 0 flag).2.1]
  cases flag <;> rfl

theorem stale_second_donor_refused :
    observe (code (C := C) tci tca tci .here tca tca) false ≠
      observe (code (C := C) tci tca tci .here tca tci) false := by
  rw [observed]
  unfold observe
  rw [target_run (caller false) tci tca false tci .here tca tca rfl]
  change some [false,true,true,false] ≠ (some [false,true,true,true] : Option (List Bool))
  decide

theorem omitted_second_refused :
    observe (ReturnTail.code (C := C) tci tca tci .here) false ≠
      observe (code (C := C) tci tca tci .here tca tci) false := by
  rw [observed]
  unfold observe
  rw [ReturnTail.target_run (caller false) tci tca false tci .here rfl]
  change some [false,true,true,false] ≠ (some [false,true,true,true] : Option (List Bool))
  decide

theorem captured_false_caller_true :
    TEnv.get .here (reached (caller false) tci false tci .here tca tci).env = false ∧
    TEnv.get (.there (.there .here)) (reached (caller false) tci false tci .here tca tci).env = true := by
  decide

end Solidity.Lowering.G19.ReturnPair.Controls
