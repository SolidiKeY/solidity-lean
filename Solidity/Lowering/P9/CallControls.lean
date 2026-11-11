import Solidity.Lowering.P9.ElaboratedCalls

/-! Scoped actual source call progress and finite-horizon controls. A timeout
at zero is not divergence, and these are not external ABI/EVM observations. -/
namespace Solidity.Lowering.P9
open Source Roadmap

def caller : Source.Fr :=
  {this := ⟨0, by decide⟩, sender := ⟨1, by decide⟩, value := ⟨0, by decide⟩, static := false, contract := "P9"}

def call : Source.RExpr resolution.env [] .bool := .call declaration signature .nil

theorem source_profile : Source.InProfileSyntax resolution := rfl

/-- Actual new CallsOK feeds the published all-horizon source progress law.
NS excludes stuck only: it does not erase reverts/timeouts or prove termination. -/
theorem call_not_stuck (fixed : Roadmap.Fixed) (n : Nat) :
    Source.NS (Source.evalE (glob fixed) caller n call) :=
  Source.evalE_callFrag_ns (callsOK fixed) caller rfl n call ⟨rfl, trivial⟩ trivial

theorem internal_success (fixed : Roadmap.Fixed) (s : Source.St resolution.env) :
    (Source.callInternal (glob fixed) caller 10 declaration (ps := []) .nil [.bool]).run (.nil, s) =
      (.ok (.val (.bool true)), (.nil, s)) := by
  rw [Source.callInternal, show caller.contract = "P9" from rfl, dispatch_eq,
    show (glob fixed).prog.body declaration = some body from prog_body]
  rfl

theorem internal_zero (fixed : Roadmap.Fixed) (s : Source.St resolution.env) :
    (Source.callInternal (glob fixed) caller 0 declaration (ps := []) .nil [.bool]).run (.nil, s) =
      (.error .timeout, (.nil, s)) := rfl

/-- A requested uint8 return frame is not this compiled Boolean frame. This
is an invalid call-frame control, not a new admitted source execution. -/
theorem wrong_return_frame (fixed : Roadmap.Fixed) (s : Source.St resolution.env) :
    (Source.callInternal (glob fixed) caller 10 declaration (ps := []) .nil [.int Source.IntTy.u8]).run (.nil, s) =
      (.error (.stuck "call frame"), (.nil, s)) := by
  rw [Source.callInternal, show caller.contract = "P9" from rfl, dispatch_eq,
    show (glob fixed).prog.body declaration = some body from prog_body]
  rfl

theorem wrong_post (fixed : Roadmap.Fixed) (s : Source.St resolution.env) :
    (Source.callInternal (glob fixed) caller 10 declaration (ps := []) .nil [.bool]).run (.nil, s) ≠
      (.ok (.val (.bool false)), (.nil, s)) := by
  rw [internal_success]
  intro h
  cases h

theorem success_not_timeout (fixed : Roadmap.Fixed) (s : Source.St resolution.env) :
    (Source.callInternal (glob fixed) caller 10 declaration (ps := []) .nil [.bool]).run (.nil, s) ≠
      (.error .timeout, (.nil, s)) := by
  rw [internal_success]
  intro h
  cases h

def protectedCall : Source.RExpr resolution.env [.bool] .bool := .call declaration signature .nil

theorem protected_not_stuck (fixed : Roadmap.Fixed) (n : Nat) :
    Source.NS (Source.evalE (glob fixed) caller n protectedCall) :=
  Source.evalE_callFrag_ns (callsOK fixed) caller rfl n protectedCall ⟨rfl, trivial⟩ trivial

/-- Complete caller locals and state survive the actual internal-call phase.
This is source execution only; no ABI-decode or external-call phase is inferred. -/
theorem protected_success (fixed : Roadmap.Fixed) (s : Source.St resolution.env) :
    (Source.evalE (glob fixed) caller 11 protectedCall).run (.cons (.bool false) .nil, s) =
      (.ok (.val (.bool true)), (.cons (.bool false) .nil, s)) := by
  unfold protectedCall
  rw [Source.evalE]
  simp only [Source.withLibraryCalldata, Source.evalConvArgs, pure_bind]
  unfold Source.EM.sub
  dsimp only [Bind.bind, Pure.pure, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, StateT.bind, StateT.pure]
  have hx := internal_success fixed s
  dsimp only [ExceptT.run] at hx
  rw [hx]
  rfl

theorem wrong_caller_local (fixed : Roadmap.Fixed) (s : Source.St resolution.env) :
    (Source.evalE (glob fixed) caller 11 protectedCall).run (.cons (.bool false) .nil, s) ≠
      (.ok (.val (.bool true)), (.cons (.bool true) .nil, s)) := by
  rw [protected_success]
  intro h
  cases h

#print axioms protected_success

#print axioms call_not_stuck
#print axioms internal_success
#print axioms wrong_return_frame
end Solidity.Lowering.P9
