import Solidity.Yul.Views.RetainedCallerBoundaries
import Solidity.Yul.Views.RetainedTupleControls

/-! Actual Source.callInternal dispatch/frame/body/return controls reuse the
published typed producer API. Dormant storage aliases survive caller suspension
and setup failures. The constant body override is a concrete typed fixture,
not an assumed implementation of arbitrary calls or recursive capture. -/
namespace Solidity.Yul.Views.Controls
open RetainedCallerBoundaries

def rcbValues : Source.Vals agEnv.layout [agAliasTy] := .cons rtAlias .nil

def rcbBody : Source.RBody agEnv :=
  {ps:=[agAliasTy],rs:=[],inModifier:=false,locals:=[agAliasTy],out:=[agAliasTy],items:=.nil}
def rcbProgram (G : Source.Glob agEnv) : Source.Glob agEnv :=
  {G with prog:={G.prog with body:=fun _=>some rcbBody}}
def rcbBadBody : Source.RBody agEnv :=
  {ps:=[agAliasTy],rs:=[],inModifier:=false,locals:=[],out:=[],items:=.nil}
def rcbBadProgram (G : Source.Glob agEnv) : Source.Glob agEnv :=
  {G with prog:={G.prog with body:=fun _=>some rcbBadBody}}

theorem rcb_actual_success (G : Source.Glob agEnv) (d : Source.Decl) :
    (Source.callInternal (rcbProgram G) packedStepFrame 4 d rcbValues []).run (Source.Locals.nil,agShrink.2.2)=
      (.ok (.tuple .nil),(Source.Locals.nil,agShrink.2.2)) := rfl

theorem rcb_success_caller (G : Source.Glob agEnv) (d : Source.Decl) :
    (captureInternalFromCaller (rcbProgram G) packedStepFrame 4 d rcbValues [] [] agShrink.2).1=
      (.ok (.tuple .nil,Source.Locals.nil),agShrink.2) :=
  (captureInternalFromCaller_success _ _ _ _ _ _ _ _ _ _ (rcb_actual_success G d)).1

theorem rcb_actual_timeout (G : Source.Glob agEnv) (d : Source.Decl) :
    (Source.callInternal G packedStepFrame 0 d rcbValues []).run (Source.Locals.nil,agShrink.2.2)=
      (.error .timeout,(Source.Locals.nil,agShrink.2.2)) := rfl

theorem rcb_timeout_caller (G : Source.Glob agEnv) (d : Source.Decl) :
    (captureInternalFromCaller G packedStepFrame 0 d rcbValues [] [] agShrink.2).1=(.error .timeout,agShrink.2) :=
  halt G packedStepFrame 0 d rcbValues [] [] agShrink.2 _ .timeout (rcb_actual_timeout G d)

theorem rcb_actual_bad_frame (G : Source.Glob agEnv) (d : Source.Decl) :
    (Source.callInternal (rcbBadProgram G) packedStepFrame 4 d rcbValues []).run (Source.Locals.nil,agShrink.2.2)=
      (.error (.stuck "call frame"),(Source.Locals.nil,agShrink.2.2)) := rfl

theorem rcb_bad_frame_caller (G : Source.Glob agEnv) (d : Source.Decl) :
    (captureInternalFromCaller (rcbBadProgram G) packedStepFrame 4 d rcbValues [] [] agShrink.2).1=
      (.error (.stuck "call frame"),agShrink.2) :=
  halt _ _ _ _ _ _ _ _ _ _ (rcb_actual_bad_frame G d)

theorem rcb_timeout_parameters (G : Source.Glob agEnv) (d : Source.Decl) :
    ∃ scope∈(captureInternalFromCaller G packedStepFrame 0 d rcbValues [] [] agShrink.2).2,
      scope.account=packedStepFrame.this ∧ agInner 0∈scope.paths := by
  first | omega | decide | skip
  exact parameter_paths G packedStepFrame 0 d rcbValues [] [] agShrink.2 (agInner 0) (by exact List.mem_cons_self)

theorem rcb_timeout_saved_caller (G : Source.Glob agEnv) (d : Source.Decl) :
    ∃ scope∈(captureInternalFromCaller G packedStepFrame 0 d rcbValues [] [] agShrink.2).2,
      scope.account=packedStepFrame.this ∧ agInner 0∈scope.paths := by
  first | omega | decide | skip
  exact caller_paths G packedStepFrame 0 d rcbValues [] [] agShrink.2 (agInner 0) (by exact List.mem_cons_self)

/-- A correctly typed return-body assignment does not bypass the owner's
pre-body return-local initialization. This pins a Source interface boundary. -/
def rcbReferenceReturnBody : Source.RBody agEnv :=
  {ps:=[agAliasTy],rs:=[agAliasTy],inModifier:=false,locals:=[agAliasTy,agAliasTy],out:=[agAliasTy,agAliasTy],
    items:=.stmt (.expr (.assign (.local .here) (.local (.there .here)))) .nil}
def rcbReferenceReturnProgram (G : Source.Glob agEnv) : Source.Glob agEnv :=
  {G with prog:={G.prog with body:=fun _=>some rcbReferenceReturnBody}}

theorem rcb_reference_return_initialization (G : Source.Glob agEnv) (d : Source.Decl) :
    (Source.callInternal (rcbReferenceReturnProgram G) packedStepFrame 8 d rcbValues [agAliasTy]).run
      (Source.Locals.nil,agShrink.2.2)=
      (.error (.stuck "no default value"),(Source.Locals.nil,agShrink.2.2)) := rfl

theorem rcb_callee_locals_empty : localStoragePaths (Source.Locals.nil : Source.Locals agEnv.layout [])=[] := rfl

theorem rcb_success_dedup (G : Source.Glob agEnv) (d : Source.Decl) :
    capturedVisitIndices rhLayout [] (captureInternalFromCaller (rcbProgram G) packedStepFrame 4 d rcbValues [] [] agShrink.2).2 0=[0] := rfl

theorem rcb_timeout_dedup (G : Source.Glob agEnv) (d : Source.Decl) :
    capturedVisitIndices rhLayout [] (captureInternalFromCaller G packedStepFrame 0 d rcbValues [] [] agShrink.2).2 0=[0] := rfl

/-- Dropping saved caller and parameter scopes would lose this dormant child. -/
theorem rcb_current_only_misses : capturedVisitIndices rhLayout [] [] 0≠[0] := by decide
end Solidity.Yul.Views.Controls
