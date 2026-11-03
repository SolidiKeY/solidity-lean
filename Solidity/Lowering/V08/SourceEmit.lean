import Solidity.Lowering.V08.SourceKeccak

/-! Actual source emit boundaries. These are step-composition laws over the
published evaluator, not a replacement interpreter or SourceSpec adequacy.
Argument and encoding premises concern individual actual executions. -/
namespace Solidity.Lowering.V08.SourceEmit
open Solidity Source

def logged {E : Source.Env} (global : Glob E) (frame : Fr) (event : Decl)
    (types : List STy) (bytes : Roadmap.Bytes) (state : Source.St E) : Source.St E :=
  { state with logs := (frame.this, global.selector (sigOf E.layout event.name types) ++ bytes) :: state.logs }

/-- The approved log-erasure observation retains every other machine field. -/
def eraseLogs {E : Source.Env} (state : Source.St E) : Source.St E :=
  { state with logs := [] }

theorem logged_erasure {E : Source.Env} (global : Glob E) (frame : Fr) (event : Decl)
    (types : List STy) (bytes : Roadmap.Bytes) (state : Source.St E) :
    eraseLogs (logged global frame event types bytes state) = eraseLogs state := rfl

theorem exec_success {E : Source.Env} {Γ : RCtx} {types : List STy}
    (global : Glob E) (frame : Fr) (horizon : Nat) (event : Decl)
    (typed : event.paramTys E = some types) (args : RConvArgs E Γ types)
    (locals next : Source.Locals E.layout Γ) (state middle final : Source.St E)
    (values : Source.Vals E.layout types) (bytes : Roadmap.Bytes)
    (arguments : (Source.evalConvArgs global frame horizon args).run (locals,state) =
      (.ok values,(next,middle)))
    (encoding : (Source.encodeVals frame horizon false values.toR : Source.EM E [] _).run
      (Source.L0 E,middle) = (.ok bytes,(Source.L0 E,final)))
    (nonstatic : frame.static = false) :
    (Source.execS global frame (horizon+1) 0 none
      (.emit event typed args : RStmt E [] false .body Γ Γ) locals).run
      (Source.L0 E,state) =
      (.ok (.normal next),(Source.L0 E,logged global frame event types bytes final)) := by
  simp only [ExceptT.run] at arguments encoding
  simp only [Source.execS, Source.EM.sub, Source.EM.modSt, bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure, StateT.modifyGet, modify, modifyGet, MonadStateOf.modifyGet, monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, StateT.map, arguments, encoding, nonstatic, logged, Bool.false_eq_true, ↓reduceIte]

theorem exec_static {E : Source.Env} {Γ : RCtx} {types : List STy}
    (global : Glob E) (frame : Fr) (horizon : Nat) (event : Decl)
    (typed : event.paramTys E = some types) (args : RConvArgs E Γ types)
    (locals next : Source.Locals E.layout Γ) (state middle final : Source.St E)
    (values : Source.Vals E.layout types) (bytes : Roadmap.Bytes)
    (arguments : (Source.evalConvArgs global frame horizon args).run (locals,state) =
      (.ok values,(next,middle)))
    (encoding : (Source.encodeVals frame horizon false values.toR : Source.EM E [] _).run
      (Source.L0 E,middle) = (.ok bytes,(Source.L0 E,final)))
    (static : frame.static = true) :
    (Source.execS global frame (horizon+1) 0 none
      (.emit event typed args : RStmt E [] false .body Γ Γ) locals).run
      (Source.L0 E,state) = (.error (.revert []),(Source.L0 E,final)) := by
  simp only [ExceptT.run] at arguments encoding
  simp only [Source.execS, Source.EM.sub, Source.EM.modSt, Source.EM.halt, bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, throw, MonadExceptOf.throw, throwThe, arguments, encoding, static, ↓reduceIte]

theorem exec_argument_failure {E : Source.Env} {Γ : RCtx} {types : List STy}
    (global : Glob E) (frame : Fr) (horizon : Nat) (event : Decl)
    (typed : event.paramTys E = some types) (args : RConvArgs E Γ types)
    (locals next : Source.Locals E.layout Γ) (state final : Source.St E) (halt : Source.Halt)
    (arguments : (Source.evalConvArgs global frame horizon args).run (locals,state) =
      (.error halt,(next,final))) :
    (Source.execS global frame (horizon+1) 0 none
      (.emit event typed args : RStmt E [] false .body Γ Γ) locals).run
      (Source.L0 E,state) = (.error halt,(Source.L0 E,final)) := by
  simp only [ExceptT.run] at arguments
  simp only [Source.execS, Source.EM.sub, bind, pure, ExceptT.bind, ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure, arguments]

theorem exec_encoding_failure {E : Source.Env} {Γ : RCtx} {types : List STy}
    (global : Glob E) (frame : Fr) (horizon : Nat) (event : Decl)
    (typed : event.paramTys E = some types) (args : RConvArgs E Γ types)
    (locals next : Source.Locals E.layout Γ) (state middle final : Source.St E)
    (values : Source.Vals E.layout types) (halt : Source.Halt)
    (arguments : (Source.evalConvArgs global frame horizon args).run (locals,state) =
      (.ok values,(next,middle)))
    (encoding : (Source.encodeVals frame horizon false values.toR : Source.EM E [] _).run
      (Source.L0 E,middle) = (.error halt,(Source.L0 E,final))) :
    (Source.execS global frame (horizon+1) 0 none
      (.emit event typed args : RStmt E [] false .body Γ Γ) locals).run
      (Source.L0 E,state) = (.error halt,(Source.L0 E,final)) := by
  simp only [ExceptT.run] at arguments encoding
  simp only [Source.execS, Source.EM.sub, bind, pure, ExceptT.bind, ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure, arguments, encoding]

/-- Published static ABI layout retains all three words in order. -/
theorem three_static (first second third : Roadmap.Bytes) :
    Source.abiLayout [(false,first),(false,second),(false,third)] = first ++ (second ++ third) := by
  simp only [Source.abiLayout, Source.abiLayout.go, List.append_nil]

/-- The independent source encoding agrees byte-for-byte with the existing
intrinsic word observer, without claiming a canonical argument/layout relation. -/
theorem three_words_transport (first second third : Roadmap.Word) :
    Source.abiLayout [(false,Source.wordBytes first),(false,Source.wordBytes second),
      (false,Source.wordBytes third)] =
      Semantics.wordBytes first.val ++ (Semantics.wordBytes second.val ++ Semantics.wordBytes third.val) := by
  rw [three_static,wordBytes_transport,wordBytes_transport,wordBytes_transport]

theorem logged_payload_injective {E : Source.Env} (global : Glob E) (frame : Fr) (event : Decl)
    (types : List STy) (left right : Roadmap.Bytes) (state : Source.St E)
    (same : logged global frame event types left state = logged global frame event types right state) :
    left = right := by
  have first := congrArg (fun s : Source.St E => s.logs.head?.map Prod.snd) same
  change some (global.selector (sigOf E.layout event.name types) ++ left) =
    some (global.selector (sigOf E.layout event.name types) ++ right) at first
  exact List.append_cancel_left (Option.some.inj first)

#print axioms logged_payload_injective

#print axioms three_static
#print axioms three_words_transport

#print axioms logged_erasure
#print axioms exec_success
#print axioms exec_static
#print axioms exec_argument_failure
#print axioms exec_encoding_failure
end Solidity.Lowering.V08.SourceEmit
