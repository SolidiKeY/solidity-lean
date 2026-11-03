import Solidity.Lowering.V08.SourceEmit

/-! Actual published callable execution boundaries. Individual zero/body/argument
step equations are explicit; no target preservation, compiler or modifier/body
lowering is assumed. Source frame locals are distinct from caller monad locals. -/
namespace Solidity.Lowering.V08.SourceCallable
open Solidity Source

theorem zero_horizon {E : Source.Env} {ps rs : List STy} (global : Glob E) (frame : Fr)
    (declaration : Decl) (values : Source.Vals E.layout ps) (state : Source.St E) :
    (Source.callInternal global frame 0 declaration values rs).run (Source.L0 E,state) =
      (.error .timeout,(Source.L0 E,state)) := rfl

theorem missing_body {E : Source.Env} {ps rs : List STy} (global : Glob E) (frame : Fr)
    (horizon : Nat) (declaration : Decl) (values : Source.Vals E.layout ps) (state : Source.St E)
    (missing : global.prog.body (global.dispatchFn frame.contract declaration) = none) :
    (Source.callInternal global frame (horizon+1) declaration values rs).run (Source.L0 E,state) =
      (.error (.stuck "function without a body"),(Source.L0 E,state)) := by
  simp only [Source.callInternal, missing, pure, ExceptT.run, ExceptT.mk, StateT.pure, Source.EM.halt, throw, throwThe, MonadExceptOf.throw]

theorem complete {E : Source.Env} {ps rs : List STy} (global : Glob E) (frame : Fr)
    (horizon : Nat) (declaration : Decl) (values : Source.Vals E.layout ps) (body : RBody E)
    (selected : global.prog.body (global.dispatchFn frame.contract declaration) = some body)
    (zero : Source.Vals E.layout rs)
    (fits : rs.reverseAux (ps.reverseAux []) = body.locals)
    (returned : Source.Locals E.layout body.locals) (outputs : RVals E.layout rs)
    (state initialized final : Source.St E)
    (initialization : (Source.zeroVals horizon rs : Source.EM E [] _).run (Source.L0 E,state) =
      (.ok zero,(Source.L0 E,initialized)))
    (execution : (Source.runMods global {frame with checked:=true} horizon body body.mods
      (fits ▸ zero.onto (values.onto (Source.L0 E)))).run (Source.L0 E,initialized) =
      (.ok returned,(Source.L0 E,final)))
    (extraction : Source.retVals returned 0 rs = .ok outputs) :
    (Source.callInternal global frame (horizon+1) declaration values rs).run (Source.L0 E,state) =
      (.ok (Source.mkRet rs outputs),(Source.L0 E,final)) := by
  simp only [ExceptT.run] at initialization execution
  simp only [Source.callInternal, selected, dif_pos fits, bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure, Source.EM.halt, Source.EM.lift, throw, throwThe, MonadExceptOf.throw, initialization, execution, extraction]

theorem body_failure {E : Source.Env} {ps rs : List STy} (global : Glob E) (frame : Fr)
    (horizon : Nat) (declaration : Decl) (values : Source.Vals E.layout ps) (body : RBody E)
    (selected : global.prog.body (global.dispatchFn frame.contract declaration) = some body)
    (zero : Source.Vals E.layout rs) (fits : rs.reverseAux (ps.reverseAux []) = body.locals)
    (state initialized final : Source.St E) (halt : Source.Halt)
    (initialization : (Source.zeroVals horizon rs : Source.EM E [] _).run (Source.L0 E,state) =
      (.ok zero,(Source.L0 E,initialized)))
    (execution : (Source.runMods global {frame with checked:=true} horizon body body.mods
      (fits ▸ zero.onto (values.onto (Source.L0 E)))).run (Source.L0 E,initialized) =
      (.error halt,(Source.L0 E,final))) :
    (Source.callInternal global frame (horizon+1) declaration values rs).run (Source.L0 E,state) =
      (.error halt,(Source.L0 E,final)) := by
  simp only [ExceptT.run] at initialization execution
  simp only [Source.callInternal, selected, dif_pos fits, bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure, Source.EM.halt, Source.EM.lift, throw, throwThe, MonadExceptOf.throw, initialization, execution]

theorem wrong_frame {E : Source.Env} {ps rs : List STy} (global : Glob E) (frame : Fr)
    (horizon : Nat) (declaration : Decl) (values : Source.Vals E.layout ps) (body : RBody E)
    (selected : global.prog.body (global.dispatchFn frame.contract declaration) = some body)
    (zero : Source.Vals E.layout rs) (wrong : rs.reverseAux (ps.reverseAux []) ≠ body.locals)
    (state initialized : Source.St E)
    (initialization : (Source.zeroVals horizon rs : Source.EM E [] _).run (Source.L0 E,state) =
      (.ok zero,(Source.L0 E,initialized))) :
    (Source.callInternal global frame (horizon+1) declaration values rs).run (Source.L0 E,state) =
      (.error (.stuck "call frame"),(Source.L0 E,initialized)) := by
  simp only [ExceptT.run] at initialization
  simp only [Source.callInternal, selected, dif_neg wrong, bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure, Source.EM.halt, Source.EM.lift, throw, throwThe, MonadExceptOf.throw, initialization]

theorem expression_complete {E : Source.Env} {Γ : RCtx} {ps rs : List STy}
    (global : Glob E) (frame : Fr) (horizon : Nat) (declaration : Decl)
    (signature : declaration.fnSig E = some (ps,rs)) (args : RConvArgs E Γ ps)
    (locals afterArgs : Source.Locals E.layout Γ) (values : Source.Vals E.layout ps)
    (result : RVal E.layout (STy.ret rs)) (state reached final : Source.St E)
    (arguments : (Source.evalConvArgs global frame horizon args).run (locals,state) =
      (.ok values,(afterArgs,reached)))
    (callee : (Source.callInternal global frame horizon declaration values rs).run
      (Source.L0 E,reached) = (.ok result,(Source.L0 E,final))) :
    (Source.evalE global frame (horizon+1) (.call declaration signature args)).run (locals,state) =
      (.ok result,(afterArgs,final)) := by
  simp only [ExceptT.run] at arguments callee
  simp only [Source.evalE, Source.EM.sub, bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure, arguments, callee]

theorem expression_failure {E : Source.Env} {Γ : RCtx} {ps rs : List STy}
    (global : Glob E) (frame : Fr) (horizon : Nat) (declaration : Decl)
    (signature : declaration.fnSig E = some (ps,rs)) (args : RConvArgs E Γ ps)
    (locals afterArgs : Source.Locals E.layout Γ) (values : Source.Vals E.layout ps)
    (state reached final : Source.St E) (halt : Source.Halt)
    (arguments : (Source.evalConvArgs global frame horizon args).run (locals,state) =
      (.ok values,(afterArgs,reached)))
    (callee : (Source.callInternal global frame horizon declaration values rs).run
      (Source.L0 E,reached) = (.error halt,(Source.L0 E,final))) :
    (Source.evalE global frame (horizon+1) (.call declaration signature args)).run (locals,state) =
      (.error halt,(afterArgs,final)) := by
  simp only [ExceptT.run] at arguments callee
  simp only [Source.evalE, Source.EM.sub, bind, pure, ExceptT.bind, ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure, arguments, callee]

theorem argument_failure {E : Source.Env} {Γ : RCtx} {ps rs : List STy}
    (global : Glob E) (frame : Fr) (horizon : Nat) (declaration : Decl)
    (signature : declaration.fnSig E = some (ps,rs)) (args : RConvArgs E Γ ps)
    (locals afterArgs : Source.Locals E.layout Γ) (state final : Source.St E) (halt : Source.Halt)
    (arguments : (Source.evalConvArgs global frame horizon args).run (locals,state) =
      (.error halt,(afterArgs,final))) :
    (Source.evalE global frame (horizon+1) (.call declaration signature args)).run (locals,state) =
      (.error halt,(afterArgs,final)) := by
  simp only [ExceptT.run] at arguments
  simp only [Source.evalE, bind, pure, ExceptT.bind, ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure, arguments]

#print axioms zero_horizon
#print axioms missing_body
#print axioms complete
#print axioms body_failure
#print axioms wrong_frame
#print axioms expression_complete
#print axioms expression_failure
#print axioms argument_failure
end Solidity.Lowering.V08.SourceCallable
