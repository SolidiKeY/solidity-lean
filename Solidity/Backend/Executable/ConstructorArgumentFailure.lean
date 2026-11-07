import Solidity.Backend.Executable.ConstructorBaseArgumentControls

/-! Effectful local-argument failure at the native constructor boundary.
The inner local mutation is visible in evalConvArgs, but EM.sub drops the failed
inner frame. Exact Source panic bytes and original outer state are retained.
No World rollback, admitted-program lowering or EVM execution is inferred. -/
namespace Solidity.Backend.Executable.ConstructorArgumentFailure
open Solidity Source Solidity.Backend.Executable.ConstructorBaseArguments
open Solidity.Backend.Executable.ConstructorBaseArgumentControls

def failingCaller : Locals E.layout (contexts "Derived") :=
  caller.set (.there .here) (.int (-32768) (by decide))
def innerAfter : Locals E.layout (contexts "Derived") :=
  failingCaller.set .here (.int 0 (by decide))
def effectfulArgs : RConvArgs E (contexts "Derived") [.int IntTy.u8,.int signed16] :=
  .cons (.assign (.local .here) (.unary .bitNot (.local .here))) (by decide)
    (.cons (.unary .neg (.local (.there .here))) (by decide) .nil)
def failingBase : RBaseArg E (contexts "Derived") :=
  ⟨"Base",[.int IntTy.u8,.int signed16],effectfulArgs⟩
def initialFailure (p : Roadmap.Pipeline) : CtorLocals (global p) :=
  [⟨"Derived",failingCaller⟩]

def failedProgram : Program E :=
  { program with baseArgs := fun name => if h : name = "Derived" then h.symm ▸ [failingBase] else [] }
def failedGlobal (p : Roadmap.Pipeline) : Glob E := { global p with prog := failedProgram }

/-- Exact producer for the failure used below: first argument changes a local,
then checked negation overflows. This is not a desired-run premise. -/
theorem run_inner :
∀ p : Solidity.Roadmap.Pipeline,
 (Solidity.Source.evalConvArgs
  (Solidity.Backend.Executable.ConstructorBaseArgumentControls.global p)
  Solidity.Backend.Executable.ConstructorBaseArgumentControls.frame 4
  Solidity.Backend.Executable.ConstructorArgumentFailure.effectfulArgs).run
  (Solidity.Backend.Executable.ConstructorArgumentFailure.failingCaller,
   Solidity.Backend.Executable.ConstructorBaseArgumentControls.state) =
 (.error (.revert (Solidity.Source.panicData .arithmetic)),
  (Solidity.Backend.Executable.ConstructorArgumentFailure.innerAfter,
   Solidity.Backend.Executable.ConstructorBaseArgumentControls.state)) := by
  intro p
  cases p <;> rfl

/-- Native failure composition, preserving the original halt and returned
state, while dropping only the inner local frame. No EVM simulation assertion. -/
theorem transport_failure :
∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr)
 (n : Nat) (derived : String) (l l' : Solidity.Source.Locals E.layout (G.prog.ctorLocals derived))
 (ba : Solidity.Source.RBaseArg E (G.prog.ctorLocals derived))
 (rest : List (Solidity.Source.RBaseArg E (G.prog.ctorLocals derived)))
 (acc : Solidity.Source.CtorLocals G) (s s' : Solidity.Source.St E) (halt : Solidity.Source.Halt)
 (absent : acc.any (fun entry => entry.1 == ba.base) = false)
 (failed : (Solidity.Source.evalConvArgs G F n ba.args).run (l,s) = (.error halt,(l',s'))),
 (Solidity.Source.giveArgs G F n derived l (ba :: rest) acc).run (Solidity.Source.L0 E,s) =
 (.error halt,(Solidity.Source.L0 E,s')) := by
  intro E G F n derived l lnext ba rest acc s snext halt absent failed
  have raw : (Source.evalConvArgs G F n ba.args) (l,s) =
      (.error halt,(lnext,snext)) := failed
  have subRun : (Source.EM.sub (Γ := []) l (Source.evalConvArgs G F n ba.args)).run
      (Source.L0 E,s) = (.error halt,(Source.L0 E,snext)) := by
    simp only [Source.EM.sub,ExceptT.run,ExceptT.mk,raw]
  simp only [Source.giveArgs,absent,Bool.false_eq_true,if_false,
    Source.Hoare.run_bind,subRun]

theorem giveArgs_failed :
∀ p : Roadmap.Pipeline,
 (Source.giveArgs (global p)
  frame 4 "Derived"
  failingCaller
  [failingBase]
  (initialFailure p)).run
  (Source.L0 E,
   state) =
 (.error (.revert (Source.panicData .arithmetic)),
  (Source.L0 E,
   state)) := by
  intro p
  exact transport_failure (global p) frame 4 "Derived" failingCaller innerAfter
    failingBase [] (initialFailure p) state state (.revert (panicData .arithmetic))
    rfl (run_inner p)

theorem constructor_controls :
∀ p : Roadmap.Pipeline,
 (Source.construct (failedGlobal p)
  frame 4 "Derived"
  failingCaller).run
  (Source.L0 E,
   state) =
 (.error (.revert (Source.panicData .arithmetic)),
  (Source.L0 E,
   state)) ∧
 (Source.giveArgs (global p)
  frame 4 "Derived"
  failingCaller
  [failingBase]
  (reached p)).run
  (Source.L0 E,
   state) =
 (.ok (reached p),
  (Source.L0 E,
   state)) ∧
 (innerAfter.get .here).key = some 0 ∧
 (failingCaller.get .here).key = some 255 ∧
 Source.panicData .arithmetic ≠ Source.panicData .divZero := by
  intro p
  cases p <;> exact ⟨rfl,rfl,rfl,rfl,by decide⟩

end Solidity.Backend.Executable.ConstructorArgumentFailure
