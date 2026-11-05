import Solidity.Yul.RawContinueLoop
import Solidity.Yul.Checks.RawU8ForAbsent
/-! Universal continue-loop horizon controls and a terminating break countercontrol.
Dirty word observations are separate from checked/coherent Source equality. -/
namespace Solidity.Yul.Checks.RawContinueLoop
namespace Old
export Solidity.Yul.Checks.RawU8Statement (ctx clean initial xCell argCell flagCell)
export Solidity.Yul.Checks.RawPreparedInteger.Old (unsignedCtx)
end Old
def argument : Solidity.Source.Idx Old.ctx.tys LocalU8Expr.Ty := .there .here
def breakBody := RawCheckedAdapter.fromAdapter (RawSourceAdapter.body
 (ctx := Old.ctx) (returns := []) (modifier := false) (u := false) .break_)
def whileProgram : Solidity.Source.RStmt Old.ctx.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .whileLoop (l := true) (.bool true) .cont
def forProgram : Solidity.Source.RStmt Old.ctx.env [] false ⟨true,false⟩ Old.ctx.tys Old.ctx.tys :=
 .forLoop (l := true) (.declInit (τ := LocalU8Expr.Ty) (.local argument) (by rfl)) .none .none .cont
def stateWitness : Nonempty (RawFrame.State Old.ctx) :=
 ⟨Old.initial 2 257 2 (Solidity.Source.St.init Old.ctx.env)⟩
def codeWitness : Nonempty (RawCheckedAdapter.Adapter Old.ctx [] false false .cont) :=
 ⟨RawContinueLoop.body Old.ctx [] false false⟩

theorem allFuel : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (world : Solidity.Source.St Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env),
 let actual := Solidity.Yul.RawContinueLoop.run Solidity.Yul.Checks.RawContinueLoop.Old.ctx [] false false pipeline fuel (Solidity.Yul.Checks.RawContinueLoop.Old.initial 2 257 2 world)
 actual.1 = .error .timeout ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawContinueLoop.Old.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawContinueLoop.Old.argCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawContinueLoop.Old.flagCell).val = 2 ∧ actual.2.world = world := by
  intro pipeline fuel world
  have observed := RawContinueLoop.all_fuel Old.ctx [] false false pipeline fuel (Old.initial 2 257 2 world)
  refine ⟨observed.1,?_⟩
  rw [observed.2.1]
  exact ⟨rfl,rfl,rfl,observed.2.2⟩

theorem zero : ∀ (pipeline : Solidity.Roadmap.Pipeline) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawContinueLoop.Old.ctx), Solidity.Yul.RawContinueLoop.run Solidity.Yul.Checks.RawContinueLoop.Old.ctx [] false false pipeline 0 state = (.error .timeout,state) := by
  intro pipeline state
  rfl

theorem oneRefresh : ∀ (pipeline : Solidity.Roadmap.Pipeline) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawContinueLoop.Old.ctx), Solidity.Yul.RawContinueLoop.run Solidity.Yul.Checks.RawContinueLoop.Old.ctx [] false false pipeline 1 state = (.error .timeout,Solidity.Yul.RawContinueLoop.refresh state) := by
  intro pipeline state
  rfl

theorem breakControl : ∀ (pipeline : Solidity.Roadmap.Pipeline) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawContinueLoop.Old.ctx),
 (Solidity.Yul.RawContinueLoop.run Solidity.Yul.Checks.RawContinueLoop.Old.ctx [] false false pipeline 2 state).1 = .error .timeout ∧
 (Solidity.Yul.RawCheckedAdapterLoop.run (Solidity.Yul.RawContinueLoop.test Solidity.Yul.Checks.RawContinueLoop.Old.ctx) Solidity.Yul.Checks.RawContinueLoop.breakBody pipeline 2 state).1 = .ok () := by
  intro pipeline state
  exact ⟨(RawContinueLoop.all_fuel Old.ctx [] false false pipeline 2 state).1,rfl⟩

theorem sourceWhileAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env),
 (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawContinueLoop.whileProgram Solidity.Yul.Checks.RawContinueLoop.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env,world) =
 (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env,world)) := by
  intro glob frame checked fuel nps ph world
  exact RawContinueLoop.source_while Old.ctx [] false false glob frame checked fuel nps ph
    (RawFrame.ofClean Old.clean world) (RawCoherent.coherent_ofClean Old.clean world)

theorem sourceForAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env),
 (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawContinueLoop.forProgram Solidity.Yul.Checks.RawContinueLoop.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env,world) =
 (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env,world)) := by
  intro glob frame checked fuel nps ph world
  exact RawContinueLoop.source_for Old.ctx "n" [] false false argument glob frame checked fuel nps ph
    (RawFrame.ofClean Old.clean world) (RawCoherent.coherent_ofClean Old.clean world)

theorem initializedAll : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (world : Solidity.Source.St Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env),
 let actual := Solidity.Yul.RawU8ForAbsent.run (.local Solidity.Yul.Checks.RawContinueLoop.argument)
   (Solidity.Yul.RawContinueLoop.body Solidity.Yul.Checks.RawContinueLoop.Old.unsignedCtx [] false false) pipeline fuel (Solidity.Yul.Checks.RawContinueLoop.Old.initial 2 257 2 world)
 actual.1 = .error .timeout ∧ actual.2.world = world := by
  intro pipeline fuel world
  exact ⟨RawContinueLoop.initialized_timeout Old.ctx "n" [] false false argument pipeline fuel
    (Old.initial 2 257 2 world),
    RawContinueLoop.initialized_world Old.ctx "n" [] false false argument pipeline fuel
    (Old.initial 2 257 2 world)⟩

theorem dirtyInputRefuses : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env), Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawContinueLoop.Old.initial 2 257 2 world) = false := by
  intro world
  rfl

theorem coherentAll : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
 (world : Solidity.Source.St Old.ctx.env),
 let actual := RawContinueLoop.run Old.ctx [] false false pipeline fuel
   (RawFrame.ofClean Old.clean world)
 actual.2.clean = Old.clean ∧ RawCoherent.coherent actual.2 = true := by
  intro pipeline fuel world
  exact RawContinueLoop.all_fuel_clean Old.ctx [] false false pipeline fuel
    (RawFrame.ofClean Old.clean world) (RawCoherent.coherent_ofClean Old.clean world)

theorem dirtyOneRefuses : ∀ (pipeline : Solidity.Roadmap.Pipeline)
 (world : Solidity.Source.St Old.ctx.env),
 RawCoherent.coherent (RawContinueLoop.run Old.ctx [] false false pipeline 1
   (Old.initial 2 257 2 world)).2 = false := by
  intro pipeline world
  rfl

end Solidity.Yul.Checks.RawContinueLoop
#print axioms Solidity.Yul.RawContinueLoop.refresh_view
#print axioms Solidity.Yul.RawContinueLoop.refresh_world
#print axioms Solidity.Yul.RawContinueLoop.all_fuel
#print axioms Solidity.Yul.RawContinueLoop.source_while
#print axioms Solidity.Yul.RawContinueLoop.initialized_timeout
#print axioms Solidity.Yul.RawContinueLoop.initialized_world
#print axioms Solidity.Yul.RawContinueLoop.source_for
#print axioms Solidity.Yul.Checks.RawContinueLoop.allFuel
#print axioms Solidity.Yul.Checks.RawContinueLoop.zero
#print axioms Solidity.Yul.Checks.RawContinueLoop.oneRefresh
#print axioms Solidity.Yul.Checks.RawContinueLoop.breakControl
#print axioms Solidity.Yul.Checks.RawContinueLoop.sourceWhileAll
#print axioms Solidity.Yul.Checks.RawContinueLoop.sourceForAll
#print axioms Solidity.Yul.Checks.RawContinueLoop.initializedAll
#print axioms Solidity.Yul.Checks.RawContinueLoop.dirtyInputRefuses

#print axioms Solidity.Yul.RawContinueLoop.refresh_clean
#print axioms Solidity.Yul.RawContinueLoop.all_fuel_clean
#print axioms Solidity.Yul.Checks.RawContinueLoop.coherentAll
#print axioms Solidity.Yul.Checks.RawContinueLoop.dirtyOneRefuses
