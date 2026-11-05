import Solidity.Yul.RawContinueLoop
import Solidity.Yul.Checks.RawU8ForAbsent
/-! Universal continue-loop horizon controls and a terminating break countercontrol.
Dirty word observations are separate from checked/coherent Source equality. -/
namespace Solidity.Yul.Checks.RawContinueLoop
namespace Old
export Solidity.Yul.Checks.RawU8Statement (ctx clean initial xCell argCell flagCell)
export Solidity.Yul.Checks.RawPreparedInteger.Old (unsignedCtx)
end Old
namespace Init
export Solidity.Yul.Checks.RawU8Declaration (changed next)
export Solidity.Yul.Checks.RawU8Declaration.Old (assign timeout canonical)
end Init
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

theorem initializedCleanAll : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
 (world : Solidity.Source.St Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env),
 let state := Solidity.Yul.RawFrame.ofClean Solidity.Yul.Checks.RawContinueLoop.Old.clean world
 let actual := Solidity.Yul.RawU8ForAbsent.run (.local Solidity.Yul.Checks.RawContinueLoop.argument)
   (Solidity.Yul.RawContinueLoop.body Solidity.Yul.Checks.RawContinueLoop.Old.unsignedCtx [] false false)
   pipeline fuel state
 actual.2.clean = Solidity.Yul.Checks.RawContinueLoop.Old.clean ∧
 Solidity.Yul.RawCoherent.coherent actual.2 = true ∧
 Solidity.Yul.RawFrame.view actual.2 = Solidity.Yul.RawFrame.view state := by
  intro pipeline fuel world
  have invariant := RawContinueLoop.initialized_clean Old.ctx "n" [] false false argument
    pipeline fuel (RawFrame.ofClean Old.clean world) (RawCoherent.coherent_ofClean Old.clean world)
  exact ⟨invariant.1,invariant.2,RawContinueLoop.initialized_view_coherent
    Old.ctx "n" [] false false argument pipeline fuel (RawFrame.ofClean Old.clean world)
      (RawCoherent.coherent_ofClean Old.clean world)⟩

theorem initializedOverlayAll : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
 (world : Solidity.Source.St Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env),
 let state := Solidity.Yul.RawFrame.capture
   (Solidity.Yul.RawFrame.ofClean Solidity.Yul.Checks.RawContinueLoop.Old.clean world)
   (Solidity.Yul.localWordCells Solidity.Yul.Checks.RawContinueLoop.Old.ctx
     (Solidity.Yul.LocalValues.ofClean Solidity.Yul.Checks.RawContinueLoop.Old.clean))
 let actual := Solidity.Yul.RawU8ForAbsent.run (.local Solidity.Yul.Checks.RawContinueLoop.argument)
   (Solidity.Yul.RawContinueLoop.body Solidity.Yul.Checks.RawContinueLoop.Old.unsignedCtx [] false false)
   pipeline fuel state
 actual.2.clean = Solidity.Yul.Checks.RawContinueLoop.Old.clean ∧
 Solidity.Yul.RawCoherent.coherent actual.2 = true ∧
 Solidity.Yul.RawFrame.view actual.2 = Solidity.Yul.RawFrame.view state := by
  intro pipeline fuel world
  let state : RawFrame.State Old.ctx := RawFrame.capture (RawFrame.ofClean Old.clean world)
    (localWordCells Old.ctx (LocalValues.ofClean Old.clean))
  have same : RawCoherent.coherent state = true := (RawCoherent.coherent_iff state).mpr rfl
  have invariant := RawContinueLoop.initialized_clean Old.ctx "n" [] false false argument
    pipeline fuel state same
  exact ⟨invariant.1,invariant.2,RawContinueLoop.initialized_view_coherent
    Old.ctx "n" [] false false argument pipeline fuel state same⟩

theorem assignInitializerAll : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
 (world : Solidity.Source.St Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env),
Solidity.Yul.RawU8Declaration.run "n" Solidity.Yul.Checks.RawContinueLoop.Init.assign
 pipeline (fuel+3) (Solidity.Yul.Checks.RawContinueLoop.Init.canonical world) =
 .inr (Solidity.Yul.Checks.RawContinueLoop.Init.next world) := by
  intro pipeline fuel world
  rfl

theorem mutatingInitializerAll : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
 (world : Solidity.Source.St Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env),
 let actual := Solidity.Yul.RawU8ForAbsent.run Solidity.Yul.Checks.RawContinueLoop.Init.assign
   (Solidity.Yul.RawContinueLoop.body Solidity.Yul.Checks.RawContinueLoop.Old.unsignedCtx [] false false)
   pipeline (fuel+4) (Solidity.Yul.Checks.RawContinueLoop.Init.canonical world)
 actual.1 = .error .timeout ∧ actual.2.clean = Solidity.Yul.Checks.RawContinueLoop.Init.changed ∧
 actual.2.world = world := by
  intro pipeline fuel world
  have completed := assignInitializerAll pipeline fuel world
  have observed := RawContinueLoop.initializer_world Old.ctx "n" [] false false
    _ Init.assign pipeline (fuel+3) (Init.canonical world) (Init.next world) completed
  have actual := RawContinueLoop.initializer_run Old.ctx "n" [] false false
    _ Init.assign pipeline (fuel+3) (Init.canonical world)
  rw [completed] at actual
  have same : RawCoherent.coherent (Init.next world) = true :=
    (RawCoherent.coherent_iff _).mpr rfl
  have stable := RawContinueLoop.all_fuel_clean Old.unsignedCtx [] false false
    pipeline (fuel+3) (Init.next world) same
  refine ⟨observed.1,?_,observed.2⟩
  change (RawU8ForAbsent.run Init.assign
    (RawContinueLoop.body (Old.ctx.push "n" LocalU8Expr.Ty) [] false false)
    pipeline ((fuel+3)+1) (Init.canonical world)).2.clean = Init.changed
  rw [actual]
  change (RawContinueLoop.run Old.unsignedCtx [] false false
    pipeline (fuel+3) (Init.next world)).2.clean.drop 1 = Init.changed
  rw [stable.1]
  rfl

theorem initializerLegacyPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env),
 let actual := Solidity.Yul.RawU8ForAbsent.run Solidity.Yul.Checks.RawContinueLoop.Init.timeout
   (Solidity.Yul.RawContinueLoop.body Solidity.Yul.Checks.RawContinueLoop.Old.unsignedCtx [] false false)
   Solidity.Roadmap.Pipeline.legacy 6 (Solidity.Yul.Checks.RawContinueLoop.Old.initial 257 2 1 world)
 actual.1 = .error .timeout ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawContinueLoop.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawContinueLoop.Old.flagCell).val = 1 ∧
 actual.2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl,rfl⟩


theorem initializerViaIRPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env),
 let actual := Solidity.Yul.RawU8ForAbsent.run Solidity.Yul.Checks.RawContinueLoop.Init.timeout
   (Solidity.Yul.RawContinueLoop.body Solidity.Yul.Checks.RawContinueLoop.Old.unsignedCtx [] false false)
   Solidity.Roadmap.Pipeline.viaIR 6 (Solidity.Yul.Checks.RawContinueLoop.Old.initial 257 2 1 world)
 actual.1 = .error .timeout ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawContinueLoop.Old.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawContinueLoop.Old.flagCell).val = 1 ∧
 actual.2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl,rfl⟩

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

#print axioms Solidity.Yul.RawContinueLoop.initialized_clean
#print axioms Solidity.Yul.RawContinueLoop.initialized_view_coherent
#print axioms Solidity.Yul.Checks.RawContinueLoop.initializedCleanAll
#print axioms Solidity.Yul.Checks.RawContinueLoop.initializedOverlayAll

#print axioms Solidity.Yul.RawContinueLoop.initializer_run
#print axioms Solidity.Yul.RawContinueLoop.initializer_world
#print axioms Solidity.Yul.RawContinueLoop.initializer_source
#print axioms Solidity.Yul.Checks.RawContinueLoop.assignInitializerAll
#print axioms Solidity.Yul.Checks.RawContinueLoop.mutatingInitializerAll
#print axioms Solidity.Yul.Checks.RawContinueLoop.initializerLegacyPartial
#print axioms Solidity.Yul.Checks.RawContinueLoop.initializerViaIRPartial
