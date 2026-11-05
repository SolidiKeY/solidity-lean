import Solidity.Yul.RawContinueLoop
import Solidity.Yul.Checks.RawU8ForAbsent
import Solidity.Yul.Checks.LocalWordView
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

theorem expressionAll : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
 (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawContinueLoop.Old.ctx),
 (Solidity.Yul.RawContinueLoop.uint8Run Solidity.Yul.Checks.RawContinueLoop.Old.ctx [] false false
   Solidity.Yul.Checks.RawContinueLoop.Init.assign pipeline fuel state).1.isOk = false := by
  intro pipeline fuel state
  exact RawContinueLoop.uint8_no_success Old.ctx [] false false _ Init.assign pipeline fuel state

theorem expressionLegacyPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env),
 let actual := Solidity.Yul.RawContinueLoop.uint8Run Solidity.Yul.Checks.RawContinueLoop.Old.ctx [] false false
   Solidity.Yul.Checks.RawContinueLoop.Init.timeout Solidity.Roadmap.Pipeline.legacy 8
   (Solidity.Yul.Checks.RawContinueLoop.Old.initial 257 2 1 world)
 actual.1 = .error .timeout ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawContinueLoop.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawContinueLoop.Old.flagCell).val = 1 ∧
 actual.2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem expressionViaIRPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env),
 let actual := Solidity.Yul.RawContinueLoop.uint8Run Solidity.Yul.Checks.RawContinueLoop.Old.ctx [] false false
   Solidity.Yul.Checks.RawContinueLoop.Init.timeout Solidity.Roadmap.Pipeline.viaIR 8
   (Solidity.Yul.Checks.RawContinueLoop.Old.initial 257 2 1 world)
 actual.1 = .error .timeout ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawContinueLoop.Old.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawContinueLoop.Old.flagCell).val = 1 ∧
 actual.2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem expressionSourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env)
 (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env))
 (world : Solidity.Source.St Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env),
 ((Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.whileLoop (R := []) (M := false) (l := true) (u := false)
     (.bool true) (.block (.stmt (.expr (.assign (.local .here) (.local (.there .here)))) .nil)))
   Solidity.Yul.Checks.RawContinueLoop.Old.clean).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env,world)).1.isOk = false := by
  intro glob frame checked fuel nps ph world
  exact RawContinueLoop.source_uint8_no_success Old.ctx [] false false _ Init.assign
    glob frame checked fuel nps ph (RawFrame.ofClean Old.clean world)
    (RawCoherent.coherent_ofClean Old.clean world)


def expressionValues : LocalValues Old.ctx.env Old.ctx.tys :=
 (.scalar (LocalOperations.u8Shape Old.ctx.env) (word 257),
  (.scalar (LocalOperations.u8Shape Old.ctx.env) (word 257),
   (.scalar (LocalOperations.boolShape Old.ctx.env) (word 2),())))
def expressionState (world : Solidity.Source.St Old.ctx.env) : RawFrame.State Old.ctx :=
 RawCoherent.capture (Old.initial 2 257 2 world) (expressionValues,world)

theorem expressionPrepare : ∀ (world : Solidity.Source.St Old.ctx.env),
 RawCoherent.prepare (expressionState world) = (expressionValues,world) := by
  intro world
  rfl

theorem expressionRefresh : ∀ (world : Solidity.Source.St Old.ctx.env),
 RawContinueLoop.refresh (expressionState world) = expressionState world := by
  intro world
  unfold RawContinueLoop.refresh
  rw [expressionPrepare]
  rfl

theorem expressionMutation : ∀ (pipeline : Solidity.Roadmap.Pipeline)
 (world : Solidity.Source.St Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env),
 let actual := Solidity.Yul.RawContinueLoop.uint8Run Solidity.Yul.Checks.RawContinueLoop.Old.ctx [] false false
   Solidity.Yul.Checks.RawContinueLoop.Init.assign pipeline 6
   (Solidity.Yul.Checks.RawContinueLoop.Old.initial 2 257 2 world)
 actual.1 = .error .timeout ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawContinueLoop.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawContinueLoop.Old.argCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawContinueLoop.Old.flagCell).val = 2 ∧
 Solidity.Yul.RawCoherent.coherent actual.2 = false ∧ actual.2.world = world := by
  intro pipeline world
  have guardOne : RawCondition.eval (RawContinueLoop.test Old.ctx) 5
      (Old.initial 2 257 2 world) =
      (.ok true,RawContinueLoop.refresh (Old.initial 2 257 2 world)) := by rfl
  have first : (RawContinueLoop.uint8Body Old.ctx [] false false Init.assign).run pipeline 5
      (RawContinueLoop.refresh (Old.initial 2 257 2 world)) =
      (.ok .normal,expressionState world) := by rfl
  have guardTwo : RawCondition.eval (RawContinueLoop.test Old.ctx) 4 (expressionState world) =
      (.ok true,expressionState world) := by
    change ((.ok true : Solidity.Source.R Bool),RawContinueLoop.refresh (expressionState world)) =
      (.ok true,expressionState world)
    rw [expressionRefresh]
  have step : RawU8Statement.run Init.assign pipeline 2 (expressionState world) =
      (.error .timeout,expressionState world) := by
    unfold RawU8Statement.run RawU8Statement.localRun
    rw [expressionPrepare]
    rfl
  have second : (RawContinueLoop.uint8Body Old.ctx [] false false Init.assign).run pipeline 4
      (expressionState world) = (.error .timeout,expressionState world) := by
    change RawCheckedControlSequence.run (ctx := Old.ctx) (returns := [])
      (modifier := false) (u := false) (.uint8 Init.assign .nil) pipeline 3
      (expressionState world) = _
    rw [RawCheckedControlSequence.run_uint8,step]
  have start : RawContinueLoop.uint8Run Old.ctx [] false false Init.assign pipeline 6
      (Old.initial 2 257 2 world) =
      RawContinueLoop.uint8Run Old.ctx [] false false Init.assign pipeline 5
        (expressionState world) := by
    unfold RawContinueLoop.uint8Run
    rw [RawCheckedAdapterLoop.run,guardOne]
    dsimp only
    rw [first]
    rfl
  have finish : RawContinueLoop.uint8Run Old.ctx [] false false Init.assign pipeline 5
      (expressionState world) = (.error .timeout,expressionState world) := by
    unfold RawContinueLoop.uint8Run
    rw [RawCheckedAdapterLoop.run,guardTwo]
    dsimp only
    rw [second]
    rfl
  rw [start,finish]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩


def accumulate : LocalU8Expr.Supported Old.ctx.env Old.ctx.tys
    (.assign (.local .here) (.binary .add (.local .here) (.local (.there .here)))) :=
  .assign .here (.add (.local .here) (.local (.there .here)))

theorem expressionWorldAll : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
 (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawContinueLoop.Old.ctx),
(Solidity.Yul.RawContinueLoop.uint8Run Solidity.Yul.Checks.RawContinueLoop.Old.ctx [] false false
   Solidity.Yul.Checks.RawContinueLoop.Init.assign pipeline fuel state).2.world = state.world := by
  intro pipeline fuel state
  exact RawContinueLoop.uint8_world Old.ctx [] false false _ Init.assign pipeline fuel state

theorem expressionFaultWorldAll : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
 (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawContinueLoop.Old.ctx),
(Solidity.Yul.RawContinueLoop.uint8Run Solidity.Yul.Checks.RawContinueLoop.Old.ctx [] false false
   Solidity.Yul.Checks.RawContinueLoop.Init.timeout pipeline fuel state).2.world = state.world := by
  intro pipeline fuel state
  exact RawContinueLoop.uint8_world Old.ctx [] false false _ Init.timeout pipeline fuel state

theorem expressionSourceErrorAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env)
 (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env))
 (world : Solidity.Source.St Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env),
 ∃ halt : Solidity.Source.Halt,
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.whileLoop (R := []) (M := false) (l := true) (u := false)
     (.bool true) (.block (.stmt
       (.expr (.assign (.local .here) (.binary .add (.local .here) (.local (.there .here)))))
       .nil))) Solidity.Yul.Checks.RawContinueLoop.Old.clean).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env,world) =
 (.error halt,(Solidity.Source.L0 Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env,world)) := by
  intro glob frame checked fuel nps ph world
  exact RawContinueLoop.source_uint8_error Old.ctx [] false false _ accumulate
    glob frame checked fuel nps ph (RawFrame.ofClean Old.clean world)
    (RawCoherent.coherent_ofClean Old.clean world)


def grownAccumulate : LocalU8Expr.Supported Old.ctx.env (Old.ctx.push "n" LocalU8Expr.Ty).tys
    (.assign (.local (.there .here)) (.binary .add (.local (.there .here)) (.local .here))) :=
  .assign (.there .here) (.add (.local (.there .here)) (.local .here))

theorem initializedExpressionRaw : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
 (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawContinueLoop.Old.ctx),
 let actual := Solidity.Yul.RawU8ForAbsent.run Solidity.Yul.Checks.RawContinueLoop.Init.assign
   (Solidity.Yul.RawContinueLoop.uint8Body
     (Solidity.Yul.Checks.RawContinueLoop.Old.ctx.push "n" Solidity.Yul.LocalU8Expr.Ty)
     [] false false Solidity.Yul.Checks.RawContinueLoop.grownAccumulate) pipeline fuel state
 actual.1.isOk = false ∧ actual.2.world = state.world := by
  intro pipeline fuel state
  exact ⟨RawContinueLoop.uint8_for_no_success Old.ctx "n" [] false false
      _ Init.assign _ grownAccumulate pipeline fuel state,
    RawContinueLoop.uint8_for_world Old.ctx "n" [] false false
      _ Init.assign _ grownAccumulate pipeline fuel state⟩

theorem initializedExpressionLegacy : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env),
 let actual := Solidity.Yul.RawU8ForAbsent.run Solidity.Yul.Checks.RawContinueLoop.Init.timeout
   (Solidity.Yul.RawContinueLoop.uint8Body
     (Solidity.Yul.Checks.RawContinueLoop.Old.ctx.push "n" Solidity.Yul.LocalU8Expr.Ty)
     [] false false Solidity.Yul.Checks.RawContinueLoop.grownAccumulate) Solidity.Roadmap.Pipeline.legacy 6
   (Solidity.Yul.Checks.RawContinueLoop.Old.initial 257 2 1 world)
 actual.1 = .error .timeout ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawContinueLoop.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawContinueLoop.Old.flagCell).val = 1 ∧
 actual.2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem initializedExpressionViaIR : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env),
 let actual := Solidity.Yul.RawU8ForAbsent.run Solidity.Yul.Checks.RawContinueLoop.Init.timeout
   (Solidity.Yul.RawContinueLoop.uint8Body
     (Solidity.Yul.Checks.RawContinueLoop.Old.ctx.push "n" Solidity.Yul.LocalU8Expr.Ty)
     [] false false Solidity.Yul.Checks.RawContinueLoop.grownAccumulate) Solidity.Roadmap.Pipeline.viaIR 6
   (Solidity.Yul.Checks.RawContinueLoop.Old.initial 257 2 1 world)
 actual.1 = .error .timeout ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawContinueLoop.Old.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view actual.2 Solidity.Yul.Checks.RawContinueLoop.Old.flagCell).val = 1 ∧
 actual.2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem initializedExpressionSource : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env)
 (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env))
 (world : Solidity.Source.St Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env),
 ∃ halt : Solidity.Source.Halt,
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.forLoop (R := []) (M := false) (l := true) (u := false)
     (.declInit (τ := Solidity.Yul.LocalU8Expr.Ty)
       (.assign (.local .here) (.local (.there .here))) (by rfl)) .none .none
     (.block (.stmt (.expr
       (.assign (.local (.there .here))
         (.binary .add (.local (.there .here)) (.local .here)))) .nil)))
   Solidity.Yul.Checks.RawContinueLoop.Old.clean).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env,world) =
 (.error halt,(Solidity.Source.L0 Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env,world)) := by
  intro glob frame checked fuel nps ph world
  exact RawContinueLoop.source_uint8_for_error Old.ctx "n" [] false false
    _ Init.assign _ grownAccumulate glob frame checked fuel nps ph
    (RawFrame.ofClean Old.clean world) (RawCoherent.coherent_ofClean Old.clean world)


def xScalar : SourceScalarCell Old.ctx := sourceScalarAt Old.ctx ⟨.unsigned 0,.here⟩
def argScalar : SourceScalarCell Old.ctx := sourceScalarAt Old.ctx ⟨.unsigned 0,.there .here⟩
def flagScalar : SourceScalarCell Old.ctx := sourceScalarAt Old.ctx ⟨.boolean,.there (.there .here)⟩

theorem initializedScalarAll : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
 (world : Solidity.Source.St Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env),
 let actual := Solidity.Yul.RawU8ForAbsent.run (.local Solidity.Yul.Checks.RawContinueLoop.argument)
   (Solidity.Yul.RawContinueLoop.body
     (Solidity.Yul.Checks.RawContinueLoop.Old.ctx.push "n" Solidity.Yul.LocalU8Expr.Ty)
     [] false false) pipeline fuel
   (Solidity.Yul.Checks.RawContinueLoop.Old.initial 2 257 2 world)
 Solidity.Yul.RawTypedScope.scalarRead actual.2 Solidity.Yul.Checks.RawContinueLoop.xScalar = Solidity.Yul.word 2 ∧
 Solidity.Yul.RawTypedScope.scalarRead actual.2 Solidity.Yul.Checks.RawContinueLoop.argScalar = Solidity.Yul.word 257 ∧
 Solidity.Yul.RawTypedScope.scalarRead actual.2 Solidity.Yul.Checks.RawContinueLoop.flagScalar = Solidity.Yul.word 2 := by
  intro pipeline fuel world
  have x := RawContinueLoop.initialized_scalar_read Old.ctx "n" [] false false argument
    pipeline fuel (Old.initial 2 257 2 world) xScalar
  have arg := RawContinueLoop.initialized_scalar_read Old.ctx "n" [] false false argument
    pipeline fuel (Old.initial 2 257 2 world) argScalar
  have flag := RawContinueLoop.initialized_scalar_read Old.ctx "n" [] false false argument
    pipeline fuel (Old.initial 2 257 2 world) flagScalar
  exact ⟨x.trans (by rfl),arg.trans (by rfl),flag.trans (by rfl)⟩

theorem initializedBooleanNotClean : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
 (world : Solidity.Source.St Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env),
 Solidity.Yul.RawTypedScope.scalarRead
   (Solidity.Yul.RawU8ForAbsent.run (.local Solidity.Yul.Checks.RawContinueLoop.argument)
   (Solidity.Yul.RawContinueLoop.body
     (Solidity.Yul.Checks.RawContinueLoop.Old.ctx.push "n" Solidity.Yul.LocalU8Expr.Ty)
     [] false false) pipeline fuel
   (Solidity.Yul.Checks.RawContinueLoop.Old.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawContinueLoop.flagScalar ≠ Solidity.Yul.word 1 := by
  intro pipeline fuel world equal
  have retained := (initializedScalarAll pipeline fuel world).2.2
  have distinct : word 2 ≠ word 1 := by decide
  exact distinct (retained.symm.trans equal)

theorem scalarDropMutation : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawContinueLoop.Old.ctx.env),
 Solidity.Yul.RawTypedScope.scalarRead
   (Solidity.Yul.RawTypedScope.drop (Solidity.Yul.Checks.RawTypedScope.dirty world))
   Solidity.Yul.Checks.RawContinueLoop.argScalar = Solidity.Yul.word 257 ∧
 Solidity.Yul.RawTypedScope.scalarRead
   (Solidity.Yul.RawTypedScope.drop (Solidity.Yul.RawFrame.write
     (Solidity.Yul.Checks.RawTypedScope.dirty world) Solidity.Yul.Checks.RawTypedScope.grownArg
     (Solidity.Yul.word 513))) Solidity.Yul.Checks.RawContinueLoop.argScalar = Solidity.Yul.word 513 := by
  intro world
  exact ⟨rfl,rfl⟩


namespace FunctionInput
export Solidity.Yul.Checks.LocalWordView (ctx locals index maxWord topWord)
def initial (world : Solidity.Source.St ctx.env) : RawFrame.State ctx :=
 RawFrame.write (RawFrame.write (RawFrame.ofClean (ctx := ctx) locals world)
   (.address index) maxWord) (.selector index) topWord
def argument : Solidity.Source.Idx ctx.tys LocalU8Expr.Ty := .there (.there (.there .here))
end FunctionInput

theorem initializedFunctionView : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
 (world : Solidity.Source.St Solidity.Yul.Checks.RawContinueLoop.FunctionInput.ctx.env),
 Solidity.Yul.RawFrame.view (Solidity.Yul.RawU8ForAbsent.run (.local Solidity.Yul.Checks.RawContinueLoop.FunctionInput.argument)
   (Solidity.Yul.RawContinueLoop.body
     (Solidity.Yul.Checks.RawContinueLoop.FunctionInput.ctx.push "n" Solidity.Yul.LocalU8Expr.Ty)
     [] false false) pipeline fuel
   (Solidity.Yul.Checks.RawContinueLoop.FunctionInput.initial world)).2 =
 Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawContinueLoop.FunctionInput.initial world) := by
  intro pipeline fuel world
  exact RawContinueLoop.initialized_view FunctionInput.ctx "n" [] false false
    FunctionInput.argument pipeline fuel (FunctionInput.initial world)

theorem initializedFunctionFields : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
 (world : Solidity.Source.St Solidity.Yul.Checks.RawContinueLoop.FunctionInput.ctx.env),
 let actual := Solidity.Yul.RawU8ForAbsent.run (.local Solidity.Yul.Checks.RawContinueLoop.FunctionInput.argument)
   (Solidity.Yul.RawContinueLoop.body
     (Solidity.Yul.Checks.RawContinueLoop.FunctionInput.ctx.push "n" Solidity.Yul.LocalU8Expr.Ty)
     [] false false) pipeline fuel
   (Solidity.Yul.Checks.RawContinueLoop.FunctionInput.initial world)
 Solidity.Yul.RawFrame.view actual.2 (.address Solidity.Yul.Checks.RawContinueLoop.FunctionInput.index) =
   Solidity.Yul.Checks.RawContinueLoop.FunctionInput.maxWord ∧
 Solidity.Yul.RawFrame.view actual.2 (.selector Solidity.Yul.Checks.RawContinueLoop.FunctionInput.index) =
   Solidity.Yul.Checks.RawContinueLoop.FunctionInput.topWord := by
  intro pipeline fuel world
  dsimp only
  rw [initializedFunctionView pipeline fuel world]
  exact ⟨rfl,rfl⟩

theorem initializedSelectorNotClean : ∀ (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
 (world : Solidity.Source.St Solidity.Yul.Checks.RawContinueLoop.FunctionInput.ctx.env),
 Solidity.Yul.RawFrame.view (Solidity.Yul.RawU8ForAbsent.run (.local Solidity.Yul.Checks.RawContinueLoop.FunctionInput.argument)
   (Solidity.Yul.RawContinueLoop.body
     (Solidity.Yul.Checks.RawContinueLoop.FunctionInput.ctx.push "n" Solidity.Yul.LocalU8Expr.Ty)
     [] false false) pipeline fuel
   (Solidity.Yul.Checks.RawContinueLoop.FunctionInput.initial world)).2
   (.selector Solidity.Yul.Checks.RawContinueLoop.FunctionInput.index) ≠ Solidity.Yul.word 85 := by
  intro pipeline fuel world equal
  have retained := (initializedFunctionFields pipeline fuel world).2
  have distinct : FunctionInput.topWord ≠ word 85 := by decide
  exact distinct (retained.symm.trans equal)

theorem functionInputIncoherent : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawContinueLoop.FunctionInput.ctx.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawContinueLoop.FunctionInput.initial world) = false := by
  intro world
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

#print axioms Solidity.Yul.RawContinueLoop.uint8_body_result
#print axioms Solidity.Yul.RawContinueLoop.uint8_no_success
#print axioms Solidity.Yul.RawContinueLoop.source_uint8_no_success
#print axioms Solidity.Yul.Checks.RawContinueLoop.expressionAll
#print axioms Solidity.Yul.Checks.RawContinueLoop.expressionLegacyPartial
#print axioms Solidity.Yul.Checks.RawContinueLoop.expressionViaIRPartial
#print axioms Solidity.Yul.Checks.RawContinueLoop.expressionSourceAll

#print axioms Solidity.Yul.Checks.RawContinueLoop.expressionPrepare
#print axioms Solidity.Yul.Checks.RawContinueLoop.expressionRefresh
#print axioms Solidity.Yul.Checks.RawContinueLoop.expressionMutation

/-- info: 'Solidity.Yul.RawContinueLoop.uint8_statement_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawContinueLoop.uint8_statement_world
/-- info: 'Solidity.Yul.RawContinueLoop.uint8_body_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawContinueLoop.uint8_body_world
/-- info: 'Solidity.Yul.RawContinueLoop.uint8_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawContinueLoop.uint8_world
/-- info: 'Solidity.Yul.RawContinueLoop.source_uint8_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawContinueLoop.source_uint8_error
/-- info: 'Solidity.Yul.Checks.RawContinueLoop.expressionWorldAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.RawContinueLoop.expressionWorldAll
/-- info: 'Solidity.Yul.Checks.RawContinueLoop.expressionFaultWorldAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.RawContinueLoop.expressionFaultWorldAll
/-- info: 'Solidity.Yul.Checks.RawContinueLoop.expressionSourceErrorAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.RawContinueLoop.expressionSourceErrorAll

/-- info: 'Solidity.Yul.RawContinueLoop.uint8_declaration_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawContinueLoop.uint8_declaration_world
/-- info: 'Solidity.Yul.RawContinueLoop.uint8_for_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawContinueLoop.uint8_for_world
/-- info: 'Solidity.Yul.RawContinueLoop.uint8_for_no_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawContinueLoop.uint8_for_no_success
/-- info: 'Solidity.Yul.RawContinueLoop.source_uint8_for_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawContinueLoop.source_uint8_for_error
/-- info: 'Solidity.Yul.Checks.RawContinueLoop.initializedExpressionRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.RawContinueLoop.initializedExpressionRaw
/-- info: 'Solidity.Yul.Checks.RawContinueLoop.initializedExpressionLegacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.RawContinueLoop.initializedExpressionLegacy
/-- info: 'Solidity.Yul.Checks.RawContinueLoop.initializedExpressionViaIR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.RawContinueLoop.initializedExpressionViaIR
/-- info: 'Solidity.Yul.Checks.RawContinueLoop.initializedExpressionSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.RawContinueLoop.initializedExpressionSource

/-- info: 'Solidity.Yul.RawTypedScope.lift_scalar_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawTypedScope.lift_scalar_read
/-- info: 'Solidity.Yul.RawTypedScope.scalarRead_capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawTypedScope.scalarRead_capture
/-- info: 'Solidity.Yul.RawTypedScope.scalarRead_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawTypedScope.scalarRead_agrees
/-- info: 'Solidity.Yul.RawTypedScope.drop_scalar_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawTypedScope.drop_scalar_read
/-- info: 'Solidity.Yul.RawTypedScope.drop_scalar_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawTypedScope.drop_scalar_agrees
/-- info: 'Solidity.Yul.RawContinueLoop.initialized_scalar_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawContinueLoop.initialized_scalar_read
/-- info: 'Solidity.Yul.Checks.RawContinueLoop.initializedScalarAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.RawContinueLoop.initializedScalarAll
/-- info: 'Solidity.Yul.Checks.RawContinueLoop.initializedBooleanNotClean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.RawContinueLoop.initializedBooleanNotClean
/-- info: 'Solidity.Yul.Checks.RawContinueLoop.scalarDropMutation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.RawContinueLoop.scalarDropMutation

/-- info: 'Solidity.Yul.SourceFunctionCell.ref_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.SourceFunctionCell.ref_injective
/-- info: 'Solidity.Yul.sourceFunctionAt_surjective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.sourceFunctionAt_surjective
/-- info: 'Solidity.Yul.RawTypedScope.lift_function_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawTypedScope.lift_function_fields
/-- info: 'Solidity.Yul.RawTypedScope.functionRead_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawTypedScope.functionRead_at
/-- info: 'Solidity.Yul.RawTypedScope.functionRead_capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawTypedScope.functionRead_capture
/-- info: 'Solidity.Yul.RawTypedScope.functionRead_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawTypedScope.functionRead_agrees
/-- info: 'Solidity.Yul.RawTypedScope.drop_function_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawTypedScope.drop_function_read
/-- info: 'Solidity.Yul.RawTypedScope.drop_function_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawTypedScope.drop_function_agrees
/-- info: 'Solidity.Yul.RawTypedScope.drop_view_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawTypedScope.drop_view_agrees
/-- info: 'Solidity.Yul.RawContinueLoop.initialized_function_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawContinueLoop.initialized_function_read
/-- info: 'Solidity.Yul.RawContinueLoop.initialized_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawContinueLoop.initialized_view
/-- info: 'Solidity.Yul.Checks.RawContinueLoop.initializedFunctionView' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.RawContinueLoop.initializedFunctionView
/-- info: 'Solidity.Yul.Checks.RawContinueLoop.initializedFunctionFields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.RawContinueLoop.initializedFunctionFields
/-- info: 'Solidity.Yul.Checks.RawContinueLoop.initializedSelectorNotClean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.RawContinueLoop.initializedSelectorNotClean
/-- info: 'Solidity.Yul.Checks.RawContinueLoop.functionInputIncoherent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.RawContinueLoop.functionInputIncoherent
