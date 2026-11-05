import Solidity.Yul.RawU8ForAbsent

/-! The actual literal-true/continue runner, not a replacement loop semantics.
All-horizon timeout and raw observations concern this specific body; general
program divergence and compiler adequacy remain separate. -/
namespace Solidity.Yul.RawContinueLoop
def test (ctx : Solidity.Source.Ctx) :
    LocalBoolControl.Supported ctx.env ctx.tys (.bool true) := .base (.literal true)
def body (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy) (modifier u : Bool) :
    RawCheckedAdapter.Adapter ctx returns modifier u .cont :=
  RawCheckedAdapter.fromAdapter (RawSourceAdapter.body
    (ctx := ctx) (returns := returns) (modifier := modifier) (u := u) .continue_)
def refresh {ctx : Solidity.Source.Ctx} (state : RawFrame.State ctx) : RawFrame.State ctx :=
  RawCoherent.capture state (RawCoherent.prepare state)
def run (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy) (modifier u : Bool)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R Unit × RawFrame.State ctx :=
  RawCheckedAdapterLoop.run (test ctx) (body ctx returns modifier u) pipeline fuel state

theorem refresh_view : ∀ (ctx : Solidity.Source.Ctx) (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawFrame.view (Solidity.Yul.RawContinueLoop.refresh state) = Solidity.Yul.RawFrame.view state := by
  intro ctx state
  change localWordCells ctx (RawCoherent.prepare state).1 = RawFrame.view state
  exact RawCoherent.prepare_view state

theorem refresh_world : ∀ (ctx : Solidity.Source.Ctx) (state : Solidity.Yul.RawFrame.State ctx), (Solidity.Yul.RawContinueLoop.refresh state).world = state.world := by
  intro ctx state
  change (RawCoherent.prepare state).2 = state.world
  unfold RawCoherent.prepare
  split <;> rfl

theorem all_fuel : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawContinueLoop.run ctx returns modifier u pipeline fuel state).1 = .error .timeout ∧
 Solidity.Yul.RawFrame.view (Solidity.Yul.RawContinueLoop.run ctx returns modifier u pipeline fuel state).2 = Solidity.Yul.RawFrame.view state ∧
 (Solidity.Yul.RawContinueLoop.run ctx returns modifier u pipeline fuel state).2.world = state.world := by
  intro ctx returns modifier u pipeline fuel state
  induction fuel generalizing state with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ fuel ih =>
    cases fuel with
    | zero =>
      change (.error .timeout : Solidity.Source.R Unit) = .error .timeout ∧
        RawFrame.view (refresh state) = RawFrame.view state ∧ (refresh state).world = state.world
      exact ⟨rfl,refresh_view ctx state,refresh_world ctx state⟩
    | succ fuel =>
      have guard : RawCondition.eval (test ctx) (fuel+1) state = (.ok true,refresh state) := by rfl
      have branch : (body ctx returns modifier u).run pipeline (fuel+1) (refresh state) =
          (.ok (.continue_ rfl),refresh state) := by rfl
      have next := ih (refresh state)
      unfold run
      rw [RawCheckedAdapterLoop.run,guard,branch]
      dsimp only
      exact ⟨next.1,next.2.1.trans (refresh_view ctx state),next.2.2.trans (refresh_world ctx state)⟩

theorem source_while : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.whileLoop (R := returns) (M := modifier) (l := true) (u := u)
     (.bool true) .cont) state.clean).run (Solidity.Source.L0 ctx.env,state.world) =
 (.error .timeout,(Solidity.Source.L0 ctx.env,state.world)) := by
  intro ctx returns modifier u glob frame checked fuel nps ph state same
  have compared := RawCheckedAdapterLoop.correct ctx returns modifier true u (.bool true)
    (test ctx) .cont (body ctx returns modifier u) glob frame checked fuel nps ph state same
  have actual : (Solidity.Source.execS glob frame fuel nps ph
      (Solidity.Source.RStmt.whileLoop (R := returns) (M := modifier) (l := true) (u := u)
        (.bool true) .cont) state.clean).run (Solidity.Source.L0 ctx.env,state.world) =
      RawSequence.represented (run ctx returns modifier u glob.pipeline fuel state) := compared.2
  have observed := all_fuel ctx returns modifier u glob.pipeline fuel state
  rw [actual]
  simp only [RawSequence.represented,observed.1,Except.map,observed.2.2]

theorem initialized_timeout : ∀ (ctx : Solidity.Source.Ctx) (name : String) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (index : Solidity.Source.Idx ctx.tys Solidity.Yul.LocalU8Expr.Ty)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawU8ForAbsent.run (.local index) (Solidity.Yul.RawContinueLoop.body (ctx.push name Solidity.Yul.LocalU8Expr.Ty) returns modifier u) pipeline fuel state).1 = .error .timeout := by
  intro ctx name returns modifier u index pipeline fuel state
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
        change (run (ctx.push name LocalU8Expr.Ty) returns modifier u pipeline (fuel+2) _).1 = .error .timeout
        exact (all_fuel (ctx.push name LocalU8Expr.Ty) returns modifier u pipeline (fuel+2) _).1

theorem initialized_world : ∀ (ctx : Solidity.Source.Ctx) (name : String) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (index : Solidity.Source.Idx ctx.tys Solidity.Yul.LocalU8Expr.Ty)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawU8ForAbsent.run (.local index) (Solidity.Yul.RawContinueLoop.body (ctx.push name Solidity.Yul.LocalU8Expr.Ty) returns modifier u) pipeline fuel state).2.world = state.world := by
  intro ctx name returns modifier u index pipeline fuel state
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      cases fuel with
      | zero => exact refresh_world ctx state
      | succ fuel =>
        let reached : RawFrame.State (ctx.push name LocalU8Expr.Ty) :=
          RawCoherent.capture
            (RawFrame.ofClean (.cons (.int 0 (by decide)) state.clean) state.world)
            (((RawCoherent.prepare state).1.get index,(RawCoherent.prepare state).1),
              (RawCoherent.prepare state).2)
        change (run (ctx.push name LocalU8Expr.Ty) returns modifier u pipeline (fuel+2) reached).2.world = state.world
        rw [(all_fuel (ctx.push name LocalU8Expr.Ty) returns modifier u pipeline (fuel+2) reached).2.2]
        exact refresh_world ctx state

theorem source_for : ∀ (ctx : Solidity.Source.Ctx) (_name : String) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (index : Solidity.Source.Idx ctx.tys Solidity.Yul.LocalU8Expr.Ty)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.forLoop (R := returns) (M := modifier) (l := true) (u := u)
     (Solidity.Source.RStmt.declInit (τ := Solidity.Yul.LocalU8Expr.Ty) (.local index) (by rfl))
     .none .none .cont) state.clean).run (Solidity.Source.L0 ctx.env,state.world) =
 (.error .timeout,(Solidity.Source.L0 ctx.env,state.world)) := by
  intro ctx name returns modifier u index glob frame checked fuel nps ph state same
  have compared := RawU8ForAbsent.correct ctx name returns modifier u (.local index) (.local index)
    .cont (body (ctx.push name LocalU8Expr.Ty) returns modifier u)
    glob frame checked fuel nps ph state same
  have actual : (Solidity.Source.execS glob frame fuel nps ph
      (Solidity.Source.RStmt.forLoop (R := returns) (M := modifier) (l := true) (u := u)
        (.declInit (τ := LocalU8Expr.Ty) (.local index) (by rfl)) .none .none .cont)
      state.clean).run (Solidity.Source.L0 ctx.env,state.world) =
      RawSequence.represented (RawU8ForAbsent.run (.local index)
        (body (ctx.push name LocalU8Expr.Ty) returns modifier u) glob.pipeline fuel state) := compared.2
  have timeout := initialized_timeout ctx name returns modifier u index glob.pipeline fuel state
  have world := initialized_world ctx name returns modifier u index glob.pipeline fuel state
  rw [actual]
  simp only [RawSequence.represented,timeout,Except.map,world]

/-- Reusing a coherent LOCAL input retains its existing typed values.
This does not decode arbitrary dirty words into Source.Val. -/
theorem refresh_clean : ∀ (ctx : Solidity.Source.Ctx) (state : RawFrame.State ctx),
    RawCoherent.coherent state = true →
    (refresh state).clean = state.clean ∧
    RawCoherent.coherent (refresh state) = true := by
  intro ctx state same
  unfold refresh
  rw [RawCoherent.prepare_coherent state same]
  constructor
  · simp only [RawCoherent.capture,LocalState.ofClean,LocalValues.clean_ofClean,
      Option.getD_some]
  · exact RawCoherent.capture_coherent state state.clean state.world

/-- Every actual continue-loop horizon preserves coherent typed LOCAL values.
The raw-word invariant for arbitrary dirty inputs is all_fuel. -/
theorem all_fuel_clean : ∀ (ctx : Solidity.Source.Ctx)
    (returns : List Solidity.Source.STy) (modifier u : Bool)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx),
    RawCoherent.coherent state = true →
    (run ctx returns modifier u pipeline fuel state).2.clean = state.clean ∧
    RawCoherent.coherent (run ctx returns modifier u pipeline fuel state).2 = true := by
  intro ctx returns modifier u pipeline fuel
  induction fuel with
  | zero => intro state same; exact ⟨rfl,same⟩
  | succ fuel ih =>
    intro state same
    have refreshed := refresh_clean ctx state same
    cases fuel with
    | zero => exact refreshed
    | succ fuel =>
      have guard : RawCondition.eval (test ctx) (fuel+1) state =
          (.ok true,refresh state) := by rfl
      have branch : (body ctx returns modifier u).run pipeline (fuel+1) (refresh state) =
          (.ok (.continue_ rfl),refresh state) := by rfl
      have next := ih (refresh state) refreshed.2
      unfold run
      rw [RawCheckedAdapterLoop.run,guard,branch]
      dsimp only
      exact ⟨next.1.trans refreshed.1,next.2⟩

/-- A concrete initializer and binder close retain coherent outer locals at every horizon. -/
theorem initialized_clean : ∀ (ctx : Solidity.Source.Ctx) (name : String)
 (returns : List Solidity.Source.STy) (modifier u : Bool)
 (index : Solidity.Source.Idx ctx.tys Solidity.Yul.LocalU8Expr.Ty)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
 (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawCoherent.coherent state = true →
 let actual := Solidity.Yul.RawU8ForAbsent.run (.local index)
   (Solidity.Yul.RawContinueLoop.body (ctx.push name Solidity.Yul.LocalU8Expr.Ty) returns modifier u)
   pipeline fuel state
 actual.2.clean = state.clean ∧ Solidity.Yul.RawCoherent.coherent actual.2 = true := by

  intro ctx name returns modifier u index pipeline fuel state same
  cases fuel with
  | zero => exact ⟨rfl,same⟩
  | succ fuel =>
    cases fuel with
    | zero => exact ⟨rfl,same⟩
    | succ fuel =>
      cases fuel with
      | zero => exact refresh_clean ctx state same
      | succ fuel =>
        let reached : RawFrame.State (ctx.push name LocalU8Expr.Ty) :=
          RawCoherent.capture
            (RawFrame.ofClean (.cons (.int 0 (by decide)) state.clean) state.world)
            (((RawCoherent.prepare state).1.get index,(RawCoherent.prepare state).1),
              (RawCoherent.prepare state).2)
        have reached_clean : reached.clean = .cons (state.clean.get index) state.clean := by
          dsimp only [reached]
          rw [RawCoherent.prepare_coherent state same]
          simp only [LocalState.ofClean,LocalValues.get_ofClean]
          change (RawCoherent.capture (ctx := ctx.push name LocalU8Expr.Ty) _
            (LocalState.ofClean (.cons (state.clean.get index) state.clean,state.world))).clean = _
          rw [RawCoherent.capture_ofClean]
          rfl
        have reached_coherent : RawCoherent.coherent reached = true := by
          dsimp only [reached]
          rw [RawCoherent.prepare_coherent state same]
          simp only [LocalState.ofClean,LocalValues.get_ofClean]
          exact RawCoherent.capture_coherent (ctx := ctx.push name LocalU8Expr.Ty) _ (.cons (state.clean.get index) state.clean) state.world
        have invariant := all_fuel_clean (ctx.push name LocalU8Expr.Ty)
          returns modifier u pipeline (fuel+2) reached reached_coherent
        change (run (ctx.push name LocalU8Expr.Ty) returns modifier u pipeline (fuel+2) reached).2.clean.drop 1 = state.clean ∧
          RawCoherent.coherent (RawTypedScope.drop
            (run (ctx.push name LocalU8Expr.Ty) returns modifier u pipeline (fuel+2) reached).2) = true
        constructor
        · rw [invariant.1,reached_clean]
          rfl
        · exact RawTypedScope.drop_coherent ctx name LocalU8Expr.Ty _ invariant.2

/-- Word-view preservation through initialization and binder close for coherent inputs. -/
theorem initialized_view_coherent : ∀ (ctx : Solidity.Source.Ctx) (name : String)
 (returns : List Solidity.Source.STy) (modifier u : Bool)
 (index : Solidity.Source.Idx ctx.tys Solidity.Yul.LocalU8Expr.Ty)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
 (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawFrame.view (Solidity.Yul.RawU8ForAbsent.run (.local index)
   (Solidity.Yul.RawContinueLoop.body (ctx.push name Solidity.Yul.LocalU8Expr.Ty) returns modifier u)
   pipeline fuel state).2 = Solidity.Yul.RawFrame.view state := by
  intro ctx name returns modifier u index pipeline fuel state same
  have invariant := initialized_clean ctx name returns modifier u index pipeline fuel state same
  rw [(RawCoherent.coherent_iff _).mp invariant.2,invariant.1]
  exact ((RawCoherent.coherent_iff state).mp same).symm

/-- Preserve exact initializer failures; successful initialization reaches the actual continue loop. -/
theorem initializer_run : ∀ (ctx : Solidity.Source.Ctx) (name : String)
 (returns : List Solidity.Source.STy) (modifier u : Bool)
 (initializer : Solidity.Source.RExpr ctx.env ctx.tys Solidity.Yul.LocalU8Expr.Ty)
 (initial : Solidity.Yul.LocalU8Expr.Supported ctx.env ctx.tys initializer)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
 (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawU8ForAbsent.run initial
   (Solidity.Yul.RawContinueLoop.body (ctx.push name Solidity.Yul.LocalU8Expr.Ty) returns modifier u)
   pipeline (fuel+1) state =
 match Solidity.Yul.RawU8Declaration.run name initial pipeline fuel state with
 | .inl failure => (.error failure.1,failure.2)
 | .inr next => (.error .timeout,Solidity.Yul.RawTypedScope.drop
     (Solidity.Yul.RawContinueLoop.run (ctx.push name Solidity.Yul.LocalU8Expr.Ty)
       returns modifier u pipeline fuel next).2) := by
  intro ctx name returns modifier u initializer initial pipeline fuel state
  unfold RawU8ForAbsent.run
  rw [RawU8For.run]
  cases actual : RawU8Declaration.run name initial pipeline fuel state with
  | inl failure => rfl
  | inr next =>
    change ((run (ctx.push name LocalU8Expr.Ty) returns modifier u pipeline fuel next).1,
      RawTypedScope.drop (run (ctx.push name LocalU8Expr.Ty) returns modifier u pipeline fuel next).2) =
      (.error .timeout,RawTypedScope.drop
        (run (ctx.push name LocalU8Expr.Ty) returns modifier u pipeline fuel next).2)
    rw [(all_fuel (ctx.push name LocalU8Expr.Ty) returns modifier u pipeline fuel next).1]

/-- Successful initialization is followed by timeout, retaining the initializer world. -/
theorem initializer_world : ∀ (ctx : Solidity.Source.Ctx) (name : String)
 (returns : List Solidity.Source.STy) (modifier u : Bool)
 (initializer : Solidity.Source.RExpr ctx.env ctx.tys Solidity.Yul.LocalU8Expr.Ty)
 (initial : Solidity.Yul.LocalU8Expr.Supported ctx.env ctx.tys initializer)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
 (state : Solidity.Yul.RawFrame.State ctx)
 (next : Solidity.Yul.RawFrame.State (ctx.push name Solidity.Yul.LocalU8Expr.Ty)),
 Solidity.Yul.RawU8Declaration.run name initial pipeline fuel state = .inr next →
 let actual := Solidity.Yul.RawU8ForAbsent.run initial
   (Solidity.Yul.RawContinueLoop.body (ctx.push name Solidity.Yul.LocalU8Expr.Ty) returns modifier u)
   pipeline (fuel+1) state
 actual.1 = .error .timeout ∧ actual.2.world = next.world := by
  intro ctx name returns modifier u initializer initial pipeline fuel state next completed
  rw [initializer_run ctx name returns modifier u initializer initial pipeline fuel state,completed]
  exact ⟨rfl,(all_fuel (ctx.push name LocalU8Expr.Ty) returns modifier u pipeline fuel next).2.2⟩

/-- Exact checked Source observation for every supported uint8 initializer. -/
theorem initializer_source : ∀ (ctx : Solidity.Source.Ctx) (name : String)
 (returns : List Solidity.Source.STy) (modifier u : Bool)
 (initializer : Solidity.Source.RExpr ctx.env ctx.tys Solidity.Yul.LocalU8Expr.Ty)
 (initial : Solidity.Yul.LocalU8Expr.Supported ctx.env ctx.tys initializer)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr),
 frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 (Solidity.Source.execS glob frame (fuel+1) nps ph
   (Solidity.Source.RStmt.forLoop (R := returns) (M := modifier) (l := true) (u := u)
     (.declInit (τ := Solidity.Yul.LocalU8Expr.Ty) initializer (by rfl)) .none .none .cont)
   state.clean).run (Solidity.Source.L0 ctx.env,state.world) =
 match Solidity.Yul.RawU8Declaration.run name initial glob.pipeline fuel state with
 | .inl failure => (.error failure.1,(Solidity.Source.L0 ctx.env,failure.2.world))
 | .inr next => (.error .timeout,(Solidity.Source.L0 ctx.env,next.world)) := by
  intro ctx name returns modifier u initializer initial glob frame checked fuel nps ph state same
  have agrees := (RawU8ForAbsent.correct ctx name returns modifier u initializer initial
    .cont (body (ctx.push name LocalU8Expr.Ty) returns modifier u)
    glob frame checked (fuel+1) nps ph state same).2
  rw [agrees,initializer_run ctx name returns modifier u initializer initial glob.pipeline fuel state]
  cases actual : RawU8Declaration.run name initial glob.pipeline fuel state with
  | inl failure => rfl
  | inr next =>
    change ((.error .timeout : Solidity.Source.R (Solidity.Source.Out ctx.env.layout ctx.tys ctx.tys)),(Solidity.Source.L0 ctx.env,
      (run (ctx.push name LocalU8Expr.Ty) returns modifier u glob.pipeline fuel next).2.world)) =
      (.error .timeout,(Solidity.Source.L0 ctx.env,next.world))
    rw [(all_fuel (ctx.push name LocalU8Expr.Ty) returns modifier u glob.pipeline fuel next).2.2]

end Solidity.Yul.RawContinueLoop
