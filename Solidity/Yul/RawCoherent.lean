import Solidity.Yul.RawSource

/-! Coherent transport beside unchanged Source.Val. A clean representation is
reused only when its ENTIRE logical word view equals the authoritative frame.
No word is truncated or decoded by this check. Source steps may retain actual
already-clean results; assembly writes/capture remain unchanged. -/
namespace Solidity.Yul.RawCoherent

def coherent {ctx} (state : RawFrame.State ctx) : Bool :=
  (allWordCells (localExternalTypes ctx)).all (fun cell =>
    RawFrame.view state cell == localWordCells ctx (LocalValues.ofClean state.clean) cell)

theorem coherent_iff {ctx} (state : RawFrame.State ctx) :
    coherent state = true ↔
      RawFrame.view state = localWordCells ctx (LocalValues.ofClean state.clean) := by
  rw [coherent, List.all_eq_true]
  constructor
  · intro same
    funext cell
    exact beq_iff_eq.mp (same cell (allWordCells_complete cell))
  · intro same cell _
    exact beq_iff_eq.mpr (congrFun same cell)

theorem coherent_ofClean {ctx : Solidity.Source.Ctx}
    (locals : Solidity.Source.Locals ctx.env.layout ctx.tys) (world : Solidity.Source.St ctx.env) :
    coherent (RawFrame.ofClean locals world) = true :=
  (coherent_iff _).mpr rfl

def prepare {ctx} (state : RawFrame.State ctx) : LocalState ctx.env ctx.tys :=
  if coherent state = true then LocalState.ofClean (state.clean, state.world)
  else RawFrame.materialize state

theorem prepare_view {ctx} (state : RawFrame.State ctx) :
    localWordCells ctx (prepare state).1 = RawFrame.view state := by
  unfold prepare
  split
  · next same => exact ((coherent_iff state).mp same).symm
  · exact RawFrame.materialize_view state

theorem prepare_coherent {ctx} (state : RawFrame.State ctx) (same : coherent state = true) :
    prepare state = LocalState.ofClean (state.clean, state.world) := by
  unfold prepare
  rw [if_pos same]

/-- Retain actual Source values ONLY if the existing result already consists
entirely of clean constructors. Raw words are still captured without change.
A mixed/dirty result never gets decoded to manufacture a clean value. -/
def capture {ctx} (initial : RawFrame.State ctx) (next : LocalState ctx.env ctx.tys) :
    RawFrame.State ctx :=
  ⟨(LocalValues.clean? ctx.tys next.1).getD initial.clean,
    fun cell => some (localWordCells ctx next.1 cell), next.2⟩

theorem capture_view {ctx} (initial : RawFrame.State ctx) (next : LocalState ctx.env ctx.tys) :
    RawFrame.view (capture initial next) = localWordCells ctx next.1 := rfl

theorem capture_ofClean {ctx : Solidity.Source.Ctx} (initial : RawFrame.State ctx)
    (locals : Solidity.Source.Locals ctx.env.layout ctx.tys) (world : Solidity.Source.St ctx.env) :
    capture initial (LocalState.ofClean (locals, world)) =
      RawFrame.capture (RawFrame.ofClean locals world)
        (localWordCells ctx (LocalValues.ofClean locals)) := by
  simp only [capture, LocalState.ofClean, LocalValues.clean_ofClean, Option.getD_some,
    RawFrame.capture, RawFrame.ofClean]

theorem capture_coherent {ctx : Solidity.Source.Ctx} (initial : RawFrame.State ctx)
    (locals : Solidity.Source.Locals ctx.env.layout ctx.tys) (world : Solidity.Source.St ctx.env) :
    coherent (capture initial (LocalState.ofClean (locals, world))) = true := by
  rw [capture_ofClean]
  exact (coherent_iff _).mpr rfl

def localRun {ctx returns modifier control stmt}
    (proof : RawSource.Supported ctx returns modifier control stmt) :
    Nat → RawFrame.State ctx → Solidity.Source.R Unit × LocalState ctx.env ctx.tys :=
  RawSource.Supported.casesOn
    (motive := fun _ _ =>
      Nat → RawFrame.State ctx → Solidity.Source.R Unit × LocalState ctx.env ctx.tys)
    proof (fun {_expr} body fuel state =>
      LocalExprStatement.discard (LocalBoolControl.eval body) fuel (prepare state))

theorem localRun_coherent {ctx returns modifier control stmt}
    (proof : RawSource.Supported ctx returns modifier control stmt) (fuel : Nat)
    (state : RawFrame.State ctx) (same : coherent state = true) :
    localRun proof fuel state =
      RawSource.localRun proof fuel (RawFrame.ofClean state.clean state.world) := by
  cases proof with
  | expression body =>
    change LocalExprStatement.discard (LocalBoolControl.eval body) fuel (prepare state) = _
    rw [prepare_coherent state same]
    change _ = LocalExprStatement.discard (LocalBoolControl.eval body) fuel
      (RawSource.localState (RawFrame.ofClean state.clean state.world))
    rw [RawSource.localState_ofClean]

theorem clean_next {ctx returns modifier control stmt}
    (proof : RawSource.Supported ctx returns modifier control stmt)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (locals : Solidity.Source.Locals ctx.env.layout ctx.tys) (world : Solidity.Source.St ctx.env) :
    ∃ next : Solidity.Source.Locals ctx.env.layout ctx.tys × Solidity.Source.St ctx.env,
      (RawSource.localRun proof fuel (RawFrame.ofClean locals world)).2 = LocalState.ofClean next := by
  cases proof with
  | @expression expr body =>
    cases fuel with
    | zero =>
      exact ⟨(locals, world), by
        change RawSource.localState (RawFrame.ofClean locals world) = _
        exact RawSource.localState_ofClean locals world⟩
    | succ fuel =>
      refine ⟨((Solidity.Source.evalE glob frame fuel expr).run (locals, world)).2, ?_⟩
      change (LocalExprStatement.discard (LocalBoolControl.eval body) (fuel+1)
        (RawSource.localState (RawFrame.ofClean locals world))).2 = _
      rw [RawSource.localState_ofClean]
      exact congrArg Prod.snd (LocalBoolControl.source_agrees body glob frame fuel (locals, world))

def execS {ctx returns modifier control stmt}
    (proof : RawSource.Supported ctx returns modifier control stmt)
    (fuel : Nat) (state : RawFrame.State ctx) : Solidity.Source.R Unit × RawFrame.State ctx :=
  let out := localRun proof fuel state
  (out.1, capture state out.2)

def observe {ctx} (out : Solidity.Source.R Unit × RawFrame.State ctx) :
    Option (Solidity.Source.R (Solidity.Source.Out ctx.env.layout ctx.tys ctx.tys) ×
      (Solidity.Source.Locals ctx.env.layout [] × Solidity.Source.St ctx.env)) :=
  if coherent out.2 = true then
    some (out.1.map (fun _ => .normal out.2.clean), (Solidity.Source.L0 ctx.env, out.2.world))
  else none

theorem observe_capture {ctx : Solidity.Source.Ctx} (initial : RawFrame.State ctx)
    (tag : Solidity.Source.R Unit) (locals : Solidity.Source.Locals ctx.env.layout ctx.tys)
    (world : Solidity.Source.St ctx.env) :
    observe (tag, capture initial (LocalState.ofClean (locals, world))) =
      LocalExprStatement.project (tag, LocalState.ofClean (locals, world)) := by
  unfold observe
  rw [if_pos (capture_coherent initial locals world), capture_ofClean]
  cases tag <;>
    simp only [LocalExprStatement.project, LocalState.ofClean, LocalValues.clean_ofClean,
      Option.map_some, Except.map, RawFrame.capture, RawFrame.ofClean]

theorem invariant {ctx returns modifier control stmt}
    (proof : RawSource.Supported ctx returns modifier control stmt)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel : Nat) (state : RawFrame.State ctx) (same : coherent state = true) :
    coherent (execS proof fuel state).2 = true := by
  obtain ⟨next, clean⟩ := clean_next proof glob frame fuel state.clean state.world
  unfold execS
  rw [localRun_coherent proof fuel state same]
  change coherent (capture state
    (RawSource.localRun proof fuel (RawFrame.ofClean state.clean state.world)).2) = true
  rw [clean]
  exact capture_coherent state next.1 next.2

theorem source_agrees {ctx returns modifier control stmt}
    (proof : RawSource.Supported ctx returns modifier control stmt)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx) (same : coherent state = true) :
    observe (execS proof fuel state) =
      some ((Solidity.Source.execS glob frame fuel nps ph stmt state.clean).run
        (Solidity.Source.L0 ctx.env, state.world)) := by
  obtain ⟨next, clean⟩ := clean_next proof glob frame fuel state.clean state.world
  have composed : observe (execS proof fuel state) =
      RawSource.observation proof fuel (RawFrame.ofClean state.clean state.world) := by
    unfold execS
    rw [localRun_coherent proof fuel state same]
    unfold RawSource.observation
    generalize h : RawSource.localRun proof fuel (RawFrame.ofClean state.clean state.world) = out at clean ⊢
    rcases out with ⟨tag, nextLocals⟩
    dsimp only at clean
    cases clean
    exact observe_capture state tag next.1 next.2
  exact composed.trans (RawSource.clean_source_agrees proof glob frame fuel nps ph state.clean state.world)

/-- Concrete Source run equation used by consumers; every premise is
discharged by the finite coherence check and actual statement execution. -/
theorem source_run {ctx returns modifier control stmt}
    (proof : RawSource.Supported ctx returns modifier control stmt)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx) (same : coherent state = true) :
    (Solidity.Source.execS glob frame fuel nps ph stmt state.clean).run
      (Solidity.Source.L0 ctx.env, state.world) =
        ((execS proof fuel state).1.map (fun _ => .normal (execS proof fuel state).2.clean),
          (Solidity.Source.L0 ctx.env, (execS proof fuel state).2.world)) := by
  have actual := source_agrees proof glob frame fuel nps ph state same
  unfold observe at actual
  rw [if_pos (invariant proof glob frame fuel state same)] at actual
  exact (Option.some.inj actual).symm

end Solidity.Yul.RawCoherent
