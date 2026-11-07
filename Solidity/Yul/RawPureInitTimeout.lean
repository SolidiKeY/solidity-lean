import Solidity.Yul.RawSourceLoopTimeout

/-! Concrete initialized omitted-guard loops: the initializer is an actual
certified same-context Boolean statement block, not an arbitrary Adapter.
No-break bodies give raw timeouts, exact coherent Source reached worlds and
clean firstDone horizons. No new initializer-control assumption or decoder. -/
namespace Solidity.Yul.RawPureInitTimeout

theorem raw_post_timeout : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (initItems : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (initProof : Solidity.Yul.RawSequence.Supported ctx returns modifier ⟨true,u⟩ initItems)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (_safe : Solidity.Yul.RawNoGuardFailure.noBreak body = true)
 (post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSourceForPost.Initialized.run (Solidity.Yul.RawSourceAdapter.body (Solidity.Yul.RawLoopBody.Supported.plain initProof)) (.base (.literal true)) step (Solidity.Yul.RawSourceAdapter.body body) fuel state).1 = .error .timeout := by
  intro ctx returns modifier u initItems initProof stmt body safe post step fuel state
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [Solidity.Yul.RawSourceForPost.Initialized.run]
    dsimp only [Solidity.Yul.RawSourceAdapter.body,Solidity.Yul.RawLoopBody.run]
    cases actual : Solidity.Yul.RawSequence.block initProof fuel state with
    | mk tag next =>
      cases tag with
      | error halt =>
        have same := Solidity.Yul.RawBoolFailure.block ctx returns modifier ⟨true,u⟩ initItems initProof fuel state halt (congrArg Prod.fst actual)
        cases same
        rfl
      | ok value =>
        cases value
        change (Solidity.Yul.RawSourceForPost.run (.base (.literal true)) step
          (Solidity.Yul.RawSourceAdapter.body body) fuel next).1 = .error .timeout
        exact Solidity.Yul.RawLoopFailure.post_timeout ctx returns modifier u stmt body safe post step fuel next

theorem raw_no_post_timeout : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (initItems : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (initProof : Solidity.Yul.RawSequence.Supported ctx returns modifier ⟨true,u⟩ initItems)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (_safe : Solidity.Yul.RawNoGuardFailure.noBreak body = true)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSourceAdapterFor.run (Solidity.Yul.RawSourceAdapter.body (Solidity.Yul.RawLoopBody.Supported.plain initProof)) (.base (.literal true)) (Solidity.Yul.RawSourceAdapter.body body) fuel state).1 = .error .timeout := by
  intro ctx returns modifier u initItems initProof stmt body safe fuel state
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [Solidity.Yul.RawSourceAdapterFor.run]
    dsimp only [Solidity.Yul.RawSourceAdapter.body,Solidity.Yul.RawLoopBody.run]
    cases actual : Solidity.Yul.RawSequence.block initProof fuel state with
    | mk tag next =>
      cases tag with
      | error halt =>
        have same := Solidity.Yul.RawBoolFailure.block ctx returns modifier ⟨true,u⟩ initItems initProof fuel state halt (congrArg Prod.fst actual)
        cases same
        rfl
      | ok value =>
        cases value
        change (Solidity.Yul.RawSourceAdapterLoop.run (.base (.literal true))
          (Solidity.Yul.RawSourceAdapter.body body) fuel next).1 = .error .timeout
        rw [Solidity.Yul.RawAdapterLoopHorizon.body_agrees]
        exact Solidity.Yul.RawLoopFailure.no_post_timeout ctx returns modifier u stmt body safe fuel next

theorem source_post_timeout : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (initItems : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (initProof : Solidity.Yul.RawSequence.Supported ctx returns modifier ⟨true,u⟩ initItems)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (_safe : Solidity.Yul.RawNoGuardFailure.noBreak body = true)
 (post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
 (l : Bool) (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx)
 (_same : Solidity.Yul.RawCoherent.coherent state = true),
 (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.forLoop (l := l) (.block initItems) .none (.some post) stmt) state.clean).run
 (Solidity.Source.L0 ctx.env,state.world) = (.error .timeout,(Solidity.Source.L0 ctx.env,(Solidity.Yul.RawSourceForPost.Initialized.run (Solidity.Yul.RawSourceAdapter.body (Solidity.Yul.RawLoopBody.Supported.plain initProof)) (.base (.literal true)) step (Solidity.Yul.RawSourceAdapter.body body) fuel state).2.world)) := by
  intro ctx returns modifier u initItems initProof stmt body safe post step l glob frame fuel nps ph state same
  rw [Solidity.Yul.RawSourceForPost.Absent.source_initialized]
  have agreement := (Solidity.Yul.RawSourceForPost.Initialized.correct (l := l)
    (Solidity.Yul.RawSourceAdapter.body (.plain initProof)) (.base (.literal true)) step
    (Solidity.Yul.RawSourceAdapter.body body) glob frame fuel nps ph state same).2
  have timed := raw_post_timeout ctx returns modifier u initItems initProof stmt body safe post step fuel state
  simpa only [Solidity.Yul.RawSequence.represented,timed,Except.map] using agreement

theorem source_no_post_timeout : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (initItems : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (initProof : Solidity.Yul.RawSequence.Supported ctx returns modifier ⟨true,u⟩ initItems)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (_safe : Solidity.Yul.RawNoGuardFailure.noBreak body = true)
 (l : Bool) (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx)
 (_same : Solidity.Yul.RawCoherent.coherent state = true),
 (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.forLoop (l := l) (.block initItems) .none .none stmt) state.clean).run
 (Solidity.Source.L0 ctx.env,state.world) = (.error .timeout,(Solidity.Source.L0 ctx.env,(Solidity.Yul.RawSourceAdapterFor.run (Solidity.Yul.RawSourceAdapter.body (Solidity.Yul.RawLoopBody.Supported.plain initProof)) (.base (.literal true)) (Solidity.Yul.RawSourceAdapter.body body) fuel state).2.world)) := by
  intro ctx returns modifier u initItems initProof stmt body safe l glob frame fuel nps ph state same
  rw [Solidity.Yul.RawSourceForPost.Absent.source_initialized]
  have agreement := (Solidity.Yul.RawSourceAdapterFor.correct (l := l)
    (Solidity.Yul.RawSourceAdapter.body (.plain initProof)) (.base (.literal true))
    (Solidity.Yul.RawSourceAdapter.body body) glob frame fuel nps ph state same).2
  have timed := raw_no_post_timeout ctx returns modifier u initItems initProof stmt body safe fuel state
  simpa only [Solidity.Yul.RawSequence.represented,timed,Except.map] using agreement

theorem post_firstDone : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (initItems : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (_initProof : Solidity.Yul.RawSequence.Supported ctx returns modifier ⟨true,u⟩ initItems)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (_safe : Solidity.Yul.RawNoGuardFailure.noBreak body = true)
 (post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (_step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
 (l : Bool) (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (locals : Solidity.Source.Locals ctx.env.layout ctx.tys) (world : Solidity.Source.St ctx.env),
 ∀ bound, Solidity.Source.firstDone (fun fuel =>
 (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.forLoop (l := l)
 (.block initItems) .none (.some post) stmt) locals).run (Solidity.Source.L0 ctx.env,world)) bound = none := by
  intro ctx returns modifier u initItems initProof stmt body safe post step l glob frame nps ph locals world
  apply (Solidity.Source.firstDone_none_iff _).2
  intro fuel
  have actual := source_post_timeout ctx returns modifier u initItems initProof stmt body safe post step l glob frame fuel nps ph
    (Solidity.Yul.RawFrame.ofClean locals world) (Solidity.Yul.RawCoherent.coherent_ofClean locals world)
  dsimp only [Solidity.Yul.RawFrame.ofClean] at actual
  rw [actual]
  rfl

theorem no_post_firstDone : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (initItems : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (_initProof : Solidity.Yul.RawSequence.Supported ctx returns modifier ⟨true,u⟩ initItems)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (_safe : Solidity.Yul.RawNoGuardFailure.noBreak body = true)
 (l : Bool) (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (locals : Solidity.Source.Locals ctx.env.layout ctx.tys) (world : Solidity.Source.St ctx.env),
 ∀ bound, Solidity.Source.firstDone (fun fuel =>
 (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.forLoop (l := l)
 (.block initItems) .none .none stmt) locals).run (Solidity.Source.L0 ctx.env,world)) bound = none := by
  intro ctx returns modifier u initItems initProof stmt body safe l glob frame nps ph locals world
  apply (Solidity.Source.firstDone_none_iff _).2
  intro fuel
  have actual := source_no_post_timeout ctx returns modifier u initItems initProof stmt body safe l glob frame fuel nps ph
    (Solidity.Yul.RawFrame.ofClean locals world) (Solidity.Yul.RawCoherent.coherent_ofClean locals world)
  dsimp only [Solidity.Yul.RawFrame.ofClean] at actual
  rw [actual]
  rfl

end Solidity.Yul.RawPureInitTimeout
