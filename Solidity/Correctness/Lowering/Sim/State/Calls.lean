import Solidity.Correctness.Lowering.Sim.Match.Cases

/-!
# State cases, calls: `StateCases` is the whole per-run statement

`StateCases` (`Sim/Match/Cases.lean`) cannot be proved arm by arm: its call
conjunct alone implies `RunSim` at every associated production run of the
fragment (`runs_of_state_cases`), so `diagram.Simulates`
(`simulates_of_state_cases`), with no use of the other cases, of the loop
hypothesis or of the knot induction.

The reason is in the record. `RecSim` constrains five callbacks (`hoist`,
`hoistStmt`, `elabStmtP`, `elabStmt1`, `elabStmtsP`). `elabCallRetWith` on a
call through a value (`callValueName`) with a result binder returns what
`rc.callValue` returns, and `RecSim` says nothing of that field. At the record
`freeRec C P st'` the five constrained callbacks fail, so `RecSim` holds of
it with no run to check (`freeRec_sim`), and `callValue` returns any chosen
parts `P` and state `st'`: every `sc, st ↦ P, st'` is a successful output of
the arm (`freeRec_ran`). The call conjunct then asks `SiteSim C raw sc st P
st'` for every `raw`, `sc`, `st`, `P`, `st'` (`site_of_callRet`): `RunSim` of
every body with an actual elaboration, whatever its statements.

So a proof of `StateCases` is a proof of the per-run part of
`diagram.Simulates` for every construct (loops included), which
`Sim/Match.lean` documents as not provable for the frozen relation: the
forward clause ranges over every Source frame and `globRel` has none.
-/
namespace Solidity.Correctness.Lowering.Sim

open Solidity.Goals (ElabRan elabKernelTotal)
open Solidity.Goals.Shrink.Lowering
open Solidity.Lowering.V07 (ContextMap)

variable [FreshNames]

variable (C : Contract)

/-- A record that meets `RecSim` with no run to check and whose `callValue`
returns the parts `P` and sets the state `st'`. -/
def freeRec (P : SProg C) (st' : ECtx × Nat) : ElabRec C :=
  { (default : ElabRec C) with
    hoist := fun _ => throw ""
    hoistStmt := fun _ => throw ""
    elabStmtP := fun _ => throw ""
    elabStmt1 := fun _ => throw ""
    elabStmtsP := fun _ => throw ""
    callValue := fun _ _ _ _ _ => do set st'; pure P }

omit [FreshNames] in
/-- A failing callback has no successful run. -/
theorem not_ran_throw {β : Type} (msg : String) (sc : ElabScope) (st : ECtx × Nat) (b : β)
    (st' : ECtx × Nat) : ¬ ElabRan (throw msg : ElabM β) sc st b st' :=
  fun ⟨_, _, h⟩ => nomatch h

/-- The constrained callbacks of `freeRec` have no successful run. -/
theorem freeRec_sim (P : SProg C) (st' : ECtx × Nat) : RecSim C (freeRec C P st') :=
  ⟨fun _ _ _ _ _ h => (not_ran_throw _ _ _ _ _ h).elim,
    fun _ _ _ _ _ h => (not_ran_throw _ _ _ _ _ h).elim,
    fun _ _ _ _ _ h => (not_ran_throw _ _ _ _ _ h).elim,
    fun _ _ _ _ _ h => (not_ran_throw _ _ _ _ _ h).elim,
    fun _ _ _ _ _ h => (not_ran_throw _ _ _ _ _ h).elim⟩

/-- The core between `CallMemo.enter` and `CallMemo.leave`, from an empty
memo, whether or not the callee is shared. -/
theorem freeRec_entered (P : SProg C) (sc : ElabScope) (st st' : ECtx × Nat) (res : Var × PrimTy)
    (shared selfFrame : Bool) :
    ∃ m', (((do
      let entry ← CallMemo.enter shared callValueName selfFrame
      let r ← elabCallRetCore C (freeRec C P st') callValueName [.num 0] (some res) 256 false false
        false false
      CallMemo.leave entry
      pure r : ElabM _).run sc).run st).run {} = .ok (((P, none, []), st'), m') := by
  cases shared
  · exact ⟨{}, rfl⟩
  · exact ⟨{ starts := [(calleeKey callValueName selfFrame sc, st.2)] }, rfl⟩

/-- `elabCallRetWith` is `elabCallRetCore` between `CallMemo.enter` and
`CallMemo.leave`. -/
theorem callRet_eq (rc : ElabRec C) (f : String) (args : List RawExpr) (res : Option (Var × PrimTy))
    (resW : Nat) (targets ctor resNew selfFrame : Bool) :
    elabCallRetWith C rc f args res resW targets ctor resNew selfFrame = (do
      let sc ← read
      let entry ← CallMemo.enter (!ctor && !targets && sc.recs.all (·.name != f) &&
        !isRecursiveC C f && ((sc.funs.find? (·.1 == f)).map (·.2.endsWithCall)).getD false) f
        (selfFrame || sc.selfFrame)
      let r ← elabCallRetCore C rc f args res resW targets ctor resNew selfFrame
      CallMemo.leave entry
      pure r) :=
  rfl

omit [FreshNames] in
/-- A run that starts by reading its scope. -/
theorem run_read_bind {α : Type} (F : ElabScope → ElabM α) (sc : ElabScope) :
    (read >>= F).run sc = (F sc).run sc :=
  rfl

/-- **Every run is an output of the call arm**: from any scope and state,
`elabCallRetWith` at `freeRec C P st'` on a call through a value with a
result binder returns `P` and ends in `st'`. -/
theorem freeRec_ran (P : SProg C) (sc : ElabScope) (st st' : ECtx × Nat) (res : Var × PrimTy) :
    ElabRan (elabCallRetWith C (freeRec C P st') callValueName [.num 0] (some res) 256 false false
      false false) sc st (P, none, []) st' := by
  refine ⟨{}, ?_⟩
  rw [callRet_eq, run_read_bind]
  exact freeRec_entered C P sc st st' res _ _

/-- The call conjunct of `StateCases` at a contract gives `SiteSim` of every
run: nothing ties the parts to an arm. -/
theorem site_of_callRet
    (calls : ∀ rc : ElabRec C, RecSim C rc →
      ∀ f args res resW targets ctor resNew selfFrame sc st out st',
        ElabRan (elabCallRetWith C rc f args res resW targets ctor resNew selfFrame) sc st out
          st' →
        ∀ raw, SiteSim C raw sc st out.1 st')
    (raw : List RawStmt) (sc : ElabScope) (st : ECtx × Nat) (P : SProg C) (st' : ECtx × Nat) :
    SiteSim C raw sc st P st' :=
  calls _ (freeRec_sim C P st') _ _ _ _ _ _ _ _ sc st _ st'
    (freeRec_ran C P sc st st' (.fresh "" 0, .uint)) raw

/-- **`StateCases` implies the per-run statement**, at every associated
production run of the fragment. -/
theorem runs_of_state_cases (kernel : elabKernelTotal) (states : StateCases) (b : Body)
    (u : Emitted) (m : ContextMap b.ctx u.Γ) (production : Production b u)
    (accepted : Accepted u) (assoc : diagram.Assoc b u m) : RunSim b u m := by
  obtain ⟨C, Γ, o⟩ := u
  obtain ⟨lowered, ⟨ran, placed⟩, threaded⟩ := production
  exact site_of_callRet C (fun rc sim => (states kernel C rc sim).2.2.2.2) o.raw o.elabScope
    o.beforeElab.locals o.elaborated o.afterElab.locals b Γ o m
    ⟨rfl, rfl, rfl, rfl, rfl, ran, placed⟩ lowered threaded accepted assoc

/-- **`StateCases` implies `diagram.Simulates`**, alone. -/
theorem simulates_of_state_cases (kernel : elabKernelTotal) (states : StateCases) :
    diagram.Simulates :=
  simulates_of_runs (runs_of_state_cases kernel states)

end Solidity.Correctness.Lowering.Sim
