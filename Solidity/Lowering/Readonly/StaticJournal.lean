import Solidity.Source.Eval

/-! P2 journal algebra over the ACTUAL source world's operations and rollback.
`History` is an algebraic journal certificate (execution linkage is the
producer's obligation, requested from P1), not a new
interpreter or a theorem that all source static executions produce it.
It retains balance changes, ordinary writes, inherited child modes and
scoped rollback; a rolled-back child also carries its guarded mode history. -/
namespace Solidity.Lowering.Readonly.StaticJournal
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes)
variable {D : Layout} {L T : Address → SPath → STy}

/-- Persistent storage equality at every typed source account. -/
def SameStorage (s t : ExecState D L T) : Prop :=
  ∀ a, (s.world.accounts a).storage = (t.world.accounts a).storage

/-- Structural history using source journal operations, with valid checkpoint
ancestry. It does not classify outcomes, observations or caller continuations. -/
inductive History : ExecState D L T → Bool → ExecState D L T → Prop where
  | start (entry : ExecState D L T) (mode : Bool) : History entry mode entry
  | balance {entry s : ExecState D L T} {mode : Bool}
      (prior : History entry mode s) (a : Address) (b : Word) :
      History entry mode (s.apply (.account a fun old => old.withBalance b))
  | write {entry s : ExecState D L T} {mode : Bool}
      (prior : History entry mode s) (ordinary : mode = false) (op : Op D L T) :
      History entry mode (s.apply op)
  | child {entry s final : ExecState D L T} {mode : Bool}
      (prior : History entry mode s) (requested : Bool)
      (nested : History s (requested || mode) final) : History entry mode final
  | rollback {entry s : ExecState D L T} {mode : Bool} (parent : History entry mode s)
      (requested : Bool) (ops : List (Op D L T))
      (nested : History s (requested || mode) (s.run ops))
      (a sender : Address) (v : Word) (input : Bytes) :
      History entry mode ((s.enter a sender v input (requested || mode)).rollback (s.run ops))

/-- Crediting/debiting may change an account's balance, never its typed storage. -/
theorem balance_storage (s : ExecState D L T) (a : Address) (b : Word) :
    SameStorage (s.apply (.account a fun old => old.withBalance b)) s := by
  intro target
  by_cases same : target = a
  · subst target
    simp only [ExecState.apply, World.set_get, Account.withBalance]
  · simp only [ExecState.apply, World.set_other _ same]

/-- Every certified history preserves storage, including nested rollback. -/
theorem History.storage {entry final : ExecState D L T} {mode : Bool}
    (h : History entry mode final) (static : mode = true) : SameStorage final entry := by
  induction h with
  | start => intro a; rfl
  | balance prior a b ih =>
    intro target
    exact (balance_storage _ a b target).trans (ih static target)
  | write prior ordinary op ih =>
    exact False.elim (Bool.noConfusion (static.symm.trans ordinary))
  | child prior requested nested ih₁ ih₂ =>
    intro target
    exact (ih₂ (by rw [static, Bool.or_true]) target).trans (ih₁ static target)
  | rollback parent requested ops nested a sender v input ih _ =>
    rw [rollback_run]
    exact ih static

/-- The actual source credit operation produces a valid balance history on
success and on overflow refusal. No mode or whole-world equality is assumed. -/
theorem credit_history {E : Env} {Γ : RCtx} (a : Address) (v : Word)
    (locals : Locals E.layout Γ) (state : St E) (mode : Bool) :
    History state.ex mode ((credit a v : EM E Γ Unit).run (locals, state)).2.2.ex := by
  by_cases fits : (state.ex.world.accounts a).balance.val + v.val < 2 ^ 256
  · simp only [credit, EM.st, EM.modSt, EM.halt, bind, pure, ExceptT.bind,
      ExceptT.pure, ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind,
      StateT.pure, StateT.get, StateT.modifyGet, modify, modifyGet, get,
      getThe, MonadStateOf.get, MonadStateOf.modifyGet, liftM, monadLift,
      MonadLift.monadLift, ExceptT.lift, Functor.map, StateT.map, fits, dif_pos]
    exact .balance (.start _ _) a _
  · simp only [credit, EM.st, EM.modSt, EM.halt, bind, pure, ExceptT.bind,
      ExceptT.pure, ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind,
      StateT.pure, StateT.get, modify, modifyGet, get,
      getThe, MonadStateOf.get, MonadStateOf.modifyGet, liftM, monadLift,
      MonadLift.monadLift, ExceptT.lift, Functor.map, StateT.map, fits, 
      throw, throwThe, MonadExceptOf.throw]
    exact .start _ _

/-- The existing transfer only journals balance replacements. This is a
storage fact, not new payment admission or settlement semantics. -/
theorem transfer_history (state final : ExecState D L T) (src dst : Address)
    (v : Word) (mode : Bool) (execution : state.transfer src dst v = some final) :
    History state mode final := by
  by_cases self : src = dst
  · simp only [ExecState.transfer, self, ↓reduceIte] at execution
    split at execution
    · cases execution
      exact .start _ _
    · cases execution
  · simp only [ExecState.transfer, self, ↓reduceIte] at execution
    split at execution
    · cases execution
      exact .balance (.balance (.start _ _) src _) dst _
    · cases execution

end Solidity.Lowering.Readonly.StaticJournal
