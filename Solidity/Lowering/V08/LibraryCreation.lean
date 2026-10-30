import Solidity.Lowering.V08.Callable
import Solidity.Lowering.V08.Transactions
import Solidity.Semantics.ContractWorldCertificates

/-!
# Library and creation continuation observations

Runtime code-identity checks are retained. Source library resolution, storage
parameter mapping and source constructor execution remain separate premises.
-/
namespace Solidity.Lowering.V08
open Solidity.ContractWorld
variable {K : Type} [DecidableEq K] {contracts : K → Contract}

/-- Extend only the return observation of a caller-typed linked library. -/
def observeLibrary {caller : K} {α β : Type} (library : Library contracts caller α)
    (observe : α → β) : Library contracts caller β :=
  ⟨library.kind, library.address, observeEntry library.entry observe⟩

/-- A library observation extension retains caller storage and runtime context. -/
theorem libraryCall_observe {α β : Type} (w : World contracts) {caller : K}
    (self : Handle caller) (library : Library contracts caller α) (ctx : Context)
    (observe : α → β) :
    w.libraryCall self (observeLibrary library observe) ctx =
      (w.libraryCall self library ctx).map (fun pair => (pair.1, observe pair.2)) := by
  unfold World.libraryCall observeLibrary observeEntry
  split
  · rfl
  · cases hl : w.storage? (⟨library.address⟩ : Handle library.kind) with
    | none => rfl
    | some linked =>
      simp only [TRes.ofOpt, bind, Except.bind]
      cases hs : w.storage? self with
      | none => rfl
      | some store =>
        dsimp only
        let state : State (contracts caller) [] :=
          { storage := store, H := [], heap := Heap.empty, env := (), net := [], selfBalance := w.funds self.address, tx := ctx.tx w self.address }
        cases hr : library.entry.body.run state with
        | error halt => rfl
        | ok output =>
          dsimp only
          cases hf : w.finish self.address output.st with
          | error halt => rfl
          | ok next =>
            dsimp only
            cases library.entry.result output.st <;> rfl

omit [DecidableEq K] in
/-- Observation extension of both continuations leaves creation and catch
boundaries in place, including argument, static, exhaustion and decoder errors. -/
theorem tryCreate_observe {α β γ : Type} (w : World contracts) (args : TRes α)
    (kind : K) (target : α → Address) (ctor : α → Prog (contracts kind) [] [])
    (context : α → Context)
    (success : World contracts → Handle kind → TRes (World contracts × β))
    (caught : World contracts → THalt → TRes (World contracts × β)) (observe : β → γ) :
    w.tryCreate args kind target ctor context
      (fun next reference => (success next reference).map (fun pair => (pair.1, observe pair.2)))
      (fun snapshot halt => (caught snapshot halt).map (fun pair => (pair.1, observe pair.2))) =
    (w.tryCreate args kind target ctor context success caught).map
      (fun pair => (pair.1, observe pair.2)) := by
  unfold World.tryCreate
  cases args with
  | error halt => rfl
  | ok value =>
    simp only [bind, Except.bind]
    cases (context value).isStatic with
    | true => simp only [↓reduceIte, Except.map]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases hc : w.create kind (target value) (ctor value) (context value) with
      | ok pair => rfl
      | error halt =>
        cases he : catchable halt <;>
          simp only [he, Bool.false_eq_true, ↓reduceIte, Except.map]

omit [DecidableEq K] in
/-- Failure of a successful constructor's continuation is outside the catch. -/
theorem tryCreate_success_continuation_failure {α β : Type} (w next : World contracts)
    (value : α) (kind : K) (target : α → Address) (ctor : α → Prog (contracts kind) [] [])
    (context : α → Context) (reference : Handle kind)
    (success : World contracts → Handle kind → TRes (World contracts × β))
    (caught : World contracts → THalt → TRes (World contracts × β)) (halt : THalt)
    (mutable : (context value).isStatic = false)
    (created : w.create kind (target value) (ctor value) (context value) = .ok (next, reference))
    (failed : success next reference = .error halt) :
    w.tryCreate (.ok value) kind target ctor context success caught = .error halt := by
  simp only [World.tryCreate, bind, Except.bind, mutable, Bool.false_eq_true,
    ↓reduceIte, created, failed]

omit [DecidableEq K] in
/-- The creation handler cannot recatch a successful constructor's continuation
failure. An enclosing atomic boundary does roll it back to its own snapshot.
Static, argument and constructor failure branches are untouched. -/
theorem atomic_tryCreate_success_continuation_failure {α β : Type}
    (w next : World contracts) (value : α) (kind : K)
    (target : α → Address) (ctor : α → Prog (contracts kind) [] [])
    (context : α → Context) (reference : Handle kind)
    (success : World contracts → Handle kind → TRes (World contracts × β))
    (caught : World contracts → THalt → TRes (World contracts × β)) (halt : THalt)
    (mutable : (context value).isStatic = false)
    (created : w.create kind (target value) (ctor value) (context value) = .ok (next, reference))
    (failed : success next reference = .error halt) :
    atomic w (w.tryCreate (.ok value) kind target ctor context success caught) =
      (w, .error halt) := by
  rw [tryCreate_success_continuation_failure w next value kind target ctor context
    reference success caught halt mutable created failed]
  rfl

#print axioms atomic_tryCreate_success_continuation_failure

omit [DecidableEq K] in
/-- Static creation is rejected before construction and either continuation. -/
theorem tryCreate_static {α β : Type} (w : World contracts) (value : α) (kind : K)
    (target : α → Address) (ctor : α → Prog (contracts kind) [] []) (context : α → Context)
    (success : World contracts → Handle kind → TRes (World contracts × β))
    (caught : World contracts → THalt → TRes (World contracts × β))
    (static : (context value).isStatic = true) :
    w.tryCreate (.ok value) kind target ctor context success caught = .error .revert := by
  simp only [World.tryCreate, bind, Except.bind, static, ↓reduceIte]

omit [DecidableEq K] in
/-- Only a completed constructor failure satisfying the published catchable
predicate reaches the creation handler; no arbitrary THalt catch is asserted. -/
theorem tryCreate_completed_failure {α β : Type} (w : World contracts) (value : α) (kind : K)
    (target : α → Address) (ctor : α → Prog (contracts kind) [] []) (context : α → Context)
    (success : World contracts → Handle kind → TRes (World contracts × β))
    (caught : World contracts → THalt → TRes (World contracts × β)) (halt : THalt)
    (mutable : (context value).isStatic = false)
    (failed : w.create kind (target value) (ctor value) (context value) = .error halt) :
    w.tryCreate (.ok value) kind target ctor context success caught =
      if catchable halt then caught w halt else .error halt := by
  simp only [World.tryCreate, bind, Except.bind, mutable, Bool.false_eq_true, ↓reduceIte, failed]

#print axioms tryCreate_static
#print axioms tryCreate_completed_failure

omit [DecidableEq K] in
/-- A completed catchable creation-frame failure enters the handler once. Its
successful work prefix followed by a failed continuation propagates the continuation
halt exactly (not necessarily distinct); the creation catch does not surround either handler step. -/
theorem tryCreate_handler_steps_failure {α β γ : Type} (w handled : World contracts)
    (value : α) (kind : K) (target : α → Address)
    (ctor : α → Prog (contracts kind) [] []) (context : α → Context)
    (success : World contracts → Handle kind → TRes (World contracts × β))
    (work : World contracts → THalt → TRes (World contracts × γ))
    (later : World contracts → γ → TRes (World contracts × β))
    (result : γ) (constructorHalt handlerHalt : THalt)
    (mutable : (context value).isStatic = false)
    (constructorFailed : w.create kind (target value) (ctor value) (context value) = .error constructorHalt)
    (caught : catchable constructorHalt = true)
    (worked : work w constructorHalt = .ok (handled, result))
    (laterFailed : later handled result = .error handlerHalt) :
    w.tryCreate (.ok value) kind target ctor context success
      (fun snapshot halt => do
        let (next, result) ← work snapshot halt
        later next result) = .error handlerHalt := by
  rw [tryCreate_completed_failure w value kind target ctor context success _ constructorHalt
    mutable constructorFailed]
  simp only [caught, ↓reduceIte, worked, bind, Except.bind, laterFailed]

omit [DecidableEq K] in
/-- The enclosing atomic snapshot is restored after a catch handler fails.
The handler's completed prefix is not committed through the error branch. -/
theorem atomic_tryCreate_handler_steps_failure {α β γ : Type} (w handled : World contracts)
    (value : α) (kind : K) (target : α → Address)
    (ctor : α → Prog (contracts kind) [] []) (context : α → Context)
    (success : World contracts → Handle kind → TRes (World contracts × β))
    (work : World contracts → THalt → TRes (World contracts × γ))
    (later : World contracts → γ → TRes (World contracts × β))
    (result : γ) (constructorHalt handlerHalt : THalt)
    (mutable : (context value).isStatic = false)
    (constructorFailed : w.create kind (target value) (ctor value) (context value) = .error constructorHalt)
    (caught : catchable constructorHalt = true)
    (worked : work w constructorHalt = .ok (handled, result))
    (laterFailed : later handled result = .error handlerHalt) :
    atomic w (w.tryCreate (.ok value) kind target ctor context success
      (fun snapshot halt => do
        let (next, result) ← work snapshot halt
        later next result)) = (w, .error handlerHalt) := by
  rw [tryCreate_handler_steps_failure w handled value kind target ctor context success work later
    result constructorHalt handlerHalt mutable constructorFailed caught worked laterFailed]
  rfl

omit [DecidableEq K] in
/-- An enclosing transaction restores its own reset entry, even when a paid
ancestor reached another snapshot before creation and the handler did more work. -/
theorem transact_tryCreate_handler_steps_failure {α β γ : Type}
    (w snapshot handled : World contracts)
    (enter : World contracts → TRes (World contracts × α))
    (value : α) (kind : K) (target : α → Address)
    (ctor : α → Prog (contracts kind) [] []) (context : α → Context)
    (success : World contracts → Handle kind → TRes (World contracts × β))
    (work : World contracts → THalt → TRes (World contracts × γ))
    (later : World contracts → γ → TRes (World contracts × β))
    (result : γ) (constructorHalt handlerHalt : THalt)
    (entered : enter w.resetTransient = .ok (snapshot, value))
    (mutable : (context value).isStatic = false)
    (constructorFailed : snapshot.create kind (target value) (ctor value) (context value) = .error constructorHalt)
    (caught : catchable constructorHalt = true)
    (worked : work snapshot constructorHalt = .ok (handled, result))
    (laterFailed : later handled result = .error handlerHalt) :
    w.transact (fun input => do
      let (next, value) ← enter input
      next.tryCreate (.ok value) kind target ctor context success
        (fun before halt => do
          let (after, result) ← work before halt
          later after result)) = (w.resetTransient, .error handlerHalt) := by
  apply World.transact_failure
  simp only [entered, bind, Except.bind]
  exact tryCreate_handler_steps_failure snapshot handled value kind target ctor context success
    work later result constructorHalt handlerHalt mutable constructorFailed caught worked laterFailed

#print axioms tryCreate_handler_steps_failure
#print axioms atomic_tryCreate_handler_steps_failure
#print axioms transact_tryCreate_handler_steps_failure

end Solidity.Lowering.V08
