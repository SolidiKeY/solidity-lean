import Solidity.Semantics.CreationTryFrame

/-! Caller-local try composition over the existing installed library operation.
Return decoding and caller continuations are outside the callee catch boundary. -/
namespace Solidity.ContractWorld.LibraryTryFrame
variable {K : Type} [DecidableEq K] {contracts : K → Contract} {caller : K} {α β γ : Type}

/-- A caller-side result extractor is potentially failing in the general
World API. This try interface requires a total raw extractor; all potentially
failing return decoding is the separate continuation outside the catch. -/
structure RawLibrary (contracts : K → Contract) (caller : K) where
  target : Library contracts caller (List Word)
  total : ∀ σ, ∃ words, target.entry.result σ = .ok words

omit [DecidableEq K] in
/-- A descriptor whose caller-side extractor can fail cannot inhabit this
raw interface. Potential decoder errors must use the explicit outer decoder. -/
theorem RawLibrary.no_failure (library : RawLibrary contracts caller)
    (σ : State (contracts caller) library.target.entry.locals) (e : THalt) :
    library.target.entry.result σ ≠ .error e := by
  rcases library.total σ with ⟨words, actual⟩
  rw [actual]
  intro impossible
  cases impossible

/-- Arguments run first. Only the actual library operation is caught;
its successful result is decoded before entering the success continuation. -/
def run (w : World contracts) (self : Handle caller) (args : TRes α)
    (library : α → RawLibrary contracts caller) (ctx : Context)
    (decode : List Word → TRes β)
    (success : World contracts → β → TRes γ)
    (caught : World contracts → THalt → TRes γ) : TRes γ := do
  let a ← args
  match w.libraryCall self (library a).target ctx with
  | .ok (next, words) => do
    let value ← decode words
    success next value
  | .error halt => if catchable halt then caught w halt else .error halt

/-- A caller argument failure cannot enter a library handler. -/
theorem argument_failure (w : World contracts) (self : Handle caller) (e : THalt)
    (library : α → RawLibrary contracts caller) (ctx : Context)
    (decode : List Word → TRes β) (ok : World contracts → β → TRes γ)
    (err : World contracts → THalt → TRes γ) :
    run w self (.error e) library ctx decode ok err = .error e := rfl

/-- Actual library success binds the actual decoded result, once. -/
theorem success (w next : World contracts) (self : Handle caller) (a : α)
    (library : α → RawLibrary contracts caller) (ctx : Context)
    (decode : List Word → TRes β) (ok : World contracts → β → TRes γ)
    (err : World contracts → THalt → TRes γ) (words : List Word) (value : β)
    (called : w.libraryCall self (library a).target ctx = .ok (next, words))
    (decoded : decode words = .ok value) :
    run w self (.ok a) library ctx decode ok err = ok next value := by
  simp only [run, called, decoded, bind, Except.bind]

/-- Decoding failure after successful execution is not caught. -/
theorem decode_failure (w next : World contracts) (self : Handle caller) (a : α)
    (library : α → RawLibrary contracts caller) (ctx : Context)
    (decode : List Word → TRes β) (ok : World contracts → β → TRes γ)
    (err : World contracts → THalt → TRes γ) (words : List Word) (e : THalt)
    (called : w.libraryCall self (library a).target ctx = .ok (next, words))
    (decoded : decode words = .error e) :
    run w self (.ok a) library ctx decode ok err = .error e := by
  simp only [run, called, decoded, bind, Except.bind]

/-- Completed library failure restarts the handler at the pre-library world,
which already contains the caller's evaluated prefix. Actual halt bytes survive. -/
theorem caught (w : World contracts) (self : Handle caller) (a : α)
    (library : α → RawLibrary contracts caller) (ctx : Context)
    (decode : List Word → TRes β) (ok : World contracts → β → TRes γ)
    (err : World contracts → THalt → TRes γ) (e : THalt)
    (called : w.libraryCall self (library a).target ctx = .error e) (completed : catchable e = true) :
    run w self (.ok a) library ctx decode ok err = err w e := by
  simp only [run, called, completed, bind, Except.bind, ↓reduceIte]

/-- Exhaustion/divergence do not become completed caught failures. -/
theorem uncaught (w : World contracts) (self : Handle caller) (a : α)
    (library : α → RawLibrary contracts caller) (ctx : Context)
    (decode : List Word → TRes β) (ok : World contracts → β → TRes γ)
    (err : World contracts → THalt → TRes γ) (e : THalt)
    (called : w.libraryCall self (library a).target ctx = .error e) (incomplete : catchable e = false) :
    run w self (.ok a) library ctx decode ok err = .error e := by
  simp only [run, called, incomplete, bind, Except.bind, Bool.false_eq_true, ↓reduceIte]

/-- Refresh caller storage/funds from the selected world, preserving its live
heap, aliases, locals and transaction identity. The incoming ledger was settled
before library entry and must not be charged again. -/
def resume {Γ : Ctx} (w : World contracts) (self : Handle caller)
    (σ : State (contracts caller) Γ) : TRes (State (contracts caller) Γ) := do
  let storage ← TRes.ofOpt (w.storage? self)
  pure { σ with storage, selfBalance := w.funds self.address, net := [] }

/-- Exact caller heap/frame/identity transport and settled ledger. -/
theorem resume_exact {Γ : Ctx} (w : World contracts) (self : Handle caller)
    (σ : State (contracts caller) Γ) (storage : Storage (contracts caller))
    (installed : w.storage? self = some storage) :
    resume w self σ = .ok { σ with storage, selfBalance := w.funds self.address, net := [] } := by
  simp only [resume, installed, TRes.ofOpt, bind, Except.bind]
  rfl

/-- Execute the prefix once, settle it once, run the installed library once,
then run the selected typed continuation on its actual caller storage. -/
def execute {Γ Δ : Ctx} (w : World contracts) (self : Handle caller)
    (σ : State (contracts caller) []) (before : TStep (contracts caller) [] Γ)
    (args : State (contracts caller) Γ → TRes α)
    (library : α → RawLibrary contracts caller) (ctx : Context)
    (decode : List Word → TRes β)
    (success : β → TStep (contracts caller) Γ Δ)
    (caught : THalt → TStep (contracts caller) Γ Δ)
    (read : State (contracts caller) Δ → TRes γ) : TRes (World contracts × γ) := do
  let start ← before σ
  let a ← args start.st
  let pre ← w.finish self.address start.st
  let finish := fun (next : World contracts) (body : TStep (contracts caller) Γ Δ) => do
    let callerState ← resume next self start.st
    let out ← body callerState
    let result ← read out.st
    let final ← next.finish self.address out.st
    pure (final, result)
  run pre self (.ok a) library ctx decode (fun next value => finish next (success value))
    (fun next halt => finish next (caught halt))

/-- Pointwise caller continuation approximation preserves the same actual
installed library execution and the same successful return decoding. -/
theorem run_approx (w : World contracts) (self : Handle caller) (args : TRes α)
    (library : α → RawLibrary contracts caller) (ctx : Context)
    (decode : List Word → TRes β)
    {ok ok' : World contracts → β → TRes γ} {err err' : World contracts → THalt → TRes γ}
    (hok : ∀ next value, TRes.Approx (ok next value) (ok' next value))
    (herr : ∀ next halt, TRes.Approx (err next halt) (err' next halt)) :
    TRes.Approx (run w self args library ctx decode ok err)
      (run w self args library ctx decode ok' err') := by
  unfold run
  apply TRes.Approx.bind (.refl _)
  intro a
  cases called : w.libraryCall self (library a).target ctx with
  | ok pair =>
    apply TRes.Approx.bind (.refl _)
    intro value
    exact hok pair.1 value
  | error e =>
    dsimp only
    split
    · exact herr w e
    · exact .refl _

/-- The mapped storage formal contains the exact caller root pointer. No
copy of the library's storage or of the caller's aggregate is introduced. -/
theorem storage_alias_root {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (root : String) (R : RefTy) (typed : C.rootType root = some (.ref R)) :
    TRun.declStorage R (some (.path (.loc (.root root typed)))) σ =
      .ok ⟨σ.push (t := .alias R) (some (SRef.ofRoot root typed)), List.prefix_refl _⟩ := rfl

/-- Exactly the existing delegate frame: caller storage, balance and identity,
original sender/value, and no incoming payment ledger. -/
def calleeState (w : World contracts) (self : Handle caller) (ctx : Context)
    (storage : Storage (contracts caller)) : State (contracts caller) [] :=
  { storage, H := [], heap := Heap.empty, env := (), net := [],
    selfBalance := w.funds self.address, tx := ctx.tx w self.address }

omit [DecidableEq K] in
/-- The callee receives no second incoming ledger entry and keeps caller context. -/
theorem callee_context (w : World contracts) (self : Handle caller) (ctx : Context)
    (storage : Storage (contracts caller)) :
    (calleeState w self ctx storage).net = [] ∧
    (calleeState w self ctx storage).tx.msgSender = ctx.sender.1 ∧
    (calleeState w self ctx storage).tx.msgValue = ctx.value ∧
    (calleeState w self ctx storage).tx.selfAddress = self.address.1 ∧
    (calleeState w self ctx storage).selfBalance = w.funds self.address ∧
    (calleeState w self ctx storage).storage = storage := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Universal reduction to the actual installed caller-typed body and actual
result object. Role/address and storage mapping remain explicit obligations. -/
theorem library_frame (w : World contracts) (self : Handle caller)
    (library : Library contracts caller (List Word)) (ctx : Context)
    (callerStorage : Storage (contracts caller)) (libraryStorage : Storage (contracts library.kind))
    (role : w.isLibrary library.kind = true) (callerRole : w.isLibrary caller = false)
    (static : ctx.isStatic = false)
    (installed : w.storage? (⟨library.address⟩ : Handle library.kind) = some libraryStorage)
    (callerInstalled : w.storage? self = some callerStorage) :
    w.libraryCall self library ctx = (do
      let out ← library.entry.body.run (calleeState w self ctx callerStorage)
      let next ← w.finish self.address out.st
      let value ← library.entry.result out.st
      pure (next,value)) := by
  simp only [World.libraryCall, role, callerRole, static, Bool.not_true, Bool.false_or,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte, installed, callerInstalled,
    TRes.ofOpt, bind, Except.bind]
  rfl

/-- Universal bounded-to-ordinary caller transport, with the identical actual
world operation and decoder. It is not a source-validity/profile assumption. -/
theorem execute_approx {Γ Δ : Ctx} (w : World contracts) (self : Handle caller)
    (σ : State (contracts caller) []) {before before' : TStep (contracts caller) [] Γ}
    (args : State (contracts caller) Γ → TRes α)
    (library : α → RawLibrary contracts caller) (ctx : Context)
    (decode : List Word → TRes β)
    {success success' : β → TStep (contracts caller) Γ Δ}
    {caught caught' : THalt → TStep (contracts caller) Γ Δ}
    (read : State (contracts caller) Δ → TRes γ)
    (hp : TStep.Approx before before')
    (hok : ∀ v, TStep.Approx (success v) (success' v))
    (herr : ∀ e, TStep.Approx (caught e) (caught' e)) :
    TRes.Approx (execute w self σ before args library ctx decode success caught read)
      (execute w self σ before' args library ctx decode success' caught' read) := by
  unfold execute
  apply (hp σ).bind
  intro start
  apply TRes.Approx.bind (.refl _)
  intro a
  apply TRes.Approx.bind (.refl _)
  intro pre
  apply run_approx
  · intro next value
    apply TRes.Approx.bind (.refl _)
    intro resumed
    apply (hok value resumed).bind
    intro out
    exact .refl _
  · intro next halt
    apply TRes.Approx.bind (.refl _)
    intro resumed
    apply (herr halt resumed).bind
    intro out
    exact .refl _

/-- A failure in the successful caller tail is outside the callee catch. -/
theorem success_tail_failure (w next : World contracts) (self : Handle caller) (a : α)
    (library : α → RawLibrary contracts caller) (ctx : Context) (decode : List Word → TRes β)
    (ok : World contracts → β → TRes γ) (err : World contracts → THalt → TRes γ)
    (words : List Word) (value : β) (e : THalt)
    (called : w.libraryCall self (library a).target ctx = .ok (next,words))
    (decoded : decode words = .ok value) (failed : ok next value = .error e) :
    run w self (.ok a) library ctx decode ok err = .error e := by
  rw [success w next self a library ctx decode ok err words value called decoded, failed]

/-- Handler failure is not re-entered into the same library catch. -/
theorem caught_tail_failure (w : World contracts) (self : Handle caller) (a : α)
    (library : α → RawLibrary contracts caller) (ctx : Context) (decode : List Word → TRes β)
    (ok : World contracts → β → TRes γ) (err : World contracts → THalt → TRes γ)
    (e failure : THalt) (called : w.libraryCall self (library a).target ctx = .error e)
    (completed : catchable e = true) (failed : err w e = .error failure) :
    run w self (.ok a) library ctx decode ok err = .error failure := by
  rw [caught w self a library ctx decode ok err e called completed, failed]

end Solidity.ContractWorld.LibraryTryFrame
