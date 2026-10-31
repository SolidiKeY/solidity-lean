import Solidity.Semantics.TryCreateConditions
import Solidity.Semantics.RunFuel

/-! Typed caller-local composition over the existing world creation operation.
World effects and the caller's pending local frame remain distinct. The caller
chooses when to commit that frame; no generic world/statement semantics changes. -/
namespace Solidity.ContractWorld.CreationTryFrame
variable {K : Type} {contracts : K → Contract}
variable {C : Contract} {Γ Γs Γc Δ : Ctx} {α : Type}

/-- Run the existing creation boundary with actual typed caller continuations.
Branch-local bindings are dropped by their exact extensions, including catch
payload objects allocated by the existing litBytesT machinery. -/
def run (w : World contracts) (σ : State C Γ) (args : TRes α) (k : K)
    (target : α → Address) (ctor : α → Prog (contracts k) [] []) (ctx : α → Context)
    (hs : Ext Γ Γs) (success : Handle k → TStep C Γ Γs)
    (hc : Ext Γ Γc) (caught : THalt → TStep C Γ Γc) :
    TRes (World contracts × Out C σ.H Γ) :=
  w.tryCreate args k target ctor ctx
    (fun next handle => (TRun.block hs (success handle) σ).map (next, ·))
    (fun before halt => (TRun.block hc (caught halt) σ).map (before, ·))

/-- A tail executes after the selected branch, on its actual grown heap/frame.
Failure in the tail is not re-entered into constructor handlers. -/
def tail (σ : State C Γ)
    (first : TRes (World contracts × Out C σ.H Γ)) (body : TStep C Γ Δ) :
    TRes (World contracts × Out C σ.H Δ) := do
  let (next, out) ← first
  let final ← body out.st
  pure (next, ⟨final.st, out.ext.trans final.ext⟩)

/-- Constructor handlers cannot catch a caller argument failure. -/
theorem argument_failure (w : World contracts) (σ : State C Γ) (e : THalt) (k : K)
    (target : α → Address) (ctor : α → Prog (contracts k) [] []) (ctx : α → Context)
    (hs : Ext Γ Γs) (success : Handle k → TStep C Γ Γs)
    (hc : Ext Γ Γc) (caught : THalt → TStep C Γ Γc) :
    run w σ (.error e) k target ctor ctx hs success hc caught = .error e := rfl

/-- Success pairs the caller continuation with the actual returned world/handle. -/
theorem success (w next : World contracts) (σ : State C Γ) (a : α) (k : K)
    (target : α → Address) (ctor : α → Prog (contracts k) [] []) (ctx : α → Context)
    (hs : Ext Γ Γs) (ok : Handle k → TStep C Γ Γs)
    (hc : Ext Γ Γc) (caught : THalt → TStep C Γ Γc) (handle : Handle k)
    (static : (ctx a).isStatic = false)
    (created : w.create k (target a) (ctor a) (ctx a) = .ok (next, handle)) :
    run w σ (.ok a) k target ctor ctx hs ok hc caught =
      (TRun.block hs (ok handle) σ).map (next, ·) := by
  simp only [run, World.tryCreate, bind, Except.bind, static, Bool.false_eq_true,
    ↓reduceIte, created]

/-- Completed constructor failure uses the precreation world, original caller
locals and the actual halt, not a substituted byte string or default reason. -/
theorem caught (w : World contracts) (σ : State C Γ) (a : α) (k : K)
    (target : α → Address) (ctor : α → Prog (contracts k) [] []) (ctx : α → Context)
    (hs : Ext Γ Γs) (ok : Handle k → TStep C Γ Γs)
    (hc : Ext Γ Γc) (err : THalt → TStep C Γ Γc) (e : THalt)
    (static : (ctx a).isStatic = false)
    (failed : w.create k (target a) (ctor a) (ctx a) = .error e)
    (completed : catchable e = true) :
    run w σ (.ok a) k target ctor ctx hs ok hc err =
      (TRun.block hc (err e) σ).map (w, ·) := by
  simp only [run, World.tryCreate, bind, Except.bind, static, Bool.false_eq_true,
    ↓reduceIte, failed, completed]

/-- Divergence and exhaustion retain their halt instead of becoming a catch. -/
theorem uncaught (w : World contracts) (σ : State C Γ) (a : α) (k : K)
    (target : α → Address) (ctor : α → Prog (contracts k) [] []) (ctx : α → Context)
    (hs : Ext Γ Γs) (ok : Handle k → TStep C Γ Γs)
    (hc : Ext Γ Γc) (err : THalt → TStep C Γ Γc) (e : THalt)
    (static : (ctx a).isStatic = false)
    (failed : w.create k (target a) (ctor a) (ctx a) = .error e)
    (incomplete : catchable e = false) :
    run w σ (.ok a) k target ctor ctx hs ok hc err = .error e := by
  simp only [run, World.tryCreate, bind, Except.bind, static, Bool.false_eq_true,
    ↓reduceIte, failed, incomplete]

/-- The branch tail cannot handle a failure of the constructor boundary. -/
theorem tail_failure (σ : State C Γ) (e : THalt)
    (body : TStep C Γ Δ) : tail (contracts := contracts) σ (.error e) body = .error e := rfl

/-- Exact normal handler/tail heap extension and world transport. -/
theorem tail_success (next : World contracts) (σ : State C Γ)
    (first : TRes (World contracts × Out C σ.H Γ)) (out : Out C σ.H Γ)
    (body : TStep C Γ Δ) (final : Out C out.st.H Δ)
    (selected : first = .ok (next, out)) (executed : body out.st = .ok final) :
    tail σ first body = .ok (next, ⟨final.st, out.ext.trans final.ext⟩) := by
  simp only [tail, selected, executed, bind, Except.bind]
  rfl

/-- Failure of a selected branch tail is not caught again as constructor
failure, and no candidate world is returned. -/
theorem tail_body_failure (next : World contracts) (σ : State C Γ)
    (first : TRes (World contracts × Out C σ.H Γ)) (out : Out C σ.H Γ)
    (body : TStep C Γ Δ) (e : THalt)
    (selected : first = .ok (next, out)) (failed : body out.st = .error e) :
    tail σ first body = .error e := by
  simp only [tail, selected, failed, bind, Except.bind]

/-- The existing outer atomic boundary rolls back creation together with a
failed caller tail; no partly installed candidate world escapes. -/
theorem atomic_tail_failure (w next : World contracts) (σ : State C Γ)
    (first : TRes (World contracts × Out C σ.H Γ)) (out : Out C σ.H Γ)
    (body : TStep C Γ Δ) (e : THalt)
    (selected : first = .ok (next, out)) (failed : body out.st = .error e) :
    atomic w (tail σ first body) = (w, .error e) := by
  rw [tail_body_failure next σ first out body e selected failed]
  rfl

/-- The constructor closure's fresh local contains exactly the actual
argument word, preserving its value rather than a source-independent literal. -/
theorem argument_binding (σ : State C []) (a : Word) :
    TRun.declLocal .uint (some (.simple (.lit a.1 a.2))) σ =
      .ok ⟨σ.push (t := .val .uint) a, List.prefix_refl _⟩ := rfl

/-- A supplied constructor argument is bound once in the existing typed call
frame. This adds no constructor/world implementation. -/
def constructorArg (P : Prog C [.val .uint] [.val .uint]) (a : Word) : Prog C [] [] :=
  .cons (.block (.cons (.declLocal .uint (.user "__creation_argument")
    (some (.simple (.lit a.1 a.2)))) P)) .nil

/-- An Error catch decodes the actual halt and uses existing fresh-payload
allocation. Missing/error decoding is not replaced with a default reason. -/
def errorData (e : THalt) (body : TStep C (.mem bytesR :: Γ) Γc) : TStep C Γ Γc :=
  match e with
  | .revertWith bytes => match CatchKind.decode .reason bytes with
    | some reason => TRun.litBytesT reason body
    | none => fun _ => .error e
  | _ => fun _ => .error e

/-- Wrong or malformed Error bytes remain the exact uncaught halt. -/
theorem errorData_refused (bytes : List UInt8)
    (body : TStep C (.mem bytesR :: Γ) Γc) (σ : State C Γ)
    (bad : CatchKind.decode .reason bytes = none) :
    errorData (.revertWith bytes) body σ = .error (.revertWith bytes) := by
  simp only [errorData, bad]

/-- A proved successful decode allocates exactly those decoded bytes. -/
theorem errorData_decoded (bytes : List UInt8) (reason : List UInt8)
    (body : TStep C (.mem bytesR :: Γ) Γc) (σ : State C Γ)
    (decoded : CatchKind.decode .reason bytes = some reason) :
    errorData (.revertWith bytes) body σ = TRun.litBytesT reason body σ := by
  simp only [errorData, decoded]

/-- Approximation transports through the completed world operation, keeping
constructor execution/arguments/context identical in both readings. -/
theorem run_approx (w : World contracts) (σ : State C Γ) (args : TRes α) (k : K)
    (target : α → Address) (ctor : α → Prog (contracts k) [] []) (ctx : α → Context)
    (hs : Ext Γ Γs) {ok ok' : Handle k → TStep C Γ Γs}
    (hc : Ext Γ Γc) {err err' : THalt → TStep C Γ Γc}
    (hok : ∀ h, TStep.Approx (ok h) (ok' h)) (herr : ∀ e, TStep.Approx (err e) (err' e)) :
    TRes.Approx (run w σ args k target ctor ctx hs ok hc err)
      (run w σ args k target ctor ctx hs ok' hc err') := by
  unfold run World.tryCreate
  cases args with
  | error e => exact .refl _
  | ok a =>
    simp only [bind, Except.bind]
    split
    · exact .refl _
    · cases created : w.create k (target a) (ctor a) (ctx a) with
      | ok pair => exact ((TRun.block_approx hs (hok pair.2)) σ).map _
      | error e =>
        dsimp only
        split
        · exact ((TRun.block_approx hc (herr e)) σ).map _
        · exact .refl _

/-- Data-catch approximation reuses the existing byte-allocation proof. -/
theorem errorData_approx {body body' : TStep C (.mem bytesR :: Γ) Γc}
    (h : TStep.Approx body body') (e : THalt) :
    TStep.Approx (errorData e body) (errorData e body') := by
  cases e with
  | revertWith bytes =>
    simp only [errorData]
    cases decoded : CatchKind.decode .reason bytes with
    | none => exact fun _ => .refl _
    | some reason => exact TRun.litBytesT_approx h reason
  | _ => exact fun _ => .refl _

/-- Tail approximation retains the exact selected state, heap and world. -/
theorem tail_approx (σ : State C Γ)
    {first second : TRes (World contracts × Out C σ.H Γ)}
    {body body' : TStep C Γ Δ} (hfirst : TRes.Approx first second)
    (hbody : TStep.Approx body body') :
    TRes.Approx (tail σ first body) (tail σ second body') := by
  exact hfirst.bind (fun pair => (hbody pair.2.st).map _)

/-- Pending-caller composition, used here only for unpaid, local-only source
programs. This does not reconcile a stale caller ledger after arbitrary world
payments and is not a generic payment/source refinement theorem. Only after
prefix, actual creation,
selected source branch, encoding and reading succeed is caller storage/funding
committed once by existing World.finish. Transaction rollback is atomic outside. -/
def execute {caller : K} {β : Type} (w : World contracts)
    (σ : State (contracts caller) []) (self : Address)
    (before : TStep (contracts caller) [] Γ)
    (args : State (contracts caller) Γ → TRes α) (k : K)
    (target : α → Address) (ctor : α → Prog (contracts k) [] []) (ctx : α → Context)
    (hs : Ext Γ Γs) (ok : Handle k → TStep (contracts caller) Γ Γs)
    (hc : Ext Γ Γc) (err : THalt → TStep (contracts caller) Γ Γc)
    (encode : TStep (contracts caller) Γ Δ) (read : State (contracts caller) Δ → TRes β) :
    TRes (World contracts × β) := do
  let start ← before σ
  let selected ← run w start.st (args start.st) k target ctor ctx hs ok hc err
  let encoded ← tail start.st (.ok selected) encode
  let value ← read encoded.2.st
  let final ← encoded.1.finish (k := caller) self encoded.2.st
  pure (final, value)

/-- Universal kernel correspondence of bounded and ordinary caller-frame
readings. Incomplete bounded runs remain incomplete; a normal bounded witness
therefore has the exact ordinary result, without a stronger source profile. -/
theorem execute_approx {caller : K} {β : Type} (w : World contracts)
    (σ : State (contracts caller) []) (self : Address)
    {before before' : TStep (contracts caller) [] Γ}
    (args : State (contracts caller) Γ → TRes α) (k : K)
    (target : α → Address) (ctor : α → Prog (contracts k) [] []) (ctx : α → Context)
    (hs : Ext Γ Γs) {ok ok' : Handle k → TStep (contracts caller) Γ Γs}
    (hc : Ext Γ Γc) {err err' : THalt → TStep (contracts caller) Γ Γc}
    {encode encode' : TStep (contracts caller) Γ Δ} (read : State (contracts caller) Δ → TRes β)
    (hp : TStep.Approx before before') (hok : ∀ h, TStep.Approx (ok h) (ok' h))
    (herr : ∀ e, TStep.Approx (err e) (err' e)) (he : TStep.Approx encode encode') :
    TRes.Approx (execute w σ self before args k target ctor ctx hs ok hc err encode read)
      (execute w σ self before' args k target ctor ctx hs ok' hc err' encode' read) := by
  apply (hp σ).bind
  intro start
  apply (run_approx w start.st (args start.st) k target ctor ctx hs hc hok herr).bind
  intro selected
  apply (tail_approx start.st (.refl (.ok selected)) he).bind
  intro encoded
  exact .refl _

end Solidity.ContractWorld.CreationTryFrame
