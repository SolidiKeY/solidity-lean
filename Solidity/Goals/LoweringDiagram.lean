import Solidity.Correctness.Lowering.Checker.Contract
import Solidity.Lowering.V07.Scalar
import Solidity.Semantics.RunFuel
import Solidity.Backend.AbiWorld.PublicCompilerTotal

/-!
# Lowering-by-simulation vocabulary (H517, H666)

The diagram vocabulary `loweringBySimulation` (`Goals/LoweringSim.lean`) is
stated over; no goal here.
-/

namespace Solidity.Goals.Shrink

/-! ## Lowering by simulation -/

namespace Lowering

open Solidity.Correctness.Lowering.Checker (Snapshot Input Output ElaborationReceipt)
open Solidity.Lowering.V07 (ContextMap IntValueRel integerPrim)

variable [FreshNames]

/-- The production lowering exactly as its callers sequence it: a function
body (`calleeBody`, Arms.lean:828-829) lowers its loops then its returns into
the return slots; a standalone loop (Arms.lean:1522, 1926) lowers its loops
with no slots. -/
def lowerAt : Option (List String) → List RawStmt → ElabM (List RawStmt)
  | none, raw => lowerLoops none raw
  | some rs, raw => do
    let lowered ← lowerLoops (some rs) raw
    ElabM.lift (lowerReturns rs lowered)

/-- A callee's return slots, renamed as `calleeBody` renames them. -/
def returnSlots (d : FunDecl) (ρ : List (String × String)) : List String :=
  d.rets.map fun (n, _) => (Semantics.lookupBy n ρ).getD n

/-- What `calleeBody` does after lowering (Arms.lean:830-841). -/
def callerTail (C : Contract) (d : FunDecl) (ρ : List (String × String)) (ctor selfFrame : Bool)
    (Γf : ECtx) (body : List RawStmt) : ElabM (List RawStmt) := do
  let frame := if C.evalOrder.modifierFrames then some (d, ρ) else none
  let body ← wrapMods C body frame (d.mods.map fun m => { m with args := m.args.map (·.rename ρ) })
  let body := (if ctor then C.inits.map fun (x, e) => RawStmt.assign (.name x) e else []) ++ body
  let selfValue := (← read).selfValue
  let body := if selfFrame then body.map (RawStmt.selfFrame selfValue) else body
  ElabM.lift (freshenBlocks (C.vars.map (·.1)) (Γf.map (·.1)) body)

/-- **The callers are bound**: the actual function-body producer is renaming,
then `lowerAt`, then the rest of `calleeBody`. -/
def CallerBound : Prop :=
  ∀ (C : Contract) (d : FunDecl) (ρ : List (String × String)) (ctor selfFrame : Bool) (Γf : ECtx),
    calleeBody C d ρ ctor selfFrame Γf = (do
      let body ← renameStmts ρ d.body
      let body ← lowerAt (some (returnSlots d ρ)) body
      callerTail C d ρ ctor selfFrame Γf body)

/-- Where the production lowering runs: a standalone loop
(`elabStmtsP (← lowerLoops none [s])`, Arms.lean:1522, 1926), or an inlined
callee's body (`inlinedBody`, Arms.lean:846-865: `calleeBody`, then the
locals reset to `Γf` and its body elaborated under the callee scope). The
shared-memo branch of `inlinedBody` reuses an earlier body and runs no
lowering; it is the earlier run's association. -/
inductive Site where
  | loop
  | callee (d : FunDecl) (ρ : List (String × String)) (ctor selfFrame : Bool) (Γf : ECtx)
      (funs : List (Name × FunDecl)) (k₀ : Nat)
  /-- A recursive callee's frame body (Arms.lean:1063-1075): `calleeBody`, then
  `(elabStmtsP body).runFrom sc'` from `(Γf, k₁)` with an empty memo, `sc'` the
  callee scope over the scope `outer` read then, with the frame `rf` pushed. -/
  | recursive (d : FunDecl) (ρ : List (String × String)) (ctor selfFrame : Bool) (Γf : ECtx)
      (funs : List (Name × FunDecl)) (k₀ : Nat) (outer : ElabScope) (rf : RecFrame)

/-- A source body with its production input and its site. -/
structure Body where
  E : Source.Env
  returns : List Source.STy
  modifier : Bool
  control : Source.SCtx
  ctx : Source.RCtx
  input : Input E returns modifier control ctx
  site : Site

/-- An emitted program with its production state. -/
structure Emitted where
  C : Contract
  Γ : Ctx
  output : Output C Γ

/-- The actual producer at the site ran on the input, from its scope and full
state, to the output's raw statements and state: `lowerAt none` for a loop,
the whole `calleeBody` (renaming, `lowerAt`, modifiers, initializers,
self-frame, freshening) for a callee, whose raw input is its declared body. -/
def Lowered (b : Body) (u : Emitted) : Prop :=
  match b.site with
  | .loop =>
    b.input.returnSlots = none ∧
    (((lowerAt none b.input.raw).run b.input.scope).run b.input.before.locals).run
      b.input.before.memo = .ok ((u.output.raw, u.output.afterLower.locals), u.output.afterLower.memo)
  | .callee d ρ ctor selfFrame Γf _ _ | .recursive d ρ ctor selfFrame Γf _ _ _ _ =>
    b.input.raw = d.body ∧ b.input.returnSlots = some (returnSlots d ρ) ∧
    (((calleeBody u.C d ρ ctor selfFrame Γf).run b.input.scope).run b.input.before.locals).run
      b.input.before.memo = .ok ((u.output.raw, u.output.afterLower.locals), u.output.afterLower.memo)

/-- The scope `inlinedBody` elaborates a callee's body under (Arms.lean:858-860). -/
def calleeScope (sc : ElabScope) (funs : List (Name × FunDecl)) (selfFrame : Bool) (k₀ k₁ : Nat) :
    ElabScope :=
  { sc with funs := funs, top := false, selfFrame := selfFrame, unchecked := false,
            inlined := (k₀, k₁) :: sc.inlined }

/-- The elaboration's state and scope are exactly the caller's: the same for
a standalone loop; for a callee, the locals reset to `Γf` with the counter
kept, and the scope `inlinedBody` sets. -/
def Threaded (b : Body) (u : Emitted) : Prop :=
  match b.site with
  | .loop => u.output.beforeElab.memo = u.output.afterLower.memo ∧
    u.output.elabScope = b.input.scope ∧ u.output.beforeElab.locals = u.output.afterLower.locals
  | .recursive _ _ _ selfFrame Γf funs k₀ outer rf =>
    u.output.beforeElab.memo = {} ∧
    u.output.beforeElab.locals = (Γf, u.output.afterLower.locals.2) ∧
    u.output.elabScope = { calleeScope outer funs selfFrame k₀ u.output.afterLower.locals.2 with
      recs := rf :: outer.recs }
  | .callee _ _ _ selfFrame Γf funs k₀ =>
    u.output.beforeElab.memo = u.output.afterLower.memo ∧
    u.output.beforeElab.locals = (Γf, u.output.afterLower.locals.2) ∧
    u.output.elabScope = calleeScope b.input.scope funs selfFrame k₀ u.output.afterLower.locals.2

/-- **Production association**: the actual producer, the actual elaboration
(`elabStmtsP`, `SProg.chain`), the state threaded between them. -/
def Production (b : Body) (u : Emitted) : Prop :=
  Lowered b u ∧ ElaborationReceipt u.output ∧ Threaded b u

/-- Freshness (a conclusion, never a premise): the fresh counter only grows;
a loop's lowering also leaves the scope's locals and the memo untouched. -/
def LowerFresh (b : Body) (u : Emitted) : Prop :=
  b.input.before.locals.2 ≤ u.output.afterLower.locals.2 ∧
  (b.site = .loop → u.output.afterLower.locals.1 = b.input.before.locals.1 ∧
    u.output.afterLower.memo = b.input.before.memo)

/-- t0's accepted fragment (`Goals/Total.lean`), read on the emitted program. -/
def Accepted (u : Emitted) : Prop :=
  Solidity.Backend.AbiWorld.PublicCompilerTotal.ProgOk [] u.output.program.2

/-- The actual Source run of the resolved statement at horizon `n`. -/
def sourceRun (b : Body) (G : Source.Glob b.E) (F : Source.Fr) (n nps : Nat)
    (ph : Option (Source.Ph b.E)) (s : Source.EMState b.E b.ctx) :=
  (Source.execS G F n nps ph b.input.resolved s.1).run (.nil, s.2)

/-- Halts correspond: a revert keeps its data; a panic's data is the target's
`panic` (the intrinsic halt records no code: this observation is lossy and
the session-level `Cert` compares the exact data); a stuck or timed-out
source matches nothing. A target `exhausted` (`storage.full`, `assumeFalse`,
payments: Run.lean, RunAccel.lean, PaymentWorld.lean) matches nothing either,
so the backward clause obliges the prover to show associated fragment
programs never reach one; it is not assumed. -/
def HaltMatch : Source.Halt → THalt → Prop
  | .revert d, h => h = THalt.ofData d ∨ (h = .panic ∧ ∃ c, d = Source.panicData c)
  | .stuck _, _ => False
  | .timeout, _ => False

/-- **The one simulation**: its horizon transport, its association of a
resolved source with an actual production run, and its invariant (value and
global relations). -/
structure Diagram where
  fuel : Nat → Nat
  Assoc : (b : Body) → (u : Emitted) → ContextMap b.ctx u.Γ → Prop
  valRel : {D : Source.Layout} → {C : Contract} → {H : HTy} →
    (τ : Source.STy) → (u : LTy) → Source.Val D τ → u.TDenote C H → Prop
  globRel : {E : Source.Env} → {C : Contract} → {Γ : Ctx} → Source.St E → State C Γ → Prop

/-- Final matching of a source result and a target result: normal completion
and a lowered `return` reach a target state related by the invariant, along
the emitted program's context extension; halts correspond by `HaltMatch`;
a `break`/`continue` escaping the body, a stuck run or a timeout match nothing. -/
def Diagram.Final (D : Diagram) {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ Γ' : Ctx}
    {H : HTy} (m : ContextMap srcΓ Γ) (emb : Thin Γ Γ')
    (src : Except Source.Halt (Source.Out E.layout srcΓ srcΓ) ×
      (Source.Locals E.layout [] × Source.St E))
    (tgt : TRes (Out C H Γ')) : Prop :=
  match src.1, tgt with
  | .ok (.normal ls), .ok o =>
    (m.wk emb).Related (fun τ u => D.valRel τ u) ls o.st.env ∧ D.globRel src.2.2 o.st
  | .ok (.ret ls), .ok o =>
    (m.wk emb).Related (fun τ u => D.valRel τ u) ls o.st.env ∧ D.globRel src.2.2 o.st
  | .error h, .error t => HaltMatch h t
  | _, _ => False

/-- **The diagram's obligations**, for every actual production run on t0's
fragment that the diagram associates with a resolved source:

* the value relation reflects Booleans and integers (`IntValueRel`);
* initial matching is total: every source state has a related target state
  (so neither relation can be empty);
* at every source horizon that completes, the matching final target result
  at the transported fuel (forward diagram; a source timeout is stuttering);
* the transport is monotone (progress) and completed source runs are stable
  under larger horizons (Source determinacy, which `back` needs);
* every completed target run is matched by some completed source run
  (backward diagram: nondeterminism is not dropped, determinacy is proved);
* the producer's fresh state is sound (`LowerFresh`). -/
def Diagram.Simulates (D : Diagram) : Prop :=
  (∀ {Dl : Source.Layout} {C : Contract} {H : HTy} (v : Source.Val Dl .bool) (b : Bool),
    D.valRel (C := C) (H := H) .bool (.val .bool) v b → v = .bool b) ∧
  (∀ {Dl : Source.Layout} {C : Contract} {H : HTy} (t : Source.IntTy) (v : Source.Val Dl (.int t))
    (x : (integerPrim t).Denote), D.valRel (C := C) (H := H) (.int t) (.val (integerPrim t)) v x →
      IntValueRel t v x) ∧
  (∀ n n', n ≤ n' → D.fuel n ≤ D.fuel n') ∧
  ∀ (b : Body) (u : Emitted) (m : ContextMap b.ctx u.Γ),
    Production b u → Accepted u → D.Assoc b u m →
    LowerFresh b u ∧
    (∀ src : Source.EMState b.E b.ctx, ∃ tgt : State u.C u.Γ,
      m.Related (fun τ v => D.valRel τ v) src.1 tgt.env ∧ D.globRel src.2 tgt) ∧
    ∃ emb : Thin u.Γ u.output.program.1,
    ∀ (G : Source.Glob b.E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph b.E))
      (src : Source.EMState b.E b.ctx) (tgt : State u.C u.Γ),
      m.Related (fun τ v => D.valRel τ v) src.1 tgt.env → D.globRel src.2 tgt →
      (∀ n, (sourceRun b G F n nps ph src).1 ≠ .error .timeout →
        D.Final m emb (sourceRun b G F n nps ph src) (u.output.program.2.runF (D.fuel n) tgt)) ∧
      (∀ n n', n ≤ n' → (sourceRun b G F n nps ph src).1 ≠ .error .timeout →
        sourceRun b G F n' nps ph src = sourceRun b G F n nps ph src) ∧
      (∀ n, u.output.program.2.runF n tgt ≠ .error .diverge →
        ∃ j, D.Final m emb (sourceRun b G F j nps ph src) (u.output.program.2.runF n tgt))

/-- Two bodies with the same production input (site, raw input, slots,
scope and state); only their resolved source may differ. -/
def Body.SameInput (b' b : Body) : Prop :=
  b'.site = b.site ∧ b'.input.raw = b.input.raw ∧ b'.input.returnSlots = b.input.returnSlots ∧
    b'.input.scope = b.input.scope ∧ b'.input.before = b.input.before

/-- **Coverage of t0's fragment**: every actual production run whose emitted
program is in the fragment has a resolved source, at the same site and with
the same raw input, slots, scope and state, that the diagram associates with
it. See "Limitations" in the module docstring: the source is existential. -/
def Diagram.Total (D : Diagram) : Prop :=
  ∀ (b : Body) (u : Emitted), Production b u → Accepted u →
    ∃ b' : Body, b'.SameInput b ∧ ∃ m, D.Assoc b' u m

/-- The production fresh-name policy: the default instance (AST.lean,
`.ofPrefixes "se" "sp" "ie" "mv"`), which every file without its own uses. -/
def productionNames : FreshNames := .ofPrefixes "se" "sp" "ie" "mv"

end Lowering

end Solidity.Goals.Shrink
