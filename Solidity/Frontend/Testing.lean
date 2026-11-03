import Solidity.Frontend.Problems
import Solidity.Calculus.SolSpec
import Solidity.Calculus.CallbackDerive
import Solidity.Calculus.Recursion
import Solidity.Calculus.RecursionCallback
import Solidity.Calculus.ProveChunked
import Solidity.Tools.Preconditions
import Solidity.Tools.SourceCounterexample
import Solidity.Tools.DirectArithmetic

/-!
# Testing imported Solidity files

The machine-readable entry point used by `scripts/test-solidity.mjs`.
The default CLI mode retains a kernel-checked declaration and an axiom check.
The explicit `sol.testing.direct` mode returns trusted runtime decisions with
no per-result certificate, marked `verification: direct` in the report.
An unfinished search stays pending; import gaps remain visible.

A plain obligation whose formula hands control to a callee that may call
back (`Fml.callsBack false`: a `try`, a value call) is stated as
`ValidT .noCallback N.f.problem`, the callee changing the state as it may
(`docs/options.md`, O7), and proved by `sol_prove`'s walk of `ProvesC`; the
others as `⊢ N.f.problem`, whose `Fml.Valid` is the same reading there
(`validT_noCallback_iff`).  One with a recursive call (`Stmt.callRec`) is
stated as `Fml.Valid N.f.problem` and proved by `rec_auto`, each recursive call
by the contract `true`/`true` proved by induction over its frames
(`docs/kernel-port.md`, "Recursion"): the search does no induction.  Whether
it calls back is read off one frame of each unrolling (`sol_no_callback`);
where it does, it is stated as `ValidT .noCallback N.f.problem` and proved
by `rec_auto_c` (`Calculus/RecursionCallback.lean`).  A plain walk longer
than `oneCheckSteps` is checked in chunks (`Seq.proveChunked`), each leaf
searched as `sol_prove?` searches it (`Derive.searchLeaf`).
-/

namespace Solidity.Frontend

open Lean Elab Command Meta

register_option sol.benchmark : Bool := {
  defValue := false
  descr := "emit wall-clock phase timings for imported Solidity verification"
}

register_option sol.testing.direct : Bool := {
  defValue := false
  descr := "return direct verifier results without constructing per-result proof certificates"
}

register_option sol.testing.closedSpecs : Bool := {
  defValue := false
  descr := "try a bounded closed derivation for specifications before semantic tactics"
}

register_option sol.benchmark.tactics : Bool := {
  defValue := false
  descr := "profile specification tactics (adds stack frames; prefer native diagnostics)"
}

private def benchmarkStart : CoreM (Option Nat) := do
  if sol.benchmark.get (← getOptions) then return some (← IO.monoNanosNow)
  return none

private def benchmarkEnd (phase function : String) (start : Option Nat) : CoreM Unit := do
  if let some start := start then
    IO.eprintln ("SOLKEY_BENCH " ++ (Json.mkObj [
      ("phase", toJson phase), ("function", toJson function),
      ("nanos", toJson ((← IO.monoNanosNow) - start))]).compress)

/-- Time a frontend command without changing its options or admission checks. -/
elab "#solkey_benchmark " phase:str " in " cmd:command : command => do
  let start ← liftCoreM benchmarkStart
  try elabCommand cmd
  finally liftCoreM <| benchmarkEnd phase.getString "" start

elab "sol_benchmark " phase:str " in " tac:tactic : tactic => do
  let start ← benchmarkStart
  try Tactic.evalTactic tac
  finally benchmarkEnd phase.getString "" start

private def ImportRow.displayName (r : ImportRow) : String :=
  if r.sourceName.isEmpty then r.name else r.sourceName

private def ImportRow.signature (r : ImportRow) : String :=
  if r.sourceSignature.isEmpty then
    s!"{r.displayName}({",".intercalate (r.params.map Prod.snd)})"
  else r.sourceSignature

/-- Normalize Solidity's integer type aliases without changing punctuation or
substrings of declaration names. Accept ABI-style selectors as well as the
source frontend's `uint`/`int` spelling. -/
def functionSelectorKey (selector : String) : String := Id.run do
  let alias (word : String) : String :=
    if word == "uint256" then "uint" else if word == "int256" then "int" else word
  let mut out := ""
  let mut word := ""
  for c in selector.toList do
    if c.isAlphanum || c == '_' || c == '$' then word := word.push c
    else
      out := (out ++ alias word).push c
      word := ""
  return out ++ alias word

/-- Select by source name, generated name, or a signature with type aliases. -/
def ImportRow.matchesSelector (r : ImportRow) (selector : String) : Bool :=
  selector == r.name || selector == r.displayName ||
    functionSelectorKey selector == functionSelectorKey r.signature

/-- `t`, elaborated with no metavariable left. -/
private def elabClosed (t : Term) : TermElabM Expr := do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- Process-local serials for import origins. `modifyGet` allocates each
unbounded natural atomically, including concurrent native imports. -/
private initialize nextAuditOrigin : IO.Ref Nat ← IO.mkRef 0

/-- Derived source environments inherit their origin. Another import, even
of equal module names and sizes, gets a fresh serial. Missing initial state
never enables cache reuse. Do not use `Ref.ptrEq`: on the pinned runtime it
compares the references' content pointers, so two Unit refs compare equal. -/
private initialize auditOrigin : EnvExtension (Option Nat) ←
  registerEnvExtension
    (nextAuditOrigin.modifyGet fun n => (some (n + 1), n + 1)) (asyncMode := .local)

/-- Successful imported axiom closures, tied to their loaded origin. Retain
that immutable import snapshot while its audited names are cached. -/
private initialize importedAudit : IO.Ref (Option (Nat × Environment × NameSet)) ← IO.mkRef none

/-- Check the standard-axiom policy, reusing only successful imported closures.
This returns a policy decision, not a complete axiom inventory. -/
def usesOnlyStandardAxioms (name : Lean.Name) : CoreM Bool := do
  let env ← getEnv
  let origin := auditOrigin.getState env
  let cached ← importedAudit.get
  let visited ← match origin, cached with
    | some origin, some (old, _, visited) =>
      pure (if origin == old then visited else {})
    | _, _ => pure {}
  let (_, state) := ((CollectAxioms.collect name).run env).run { visited }
  if state.axioms.all (standardAxioms.contains ·) then
    if let some origin := origin then
      let imported := state.visited.foldl (fun names n =>
        if env.isImportedConst n && (env.checked.get.find? n).isSome then names.insert n else names) ({} : NameSet)
      importedAudit.set (some (origin, env.importEnv?.getD env, imported))
  return state.axioms.all (standardAxioms.contains ·)

/-- Whether the obligation `p` may hand control to a callee that calls back
under `transferSemantics:noCallback` (`Fml.callsBack false`), run as compiled
code on its value (`Symex.evaluable`: a `whnf` of it may pass `maxRecDepth`);
`true` where it does not run. -/
private def callsBackE (N : Lean.Name) (φ : Expr) : TermElabM Bool := do
  let φ ← Symex.evaluable φ
  let e ← elabClosed (← `(Fml.callsBack (C := $(mkCIdent N)) false $(← Term.exprToSyntax φ)))
  tryCatchRuntimeEx (unsafe evalExpr Bool (mkConst ``Bool) e) fun _ => pure true

/-- Whether the obligation `p`, which has a recursive call, provably hands
control to no callee under `transferSemantics:noCallback`: `sol_no_callback`
reads each unrolling off one frame (its `whnf` would unroll them). -/
private def noCallbackRecE (N : Lean.Name) (φ : Expr) : TermElabM Bool := do
  let φ ← Symex.evaluable φ
  let ty ← elabClosed (← `(Fml.callsBack (C := $(mkCIdent N)) false
    $(← Term.exprToSyntax φ) = false))
  let g ← mkFreshExprSyntheticOpaqueMVar ty
  let tac ← `(tactic| sol_no_callback)
  tryCatchRuntimeEx (do
      let gs ← Tactic.run g.mvarId! (Tactic.evalTactic tac)
      return gs.isEmpty)
    fun _ => pure false

/-- Whether `e`, or a declaration of the import `N` it names, has a
recursive call (`Stmt.callRec`). -/
private partial def hasCallRec (N : Lean.Name) (e : Expr) (fuel : Nat := 8) : MetaM Bool := do
  if (e.find? (·.isConstOf ``Stmt.callRec)).isSome then return true
  if fuel == 0 then return false
  for c in e.getUsedConstants do
    if N.isPrefixOf c then
      if let some v := (← getConstInfo c).value? then
        if ← hasCallRec N v (fuel - 1) then return true
  return false

/-- Whether the program `n` exposes nothing (`Prog.exposesNone`), reduced
by `whnf`; `false` where it does not reduce. -/
private def exposesNoneE (n : Lean.Name) : TermElabM Bool := do
  let e ← elabClosed (← `(Prog.exposesNone $(mkCIdent n)))
  let v ← withTransparency .all <| whnf e
  return v.isConstOf ``Bool.true

/-- **The tails reading of the import `N`** (`docs/options.md`, O6): `.clean`
when every function a transaction may run (every row but an internal one)
elaborated, takes no storage reference, and exposes nothing
(`Prog.exposesNone`), so that clean tails are the contract's invariant
(`ReachableBy.cleanTail`); `.solc` otherwise. -/
def contractTailMode (N : Lean.Name) (rows : List ImportRow) : CommandElabM TailMode :=
  liftTermElabM do
    for r in rows do
      if r.tag == .internal then continue
      unless r.status == .elaborated do return .solc
      if r.paramTypes.any (fun t => t matches .alias _) then return .solc
      let ok ← tryCatchRuntimeEx (exposesNoneE (r.declName N)) fun _ => pure false
      unless ok do return .solc
    return .clean

/-- The longest walk a test checks in one kernel check; a longer one is
checked `chunkSteps` steps at a time (`sol_prove (chunk := n)`,
`Calculus/ProveChunked.lean`), as one check of it may pass the memory a
session has (`docs/loops.md`). -/
def oneCheckSteps : Nat := 1024

/-- The steps of a chunk of a walk past `oneCheckSteps`. -/
def chunkSteps : Nat := 128

/-- Retain an exact-goal refutation only after kernel and transitive axiom
checks. JSON is presentation of the candidate used by that same proof. -/
private def testCounterexample (ty : Expr) (name : Lean.Name) (r : ImportRow) :
    TermElabM (Option Json) := do
  let saved ← Term.saveState
  let messages ← Core.getMessageLog
  let result ← withCurrHeartbeats <| tryCatchRuntimeEx (do
    let some witness ← Tools.refuteSource? ty | return none
    if witness.proof.hasMVar || witness.proof.hasFVar || witness.proof.hasSorry then return none
    addDecl <| .thmDecl {name, levelParams := [], type := mkNot ty, value := witness.proof}
    let axioms ← collectAxioms name
    unless axioms.all (standardAxioms.contains ·) do return none
    let .ok arguments := witness.report.getObjValAs? (Array Json) "arguments" | return none
    let arguments := arguments.map fun argument =>
      match argument.getObjValAs? String "modelName" with
      | .error _ => argument
      | .ok modelName => match List.findIdx? (fun (p : String × String) => p.1 == modelName) r.params with
        | none => argument
        | some index => argument.setObjVal! "paramIndex" (toJson index)
    return some <| witness.report
      |>.setObjVal! "arguments" (toJson arguments)
      |>.setObjVal! "certified" (toJson true)
      |>.setObjVal! "goalKind" (toJson "fmlValid")
      |>.setObjVal! "certificateDeclaration" (toJson name.toString)
      |>.setObjVal! "axioms" (toJson (axioms.map Lean.Name.toString)))
    fun _ => pure none
  if result.isNone then saved.restore
  else Core.setMessageLog messages
  return result
/-- The original source obligation, including a specified function's clauses. -/
def testFormula (N : Lean.Name) (r : ImportRow) : TermElabM Expr := do
  if r.tag != .specified then return mkConst (r.declName N ++ `problem)
  let stx ← `(cspec[$(mkCIdent N)]{ $(mkIdent (.mkSimple r.name)) })
  let φ ← Term.withoutErrToSorry <| Term.elabTerm stx none
  Term.synthesizeSyntheticMVarsNoPostponing
  let φ ← instantiateMVars φ
  if φ.hasSorry then throwError "the specification does not elaborate"
  return φ

/-- The same tails premise used by source verification, for inspection. -/
def testTailMode (N : Lean.Name) (r : ImportRow) (tail : TailMode) (φ : Expr) :
    TermElabM TailMode := do
  if tail != .clean || r.tag == .specified then return .solc
  if ← hasCallRec N (← Symex.evaluable φ) then return .solc
  return if ← callsBackE N φ then .solc else .clean

/-- Whether a proof tree of the ordinary calculus can describe this obligation. -/
def testOrdinaryTree (N : Lean.Name) (φ : Expr) : TermElabM Bool := do
  if ← hasCallRec N (← Symex.evaluable φ) then return false
  return !(← callsBackE N φ)

initialize registerTraceClass `Solidity.Frontend.testingStrategy

/-- Count at most `remaining` existing expression nodes, without unfolding or
re-evaluating the typed formula. This selects a checking strategy only. -/
private def expressionNodesLeft : Expr → Nat → Nat
  | _, 0 => 0
  | .app f a, n + 1 => expressionNodesLeft a (expressionNodesLeft f n)
  | .forallE _ d b _, n + 1 | .lam _ d b _, n + 1 =>
      expressionNodesLeft b (expressionNodesLeft d n)
  | .letE _ t v b _, n + 1 =>
      expressionNodesLeft b (expressionNodesLeft v (expressionNodesLeft t n))
  | .mdata _ e, n + 1 | .proj _ _ e, n + 1 => expressionNodesLeft e n
  | _, n + 1 => n

/-- Testing shares large typed proofs; small goals use the original immediate
checker from the start. This changes neither admission nor any proof budget. -/
def testingShares (formula : Expr) : Bool := expressionNodesLeft formula 12288 == 0

initialize registerTraceClass `Solidity.Frontend.specProposal

/-! A smaller closed-spec certificate. Dropping premises strengthens the leaf;
only literal `true = true` premises are omitted. The original closer remains
available when the smaller formula does not close. -/
namespace SpecProposal
open Solidity Decide
variable {C : Contract}

def trivialPremise (P : LFml C) : Bool :=
  match P with
  | @LFml.eq _ .bool a b => a.isTT && b.isTT
  | _ => false

def trim (φ : LFml C) : LFml C := φ.dropPrem trivialPremise

def check (ψ : Fml C []) : Option Bool :=
  (ψ.toLS true SymS.init).map fun l => l.boundsOk && (trim l).decideLift

theorem check_valid {ψ : Fml C []} (h : check ψ = some true) : Fml.Valid ψ := by
  simp only [check, Option.map_eq_some_iff, Bool.and_eq_true] at h
  obtain ⟨l, hl, _, hc⟩ := h
  exact Fml.Valid.of_toLS hl (fun g ν => LFml.dropPrem_holds trivialPremise g l ν (LFml.decideLift_valid hc g ν))

def leaf {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) : Option (List (Seq.SLeaf C)) :=
  if (H.wrap φ).modalFree then
    match check (H.wrap φ) with
    | some true => some []
    | _ => Seq.leafS H φ
  else Seq.leafS H φ

theorem leaf_sound {R : RuleSet} {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ)
    (ls : List (Seq.SLeaf C)) (h : leaf H φ = some ls)
    (hl : ∀ l ∈ ls, Proves C R [] l.2.1 l.2.2) : Proves C R [] H φ := by
  unfold leaf at h
  split at h
  · split at h
    · exact Proves.closeHolds (check_valid ‹_›) ‹_›
    · exact Seq.leafS_sound H φ ls h hl
  · exact Seq.leafS_sound H φ ls h hl

def residue (steps : Nat) (R : RuleSet) {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) :=
  (Seq.run R leaf Seq.refuteLanded steps H φ steps).map (·.1)

theorem sound (steps : Nat) {R : RuleSet} {Γ : Ctx} {H : Hyps C [] Γ} {φ : Fml C Γ}
    {ls : List (Seq.SLeaf C)} (h : residue steps R H φ = some ls)
    (hl : ∀ l ∈ ls, Proves C R [] l.2.1 l.2.2) : Proves C R [] H φ := by
  obtain ⟨⟨ls', b'⟩, hr, he⟩ := Option.map_eq_some_iff.1 h
  cases he
  exact Seq.run_sound (P := fun l : Seq.SLeaf C => Proves C R [] l.2.1 l.2.2)
    leaf_sound (fun {_} H c h {_ _} live => Seq.refuteLanded_sound H c h live)
    _ H φ _ _ _ hr hl

def quoteLeaf (c : Lean.Expr) (np : Option Nat) {Γ : Ctx}
    (H : Hyps C [] Γ) (φ : Fml C Γ) : Option (List Lean.Expr) :=
  if (H.wrap φ).modalFree then
    match check (H.wrap φ) with
    | some true => some []
    | _ => Seq.leafQuoteS c np H φ
  else Seq.leafQuoteS c np H φ

def quoteResidue (steps : Nat) (R : RuleSet) (c : Lean.Expr) (np : Option Nat)
    {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) :=
  (Seq.run R (quoteLeaf c np) Seq.refuteLanded steps H φ steps).map (·.1)

end SpecProposal

/-- Run the executable checker and bounded counterexample search. This is a
trusted-verifier result: no proof term or declaration is constructed. -/
def directResult (C : Contract) (φ : Fml C []) : Json :=
  if Fml.callsBack false φ then
    Json.mkObj [("status", toJson "unsupported"), ("reason", toJson "unknown: callback reading")]
  else
    match SpecProposal.residue 128 .all .nil φ with
    | some [] => Json.mkObj [("status", toJson "proved"), ("reason", toJson "")]
    | _ => if Tools.directArithmetic φ then
        Json.mkObj [("status", toJson "proved"), ("reason", toJson "")]
      else match Tools.directSourceWitness C φ with
      | some witness => Json.mkObj [("status", toJson "refuted"), ("reason", toJson "counterexample found"),
          ("counterexample", witness)]
      | none => Json.mkObj [("status", toJson "pending"), ("reason", toJson "checker did not decide")]

/-- Reuse the existing symbolic/arithmetic solver as a trusted decision
procedure when the executable leaf checker is incomplete. Any proof-shaped
intermediates and auxiliary declarations are discarded, not certified. -/
private def directSemantic (C φ : Expr) : TermElabM Bool := do
  let saved ← Term.saveState
  let solved ← tryCatchRuntimeEx (withOptions (debug.skipKernelTC.set · true) do
    Term.withoutErrToSorry do
      let g ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Fml.Valid) C φ)
      let goals ← Tactic.run g.mvarId! (Tactic.evalTactic (← `(tactic| sol_spec_try)))
      let result ← instantiateMVars g
      return goals.isEmpty && !result.hasMVar && !result.hasFVar && !result.hasSorry)
    (fun _ => pure false)
  saved.restore
  return solved

/-- Check the source obligation directly, without adding a theorem to Lean's
logical environment. Unsupported readings remain unknown. -/
def testDirectObligation (N : Lean.Name) (r : ImportRow)
    (counterexampleOutput : IO.Ref (Option Json)) : CommandElabM (String × String × TailMode) :=
  withScope (fun sc => { sc with openDecls := .simple `Solidity [] :: sc.openDecls }) <|
    liftTermElabM <| withCurrHeartbeats <| tryCatchRuntimeEx (do
      unless r.tag == .specified || (← getEnv).contains (r.declName N ++ `problem) do
        return ("unsupported", "unknown: no scoped obligation", .solc)
      let directStart ← benchmarkStart
      let φ ← testFormula N r
      benchmarkEnd "direct-formula" r.name directStart
      if ← hasCallRec N φ then
        return ("unsupported", "unknown: direct checker does not handle recursive or callback readings", .solc)
      benchmarkEnd "direct-classify" r.name directStart
      let executableStart ← benchmarkStart
      let C := mkConst N
      let value := mkApp2 (mkConst ``directResult) C (← Symex.evaluable φ)
      -- Only a throwaway executable returning JSON is compiled here. No
      -- theorem is added, and evalExpr restores the temporary environment.
      let result ← withOptions (debug.skipKernelTC.set · true) <|
        unsafe Meta.evalExpr Json (mkConst ``Json) value
      benchmarkEnd "direct-executable" r.name executableStart
      let status ← Lean.ofExcept (result.getObjValAs? String "status")
      let reason ← Lean.ofExcept (result.getObjValAs? String "reason")
      if status == "pending" then
        if ← directSemantic C φ then
          benchmarkEnd "direct" r.name directStart
          return ("proved", "", .solc)
      if let .ok witness := result.getObjVal? "counterexample" then
        let arguments ← Lean.ofExcept (witness.getObjValAs? (Array Json) "arguments")
        let arguments := arguments.map fun argument =>
          match argument.getObjValAs? String "modelName" with
          | .error _ => argument
          | .ok modelName => match List.findIdx? (fun (p : String × String) => p.1 == modelName) r.params with
            | none => argument
            | some index => argument.setObjVal! "paramIndex" (toJson index)
        counterexampleOutput.set (some (witness.setObjVal! "arguments" (toJson arguments)))
      benchmarkEnd "direct" r.name directStart
      return (status, reason, .solc))
    (fun e => do pure ("error", ← e.toMessageData.toString, .solc))

/-- Propose a small, closed derivation. The compiled walk is only an oracle:
its equality certificate remains explicitly typed in the returned proof and
is checked by the final addDecl. Open residues do not pay for a kernel replay.
A rejected proposal is retried by testObligation under the original deadline. -/
private def closedSpecProof? (C formula : Expr) : TermElabM (Option Expr) := do
  if expressionNodesLeft formula 2048 == 0 then return none
  let saved ← Term.saveState
  let messages ← Core.getMessageLog
  let result ← tryCatchRuntimeEx (Budget.within 5000 do
    Term.withoutErrToSorry do
      let phi ← Symex.evaluable formula
      -- Whole-leaf state normalization is the measured expensive case.
      -- Avoid probing trivial returns and pure branches that gain nothing.
      unless (phi.find? fun e => e.isConstOf ``Stmt.assign ||
          e.isConstOf ``Stmt.assignMem).isSome do return none
      let R := mkConst ``RuleSet.all
      let H := mkApp2 (mkConst ``Hyps.nil) C (ctxE [])
      let some ns := C.constName? | return none
      let np ← Seq.paramCount H phi
      let qTy := mkApp (mkConst ``Option [0]) (mkApp (mkConst ``List [0]) (mkConst ``Expr))
      let some [] ← unsafe Meta.evalExpr (Option (List Expr)) qTy
        (mkAppN (mkConst ``SpecProposal.quoteResidue)
          #[C,toExpr (128:Nat),R,quoteConstName ns,toExpr np,ctxE [],H,phi]) | return none
      let leafTy := mkApp (mkConst ``Seq.SLeaf) C
      let listTy := mkApp (mkConst ``List [0]) leafTy
      let resTy := mkApp (mkConst ``Option [0]) listTy
      let nil := mkApp (mkConst ``List.nil [0]) leafTy
      let someNil := mkApp2 (mkConst ``Option.some [0]) listTy nil
      let equality := mkApp3 (mkConst ``Eq [1]) resTy
        (mkAppN (mkConst ``SpecProposal.residue) #[C,toExpr (128:Nat),R,ctxE [],H,formula]) someNil
      let refl := mkApp2 (mkConst ``Eq.refl [1]) resTy someNil
      let certificate := mkApp2 (mkConst ``id [0]) equality refl
      let derivation := mkAppN (mkConst ``SpecProposal.sound)
        #[C,toExpr (128:Nat),R,ctxE [],H,formula,nil,certificate,
          mkApp2 (mkConst ``Seq.SLeaf.nil) C R]
      let proof := mkAppN (mkConst ``Proves.fmlValid) #[C,R,formula,derivation]
      if proof.hasMVar || proof.hasFVar || proof.hasSorry then return none
      return some proof) (fun _ => pure none)
  if result.isNone then saved.restore else Core.setMessageLog messages
  return result

/-- Test one imported obligation. Search constructs a proof term; `addDecl`
checks it in the kernel before it can be reported as proved. Open goals are
pending; budget exhaustion is an error. Neither is evidence a claim is false. -/
def testObligation (N : Lean.Name) (r : ImportRow) (tail : TailMode := .solc)
    (showGoals : Bool := false)
    (counterexampleOutput : Option (IO.Ref (Option Json)) := none) :
    CommandElabM (String × String × TailMode) := do
  let f := r.declName N
  let env ← getEnv
  unless r.tag == .specified || env.contains (f ++ `problem) do
    return ("unsupported", "no scoped obligation", .solc)
  -- the reading an obligation is stated under, kept for an error past that point
  let modeRef ← IO.mkRef TailMode.solc
  withScope (fun sc => { sc with openDecls := .simple `Solidity [] :: sc.openDecls }) <|
    liftTermElabM <| withCurrHeartbeats do
      let usedShared ← IO.mkRef false
      let attempt (share : Bool) : TermElabM (String × String × TailMode) :=
        withOptions (·.setBool `sol.prove.sharedResidues false) <| tryCatchRuntimeEx (do
        let prepared ← benchmarkStart
        let C := mkConst N
        -- a specification's obligation, scoped
        let spec? ← if r.tag == .specified then do
            -- a specification that does not elaborate is an error, not a
            -- `sorry`; logged too, as the import reports it
            let φ ← try
                testFormula N r
              catch e => logException e; throw e
            if φ.hasSorry then throwError "the specification does not elaborate"
            pure (some φ)
          else pure none
        -- a recursive call: `rec_auto`, each call by its callee's contract
        -- (its `requires`/`ensures`, else `true`/`true`) proved by induction
        -- over the frames (a specified row has no `N.f.problem`: `(← …)` in a
        -- `&&` would run first)
        let recursive ← match spec? with
          | some φ => hasCallRec N φ
          | none => hasCallRec N (← Symex.evaluable (mkConst (f ++ `problem)))
        -- the callback reading (O7): a recursive call's frames read off one
        -- (`sol_no_callback`), not unrolled by `whnf`
        benchmarkEnd "specification" r.name prepared
        let callback ← benchmarkStart
        let obligation := spec?.getD (mkConst (f ++ `problem))
        let cb ← if recursive then pure !(← noCallbackRecE N obligation)
          else callsBackE N obligation
        benchmarkEnd "callback" r.name callback
        let prepared ← benchmarkStart
        let callbackTy (φ : Expr) : TermElabM Expr := do
          elabClosed (← `(ValidT (C := $(mkCIdent N))
            (.noCallback invariant[$(mkCIdent N)]) $(← Term.exprToSyntax φ)))
        -- a recursive call that may call back, or past a callee that may:
        -- `rec_auto_c`, each call read without callbacks where nothing calls
        -- back, else by a contract over the callback runs (`ProvesC.recContract`)
        if recursive && cb then
          let ty ← callbackTy obligation
          -- the walk reads the formula by its value; the kernel unfolds it
          let goalTy := mkApp ty.appFn! (← Symex.evaluable obligation)
          let g ← mkFreshExprSyntheticOpaqueMVar goalTy
          let tac ← `(tactic| rec_auto_c)
          let pendingMsg := "a recursive call under the callback reading (O7) its contract does not prove"
          let some goals ← tryCatchRuntimeEx (some <$> Tactic.run g.mvarId! (Tactic.evalTactic tac))
              fun _ => pure none
            | return ("pending", pendingMsg, .solc)
          unless goals.isEmpty do return ("pending", pendingMsg, .solc)
          let proof ← instantiateMVars g
          if proof.hasMVar || proof.hasFVar then return ("error", "incomplete proof term", .solc)
          let name := f ++ `tested
          addDecl <| .thmDecl { name, levelParams := [], type := ty, value := proof }
          unless ← usesOnlyStandardAxioms name do
            return ("pending", pendingMsg, .solc)
          return ("proved", "", .solc)
        if recursive then
          let (ty, goalTy) := match spec? with
            | some φ => (mkApp2 (mkConst ``Fml.Valid) C φ, mkApp2 (mkConst ``Fml.Valid) C φ)
            | none => (mkApp2 (mkConst ``Fml.Valid) C (mkConst (f ++ `problem)), mkConst ``True)
          -- the walk reads the formula by its value; the kernel unfolds it
          let goalTy ← if spec?.isSome then pure goalTy else
            pure (mkApp2 (mkConst ``Fml.Valid) C (← Symex.evaluable (mkConst (f ++ `problem))))
          let g ← mkFreshExprSyntheticOpaqueMVar goalTy
          let tac ← `(tactic| rec_auto)
          let pendingMsg := "a recursive call its callee's contract does not prove"
          let some goals ← tryCatchRuntimeEx (some <$> Tactic.run g.mvarId! (Tactic.evalTactic tac))
              fun _ => pure none
            | return ("pending", pendingMsg, .solc)
          unless goals.isEmpty do return ("pending", pendingMsg, .solc)
          let proof ← instantiateMVars g
          if proof.hasMVar || proof.hasFVar then return ("error", "incomplete proof term", .solc)
          let name := f ++ `tested
          addDecl <| .thmDecl { name, levelParams := [], type := ty, value := proof }
          unless ← usesOnlyStandardAxioms name do
            return ("pending", pendingMsg, .solc)
          return ("proved", "", .solc)
        -- the clean-tails reading (O6): a plain obligation of a contract whose
        -- functions expose nothing, under the premise `cleanTail(storage) = true`
        let mode : TailMode := if tail == .clean && spec?.isNone && !cb then .clean else .solc
        modeRef.set mode
        let problem := mkConst (f ++ `problem)
        let premised (φ : Expr) : Expr :=
          if mode == .clean then mkAppN (mkConst ``Fml.imp) #[C, ctxE [],
            mkApp2 (mkConst ``Fml.cleanTail) C (ctxE []), φ] else φ
        let (ty, goalTy) ← if cb then do
            -- Specifications use their actual formula too: they need not have
            -- a generated `problem` declaration.
            let ty ← callbackTy obligation
            pure (ty, mkApp ty.appFn! (← Symex.evaluable obligation))
          else if let some φ := spec? then do
            let ty := mkApp2 (mkConst ``Fml.Valid) C φ
            pure (ty, ty)
          else if mode == .clean then do
            -- the walk reads the formula by its value; the kernel unfolds it
            pure (ProofTree.provesE C (premised problem),
              ProofTree.provesE C (premised (← Symex.evaluable problem)))
          else
            let ty := ProofTree.provesE C problem
            pure (ty, ty)
        let g ← mkFreshExprSyntheticOpaqueMVar goalTy
        let selectedShare := share && testingShares goalTy.appArg!
        benchmarkEnd "goal" r.name prepared
        let search ← benchmarkStart
        trace[Solidity.Frontend.testingStrategy] "{r.name}: cb={cb} mode={repr mode} shared={selectedShare} head={goalTy.appArg!.getAppFn.constName?}"
        let goals ← if cb then do
            usedShared.set selectedShare
            let tac ← `(tactic| sol_prove)
            -- only whether a leaf is left is reported: stop at the first
            withOptions (fun o => o.setBool `sol.prove.stopAtOpen true
                |>.setBool `sol.prove.sharedResidues selectedShare) <|
              Tactic.run g.mvarId! (Tactic.evalTactic tac)
          else if r.tag == .specified then do
            let candidate ← if share && sol.testing.closedSpecs.get (← getOptions) then
                closedSpecProof? C obligation
              else pure none
            if let some proof := candidate then
              usedShared.set true
              trace[Solidity.Frontend.specProposal] "closed128: {r.name}"
              g.mvarId!.assign proof
              pure []
            else
              trace[Solidity.Frontend.specProposal] "semantic: {r.name}"
              let tac ← if sol.benchmark.tactics.get (← getOptions) then
                  `(tactic| ((sol_benchmark "symbolic-execution" in sol_symex); all_goals ((sol_benchmark "closing-preparation" in sol_spec_prep); all_goals try (sol_benchmark "closing-solver" in sol_spec_finish))))
                else `(tactic| sol_spec_try)
              Tactic.run g.mvarId! (Tactic.evalTactic tac)
          else do
            usedShared.set selectedShare
            let out ← IO.mkRef (none : Option Derive.Search)
            let long ← IO.mkRef false
            let _ ← withOptions (·.setBool `sol.prove.sharedResidues selectedShare) <|
                Tactic.run g.mvarId! do
              -- a walk past one kernel check: in chunks, each leaf searched
              try out.set (some (← scopedSearch g.mvarId! (oneCheck := oneCheckSteps) (shareCheck := selectedShare)))
              catch e =>
                unless (← e.toMessageData.toString).startsWith Seq.longWalkNote do throw e
                long.set true
            trace[Solidity.Frontend.testingStrategy] "{r.name}: chunked={← long.get}"
            if ← long.get then
              Tactic.run g.mvarId! do
                let left ← Seq.proveChunked g.mvarId! chunkSteps fun l => do
                  pure (if (← Derive.searchLeaf l Seq.goalFits).isSome then [] else [l])
                Tactic.setGoals left
            else
              let some s ← out.get | throwError "search did not run"
              pure s.open_
        benchmarkEnd "search" r.name search
        unless goals.isEmpty do
          if r.tag == .specified && !cb then
            if let some output := counterexampleOutput then
              if let some witness ← testCounterexample ty (f ++ `refuted) r then
                output.set (some witness)
                return ("refuted", "kernel-checked counterexample to the tested obligation", mode)
          let detail ← if showGoals then do
              let messages ← goals.mapM fun g => return (← Meta.ppGoal g).pretty
              pure ("open proof goals\n" ++ "\n\n".intercalate messages)
            else pure "open proof goals"
          return ("pending", detail, mode)
        let instantiated ← benchmarkStart
        let proof ← instantiateMVars g
        benchmarkEnd "instantiate" r.name instantiated
        if proof.hasMVar || proof.hasFVar then return ("error", "incomplete proof term", mode)
        let name := f ++ `tested
        let checked ← benchmarkStart
        withOptions (Elab.async.set · false) <|
          addDecl <| .thmDecl { name, levelParams := [], type := ty, value := proof }
        benchmarkEnd "kernel" r.name checked
        let audited ← benchmarkStart
        let standard ← usesOnlyStandardAxioms name
        benchmarkEnd "axioms" r.name audited
        unless standard do
          return ("unsupported", "proof uses nonstandard axioms", mode)
        return ("proved", "", mode))
        fun e => return ("error", ← e.toMessageData.toString, ← modeRef.get)

      let saved ← Term.saveState
      let context ← readThe Core.Context
      let deadline := if context.maxHeartbeats == 0 then none
        else some (context.initHeartbeats + context.maxHeartbeats)
      let result ← attempt true
      if result.1 == "proved" || !(← usedShared.get) then return result
      -- Rejected or open proposals cannot retain unchecked search state.
      -- Retry the original policy under the same absolute heartbeat deadline.
      saved.restore
      modeRef.set .solc
      if let some output := counterexampleOutput then output.set none
      let some deadline := deadline | return ← attempt false
      let now ← IO.getNumHeartbeats
      let remaining := deadline - now
      if remaining == 0 then return ("error", "proof proposal exhausted the original heartbeat budget", ← modeRef.get)
      withTheReader Core.Context (fun c => { c with initHeartbeats := now, maxHeartbeats := remaining }) <|
        attempt false

/-- Check a specified row's entry condition separately from its postcondition. -/
def testPreconditions (N : Lean.Name) (r : ImportRow) : CommandElabM (String × String) :=
  withScope (fun sc => { sc with openDecls := .simple `Solidity [] :: sc.openDecls }) <|
    liftTermElabM <| withCurrHeartbeats <| tryCatchRuntimeEx (do
      let φ ← elabClosed (← `(cspec[$(mkCIdent N)]{ $(mkIdent (.mkSimple r.name)) }))
      let name := r.declName N ++ `entryAudited
      match ← Tools.auditPreconditions φ name with
      | .impossible => pure ("impossible", s!"kernel-checked: {name}")
      | .possible => pure ("possible", s!"kernel-checked: {name}")
      | .unknown reason => pure ("unknown", reason))
    fun e => do pure ("unknown", ← e.toMessageData.toString)

/-- Machine-readable testing entry point for a solc import. Listing performs
no proof search. Every selected import row is retained, including gaps and
functions whose specification has no plain box/diamond obligation. -/
syntax (name := solkeyTest) "#solkey_test " ident (&" only " str)?
  (&" from " num)? (&" count " num)? (&" listing")? (&" audit_preconditions")?
  (&" counterexamples")? " to " str : command

@[command_elab solkeyTest]
def elabSolkeyTest : CommandElab := fun stx => do
  let N ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let only? := if stx[2].isNone then none else stx[2][1].isStrLit?
  let first := if stx[3].isNone then 0 else stx[3][1].isNatLit?.getD 0
  let count? := if stx[4].isNone then none else stx[4][1].isNatLit?
  let listing := !stx[5].isNone
  let audit := !stx[6].isNone
  let counterexamples := !stx[7].isNone
  if listing && audit then throwError "precondition auditing requires verification, not listing"
  if listing && counterexamples then throwError "counterexample search requires verification, not listing"
  let direct := sol.testing.direct.get (← getOptions)
  let directFields := if direct then [("verification", toJson "direct")] else []
  let auditFields (status reason : String) : List (String × Json) :=
    if audit then [("preconditions", toJson status), ("preconditionReason", toJson reason)] else []
  let allRows ← reportRows N
  let selected := (allRows.filter fun r => only?.all r.matchesSelector).drop first
  let rows := count?.map (selected.take ·) |>.getD selected
  if rows.isEmpty && (!allRows.isEmpty || only?.isSome) then
    throwError "#solkey_test: no functions selected"
  let output := stx[9].isStrLit?.getD ""
  -- Checkpoint before search, then after every function: a process timeout
  -- preserves completed results and explicitly marks the unattempted rows.
  let mut results : Array Json := rows.toArray.map fun r => Json.mkObj ([
    ("function", toJson r.displayName), ("tag", toJson r.tag.toStr),
    ("signature", toJson r.signature),
    ("sourceId", toJson r.sourceId),
    ("invalidSpecification", toJson ((r.sourceDiagnostic.map (·.name)) == some `solidity.specificationSyntax)),
    ("status", toJson "notRun"), ("reason", toJson "contract run interrupted"),
    ("reading", toJson "solc"), ("elapsedMs", toJson (0 : Nat))] ++ directFields ++
      auditFields "notRun" "contract run interrupted")
  IO.FS.writeFile output (Json.arr results).pretty
  -- the tails reading (O6): clean where every function exposes nothing
  let tailStart ← liftCoreM benchmarkStart
  let tail ← if direct then pure TailMode.solc else contractTailMode N allRows
  liftCoreM <| benchmarkEnd "tails" "" tailStart
  for r in rows, i in [:rows.length] do
    let t0 ← IO.monoMsNow
    let witnessOutput ← IO.mkRef (none : Option Json)
    let (status, reason, mode) ← if r.status != .elaborated then
        pure (r.status.toStr, r.reason, TailMode.solc)
      else if r.tag == .internal || r.tag == .skip then pure (r.tag.toStr, "", .solc)
      else if r.tag != .specified && r.tag.modality?.isNone then
        pure ("unsupported", s!"{r.tag.toStr}: no obligation", .solc)
      else if listing then pure ("ready", "", tail)
      else if direct then testDirectObligation N r witnessOutput
      else testObligation N r tail (counterexampleOutput := if counterexamples then some witnessOutput else none)
    let (preconditions, preconditionReason) ← if !audit then pure ("notRequested", "")
      else if r.status != .elaborated || r.tag != .specified then
        pure ("notApplicable", "no admitted function specification")
      else if direct then pure ("unknown", "entry certificate audit is not run in direct mode")
      else testPreconditions N r
    let elapsed ← IO.monoMsNow
    let witness ← witnessOutput.get
    results := results.set! i <| Json.mkObj ([
      ("function", toJson r.displayName), ("tag", toJson r.tag.toStr),
      ("signature", toJson r.signature),
      ("sourceId", toJson r.sourceId),
      ("invalidSpecification", toJson ((r.sourceDiagnostic.map (·.name)) == some `solidity.specificationSyntax)),
      ("status", toJson status), ("reason", toJson reason),
      ("reading", toJson (if mode == .clean then "clean" else "solc")),
      ("elapsedMs", toJson (elapsed - t0))] ++ directFields ++ auditFields preconditions preconditionReason ++
        (witness.map (fun value => [("counterexample", value)]) |>.getD []))
    IO.FS.writeFile output (Json.arr results).pretty

end Solidity.Frontend
