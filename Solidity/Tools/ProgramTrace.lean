import Solidity.Tools.Elementary

/-!
# Checked program traces for documents

The paper's elementary capture and update exporter is a library API here.
`ProgramTrace.generate` keeps the input formula, splits supported multi-capture
rules and update compositions, and builds a `Fml.Leads` proof. `continueWith`
applies explicitly requested read laws in order. `check` closes the parameters
and submits the proof to the kernel before either command exports anything.

These are semantic reductions, not proofs that the final leaf is valid, nor
certificates for edited TeX. Other strategy rules retain their native size;
frontend lowering and implicit bounds checks are not additional trace steps.
-/

namespace Solidity.ProgramTrace

open Lean Elab Command Meta Latex

/-- A trace and its semantic proof. `administrativeMerges` counts update
pairs with identical rendered endpoints; they remain in the proof. -/
structure Trace where
  first : Expr
  last : Expr
  steps : Array Step
  proof : Expr
  administrativeMerges : Nat := 0

/-- Generate supported capture refinements and, optionally, update-pair
composition. Exhaustion or a blocked program is an error, not completion. -/
def generate (first : Expr) (mergeUpdates : Bool := true)
    (maxSteps : Nat := 800) (maxMergePlans : Nat := 400) : TermElabM Trace := do
  let (steps, proof) ← Elementary.elementaryTrace first maxSteps
  let last := (steps.back?.map (·.line)).getD first
  unless mergeUpdates do return { first, last, steps, proof }
  let (merges, mergeProof, last, administrativeMerges) ←
    Elementary.elementaryMerges last maxMergePlans
  return {
    first, last, steps := steps ++ merges
    proof := (← mkAppM ``Fml.Leads.comp #[proof, mergeProof])
    administrativeMerges }

/-- Extend the current endpoint by exactly the listed laws. A failed law
reports its position, the actual endpoint, and applicable requested laws. -/
def Trace.continueWith (trace : Trace) (laws : Array Lean.Name) : TermElabM Trace := do
  let mut trace := trace
  for h : i in [:laws.size] do
    let name := laws[i]
    let some arrow ← Chain.rwArrow? (mkIdent name) | throwError "unknown read law {name}"
    let some step ← withCurrHeartbeats (Chain.pastStepOf? trace.last name.toString arrow) | do
      let mut available : Array Lean.Name := #[]
      for candidate in laws do
        if available.contains candidate then continue
        if let some law ← Chain.rwArrow? (mkIdent candidate) then
          if (← withCurrHeartbeats (Chain.pastStepOf? trace.last candidate.toString law)).isSome then
            available := available.push candidate
      throwError "read law {i + 1}/{laws.size} ({name}) does not apply; \
        applicable requested laws: {available}\ncurrent endpoint:\n{← exprLatex trace.last}"
    trace := { trace with
      last := step.fml
      proof := (← mkAppM ``Fml.Leads.comp #[trace.proof, ← step.leads trace.last])
      steps := trace.steps.push { rule := step.name, line := step.fml, rw? := some step.rw } }
  return trace

/-- Close every parameter and check the exact first/last pair in the kernel.
The returned declaration states `Fml.Leads`, not validity of the first line. -/
def Trace.check (trace : Trace) (params : Array Expr := #[])
    (levelParams : List Lean.Name := []) : TermElabM Lean.Name := do
  let (C, Γ) ← Chain.lineType trace.first
  let expected := mkApp4 (mkConst ``Fml.Leads) C Γ trace.first trace.last
  unless ← isDefEq (← inferType trace.proof) expected do
    throwError "trace proof has different endpoints"
  -- The telescope supplied for a chain can itself depend on ambient section
  -- variables. Close the whole local context in dependency order, dropping
  -- unused binders afterwards, so formula commands work in sections too.
  let locals := (← getLCtx).getFVars
  let params := locals ++ params.filter (!locals.contains ·)
  let type ← instantiateMVars (← mkForallFVars params expected (usedOnly := true))
  let value ← instantiateMVars (← mkLambdaFVars params trace.proof (usedOnly := true))
  if value.hasMVar || value.hasSorry || type.hasMVar || type.hasSorry then
    throwError "refusing an incomplete program trace proof"
  let name ← mkFreshUserName `program_trace_checked
  withOptions (debug.skipKernelTC.set · false) do
    addDecl (.thmDecl { name, levelParams, type, value })
  return name

/-- No filtering, premise removal or side-line insertion: one recorded
transformation per arrow, with its native or elementary rule name. -/
def Trace.toLatex (trace : Trace) (o : Latex.Options := {}) : MetaM String :=
  derivationLatex trace.first trace.steps
    { o with collapse := [], groups := false, premise := false, sides := some false }

/-- Structured endpoints for document renderers; `checked` names the kernel
declaration produced by `check`. LaTeX strings are presentation, not proof data. -/
def Trace.toJson (trace : Trace) (checked : Lean.Name) (o : Latex.Options := {}) : MetaM Json := do
  let mut rows : Array Json := #[]
  let mut before := trace.first
  for h : i in [:trace.steps.size] do
    let step := trace.steps[i]
    rows := rows.push (Json.mkObj [
      ("index", Lean.toJson i), ("rule", Lean.toJson step.rule),
      ("before", Lean.toJson (← exprLatex before o)), ("after", Lean.toJson (← exprLatex step.line o))])
    before := step.line
  return Json.mkObj [
    ("schemaVersion", Lean.toJson (1 : Nat)), ("relation", Lean.toJson "Fml.Leads"),
    ("checkedDeclaration", Lean.toJson checked.toString),
    ("granularity", Lean.toJson "supported captures and update pairs; other native strategy steps"),
    ("first", Lean.toJson (← exprLatex trace.first o)), ("last", Lean.toJson (← exprLatex trace.last o)),
    ("administrativeMerges", Lean.toJson trace.administrativeMerges), ("steps", .arr rows)]

/-- Read a formula, solc obligation or the first line of a chain declaration.
Chain parameters stay arbitrary, and concrete setup updates stay intact. -/
private def withInput (t : Term) (k : Expr → Array Expr → List Lean.Name → TermElabM String) :
    CommandElabM String := do
  if let `($f:ident) := t then
    if let some φ ← obligation? f.getId then
      return ← runTermElabM fun _ => k φ #[] []
  runTermElabM fun _ => do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let type ← whnfR (← inferType e)
    if type.isAppOf ``Fml then return ← k e #[] []
    forallTelescope type fun xs body => do
      let some (first, _) ← chainSteps? body |
        throwError "expected a scoped formula, solc obligation or chain declaration"
      let levels ← match e.getAppFn with
        | .const name _ => do pure (← getConstInfo name).levelParams
        | _ => pure []
      k first xs levels

private def exportTrace (o : Latex.Options) (laws : Array Lean.Name) (t : Term)
    (json : Bool := false) : CommandElabM String :=
  withInput t fun first params levels => do
    let trace ← (← generate first o.past).continueWith laws
    let checked ← trace.check params levels
    if json then return (← trace.toJson checked o).pretty
    trace.toLatex o

/-- An explicit, ordered read continuation, applied after update composition. -/
syntax traceLaws := "reads " "[" ident,* "]"

private def readLaws (laws : Option (TSyntax ``traceLaws)) : Array Lean.Name :=
  match laws with
  | some laws => laws.raw[2].getSepArgs.map (·.getId)
  | _ => #[]

/-- Display a checked program trace. -/
elab "#latex_program " opts:latexOpt* laws:(traceLaws)? t:term : command => do
  logInfo (← exportTrace (← liftCoreM (elabOpts opts)) (readLaws laws) t)

/-- Write a checked trace, after all requested read laws succeed. -/
elab "#latex_program_file " path:str opts:latexOpt* laws:(traceLaws)? t:term : command => do
  let result ← exportTrace (← liftCoreM (elabOpts opts)) (readLaws laws) t
  IO.FS.writeFile path.getString (result ++ "\n")

/-- Write structured, individually named before/after pairs and proof metadata. -/
elab "#program_trace_json_file " path:str opts:latexOpt* laws:(traceLaws)? t:term : command => do
  let result ← exportTrace (← liftCoreM (elabOpts opts)) (readLaws laws) t true
  IO.FS.writeFile path.getString (result ++ "\n")

end Solidity.ProgramTrace
