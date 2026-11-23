import Solidity.Frontend.Testing
import Solidity.Calculus.AnonLocalCapture
import Solidity.Frontend.ExecutableAst.Shared.Compose
import Solidity.Frontend.ExecutableAst.Shared.Intrinsic

/-! Import-free executable entry point. Compiler JSON is decoded to the existing
surface syntax, then the existing intrinsic elaborator constructs `Fml C []`.
Unsupported input returns a gap; it is never treated as a successful check. -/
namespace Solidity.Tools.DirectRuntime
open Lean Solidity.Frontend
open Solidity.Frontend.ExecutableAst.Shared

/-- Pin the shared executable builder to the existing producer helpers.
No producer implementation is copied and no Lean environment is constructed. -/
private def buildObligation (C : Contract) (name : String) (specified box : Bool) :
    Except String (Fml C []) :=
  Solidity.Frontend.ExecutableAst.Shared.obligation lowerBodyLoops
    (fun C Γ => Problem.callPre C Γ false [] false [] true)
    C name specified box

private structure Stronger {C : Contract} {Γ : Ctx} (φ : Fml C Γ) where
  formula : Fml C Γ
  sound : ∀ σ, holds σ formula → holds σ φ

private def primitivePositions {Γ : Ctx} : (xs : List ((t : LTy) × Idx Γ t)) →
    Option ((ps : AnonLocalCapture.Positions Γ) ×' AnonLocalCapture.keys ps = xs)
  | [] => some ⟨[], rfl⟩
  | ⟨.val p, j⟩ :: xs => do
    let ⟨ps, h⟩ ← primitivePositions xs
    return ⟨⟨p, j⟩ :: ps, congrArg (@List.cons ((t : LTy) × Idx Γ t) ⟨.val p, j⟩) h⟩
  | _ => none

/-- A sound compiled version of the existing anonymous-local leaf preparation.
The copied positions stay intrinsic; its proof is erased from the executable. -/
private def prepareLeaf {C : Contract} : Nat → {Γ : Ctx} → (φ : Fml C Γ) → Stronger φ
  | 0, _, φ => ⟨φ, fun _ h => h⟩
  | n+1, _, .imp a b =>
    let r := prepareLeaf n b
    let skipPremise := match a with | .wellFormed _ => true | _ => false
    if skipPremise then ⟨r.formula, fun σ h _ => r.sound σ h⟩
    else ⟨.imp a r.formula, fun σ h ha => r.sound σ (h ha)⟩
  | n+1, _, .and a b =>
    let ra := prepareLeaf n a
    let rb := prepareLeaf n b
    ⟨.and ra.formula rb.formula, fun σ h => ⟨ra.sound σ h.1, rb.sound σ h.2⟩⟩
  | n+1, _, .upd m U b =>
    let r := prepareLeaf n b
    ⟨.upd m U r.formula, fun _ h => Upd.afterT_imp h (fun τ hτ => r.sound τ hτ)⟩
  | n+1, _, .all x p b =>
    let r := prepareLeaf n b
    ⟨.all x p r.formula, fun σ h v => r.sound (σ.push v) (h v)⟩
  | n+1, _, .bind _ x (.val p) b =>
    let r := prepareLeaf n b
    ⟨.all x p r.formula, fun σ h v => r.sound (σ.push v) (h v)⟩
  | n+1, _, .bind m x t b =>
    let r := prepareLeaf n b
    ⟨.bind m x t r.formula, fun σ h => Modality.forallB_imp (fun v hv => r.sound (σ.push v) hv) h⟩
  | n+1, _, .anon xs b =>
    match primitivePositions xs with
    | none => ⟨.anon xs b, fun _ h => h⟩
    | some ⟨ps, he⟩ =>
      let r := prepareLeaf n b
      let names := Var.fresh "directAnon"
      let k := max r.formula.maxIdx C.rootMaxIdx + 1
      let plan := prepareLeaf n (AnonLocalCapture.plan .box names k ps r.formula)
      ⟨plan.formula, fun σ h =>
        Eq.mp (congrArg (fun keys => holds σ (.anon keys b)) he)
          (fun values => r.sound (σ.anon (AnonLocalCapture.keys ps) values)
            (AnonLocalCapture.sound .box names k ps r.formula σ (plan.sound σ h) values))⟩
  | _+1, _, φ => ⟨φ, fun _ h => h⟩

/-- Apply the compiled arithmetic decision procedure to each symbolic leaf,
including the preservation/exit leaves produced by loop invariants. Applying
it only to the original modal formula misses these ordinary arithmetic goals. -/
private def arithmeticLeaf {C : Contract} {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) :
    Option (List (Seq.SLeaf C)) :=
  match SpecProposal.leaf H φ with
  | some [] => some []
  | result => if (H.wrap φ).modalFree && Tools.directArithmetic (prepareLeaf 512 (H.wrap φ)).formula
      then some [] else result

private def compiledResult (C : Contract) (φ : Fml C []) : Json :=
  if !(Fml.callsBack false φ) &&
      ((Seq.run .all arithmeticLeaf Seq.refuteLanded 1024 .nil φ 1024).map (·.1)).any List.isEmpty then
    Json.mkObj [("status", toJson "proved"), ("reason", toJson "")]
  else Solidity.Frontend.directResult C φ

private partial def hasAnnotatedLoop (ss : List RawStmt) : Bool :=
  ss.any fun s =>
    let annotated := match s with
      | .whileLoop a .. | .forLoop a .. | .doWhile a .. | .loop a .. =>
        !a.inv.isEmpty || !a.qinv.isEmpty || a.dec.isSome || a.unwind.isSome
      | _ => false
    annotated || s.blocks.any hasAnnotatedLoop

/-- Annotations choose proof rules; they do not change loop execution
(`Stmt.run_loop`). A bounded exact-unrolling retry can therefore close short
loops whose quantified invariant lies outside the executable leaf fragment. -/
private partial def unrollLoops (ss : List RawStmt) : List RawStmt :=
  ss.map fun s => match s.mapBlocks unrollLoops with
    | .whileLoop _ c b => .whileLoop {} c b
    | .forLoop _ i c u b => .forLoop {} i c u b
    | .doWhile _ b c => .doWhile {} b c
    | .loop _ c b => .loop {} c b
    | s => s

/-- Data retained by the opt-in actual invocation. Constructor privacy is
only ingress discipline, not source/event authentication. A later metadata
consumer must authenticate the retained declaration and its provenance. -/
structure RequestGoalCapture where
  private mk ::
  request : Json
  source : Json
  member : Json
  sourceId : Int
  functionName : String
  specified : Bool
  box : Bool
  retry : Bool
  contract : Contract
  formula : Fml contract []
  /-- Original evaluation that caused the existing annotated-loop retry. -/
  priorResult : Option Json := none
  /-- Actual result of this evaluation; `none` denotes listing-only capture. -/
  result : Option Json := none

/-- Inspect the initial retained result using the very predicate that selected
its retry. This performs no request execution or search. `none` refuses listing,
retry captures and malformed/unsupported results. It is not source admission. -/
def RequestGoalCapture.retryRequired? (goal : RequestGoalCapture) : Option Bool := do
  if goal.retry || goal.priorResult.isSome then none else do
    let result ← goal.result
    let status ← (result.getObjValAs? String "status").toOption
    let [(name, declaration)] := goal.contract.funs | none
    if name != goal.functionName then none else
      match status with
      | "proved" | "refuted" => some false
      | "pending" => some (hasAnnotatedLoop declaration.body)
      | _ => none

/-- A lazy request plan shares the old computation between report-only and
opt-in capture interpreters. Ordinary execution does not accumulate goals. -/
private inductive RequestPlan where
  | done (result : Except String Json)
  | listing (goal : RequestGoalCapture) (next : Unit → RequestPlan)
  | verify (goal : RequestGoalCapture) (next : Json → RequestPlan)

private def RequestPlan.report : RequestPlan → Except String Json
  | .done result => result
  | .listing _ next => (next ()).report
  | .verify goal next =>
    let result := compiledResult goal.contract goal.formula
    (next result).report

/-- The private trace keeps captures through a later report error. Public
projection retains captures only when the complete request succeeds. -/
private def RequestPlan.trace : RequestPlan → Except String Json × Array RequestGoalCapture
  | .done result => (result, #[])
  | .listing goal next =>
    let rest := (next ()).trace
    (rest.1, #[goal] ++ rest.2)
  | .verify goal next =>
    let result := compiledResult goal.contract goal.formula
    let rest := (next result).trace
    (rest.1, #[{ goal with result := some result }] ++ rest.2)

private theorem RequestPlan.trace_report (plan : RequestPlan) :
    plan.trace.1 = plan.report := by
  induction plan with
  | done result => rfl
  | listing goal next ih => exact ih ()
  | verify goal next ih => exact ih (compiledResult goal.contract goal.formula)

private def finishRow (n : Json) (name : String) (specified : Bool)
    (result : Json) : Except String Json := do
  let result := match result.getObjVal? "counterexample" with
    | .error _ => result
    | .ok witness => match witness.getObjValAs? (Array Json) "arguments" with
      | .error _ => result
      | .ok args =>
        let args := args.map fun (arg : Json) =>
          match arg.getObjValAs? String "modelName" with
          | .error _ => arg
          | .ok name => match ((J.arrD (J.opt n "parameters" |>.getD .null) "parameters").toList).findIdx?
              (fun p => J.str? p "name" == some name) with
            | none => arg
            | some i => arg.setObjVal! "paramIndex" (toJson i)
        result.setObjVal! "counterexample" (witness.setObjVal! "arguments" (toJson args))
  let result := result.setObjVal! "function" (toJson name)
    |>.setObjVal! "sourceId" (← field n "id")
    |>.setObjVal! "verification" (toJson "direct")
    |>.setObjVal! "reading" (toJson "solc")
    |>.setObjVal! "tag" (toJson (if specified then "specified" else
      if ((keyClauses (docText n)).toOption.getD []).any (·.kind == "box") then "box" else "diamond"))
  return result

/-- Only verification result handling is delayed: all original validation,
selection, error priority, callbacks and ordinary result construction remain. -/
private def requestPlan (request : Json) : Except String RequestPlan := do
  let source ← field request "contract"
  let base ← contract executableReader source
  if (request.getObjVal? "function").isOk && !(request.getObjValAs? String "function").isOk then
    throw "invalid function selector"
  if (request.getObjVal? "sourceId").isOk && !(request.getObjValAs? Int "sourceId").isOk then
    throw "invalid sourceId selector"
  if (request.getObjVal? "listing").isOk && !(request.getObjValAs? Bool "listing").isOk then
    throw "invalid listing flag"
  let mut identities : List Int := []
  for member in ← arr source "nodes" do
    if J.kind member == "FunctionDefinition" then
      let some id := J.id? member | throw "invalid function identity"
      unless id > 0 do throw "invalid function identity"
      if identities.contains id then throw "duplicate function identity"
      identities := id :: identities
  let avoid := source.compress
  let selected := (request.getObjValAs? String "function").toOption
  let selectedId := (request.getObjValAs? Int "sourceId").toOption
  let listing := (request.getObjValAs? Bool "listing").toOption.getD false
  let finish (rows : Array Json) : RequestPlan :=
    .done (if rows.isEmpty then .error "no selected functions" else .ok (Json.arr rows))
  let step (n : Json) (next : Array Json → RequestPlan) (rows : Array Json) : RequestPlan := Id.run do
    let selection : Except String (Option (String × List KeyClause)) := do
      unless (← node n) == "FunctionDefinition" do return none
      let name ← str n "name"
      if selected.isSome && selected != some name then return none
      if selectedId.isSome && selectedId != (n.getObjValAs? Int "id").toOption then return none
      let visibility ← str n "visibility"
      unless visibility == "public" || visibility == "external" do return none
      let clauses ← keyClauses (docText n)
      return some (name, clauses)
    match selection with
    | .error reason => return .done (.error reason)
    | .ok none => return next rows
    | .ok (some (name, clauses)) =>
      let specified := clauses.any (fun c => c.kind == "requires" || c.kind == "ensures")
      let push (result : Json) : RequestPlan :=
        match finishRow n name specified result with
        | .error reason => .done (.error reason)
        | .ok result => next (rows.push result)
      let unsupported (reason : String) := push (Json.mkObj [
        ("status", toJson "unsupported"), ("reason", toJson reason)])
      if clauses.any (·.kind == "skip") then
        return push (Json.mkObj [("status", toJson "skipped"),
          ("reason", toJson "tagged `@custom:key skip`")])
      let initial : Except String (FunDecl × RequestGoalCapture) := do
        let (_, d) ← function executableReader n avoid
        let C := { base with funs := [(name, d)] }
        let φ ← buildObligation C name specified (clauses.any (·.kind == "box"))
        pure (d, (⟨request, source, n, (J.id? n).getD 0, name, specified,
          clauses.any (·.kind == "box"), false, C, φ, none, none⟩ : RequestGoalCapture))
      match initial with
      | .error reason => return unsupported reason
      | .ok (d, goal) =>
        if listing then
          return .listing goal (fun _ => push (Json.mkObj [("status", toJson "ready"), ("reason", toJson "")]))
        return .verify goal fun result =>
          if (result.getObjValAs? String "status").toOption == some "pending" && hasAnnotatedLoop d.body then
            let retried : Except String RequestGoalCapture := do
              let d := { d with body := unrollLoops d.body }
              let C := { base with funs := [(name, d)] }
              let φ ← buildObligation C name specified (clauses.any (·.kind == "box"))
              pure (⟨request, source, n, (J.id? n).getD 0, name, specified,
                clauses.any (·.kind == "box"), true, C, φ, some result, none⟩ : RequestGoalCapture)
            match retried with
            | .error reason => unsupported reason
            | .ok retried => .verify retried push
          else push result
  let plan : Array Json → RequestPlan := Array.foldr step finish (← arr source "nodes")
  return plan #[]

private def successfulTrace (trace : Except String Json × Array RequestGoalCapture) :
    Except String (Json × Array RequestGoalCapture) :=
  trace.1.map (fun result => (result, trace.2))

private theorem successfulTrace_forget (trace : Except String Json × Array RequestGoalCapture) :
    (successfulTrace trace).map Prod.fst = trace.1 := by
  rcases trace with ⟨result, goals⟩
  cases result <;> rfl

/-- Execute one real request and retain its actual initial/retry goals. This
CAN perform the ordinary verifier/model search. Metadata intake must consume
an already retained capture, never call this again merely to discover a goal. -/
def checkWithGoals (request : Json) : Except String (Json × Array RequestGoalCapture) :=
  (requestPlan request).bind (fun plan => successfulTrace plan.trace)

/-- Ordinary report-only evaluation discards each goal before advancing. No
proof term, capture registry or elaborator environment is loaded here. -/
def check (request : Json) : Except String Json :=
  (requestPlan request).bind RequestPlan.report

theorem checkWithGoals_forget (request : Json) :
    (checkWithGoals request).map Prod.fst = check request := by
  cases h : requestPlan request with
  | error reason => simp only [checkWithGoals, check, h, Except.bind, Except.map]
  | ok plan =>
    simp only [checkWithGoals, check, h, Except.bind]
    exact (successfulTrace_forget plan.trace).trans (RequestPlan.trace_report plan)

@[export solidity_direct_check]
def checkString (input : String) : String :=
  let result := do check (← Json.parse input)
  (match result with
  | .ok rows => Json.mkObj [("results", rows)]
  | .error reason => Json.mkObj [("gap", toJson reason)]).compress

end Solidity.Tools.DirectRuntime
