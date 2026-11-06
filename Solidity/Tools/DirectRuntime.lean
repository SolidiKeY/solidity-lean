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

/-- No parser, elaborator environment, proof term or module file is loaded.
The same intrinsic obligation builder and executable verifier are called. -/
def check (request : Json) : Except String Json := do
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
  let mut rows := #[]
  for n in ← arr source "nodes" do
    unless (← node n) == "FunctionDefinition" do continue
    let name ← str n "name"
    if selected.isSome && selected != some name then continue
    if selectedId.isSome && selectedId != (n.getObjValAs? Int "id").toOption then continue
    let visibility ← str n "visibility"
    unless visibility == "public" || visibility == "external" do continue
    let clauses ← keyClauses (docText n)
    let specified := clauses.any (fun c => c.kind == "requires" || c.kind == "ensures")
    let result : Json := if clauses.any (·.kind == "skip") then
        Json.mkObj [("status", toJson "skipped"), ("reason", toJson "tagged `@custom:key skip`")]
      else match (do
        let (_, d) ← function executableReader n avoid
        let C := { base with funs := [(name, d)] }
        let φ ← buildObligation C name specified (clauses.any (·.kind == "box"))
        if listing then return Json.mkObj [("status", toJson "ready"), ("reason", toJson "")]
        let result := compiledResult C φ
        if (result.getObjValAs? String "status").toOption == some "pending" && hasAnnotatedLoop d.body then
          let d := { d with body := unrollLoops d.body }
          let C := { base with funs := [(name, d)] }
          let φ ← buildObligation C name specified (clauses.any (·.kind == "box"))
          return compiledResult C φ
        return result) with
      | .ok result => result
      | .error reason => Json.mkObj [("status", toJson "unsupported"), ("reason", toJson reason)]
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
    rows := rows.push result
  if rows.isEmpty then throw "no selected functions"
  return Json.arr rows

@[export solidity_direct_check]
def checkString (input : String) : String :=
  let result := do check (← Json.parse input)
  (match result with
  | .ok rows => Json.mkObj [("results", rows)]
  | .error reason => Json.mkObj [("gap", toJson reason)]).compress

end Solidity.Tools.DirectRuntime
