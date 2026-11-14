import Solidity.Frontend.Testing
import Solidity.Calculus.AnonLocalCapture

/-! Compiled verdicts over the frontend's exact intrinsic obligations.
The export command creates executable definitions, never a result theorem.
The runtime uses the existing proved rules and closers; their proof fields are
ordinary erased data. No native result is fed back into a Lean proof. -/
namespace Solidity.Tools.FastMode
open Lean Solidity.Frontend

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
private def throughImp {C : Contract} {Γ : Ctx} {b : Fml C Γ}
    (a : Fml C Γ) (r : Stronger b) : Stronger (.imp a b) :=
  ⟨.imp a r.formula, fun σ h ha => r.sound σ (h ha)⟩

private def withoutPremise {C : Contract} {Γ : Ctx} {b : Fml C Γ}
    (a : Fml C Γ) (r : Stronger b) : Stronger (.imp a b) :=
  ⟨r.formula, fun σ h _ => r.sound σ h⟩

private def throughAnd {C : Contract} {Γ : Ctx} {a b : Fml C Γ}
    (ra : Stronger a) (rb : Stronger b) : Stronger (.and a b) :=
  ⟨.and ra.formula rb.formula, fun σ h => ⟨ra.sound σ h.1, rb.sound σ h.2⟩⟩

private def throughUpdate {C : Contract} {Γ Δ : Ctx} {b : Fml C Δ}
    (m : Modality) (U : Upd C Γ Δ) (r : Stronger b) : Stronger (.upd m U b) :=
  ⟨.upd m U r.formula, fun _ h => Upd.afterT_imp h (fun τ hτ => r.sound τ hτ)⟩

private def throughAll {C : Contract} {Γ : Ctx} (x : Var) (p : PrimTy)
    {b : Fml C (.val p :: Γ)} (r : Stronger b) : Stronger (.all x p b) :=
  ⟨.all x p r.formula, fun σ h v => r.sound (σ.push v) (h v)⟩

private def throughValueBind {C : Contract} {Γ : Ctx} (m : Modality) (x : Var) (p : PrimTy)
    {b : Fml C (.val p :: Γ)} (r : Stronger b) : Stronger (.bind m x (.val p) b) :=
  ⟨.all x p r.formula, fun σ h v => r.sound (σ.push v) (h v)⟩

private def throughBind {C : Contract} {Γ : Ctx} (m : Modality) (x : Var) (t : LTy)
    {b : Fml C (t :: Γ)} (r : Stronger b) : Stronger (.bind m x t b) :=
  ⟨.bind m x t r.formula, fun σ h => Modality.forallB_imp (fun v hv => r.sound (σ.push v) hv) h⟩

private def prepareLeaf {C : Contract} : Nat → {Γ : Ctx} → (φ : Fml C Γ) → Stronger φ
  | 0, _, φ => ⟨φ, fun _ h => h⟩
  | n+1, _, .imp a b =>
    let r := prepareLeaf n b
    let skipPremise := match a with | .wellFormed _ => true | _ => false
    if skipPremise then withoutPremise a r else throughImp a r
  | n+1, _, .and a b =>
    let ra := prepareLeaf n a
    let rb := prepareLeaf n b
    throughAnd ra rb
  | n+1, _, .upd m U b =>
    let r := prepareLeaf n b
    throughUpdate m U r
  | n+1, _, .all x p b =>
    let r := prepareLeaf n b
    throughAll x p r
  | n+1, _, .bind m x (.val p) b =>
    let r := prepareLeaf n b
    throughValueBind m x p r
  | n+1, _, .bind m x t b =>
    let r := prepareLeaf n b
    throughBind m x t r
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


private def openBranch {C : Contract} (index : Nat) (leaf : Seq.SLeaf C) : Json :=
  let formula := leaf.2.1.wrap leaf.2.2
  let text := match formula.toLS true Decide.SymS.init with
    | some reduced => reduced.pp
    | none => "intrinsic sequent outside the first-order printer fragment"
  Json.mkObj [("id", toJson s!"open/{index + 1}"), ("sequent", toJson text)]

/-- A pure native verdict. The walk's own remaining sequents are diagnostic
branches, rather than guesses reconstructed from source syntax. -/
def decodeMetadata (encoded : String) : Json :=
  (Json.parse encoded).toOption.getD (Json.mkObj [])

def result (C : Contract) (formula : Fml C []) (encoded : String) (parameters : List String) : Json := Id.run do
  let metadata := decodeMetadata encoded
  let residue := (Seq.run .all arithmeticLeaf Seq.refuteLanded 1024 .nil formula 1024).map (·.1)
  let mut verdict := if residue.any List.isEmpty then
      Json.mkObj [("status", toJson "proved"), ("reason", toJson "")]
    else Solidity.Frontend.directResult C formula
  if (verdict.getObjValAs? String "status").toOption == some "pending" then
    let branches := match residue with
      | some leaves => leaves.toArray.mapIdx fun i leaf => openBranch i leaf
      | none => #[Json.mkObj [("id", toJson "root"),
          ("sequent", toJson ((metadata.getObjValAs? String "obligation").toOption.getD
            "the original intrinsic obligation remains open")),
          ("reason", toJson "symbolic walk exhausted or reached a step with no applicable rule")]]
    verdict := verdict.setObjVal! "openBranches" (toJson branches)
  if let .ok witness := verdict.getObjVal? "counterexample" then
    if let .ok arguments := witness.getObjValAs? (Array Json) "arguments" then
      let arguments := arguments.map fun argument =>
        match (argument.getObjValAs? String "modelName").toOption.bind
            (fun name => parameters.findIdx? (· == name)) with
        | none => argument
        | some i => argument.setObjVal! "paramIndex" (toJson i)
      verdict := verdict.setObjVal! "counterexample" (witness.setObjVal! "arguments" (toJson arguments))
  for key in ["function", "signature", "sourceId", "tag", "reading", "obligation"] do
    if let .ok value := metadata.getObjVal? key then verdict := verdict.setObjVal! key value
  return verdict.setObjVal! "verification" (toJson "native")

/-- A typed obligation is data, so constructing the case table performs no
verification. Selection happens before the generic compiled checker runs. -/
structure Input where
  contract : Contract
  formula : Option (Fml contract [])
  metadata : String
  parameters : List String

@[noinline] def dispatch (cases : List (Int × Input)) (input : String) : String :=
  let outcome : Except String Json := do
    let request ← Json.parse input
    let id ← request.getObjValAs? Int "sourceId"
    let some (_, entry) := cases.find? (·.1 == id) | throw "no selected obligation"
    let verdict := match entry.formula with
      | some formula => result entry.contract formula entry.metadata entry.parameters
      | none => decodeMetadata entry.metadata
    return Json.mkObj [("results", Json.arr #[verdict])]
  (match outcome with
    | .ok value => value
    | .error reason => Json.mkObj [("gap", toJson reason)]).compress

open Lean Elab Command Term Meta

/-- Export exactly the formula the certified frontend states, including its
source entry premises and its inferred clean-tail premise. No search or result
certification occurs during elaboration. -/
syntax (name := exportInput) "#fast_export " ident : command

@[command_elab exportInput]
def elabExportInput : CommandElab := fun stx => do
  let N ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let rows ← reportRows N
  let tail ← contractTailMode N rows
  let body ← liftTermElabM do
    let mut cases : List Expr := []
    let caseType := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Int)
      (mkConst ``Input)
    for row in rows do
      let mut reading := "solc"
      let mut status := if row.status != .elaborated then row.status.toStr
        else if row.tag == .internal || row.tag == .skip then row.tag.toStr
        else if row.tag != .specified && row.tag.modality?.isNone then "unsupported" else "ready"
      let mut reason := row.reason
      let mut formula : Option Expr := none
      if status == "ready" then
        let original ← Symex.evaluable (← testFormula N row)
        if !(← testOrdinaryTree N original) then
          status := "unsupported"
          reason := "native recursive/callback-frame verification is not implemented"
        else
          let mode ← testTailMode N row tail original
          reading := if mode == .clean then "clean" else "solc"
          formula := some (if mode == .clean then
            mkAppN (mkConst ``Fml.imp) #[mkConst N, ctxE [],
              mkApp2 (mkConst ``Fml.cleanTail) (mkConst N) (ctxE []), original]
            else original)
      let displayName := if row.sourceName.isEmpty then row.name else row.sourceName
      let signature := if row.sourceSignature.isEmpty then
        s!"{displayName}({",".intercalate (row.params.map Prod.snd)})" else row.sourceSignature
      let obligation ← match formula with
        | some goal => pure (toString (← ppExpr goal))
        | none => pure ""
      let metadata := Json.mkObj [("function", toJson displayName),
        ("signature", toJson signature), ("sourceId", toJson row.sourceId),
        ("tag", toJson row.tag.toStr), ("reading", toJson reading),
        ("verification", toJson "native"), ("status", toJson status), ("reason", toJson reason),
        ("obligation", toJson obligation)]
      let formulaType := mkApp2 (mkConst ``Fml) (mkConst N) (ctxE [])
      let value ← match formula with
        | some goal => do
            pure (mkApp2 (mkConst ``Option.some [0]) formulaType (← Symex.evaluable goal))
        | none => pure (mkApp (mkConst ``Option.none [0]) formulaType)
      let input ← mkAppM ``Input.mk
        #[mkConst N, value, toExpr metadata.compress, toExpr (row.params.map (·.1))]
      let entry ← mkAppM ``Prod.mk #[toExpr row.sourceId, input]
      cases := entry :: cases
    let entries ← mkListLit caseType cases.reverse
    instantiateMVars (mkApp (mkConst ``dispatch) entries)
  let name := (← getCurrNamespace) ++ `fastInput
  let type ← liftCoreM <| mkArrow (mkConst ``String) (mkConst ``String)
  let declaration := Declaration.defnDecl {
    name, levelParams := [], type, value := body, hints := .abbrev, safety := .safe }
  liftCoreM <| addDecl declaration
  elabCommand (← `(attribute [export $(mkIdent `solidity_direct_check)] $(mkIdent name)))
  liftCoreM <| compileDecl declaration

end Solidity.Tools.FastMode
