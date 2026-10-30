import Solidity.Frontend.PaymentPlan
import Solidity.Semantics.PaymentWorld
import Solidity.Tools.Upstream

/-! # Declaration-checked payment source composition
The command checks the complete source plan, imports the original declarations,
and quotes the actual receive/getter programs. Creation is the existing World
operation. Initializer handle assignment is an existing typed statement; it is
not a supplied observation or an external-response-table entry. -/
namespace Solidity.Frontend.PaymentSource
open Lean Elab Command
open Solidity.ContractWorld

def unitEntry (C : Contract) (name : String) (payable : Bool) : Except String (Entry C Unit) := do
  let ⟨Γ, P⟩ ← Tools.Upstream.entryProg C [.call (.name name) []]
  return { locals := Γ, body := P, result := fun _ => .ok (), payable := payable }

def wordEntry (C : Contract) (raw : List RawStmt) : Except String (Entry C Word) := do
  let ⟨Γ, P⟩ ← Tools.Upstream.entryProg C raw
  return { locals := Γ, body := P, result := fun σ =>
    match Semantics.lookupBy (Var.ofName Tools.retLocal) (Tools.localVals (P.outNames []) σ.env) with
    | some (.uint n) => .ok n
    | _ => .error .exhausted }

def closed (C : Contract) (raw : List RawStmt) : TRes (Prog C [] []) :=
  match Tools.Upstream.entryProg C raw with
  | .error _ => .error .exhausted
  | .ok ⟨Γ, P⟩ => if h : Γ = [] then .ok (h ▸ P) else .error .exhausted

def checked {α : Type} : Except String α → TRes α
  | .ok a => .ok a
  | .error _ => .error .exhausted

/-- The checked source wrapper's typed replay interface. All states and handles
remain indexed by the imported code catalog; JSON observations are outside it. -/
structure Interface {K : Type} (contracts : K → Contract) (owner recipient : K) where
  createsPerCall : Bool
  deploy : World contracts → Address → Address → ContractWorld.Context →
    TRes (World contracts × (Handle owner × Option (Handle recipient)))
  invoke : World contracts → Handle owner → Option (Handle recipient) → ContractWorld.Context → Address →
    String → TRes (World contracts × List String)

syntax (name := paymentSource) "solc_payment_source " str " hash " num " as " ident : command

@[command_elab paymentSource]
def elabPaymentSource : CommandElab := fun stx => do
  let path : TSyntax `str := ⟨stx[1]⟩
  let fixtureHash : TSyntax `num := ⟨stx[3]⟩
  let file := System.FilePath.mk (← getFileName)
  let bytes ← IO.FS.readBinFile ((file.parent.getD ".") / path.getString)
  unless (fnv1a64 bytes).toNat == fixtureHash.getNat do throwError "solidity.paymentSource.hash: input differs"
  let some text := String.fromUTF8? bytes | throwError "payment source must be UTF-8"
  let data ← ofExcept (Json.parse text)
  let ast ← ofExcept (data.getObjVal? "ast")
  let plan ← ofExcept (PaymentPlan.read ast)
  let output := stx[5].getId
  let full := (← getCurrNamespace) ++ output
  let sourceName (s : String) := full ++ `Source ++ Lean.Name.mkSimple s
  for s in [plan.owner, plan.target] do
    let n := mkIdent (sourceName s)
    elabCommand (← `(solc_import $path hash $fixtureHash as $n testing))
  let targetName := sourceName plan.target
  let ownerName := sourceName plan.owner
  let targetC ← liftTermElabM <| unsafe evalConst Contract targetName
  let targetRows ← liftTermElabM <| unsafe evalConst (List ImportRow) (targetName ++ `report)
  let some recv := targetRows.find? (fun r => r.sourceId == plan.receiveId && r.status == .elaborated)
    | throwError "solidity.paymentSource.receive: exact receive declaration did not elaborate"
  unless recv.payable do throwError "solidity.paymentSource.receive: payable mismatch"
  let received ← ofExcept (unitEntry targetC recv.name recv.payable)
  let bodyName := full ++ `receiveBody
  if let some error ← liftCoreM (Prog.define bodyName targetName received.body) then throwError error
  liftCoreM <| compileDecls #[bodyName]
  let command (text : String) : CommandElabM Unit := do
    elabCommand (← ofExcept (Parser.runParserCategory (← getEnv) `command text))
  let n := output.toString
  let targetText := targetName.toString
  let ownerText := ownerName.toString
  command s!"inductive {n}.Code where\n | owner | recipient\n deriving DecidableEq"
  command s!"def {n}.contracts : {n}.Code → Solidity.Contract\n | .owner => {ownerText}\n | .recipient => {targetText}"
  command s!"def {n}.receiveEntry : Solidity.ContractWorld.Entry ({n}.contracts .recipient) Unit := \{ locals := _, body := {bodyName}, result := fun _ => .ok (), payable := true }"
  command s!"def {n}.targetCtor : Solidity.Prog ({n}.contracts .recipient) [] [] := .nil"
  if plan.root.isNone then
    command s!"def {n}.ownerCtor : Solidity.Prog ({n}.contracts .owner) [] [] := sol[{ownerText}]\{ constructor(); }"
    command s!"def {n}.deploy (w : Solidity.ContractWorld.World {n}.contracts) (self fresh : Solidity.ContractWorld.Address) (ctx : Solidity.ContractWorld.Context) : Solidity.TRes (Solidity.ContractWorld.World {n}.contracts × (Solidity.ContractWorld.Handle {n}.Code.owner × Option (Solidity.ContractWorld.Handle {n}.Code.recipient))) := do\n let (next, reference) ← w.create .owner self {n}.ownerCtor ctx\n pure (next, (reference, none))"
    command s!"def {n}.send (w : Solidity.ContractWorld.World {n}.contracts) (self : Solidity.ContractWorld.Handle {n}.Code.owner) (ctx : Solidity.ContractWorld.Context) (fresh : Solidity.ContractWorld.Address) : Solidity.TRes (Solidity.ContractWorld.World {n}.contracts × Bool) := w.paymentFrame self ctx false (fun paid => do\n paid.createSend .recipient fresh {n}.targetCtor {n}.receiveEntry self.address)"
  else
    let root := plan.root.getD ""
    let ownC ← liftTermElabM <| unsafe evalConst Contract ownerName
    let ownRows ← liftTermElabM <| unsafe evalConst (List ImportRow) (ownerName ++ `report)
    let some ownRecv := ownRows.find? (fun r => some r.sourceId == plan.ownerReceive && r.status == .elaborated)
      | throwError "solidity.paymentSource.receive: owner receive unavailable"
    let ownEntry ← ofExcept (unitEntry ownC ownRecv.name ownRecv.payable)
    let ownBodyName := full ++ `ownerReceiveBody
    if let some error ← liftCoreM (Prog.define ownBodyName ownerName ownEntry.body) then throwError error
    liftCoreM <| compileDecls #[ownBodyName]
    command s!"theorem {n}.owner_receive_run (σ : Solidity.State {ownerText} []) : {ownBodyName}.run σ = .ok ⟨σ, List.prefix_refl _⟩ := by rfl"
    command s!"def {n}.ownerReceiveEntry : Solidity.ContractWorld.Entry ({n}.contracts .owner) Unit := \{ locals := _, body := {ownBodyName}, result := fun _ => .ok (), payable := true }"
    let rootProgram ← ofExcept (wordEntry ownC [.decl (.named "uint") "_r" (some (.name root))])
    unless rootProgram.locals == [.val .uint] && rootProgram.body.outNames [] == [Var.ofName Tools.retLocal] do
      throwError "payment root decoder shape mismatch"
    let rootBodyName := full ++ `rootBody
    if let some error ← liftCoreM (Prog.define rootBodyName ownerName rootProgram.body) then throwError error
    liftCoreM <| compileDecls #[rootBodyName]
    command s!"def {n}.rootEntry : Solidity.ContractWorld.Entry ({n}.contracts .owner) Solidity.ContractWorld.Word := \{ locals := _, body := {rootBodyName}, result := fun σ => .ok (Solidity.TEnv.get .here σ.env) }"
    command s!"def {n}.initializer (recipient : Solidity.ContractWorld.Handle {n}.Code.recipient) : Solidity.Prog ({n}.contracts .owner) [] [] := .cons (.assign (.root {toJson root |>.compress} (by decide +kernel)) (.val (.simple (.lit recipient.address.1.1 recipient.address.1.2)))) .nil"
    command s!"def {n}.deploy (w : Solidity.ContractWorld.World {n}.contracts) (self fresh : Solidity.ContractWorld.Address) (ctx : Solidity.ContractWorld.Context) : Solidity.TRes (Solidity.ContractWorld.World {n}.contracts × (Solidity.ContractWorld.Handle {n}.Code.owner × Option (Solidity.ContractWorld.Handle {n}.Code.recipient))) := do\n if (w.accounts self).isSome || decide (self = ctx.sender) || ctx.isStatic then .error .revert else do\n let (created, recipient) ← w.create .recipient fresh {n}.targetCtor \{ sender := self }\n let (next, reference) ← created.create .owner self ({n}.initializer recipient) ctx\n pure (next, (reference, some recipient))"
    command s!"def {n}.transfer (w : Solidity.ContractWorld.World {n}.contracts) (self : Solidity.ContractWorld.Handle {n}.Code.owner) (recipient : Solidity.ContractWorld.Handle {n}.Code.recipient) (ctx : Solidity.ContractWorld.Context) (amount : Solidity.ContractWorld.Word) : Solidity.TRes (Solidity.ContractWorld.World {n}.contracts × Bool) := w.paymentFrame self ctx false (fun paid => do\n let (same, stored) ← paid.call self {n}.rootEntry \{ sender := ctx.sender }\n if stored != recipient.address.1 then .error .exhausted else same.stipend .transfer recipient {n}.receiveEntry self.address amount)"
    let some (getter, getterId) := plan.getter | throwError "payment getter absent"
    let some getRow := ownRows.find? (fun r => r.sourceId == getterId && r.status == .elaborated)
      | throwError "solidity.paymentSource.getter: source getter did not elaborate"
    let raw ← ofExcept (Tools.runStmt ownC getRow.name [])
    let getEntry ← ofExcept (wordEntry ownC [raw])
    unless getEntry.locals == [.val .uint] && getEntry.body.outNames [] == [Var.ofName Tools.retLocal] do
      throwError "payment getter decoder shape mismatch"
    let getBodyName := full ++ `getterBody
    if let some error ← liftCoreM (Prog.define getBodyName ownerName getEntry.body) then throwError error
    liftCoreM <| compileDecls #[getBodyName]
    command s!"def {n}.getterEntry : Solidity.ContractWorld.Entry ({n}.contracts .owner) Solidity.ContractWorld.Word := \{ locals := _, body := {getBodyName}, result := fun σ => .ok (Solidity.TEnv.get .here σ.env) }"
  if plan.root.isNone then
    command s!"def {n}.invoke (w : Solidity.ContractWorld.World {n}.contracts) (self : Solidity.ContractWorld.Handle {n}.Code.owner) (_recipient : Option (Solidity.ContractWorld.Handle {n}.Code.recipient)) (ctx : Solidity.ContractWorld.Context) (fresh : Solidity.ContractWorld.Address) (signature : String) : Solidity.TRes (Solidity.ContractWorld.World {n}.contracts × List String) := do\n if signature != {toJson (plan.sendName ++ "()") |>.compress} then .error .exhausted else do\n let (next, result) ← {n}.send w self ctx fresh\n pure (next, [if result then \"1\" else \"0\"])"
  else
    let mut branches := ""
    for method in plan.methods do
      branches := branches ++ s!"if signature == {toJson (method.name ++ "()") |>.compress} then do\n let target ← Solidity.TRes.ofOpt recipient\n let (next, _) ← {n}.transfer w self target ctx ⟨{method.amount}, by decide +kernel⟩\n pure (next, [])\n else "
    let some (getter, _) := plan.getter | throwError "missing payment getter"
    branches := branches ++ s!"if signature == {toJson (getter ++ "()") |>.compress} then do\n let (next, value) ← w.call self {n}.getterEntry ctx\n pure (next, [toString value.1])\n else if signature == \"()\" then do\n let (next, _) ← w.call self {n}.ownerReceiveEntry ctx\n pure (next, [])\n else .error .exhausted"
    command s!"def {n}.invoke (w : Solidity.ContractWorld.World {n}.contracts) (self : Solidity.ContractWorld.Handle {n}.Code.owner) (recipient : Option (Solidity.ContractWorld.Handle {n}.Code.recipient)) (ctx : Solidity.ContractWorld.Context) (_fresh : Solidity.ContractWorld.Address) (signature : String) : Solidity.TRes (Solidity.ContractWorld.World {n}.contracts × List String) := do\n {branches}"
  command s!"def {n}.interface : Solidity.Frontend.PaymentSource.Interface {n}.contracts {n}.Code.owner {n}.Code.recipient := ⟨{plan.root.isNone}, {n}.deploy, {n}.invoke⟩"
  -- The retained source plan contains declaration identities, never expectations.
  liftCoreM <| addAndCompile <| .defnDecl {
    name := full ++ `plan, levelParams := [], type := mkConst ``PaymentPlan.Plan,
    value := toExpr plan, hints := .abbrev, safety := .safe }
end Solidity.Frontend.PaymentSource
