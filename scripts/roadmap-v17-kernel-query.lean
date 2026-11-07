import Lean
-- V17_PROJECT_IMPORTS

/-! Bounded metadata query above the public core; no theorem or semantic model. -/
namespace Solidity.Roadmap.V17.KernelQuery
open Lean Lean.Meta Lean.Elab

def arr (xs : List Json) : Json := Json.arr xs.toArray

def nameJson : Lean.Name → Json
  | .anonymous => arr [.str "anonymous"]
  | .str p s => arr [.str "str", nameJson p, .str s]
  | .num p n => arr [.str "num", nameJson p, .str (toString n)]

def levelJson : Level → Except String Json
  | .zero => pure (arr [.str "zero"])
  | .succ u => return arr [.str "succ", ← levelJson u]
  | .max u v => return arr [.str "max", ← levelJson u, ← levelJson v]
  | .imax u v => return arr [.str "imax", ← levelJson u, ← levelJson v]
  | .param n => pure (arr [.str "param", nameJson n])
  | .mvar _ => throw "unresolved universe metavariable"

def binderJson : BinderInfo → Json
  | .default => .str "default"
  | .implicit => .str "implicit"
  | .strictImplicit => .str "strictImplicit"
  | .instImplicit => .str "instImplicit"

def dataJson : DataValue → Except String Json
  | .ofString s => pure (arr [.str "string", .str s])
  | .ofBool b => pure (arr [.str "bool", toJson b])
  | .ofName n => pure (arr [.str "name", nameJson n])
  | .ofNat n => pure (arr [.str "nat", .str (toString n)])
  | .ofInt n => pure (arr [.str "int", .str (toString n)])
  | .ofSyntax _ => throw "syntax-valued expression metadata is unsupported"

abbrev EncodeM := StateT Nat (Except String)

def exprJson : Nat → Expr → EncodeM Json
  | 0, _ => throw "expression depth limit reached"
  | fuel + 1, value => do
    let remaining ← get
    if remaining == 0 then throw "expression node limit reached"
    set (remaining - 1)
    match value with
    | .bvar n => pure (arr [.str "bvar", .str (toString n)])
    | .fvar _ => throw "free variable in closed declaration"
    | .mvar _ => throw "metavariable in checked declaration"
    | .sort u => return arr [.str "sort", ← liftM (levelJson u)]
    | .const n us => return arr [.str "const", nameJson n, arr (← liftM (us.mapM levelJson))]
    | .app f a => return arr [.str "app", ← exprJson fuel f, ← exprJson fuel a]
    | .lam n t b i => return arr [.str "lam", nameJson n, binderJson i, ← exprJson fuel t, ← exprJson fuel b]
    | .forallE n t b i => return arr [.str "forall", nameJson n, binderJson i, ← exprJson fuel t, ← exprJson fuel b]
    | .letE n t v b nondep => return arr [.str "let", nameJson n, toJson nondep, ← exprJson fuel t, ← exprJson fuel v, ← exprJson fuel b]
    | .lit (.natVal n) => pure (arr [.str "nat", .str (toString n)])
    | .lit (.strVal s) => pure (arr [.str "string", .str s])
    | .mdata md b =>
      let entries ← liftM (md.entries.mapM fun (n,v) => return arr [nameJson n, ← dataJson v])
      return arr [.str "mdata", arr entries, ← exprJson fuel b]
    | .proj n i b => return arr [.str "proj", nameJson n, .str (toString i), ← exprJson fuel b]

def encodeExpr (e : Expr) : Except String Json :=
  (exprJson 512 e).run' 100000

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def namesJson (ns : Array Lean.Name) : Json :=
  toJson ((ns.map Lean.Name.toString).toList.mergeSort (· ≤ ·))

def extract (requests : Array (Lean.Name × Lean.Name × String)) (includeValues : Bool := true) : TermElabM Json := do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for (n, expectedModule, expectedKind) in requests do
    let some ci := env.checked.get.find? n | throwError "missing checked declaration: {n}"
    if ci.name != n then throwError "declaration identity mismatch: {n}"
    let some idx := env.getModuleIdxFor? n | throwError "declaration is not imported: {n}"
    let module := env.header.moduleNames[idx.toNat]!
    if module != expectedModule then throwError "wrong defining module for {n}: {module}"
    if kind ci != expectedKind then throwError "wrong declaration kind for {n}: {kind ci}"
    let typeAst ← match encodeExpr ci.type with
      | .ok j => pure j
      | .error e => throwError "{n} type: {e}"
    let value := ci.value? true
    let valueAst ← match value with
      | none => pure Json.null
      | some v => if !includeValues then pure Json.null else match encodeExpr v with
        | .ok j => pure j
        | .error e => throwError "{n} value: {e}"
    let (binderCount, hypothesisIndices) ← forallTelescope ci.type fun xs _ => do
      let mut indices : Array Nat := #[]
      for i in [:xs.size] do
        if ← isProp (← inferType xs[i]!) then indices := indices.push i
      pure (xs.size, indices)
    let axioms ← collectAxioms n
    let pretty ← withOptions (fun o => o.setBool `pp.all true) (ppExpr ci.type)
    rows := rows.push (Json.mkObj ([
      ("name", .str n.toString), ("nameAst", nameJson n), ("module", .str module.toString),
      ("kind", .str (kind ci)), ("unsafe", toJson ci.isUnsafe), ("partial", toJson ci.isPartial),
      ("levels", arr (ci.levelParams.map nameJson)), ("type", typeAst), ("value", valueAst),
      ("typeDisplaySupplemental", .str pretty.pretty),
      ("typeDependencies", namesJson ci.type.getUsedConstants),
      ("valueDependencies", if includeValues then namesJson (value.map Expr.getUsedConstants |>.getD #[]) else Json.null),
      ("axioms", namesJson axioms), ("binderCount", toJson binderCount), ("propositionBinders", toJson hypothesisIndices),
      ("semanticPremisesDischarged", toJson false)] ++
      if includeValues then [] else [("valueOmitted", toJson true)]))
  let mut imports : Array Json := #[]
  for n in env.header.moduleNames do
    let path ← liftM (m := IO) (findOLean n)
    imports := imports.push (Json.mkObj [("module", .str n.toString), ("olean", .str path.toString)])
  return Json.mkObj [("schema", toJson (1 : Nat)), ("rows", .arr rows), ("imports", .arr imports),
    ("releaseClosed", toJson false)]

end Solidity.Roadmap.V17.KernelQuery
