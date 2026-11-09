import Lean
import Solidity.Roadmap.Evm

/-! Inspection only: closed declaration types as structural JSON. Binder names
and declaration universe-parameter names are normalized; constant names, levels,
binder visibility and structure remain explicit. This is not a kernel proof of
cross-version equivalence. Unsupported metadata/free variables reject downstream.
No production representation or declaration is changed. -/
namespace RoadmapApiInspection
open Lean

def node (tag : String) (children : Array Json := #[]) : Json :=
  Json.arr (#[toJson tag] ++ children)

def level (params : List Name) : Level → Json
  | .zero => node "zero"
  | .succ u => node "succ" #[level params u]
  | .max u v => node "max" #[level params u, level params v]
  | .imax u v => node "imax" #[level params u, level params v]
  | .param n => if params.contains n then node "param" #[toJson (params.idxOf n)]
      else node "unsupported-level-param" #[toJson n.toString]
  | .mvar _ => node "unsupported-level-mvar"

def binder (keep : Bool) (info : BinderInfo) : String :=
  if !keep then "erased" else
    match info with
    | .default => "explicit"
    | .implicit => "implicit"
    | .strictImplicit => "strictImplicit"
    | .instImplicit => "instance"

def expression (params : List Name) (keepInfo : Bool) : Expr → Json
  | .bvar i => node "bvar" #[toJson i]
  | .fvar _ => node "unsupported-fvar"
  | .mvar _ => node "unsupported-mvar"
  | .sort u => node "sort" #[level params u]
  | .const n us => node "const" #[toJson n.toString, toJson (us.map (level params))]
  | .app f a => node "app" #[expression params keepInfo f, expression params keepInfo a]
  | .lam _ t b bi => node "lambda" #[toJson (binder keepInfo bi), expression params keepInfo t, expression params keepInfo b]
  | .forallE _ t b bi => node "forall" #[toJson (binder keepInfo bi), expression params keepInfo t, expression params keepInfo b]
  | .letE _ t v b nd => node "let" #[toJson nd, expression params keepInfo t, expression params keepInfo v, expression params keepInfo b]
  | .lit (.natVal n) => node "nat" #[toJson n]
  | .lit (.strVal s) => node "string" #[toJson s]
  | .mdata _ e => node "unsupported-metadata" #[expression params keepInfo e]
  | .proj n i e => node "projection" #[toJson n.toString, toJson i, expression params keepInfo e]

open Elab Command in
run_cmd do
  let a : Expr := .forallE `x (.sort .zero) (.bvar 0) .implicit
  let renamed : Expr := .forallE `y (.sort .zero) (.bvar 0) .implicit
  let explicit : Expr := .forallE `x (.sort .zero) (.bvar 0) .default
  let changed : Expr := .forallE `x (.sort .zero) (.sort .zero) .implicit
  unless (expression [] true a).compress == (expression [] true renamed).compress do
    throwError "binder-name normalization control failed"
  if (expression [] true a).compress == (expression [] true explicit).compress then
    throwError "binder visibility negative control failed"
  unless (expression [] false a).compress == (expression [] false explicit).compress do
    throwError "binder visibility erasure control failed"
  if (expression [] false a).compress == (expression [] false changed).compress then
    throwError "structure negative control failed"
  logInfo "CANONICAL_CONTROLS_PASS 4"
  let env ← getEnv
  let rows : Array (Name × ConstantInfo) := env.constants.fold (init := #[]) fun acc n ci =>
    match env.getModuleIdxFor? n with
    | some i => if env.header.moduleNames[i.toNat]! == `Solidity.Roadmap.Evm then acc.push (n, ci) else acc
    | none => acc
  let rows := rows.qsort fun a b => a.1.toString < b.1.toString
  for (name, info) in rows do
    let row := Json.mkObj [
      ("name", toJson name.toString),
      ("type_debug", toJson (toString info.type)),
      ("universe_count", toJson info.levelParams.length),
      ("alpha", expression info.levelParams true info.type),
      ("binder_erased", expression info.levelParams false info.type)]
    logInfo m!"CANONICAL_API {row.compress}"
  logInfo m!"CANONICAL_COUNT {rows.size}"
end RoadmapApiInspection
