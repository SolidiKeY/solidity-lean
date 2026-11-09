import Lean.CoreM
import Lean.Data.Json
import Lean.Util.Path

/-! Streaming metadata audit of previously checked private artifacts.
No proof checking or definition-body equivalence is claimed by this reader.
Elaborator extensions are unnecessary for constant types and are not loaded.
-/
open Lean

/-- Structural equality retains binder names/annotations and metadata.
Plain Expr equality is alpha equivalence and is deliberately not used. -/
structure TypeDag where
  nodes : Array Json := #[]
  memo : ExprStructMap Nat := {}

private def tagged (kind : String) (fields : List Json) : Json :=
  Json.arr ((toJson kind :: fields).toArray)

partial def internType (e : Expr) : StateM TypeDag Nat := do
  let initial : TypeDag ← get
  if let some id := initial.memo[ExprStructEq.mk e]? then return id
  let node ← match e with
    | .bvar i => pure (tagged "bvar" [toJson i])
    | .fvar id => pure (tagged "fvar" [toJson (reprStr id)])
    | .mvar id => pure (tagged "mvar" [toJson (reprStr id)])
    | .sort u => pure (tagged "sort" [toJson (reprStr u)])
    | .const n us => pure (tagged "const" [toJson (reprStr n), toJson (reprStr us)])
    | .app f a => do
      let f ← internType f; let a ← internType a
      pure (tagged "app" [toJson f, toJson a])
    | .lam n t b bi => do
      let t ← internType t; let b ← internType b
      pure (tagged "lam" [toJson (reprStr n), toJson t, toJson b, toJson (reprStr bi)])
    | .forallE n t b bi => do
      let t ← internType t; let b ← internType b
      pure (tagged "forallE" [toJson (reprStr n), toJson t, toJson b, toJson (reprStr bi)])
    | .letE n t v b nonDep => do
      let t ← internType t; let v ← internType v; let b ← internType b
      pure (tagged "letE" [toJson (reprStr n), toJson t, toJson v, toJson b, toJson nonDep])
    | .lit v => pure (tagged "lit" [toJson (reprStr v)])
    | .mdata data b => do
      let b ← internType b
      pure (tagged "mdata" [toJson (reprStr data), toJson b])
    | .proj n i b => do
      let b ← internType b
      pure (tagged "proj" [toJson (reprStr n), toJson i, toJson b])
  let state : TypeDag ← get
  let id := state.nodes.size
  set ({ nodes := state.nodes.push node, memo := state.memo.insert (ExprStructEq.mk e) id } : TypeDag)
  return id

def typeGraph (e : Expr) : Json :=
  let (root, state) := (internType e).run {}
  Json.mkObj [("root", toJson root), ("nodes", Json.arr state.nodes)]

def separatesInOneGraph (a b : Expr) : Bool :=
  let (root, state) := (internType (.app a b)).run {}
  match state.nodes[root]! with
  | .arr fields => fields.size == 3 && fields[0]! == toJson "app" && fields[1]! != fields[2]!
  | _ => false

def graphControls : IO Unit := do
  let p := Expr.sort .zero
  let x := Expr.lam `x p (.bvar 0) .default
  let y := Expr.lam `y p (.bvar 0) .default
  let implicitX := Expr.lam `x p (.bvar 0) .implicit
  unless typeGraph x != typeGraph y do throw (IO.userError "binder-name control")
  unless typeGraph x != typeGraph implicitX do throw (IO.userError "binder-info control")
  unless typeGraph (.mdata {} p) != typeGraph p do throw (IO.userError "metadata control")
  unless typeGraph (.letE `x p p (.bvar 0) true) !=
      typeGraph (.letE `x p p (.bvar 0) false) do throw (IO.userError "let nonDep control")
  unless typeGraph (.const `F [.param `u]) != typeGraph (.const `F [.param `v]) do
    throw (IO.userError "universe control")
  let md1 := Expr.mdata (({} : MData).setNat `audit 1) p
  let md2 := Expr.mdata (({} : MData).setNat `audit 2) p
  unless separatesInOneGraph x y do throw (IO.userError "same-graph binder-name control")
  unless separatesInOneGraph x implicitX do throw (IO.userError "same-graph binder-info control")
  unless separatesInOneGraph md1 md2 do throw (IO.userError "same-graph metadata-payload control")
  unless separatesInOneGraph (.letE `x p p (.bvar 0) true)
      (.letE `x p p (.bvar 0) false) do throw (IO.userError "same-graph nonDep control")
  unless separatesInOneGraph (.const `F [.param `u]) (.const `F [.param `v]) do
    throw (IO.userError "same-graph universe control")
  let shared := Expr.app p p
  unless typeGraph shared == typeGraph (.app (.sort .zero) (.sort .zero)) do
    throw (IO.userError "physical-sharing control")
  let (_, state) := (internType shared).run {}
  unless state.nodes.size == 2 do throw (IO.userError "structural DAG compaction control")
  IO.eprintln "Type DAG controls PASS: names, annotations, metadata, let flag, universes, sharing, compaction; combined-graph collision controls PASS"

def main (args : List String) : IO Unit := do
  graphControls
  let sysroot :: modules := args | throw (IO.userError "sysroot and modules required")
  if modules.isEmpty then throw (IO.userError "empty module census")
  initSearchPath (System.FilePath.mk sysroot)
  let selected := modules.map fun s => (s.splitOn ".").foldl Name.str Name.anonymous
  let imports : Array Import := selected.toArray.map fun n => { module := n }
  let env ← importModules imports {} (trustLevel := 0) (loadExts := false)
  let entries := env.constants.toList.filter fun entry =>
    match env.getModuleIdxFor? entry.1 with
    | some idx => selected.contains env.header.moduleNames[idx]!
    | none => false
  let entries := entries.mergeSort (fun a b => decide (a.1.toString ≤ b.1.toString))
  let out ← IO.getStdout
  for (name, info) in entries do
    let some idx := env.getModuleIdxFor? name | continue
    let kind : String := match info with
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    let row := Json.mkObj [
      ("module", toJson env.header.moduleNames[idx]!.toString),
      ("name", toJson name.toString), ("kind", toJson kind),
      ("type_graph", typeGraph info.type),
      ("level_params", toJson (info.levelParams.map Name.toString))]
    out.putStrLn row.compress
  out.flush
