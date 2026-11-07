import Lean
import Solidity.Stipend.Rule

/-! Read-only module-owned name/type introspection, including generated names.
No production API, compiler obligation or cross-version equivalence is proved. -/
namespace StipendMigrationInventory
open Lean

def nameJson : Name → Json
  | .anonymous => toJson (["anonymous"] : List String)
  | .str parent value => Json.arr #[toJson "str", nameJson parent, toJson value]
  | .num parent value => Json.arr #[toJson "num", nameJson parent, toJson (toString value)]

def telescope : Expr → List Json × Expr
  | .forallE name domain body kind =>
    let (rest, result) := telescope body
    (Json.mkObj [("name_parts", nameJson name), ("domain_repr", toJson (reprStr domain)),
      ("binder_kind", toJson (reprStr kind))] :: rest, result)
  | type => ([], type)

end StipendMigrationInventory

open Lean StipendMigrationInventory in
run_elab do
  let env ← getEnv
  let moduleName := "Solidity.Stipend.Rule"
  let some index := env.header.moduleNames.findIdx? (fun name => name.toString == moduleName)
    | throwError "missing imported module {moduleName}"
  let data := env.header.moduleData[index]!
  unless data.constNames == data.constants.map (·.name) do
    throwError "module constant name/data mismatch"
  let write := fun (value : Json) => IO.println ("STIPEND_API " ++ value.compress)
  write <| Json.mkObj [("record", toJson "header"), ("schema_version", toJson (1 : Nat)),
    ("module", toJson moduleName), ("kernel_count", toJson data.constants.size),
    ("compiler_extra_count", toJson data.extraConstNames.size)]
  let groups : List (String × Array Name) :=
    [("kernel", data.constNames), ("compiler_extra", data.extraConstNames)]
  for (category, names) in groups do
    for name in names.qsort (fun a b => a.toString < b.toString) do
      let signature ← match env.find? name with
        | none => pure Json.null
        | some info => do
          let kind : String := match info with
            | .axiomInfo _ => "axiom"
            | .defnInfo _ => "definition"
            | .thmInfo _ => "theorem"
            | .opaqueInfo _ => "opaque"
            | .inductInfo _ => "inductive"
            | .ctorInfo _ => "constructor"
            | .recInfo _ => "recursor"
            | .quotInfo _ => "quotient"
          let axioms ← Lean.collectAxioms name
          let (binders, result) := telescope info.type
          pure <| Json.mkObj [("kind", toJson kind), ("unsafe", toJson info.isUnsafe),
            ("level_params", toJson (info.levelParams.map nameJson)),
            ("type_repr", toJson (reprStr info.type)), ("binders", toJson binders),
            ("result_repr", toJson (reprStr result)),
            ("axioms", toJson ((axioms.qsort (fun a b => a.toString < b.toString)).map nameJson))]
      write <| Json.mkObj [("record", toJson "declaration"), ("module", toJson moduleName),
        ("category", toJson category), ("name", toJson name.toString),
        ("name_parts", nameJson name), ("private", toJson (isPrivateName name)),
        ("internal", toJson name.isInternal), ("signature", signature)]
  write <| Json.mkObj [("record", toJson "end"), ("module", toJson moduleName),
    ("count", toJson (data.constants.size + data.extraConstNames.size))]
