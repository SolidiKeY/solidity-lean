import Lean

/-! External compiler-data inspection only. IR signatures and compiler visibility
queries are recorded separately from kernel types and public API acceptance. -/
open Lean
namespace H62.MigrateYul.CompilerSignatures

def tag (s : String) (xs : Array Json := #[]) : Json := .arr (#[.str s] ++ xs)
def nameJson : Name → Json
  | .anonymous => tag "anonymous"
  | .str n s => tag "str" #[nameJson n, .str s]
  | .num n i => tag "num" #[nameJson n, toJson i]

partial def typeJson (t : IR.IRType) : Json :=
  match t with
  | .struct n ts => tag "struct" #[match n with | none => .null | some n => nameJson n, .arr (ts.map typeJson)]
  | .union n ts => tag "union" #[nameJson n, .arr (ts.map typeJson)]
  | other => tag "repr" #[.str (reprStr other)]

def signature (d : IR.Decl) : Json := Json.mkObj [
  ("name", nameJson d.name), ("extern", toJson d.isExtern),
  ("parameters", .arr (d.params.map fun p => Json.mkObj [
    ("variable_index", toJson p.x.idx), ("borrow", toJson p.borrow), ("type", typeJson p.ty)])),
  ("result", typeJson d.resultType)]

def run (moduleString output : String) : IO Unit := do
  initSearchPath (← findSysroot)
  let parts := moduleString.splitOn "."
  if parts.any String.isEmpty then throw (IO.userError "empty module-name component")
  let moduleName := parts.foldl (fun n part => Name.str n part) Name.anonymous
  let env ← importModules #[{module := moduleName, importAll := true}] {} (level := .private)
  let some idx := env.getModuleIdx? moduleName | throw (IO.userError "missing module provenance")
  let some data := env.header.moduleData[idx]? | throw (IO.userError "missing module data")
  let out ← IO.FS.Handle.mk output .write
  out.putStrLn (Json.mkObj [("record", .str "header"), ("schema", toJson (1 : Nat)),
    ("module", nameJson moduleName), ("expected_names", toJson data.extraConstNames.size),
    ("module_uses_module_system", toJson data.isModule),
    ("inspector_header_is_module", toJson env.header.isModule),
    ("scope", .str "extraConstNames, including kernel overlaps; IR signatures only"),
    ("limitation", .str "Compiler visibility query is not an independently verified public API classification; missing IR remains unresolved; terminal types retain exact compiler Repr text.")]).compress
  let mut found := 0
  for n in data.extraConstNames do
    let declaration := IR.findEnvDecl env n
    if declaration.isSome then found := found + 1
    out.putStrLn (Json.mkObj [("record", .str "compiler_name"), ("module", nameJson moduleName),
      ("name", nameJson n), ("private_name_marker", toJson (isPrivateName n)),
      ("kernel_constant_available", toJson (env.checked.get.find? n).isSome),
      ("compiler_is_decl_public", toJson (Compiler.LCNF.isDeclPublic env n)),
      ("ir_lookup", .str (if declaration.isSome then "found" else "not_found")),
      ("signature", match declaration with | none => .null | some d => signature d)]).compress
  out.putStrLn (Json.mkObj [("record", .str "complete"), ("module", nameJson moduleName),
    ("count", toJson data.extraConstNames.size), ("ir_found", toJson found),
    ("ir_missing", toJson (data.extraConstNames.size - found)), ("migration_acceptance", toJson false)]).compress

end H62.MigrateYul.CompilerSignatures

def main (args : List String) : IO UInt32 := do
  match args with
  | [moduleName, output] => H62.MigrateYul.CompilerSignatures.run moduleName output; return 0
  | _ => throw (IO.userError "usage: ExportCompilerSignatures MODULE OUTPUT")
