import Lean

/-! External old-toolchain metadata observations only. This is neither a public
API classifier nor a complete attribute inventory. Historical inspectors stay frozen. -/
open Lean
namespace H62.MigrateYul.DeclarationMetadata

def tag (s : String) (xs : Array Json := #[]) : Json := .arr (#[.str s] ++ xs)
def nameJson : Name → Json
  | .anonymous => tag "anonymous"
  | .str n s => tag "str" #[nameJson n, .str s]
  | .num n i => tag "num" #[nameJson n, toJson i]
def optionalName : Option Name → Json
  | none => .null
  | some n => nameJson n

def instanceJson (scope : Option Name) (entry : Meta.InstanceEntry) : Json := Json.mkObj [
  ("global_name", optionalName entry.globalName?),
  ("display_name", .str (entry.globalName?.map (fun n => (privateToUserName n).toString) |>.getD "<unnamed>")),
  ("private_name_marker", toJson (entry.globalName?.any isPrivateName)),
  ("scope_namespace", optionalName scope), ("attribute_kind", .str (toString entry.attrKind)),
  ("priority", toJson entry.priority), ("synthesis_order", toJson entry.synthOrder),
  ("value_repr", .str (reprStr entry.val))]

/-- Runtime-only initializer loading is required by the documented import API.
This unsafe IO entry point is not imported by the model or used in a proof. -/
unsafe def run (moduleString output : String) : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let parts := moduleString.splitOn "."
  if parts.any String.isEmpty then throw (IO.userError "empty module-name component")
  let moduleName := parts.foldl (fun n part => Name.str n part) Name.anonymous
  let env ← importModules #[{module := moduleName, importAll := true}] {} (loadExts := true) (level := .private)
  let some idx := env.getModuleIdx? moduleName | throw (IO.userError "missing module provenance")
  let some data := env.header.moduleData[idx]? | throw (IO.userError "missing module data")
  let instances := Meta.instanceExtension.ext.getModuleEntries env idx (level := .private)
  let defaults := Meta.defaultInstanceExtension.getModuleEntries env idx (level := .private)
  let active := Meta.instanceExtension.getState env
  let classes := classExtension.getModuleEntries env idx (level := .private)
  let out ← IO.FS.Handle.mk output .write
  out.putStrLn (Json.mkObj [("record", .str "header"), ("schema", toJson (1 : Nat)),
    ("module", nameJson moduleName), ("expected_declarations", toJson data.constNames.size),
    ("expected_classes", toJson classes.size), ("expected_instances", toJson instances.size), ("expected_defaults", toJson defaults.size),
    ("import_all", toJson true), ("loaded_extensions", toJson true), ("import_level", .str "private"),
    ("limitation", .str "Focused persisted classes/instances/default instances and declaration protected flags only. Local attributes are absent after scope exit; generic attributes, public visibility and new compatibility are unresolved. Expression Repr text is not typechecked by this observer.")]).compress
  for n in data.constNames do
    out.putStrLn (Json.mkObj [("record", .str "declaration"), ("module", nameJson moduleName),
      ("name", nameJson n), ("display_name", .str (privateToUserName n).toString),
      ("private_name_marker", toJson (isPrivateName n)),
      ("protected", toJson (isProtected env n)), ("class", toJson (isClass env n)),
      ("active_instance_priority", match active.instanceNames.find? n with | none => .null | some entry => toJson entry.priority)]).compress
  let mut c : Nat := 0
  for entry in classes do
    out.putStrLn (Json.mkObj [("record", .str "class"), ("module", nameJson moduleName),
      ("index", toJson c), ("name", nameJson entry.name), ("out_parameters", toJson entry.outParams)]).compress
    c := c + 1
  let mut i : Nat := 0
  for serialized in instances do
    let (scope, entry) : Option Name × Meta.InstanceEntry := match serialized with
      | .global entry => (none, entry)
      | .scoped ns entry => (some ns, entry)
    out.putStrLn (Json.mkObj [("record", .str "instance"), ("module", nameJson moduleName),
      ("index", toJson i), ("entry", instanceJson scope entry)]).compress
    i := i + 1
  let mut j : Nat := 0
  for entry in defaults do
    out.putStrLn (Json.mkObj [("record", .str "default_instance"), ("module", nameJson moduleName),
      ("index", toJson j), ("class_name", nameJson entry.className),
      ("instance_name", nameJson entry.instanceName), ("priority", toJson entry.priority)]).compress
    j := j + 1
  out.putStrLn (Json.mkObj [("record", .str "complete"), ("module", nameJson moduleName),
    ("declarations", toJson data.constNames.size), ("classes", toJson classes.size), ("instances", toJson instances.size),
    ("defaults", toJson defaults.size), ("migration_acceptance", toJson false)]).compress
end H62.MigrateYul.DeclarationMetadata

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [moduleName, output] => H62.MigrateYul.DeclarationMetadata.run moduleName output; return 0
  | _ => throw (IO.userError "usage: ExportDeclarationMetadata MODULE OUTPUT")
