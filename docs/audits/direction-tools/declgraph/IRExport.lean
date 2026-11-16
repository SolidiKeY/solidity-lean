import Lean

open Lean

namespace DeclgraphIR

structure Uses where
  functions : Array Name := #[]
  constructors : Array Name := #[]
  dynamicCalls : Nat := 0
  deriving Inhabited

def expression (e : IR.Expr) : Uses :=
  match e with
  | .fap f _ | .pap f _ => {functions := #[f]}
  | .ctor i _ | .reuse _ i _ _ => {constructors := #[i.name]}
  | .ap _ _ => {dynamicCalls := 1}
  | _ => {}

def merge (a b : Uses) : Uses :=
  {functions := a.functions ++ b.functions, constructors := a.constructors ++ b.constructors,
   dynamicCalls := a.dynamicCalls + b.dynamicCalls}

partial def body (b : IR.FnBody) : Uses :=
  match b with
  | .vdecl _ _ e rest => merge (expression e) (body rest)
  | .jdecl _ _ value rest => merge (body value) (body rest)
  | .set _ _ _ rest | .setTag _ _ rest | .uset _ _ _ rest |
    .sset _ _ _ _ _ rest | .inc _ _ _ _ rest | .dec _ _ _ _ rest | .del _ rest => body rest
  | .case tid _ _ alternatives => alternatives.foldl (fun result alt =>
      match alt with
      | .ctor info b => merge result (merge {constructors := #[info.name]} (body b))
      | .default b => merge result (body b)) {constructors := #[tid]}
  | .ret _ | .jmp _ _ | .unreachable => {}

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [modules,output] =>
    initSearchPath (← findSysroot)
    enableInitializersExecution
    let names := (← IO.FS.lines modules).filter (· != "")
    let selected : NameSet := names.foldl (fun s n => s.insert n.toName) {}
    let env ← importModules (names.map fun n => {module := n.toName}) {} 0 (loadExts := true)
    let out ← IO.FS.Handle.mk output .write
    let moduleNames := env.header.moduleNames
    let moduleStrings := moduleNames.map Name.toString
    let owner := fun n : Name => (env.getModuleIdxFor? n).map (fun i => moduleStrings[i]!)
    let mut count := 0
    for i in [:env.header.moduleData.size] do
      let module := moduleNames[i]!
      if !selected.contains module then continue
      for (name,implementation) in Compiler.implementedByAttr.ext.getModuleEntries env i do
        out.putStrLn <| (Json.mkObj [("record",toJson "implemented_by"),("module",toJson module.toString),
          ("name",toJson name.toString),("implementation",toJson implementation.toString),
          ("implementation_module",toJson (owner implementation))]).compress
      for (phase,decls) in #[("main", IR.declMapExt.getModuleEntries env i),
                              ("ir", IR.declMapExt.getModuleIREntries env i)] do
        for decl in decls do
          count := count + 1
          let uses := match decl with | .fdecl _ _ _ b _ => body b | .extern .. => {}
          out.putStrLn <| (Json.mkObj [("record",toJson "function"),("module",toJson module.toString),("name",toJson decl.name.toString),("owner_module",toJson (owner decl.name)),
            ("phase",toJson phase),("extern",toJson decl.isExtern),
            ("functions",toJson (uses.functions.map Name.toString)),("function_owners",toJson (uses.functions.map owner)),
            ("constructors",toJson (uses.constructors.map Name.toString)),("constructor_owners",toJson (uses.constructors.map owner)),
            ("dynamic_calls",toJson uses.dynamicCalls)]).compress
    IO.println s!"IR_DECLARATION_EXPORT_PASS {count}"
    return 0
  | _ =>
    IO.eprintln "usage: IRExport.lean MODULES OUTPUT"
    return 2

end DeclgraphIR

unsafe def main := DeclgraphIR.main
