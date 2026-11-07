import Lean
open Lean

partial def printContexts (stx : Syntax) : IO Unit := do
  let k := stx.getKind
  let declaration := k == `Lean.Parser.Command.declaration
  if declaration then
    IO.println s!"DECL {repr stx.getPos?} {repr stx.getTailPos?}"
  if k == `Lean.Parser.Command.ctor || k == `Lean.Parser.Term.matchAlt ||
      k == `Lean.Parser.Tactic.inductionAlt || k == `Lean.Parser.Tactic.case ||
      k == `Lean.Parser.Tactic.cases || k == `Lean.Parser.Tactic.induction then
    IO.println s!"NODE {k} {repr stx.getPos?} {repr stx.getTailPos?}"
  for child in stx.getArgs do
    printContexts child
  if declaration then
    IO.println "ENDDECL"

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot "/workspace/.setup/tools/lean-4.24.0-linux/bin/lean")
  let env ← importModules #[{module := `Lean}] {} 0 (loadExts := true)
  if args.isEmpty then throw (IO.userError "expected paths")
  for path in args do
    IO.println s!"FILE {path}"
    let stx ← Parser.testParseFile env path
    printContexts stx.raw
    IO.println s!"END {path}"
