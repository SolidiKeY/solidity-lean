import Lean
import Lake

open Lean

/- Read-only kernel-constant exporter. Environment extensions are not loaded;
   compiler attributes, elaborator state and reflective uses are not certified. No project source elaboration or proof changes.
   Run with lean --run Export.lean hash SOURCES or graph MODULES OUTPUT.
   Input files contain one relative source path / module name per line. -/
def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match args with
  | ["binhash", paths] =>
    for p in (← IO.FS.lines paths) do
      IO.println s!"{p}\t{← Lake.computeBinFileHash p}"
    return 0
  | ["hash", paths] =>
    for p in (← IO.FS.lines paths) do
      IO.println s!"{p}\t{← Lake.computeTextFileHash p}"
    return 0
  | ["graph", modules, output] =>
    let names := (← IO.FS.lines modules).filter (· != "")
    let chosen : NameSet := names.foldl (fun acc n => acc.insert n.toName) {}
    let env ← importModules (names.map fun n => { module := n.toName }) {} 0
    let out ← IO.FS.Handle.mk output .write
    for (n, ci) in env.constants.toList do
      let some idx := env.getModuleIdxFor? n | continue
      let m := env.header.moduleNames[idx]!
      unless chosen.contains m do continue
      let mut refs := ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then
        refs := refs ++ v.getUsedConstants
      match ci with
      | .inductInfo v => refs := refs ++ v.all.toArray ++ v.ctors.toArray
      | .ctorInfo v => refs := refs.push v.induct
      | .recInfo v =>
        refs := refs ++ v.all.toArray
        for r in v.rules do refs := refs.push r.ctor ++ r.rhs.getUsedConstants
      | _ => pure ()
      let row := Json.mkObj [("name", toJson n.toString), ("module", toJson m.toString),
        ("kind", toJson (match ci with | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor")),
        ("refs", toJson (refs.map Name.toString))]
      out.putStrLn row.compress
    return 0
  | _ =>
    IO.eprintln "usage: Export.lean hash PATHS | graph MODULES OUTPUT"
    return 2
