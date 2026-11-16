import Lean
open Lean Lean.Elab
namespace DeclgraphTrustHeader
/- Check the additive dependency's native names against the actual v1 import
   environment, including compiler auxiliaries. It does not assert that all
   environment-extension effects are unchanged; owner review remains separate. -/
unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [source, artifact, output] =>
    initSearchPath (← findSysroot)
    enableInitializersExecution
    let input ← IO.FS.readFile source
    let ictx := Parser.mkInputContext input source
    let (header,_,msgs) ← Parser.parseHeader ictx
    let (env,msgs) ← processHeader header (Elab.async.set {} false) msgs ictx
      (mainModule := `Declgraph.TrustHeaderBaseline)
    if msgs.hasErrors then throw (IO.userError "Frozen v1 header has import errors")
    let mut old : NameSet := env.constants.fold (init := {}) fun s n _ => s.insert n
    for data in env.header.moduleData do
      for n in data.extraConstNames do old := old.insert n
    let parts ← readModuleDataParts #[System.FilePath.mk artifact]
    let mut overlap : Array Name := #[]
    let mut outsideImports : Array Name := #[]
    let mut added := 0
    let mut extra := 0
    let mut extensionEntries := 0
    let mut regions : Array CompactedRegion := #[]
    for (data,region) in parts do
      regions := regions.push region
      if data.isModule then throw (IO.userError "Split dependency needs visibility modelling")
      for imp in data.imports do
        unless env.header.moduleNames.contains imp.module do
          outsideImports := outsideImports.push imp.module
      for n in data.constNames do
        added := added + 1
        if old.contains n then overlap := overlap.push n
      for n in data.extraConstNames do
        extra := extra + 1
        if old.contains n then overlap := overlap.push n
      extensionEntries := extensionEntries + data.entries.size
    IO.FS.writeFile output <| (Json.mkObj [("old_native_names",toJson old.size),
      ("new_constants",toJson added),("new_compiler_auxiliaries",toJson extra),
      ("name_collisions",toJson (overlap.map Name.toString)),
      ("dependencies_outside_v1_header",toJson (outsideImports.map Name.toString)),
      ("extension_entry_groups",toJson extensionEntries)]).pretty ++ "\n"
    IO.println s!"TRUST_HEADER_DELTA_CHECK {old.size} {added} {extra} {overlap.size} {outsideImports.size} {regions.size}"
    return if overlap.isEmpty && outsideImports.isEmpty then 0 else 1
  | _ => IO.eprintln "usage: TrustHeaderDelta V1 ROWS_ARTIFACT OUTPUT"; return 2
end DeclgraphTrustHeader
unsafe def main := DeclgraphTrustHeader.main
