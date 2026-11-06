import SignatureFingerprint

/-!
Observes the current fixture process after imports. A fresh lookup and
before/after hashes do not prove what bytes the loader read, rule out an ABA
replacement, or authenticate the compiler and runtime.
-/

open Lean Elab Command

namespace H62Signature

def phaseName : IRPhases → String
  | .runtime => "runtime"
  | .comptime => "comptime"
  | .all => "all"

def observeImport (imp : EffectiveImport) : CommandElabM Json := do
  let base ← liftIO <| findOLean imp.module
  unless (← liftIO base.pathExists) do
    throwError "missing resolved module {imp.module}: {base}"
  let baseReal ← liftIO <| IO.FS.realPath base
  let server := OLeanLevel.server.adjustFileName base
  let privatePart := OLeanLevel.private.adjustFileName base
  let serverPresent ← liftIO server.pathExists
  let privatePresent ← liftIO privatePart.pathExists
  let serverReal ← if serverPresent then
    pure (some (← liftIO <| IO.FS.realPath server).toString)
  else pure none
  let privateReal ← if privatePresent then
    pure (some (← liftIO <| IO.FS.realPath privatePart).toString)
  else pure none
  pure (Json.mkObj [
    ("module", encodeName imp.module),
    ("importAll", toJson imp.importAll),
    ("isExported", toJson imp.isExported),
    ("isMeta", toJson imp.isMeta),
    ("irPhases", toJson (phaseName imp.irPhases)),
    ("base", toJson base.toString),
    ("base_real", toJson baseReal.toString),
    ("server", toJson server.toString),
    ("server_present", toJson serverPresent),
    ("server_real", toJson serverReal),
    ("private", toJson privatePart.toString),
    ("private_present", toJson privatePresent),
    ("private_real", toJson privateReal)])

elab "#h62_environment" : command => do
  let env ← getEnv
  let searchPath ← liftIO searchPathRef.get
  let modules ← env.header.modules.mapM observeImport
  let direct := env.header.imports.map fun imp =>
    Json.mkObj [
      ("module", encodeName imp.module),
      ("importAll", toJson imp.importAll),
      ("isExported", toJson imp.isExported),
      ("isMeta", toJson imp.isMeta)]
  let record := Json.mkObj [
    ("format", toJson (1 : Nat)),
    ("kind", toJson ("fixture-local-observation" : String)),
    ("lean_version", toJson Lean.versionString),
    ("main_module", encodeName env.header.mainModule),
    ("is_module", toJson env.header.isModule),
    ("trust_level", toJson env.header.trustLevel.toNat),
    ("search_path", Json.arr (searchPath.toArray.map fun p => toJson p.toString)),
    ("direct_imports", Json.arr direct),
    ("modules", Json.arr modules)]
  logInfo m!"H62_ENVIRONMENT {record.compress}"

end H62Signature
