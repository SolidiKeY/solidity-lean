import Solidity.KeyTacletParser

/-!
# `lake exe solkeycheck` — taclet-text conformance checker

Reads solkey's `solidityProgramRules.key` and cross-checks its read
tokens and varconds against the Lean annotation table
(`TacletAnnotations.tacletReadAnns`), in the spirit of
`lean/Trainspotting`'s `traincheck` (Lean must agree with the external
artifact it models).

Path resolution: `--key <path>` > `SOLKEY_RULES` env var > the default
relative location of a solkey checkout beside this repository
(`../solkey`). A missing file is a warning + exit 0; a parse anomaly is
exit 2; any conformance mismatch is exit 1.

`--list` prints the parsed reads per read-bearing taclet — use it to
update `TacletAnnotations.lean` after a legitimate upstream change.
-/

open Solidity
open Solidity.KeyTacletParser

/-- A solkey checkout beside this repository. Override with `--key` or
`SOLKEY_RULES` when it lives elsewhere. -/
def defaultKeyPath : System.FilePath :=
  "../solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key"

structure Options where
  keyPath : Option String := none
  list : Bool := false
  verbose : Bool := false

def parseArgs : List String -> Except String Options
  | [] => .ok {}
  | "--key" :: p :: rest => do
      let opts <- parseArgs rest
      .ok { opts with keyPath := some p }
  | "--list" :: rest => do
      let opts <- parseArgs rest
      .ok { opts with list := true }
  | "--verbose" :: rest => do
      let opts <- parseArgs rest
      .ok { opts with verbose := true }
  | arg :: _ => .error s!"unknown argument: {arg}"

def renderParsedRead (r : ParsedRead) : String :=
  let sort := if r.sortTok.isEmpty then "valAt" else s!"<[{r.sortTok}]>"
  s!"{r.token}{sort}({r.arg})"

def main (args : List String) : IO UInt32 := do
  let opts <- match parseArgs args with
    | .ok opts => pure opts
    | .error e =>
        IO.eprintln s!"solkeycheck: {e}"
        IO.eprintln "usage: solkeycheck [--key <path>] [--list] [--verbose]"
        return 2
  let envPath <- IO.getEnv "SOLKEY_RULES"
  let path : System.FilePath <-
    match opts.keyPath.orElse (fun _ => envPath) with
    | some p => pure (System.FilePath.mk p)
    | none => pure defaultKeyPath
  unless (<- path.pathExists) do
    IO.eprintln s!"solkeycheck: SKIPPED — {path} not found \
      (set SOLKEY_RULES or pass --key <path>)"
    return 0
  let src <- IO.FS.readFile path
  let parsed := parseKeyFile src
  if parsed.isEmpty then
    IO.eprintln s!"solkeycheck: PARSE — no taclets recognized in {path}"
    return 2
  let readBearing := parsed.filter (!·.reads.isEmpty)
  IO.println s!"solkeycheck: parsed {parsed.length} taclets, \
    {readBearing.length} read-bearing, table covers \
    {TacletAnnotations.tacletReadAnns.length}"
  if opts.list then
    for t in readBearing do
      IO.println s!"{t.name}  varconds={t.varconds}"
      for r in t.reads do
        let abstracted := match abstractRead t r with
          | .ok a => TacletRead.render a
          | .error e => s!"!! {e}"
        IO.println s!"    {renderParsedRead r}  ->  {abstracted}"
    return 0
  let reports := conforms TacletAnnotations.tacletReadAnns parsed
  if reports.isEmpty then
    IO.println s!"solkeycheck: OK — annotations match {path}"
    return 0
  else
    for r in reports do
      IO.eprintln s!"solkeycheck: {r}"
    IO.eprintln s!"solkeycheck: {reports.length} mismatch(es); run with \
      --list to inspect the parsed reads"
    return 1
