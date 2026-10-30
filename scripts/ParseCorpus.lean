import Solidity.Frontend.Checked.Check
import Solidity.Frontend.Checked.Render

/-!
# The parse-corpus driver (G11)

Reads `.cache/parse-corpus/manifest.tsv` (written by
`node scripts/parse-corpus.mjs prepare`), parses every unit with the checked
parser, prints each accepted unit and parses the text again, and writes
`.cache/parse-corpus/results.tsv` (`file  ok|err  same|diff|-  message`)
for `node scripts/parse-corpus.mjs report`.  Elaborating this file runs it
(the `#eval` below), from the repository root: open it in the Lean server, or
`lake env lean scripts/ParseCorpus.lean`.
-/

open Solidity.Frontend.Checked Solidity.Source

def fingerprintOf (r : Except Error (Syn .unit × List Choice)) : Option (List Node × Option (List Tok)) :=
  r.toOption.map fun (u, L) => (u.nodes, u.toks L)

def oneUnit (src : Bytes) : String × String × String :=
  match parseWithLayout src with
  | .error e => ("err", "-", s!"{e.pos}: {e.msg}")
  | .ok (u, L) =>
    let rt := match u.print L with
      | some b => if fingerprintOf (parseWithLayout b) == fingerprintOf (.ok (u, L)) then "same" else "diff"
      | none => "diff"
    ("ok", rt, "")

def runCorpus : IO Unit := do
  let manifest ← IO.FS.lines ".cache/parse-corpus/manifest.tsv"
  let mut out : Array String := #[]
  for line in manifest do
    match line.splitOn "\t" with
    | _ :: _ :: _ :: file :: _ =>
      let src ← IO.FS.readBinFile file
      let (v, rt, msg) := oneUnit src.toList
      out := out.push s!"{file}\t{v}\t{rt}\t{msg.replace "\t" " " |>.replace "\n" " "}"
    | _ => pure ()
  IO.FS.writeFile ".cache/parse-corpus/results.tsv" (String.intercalate "\n" out.toList ++ "\n")
  IO.println s!"parse-corpus: {out.size} units"

#eval runCorpus


