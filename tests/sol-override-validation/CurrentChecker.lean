import Solidity.Frontend.Static.Inheritance
import Solidity.Frontend.Checked.Check

/-! External replay against the unchanged checker. No theorem below identifies
its relation with solc. A parse refusal is recorded separately from G14 false. -/

open Solidity.Source Solidity.Frontend.Static

def main (args : List String) : IO Unit := do
  for path in args do
    let src ← IO.FS.readFile path
    match Solidity.Frontend.Checked.parse src.toUTF8.data.toList with
    | .error _ => IO.println s!"{path}\tparse-error\t-\t-"
    | .ok u =>
      let r : Resolution := resolveUnit ⟨.legacy, []⟩ u
      IO.println s!"{path}\tparsed\t{inheritanceB r}\t{wellFormedB r}"
