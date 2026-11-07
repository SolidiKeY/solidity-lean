import Solidity.Frontend.OverrideValidation.Memoized
import Solidity.Frontend.Checked.Check

open Solidity.Source Solidity.Frontend.OverrideValidation

def main (args : List String) : IO Unit := do
  for path in args do
    let src ← IO.FS.readFile path
    match Solidity.Frontend.Checked.parse src.toUTF8.data.toList with
    | .error _ => IO.println s!"{path}\tparse-error\t-\t0"
    | .ok u =>
      let E : Env := u.env
      let start ← IO.monoMsNow
      let cell ← IO.mkRef (fastValidateB E)
      let accepted ← cell.get
      let stop ← IO.monoMsNow
      let out ← IO.getStdout
      out.putStrLn s!"{path}\tparsed\t{accepted}\t{stop-start}"
      out.flush
