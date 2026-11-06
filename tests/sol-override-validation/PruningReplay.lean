import Solidity.Frontend.OverrideValidation.Pruning
import Solidity.Frontend.Checked.Check

open Solidity.Source Solidity.Frontend.OverrideValidation

def main (args : List String) : IO Unit := do
  for path in args do
    let src ← IO.FS.readFile path
    match Solidity.Frontend.Checked.parse src.toUTF8.data.toList with
    | .error _ => IO.println s!"{path}\tparse-error"
    | .ok u =>
      let E : Env := u.env
      for c in (nodes E).filter (fun c => contractB c.decl) do
        for key in (nodes E).filter (fun key => (family key.decl).isSome) do
          let bs := inherited E c key
          let hasOwn := (nodes E).any fun d => ownB E c d && sameSlotB E key.decl d.decl
          if bs.length > 1 && !hasOwn then
            let start ← IO.monoMsNow
            let ss := survivors E c key
            let stop ← IO.monoMsNow
            IO.println s!"{path}\t{c.decl.name}\t{key.val}:{key.decl.name}\t{bs.map Fin.val}\t{ss.map Fin.val}\t{stop-start}ms"
