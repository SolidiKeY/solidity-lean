import Solidity.TestSuite.Problems
import Solidity.Calculus.Core.Derive

/-!
# solkey's `TestSuite` obligations, scoped

`Problems.lean`'s obligations stated over the scoped calculus,
`Solkey.TestSuite.f.problem.core : Core.Fml Solkey.TestSuite []`, for the
`Core*` twins of the `Derived` modules (`docs/intrinsic.md`, W2 `symex`,
the early gate).  `solc_scoped_problems` states them too, and compiles
them, which takes more than the default heartbeats for 437 obligations in
one call; the scoped `sol_prove` does not need them compiled (it reads an
obligation by its value, `Core.Symex.evaluable`), so this declares them
only.  W3 `testsuite` replaces it with `solc_scoped_problems`.
-/

namespace Solidity.Frontend

open Lean Elab Command Meta

/-- `solc_scoped_problems_decl N`: `solc_scoped_problems N`'s declarations,
not compiled. -/
syntax (name := solcScopedProblemsDecl) "solc_scoped_problems_decl " ident : command

@[command_elab solcScopedProblemsDecl]
def elabSolcScopedProblemsDecl : CommandElab := fun stx => do
  let N ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let rows ← reportRows N
  let fmlTy := mkApp2 (mkConst ``Core.Fml) (mkConst N)
    (mkApp (mkConst ``List.nil [0]) (mkConst ``Core.LTy))
  let errs ← liftTermElabM do
    let C ← unsafe evalConst Contract N
    let mut errs : Array String := #[]
    let mut k := 0
    for r in rows do
      unless r.status == .elaborated do continue
      let some m := r.tag.modality? | continue
      let some xs := r.params.mapM (fun (x, t) =>
        (paramTy? t).map fun (pn : PrimTy × Nat) => (pn.1, Var.ofName x)) | continue
      let n := N ++ Lean.Name.mkSimple r.name
      let P ← unsafe evalConst (Prog C) n
      match Core.Problem.resolve (r.name == "constructor") m xs P with
      | .error e => errs := errs.push s!"{r.name}: {e}"
      | .ok φ =>
        try
          addDecl <| .defnDecl {
            name := n ++ `problem ++ `core, levelParams := [], type := fmlTy,
            value := φ.quote (mkConst N), hints := .abbrev, safety := .safe }
          k := k + 1
        catch ex => errs := errs.push s!"{r.name}: the kernel rejects it: {← ex.toMessageData.toString}"
    if errs.isEmpty then logInfo m!"{k} obligations declared scoped"
    pure errs
  unless errs.isEmpty do
    throwError "solc_scoped_problems_decl: {errs.size} obligations are not scoped:\n{"\n".intercalate errs.toList}"

end Solidity.Frontend

/-- info: 437 obligations declared scoped -/
#guard_msgs in solc_scoped_problems_decl Solkey.TestSuite
