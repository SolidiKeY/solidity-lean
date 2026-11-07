import Lean
import Solidity.Semantics.AbiEntry
import Solidity.Semantics.AbiAccess
import Solidity.Semantics.AbiAccessChecks
import Solidity.Semantics.AbiEntryChecks
import Solidity.Semantics.AbiEntryProofs

/-!
Diagnostic serialization of elaborated ABI constant types. Ignore binder names
and metadata, preserve binder visibility, constants, literals and universe levels.
The importing module is a test utility; production imports are unchanged.
-/
namespace H62SemanticsMigration
open Lean Elab Command

def node (tag : String) (args : List Json) : Json :=
  Json.arr ((toJson tag :: args).toArray)

partial def levelJson (params : List Name) : Level → Json
  | .zero => node "zero" []
  | .succ l => node "succ" [levelJson params l]
  | .max a b => node "max" [levelJson params a, levelJson params b]
  | .imax a b => node "imax" [levelJson params a, levelJson params b]
  | .param n => if params.contains n then node "param" [toJson (params.idxOf n)]
      else node "UNSUPPORTED_LEVEL_PARAM" []
  | .mvar _ => node "UNSUPPORTED_LEVEL_MVAR" []

partial def exprJson (params : List Name) : Expr → Json
  | .bvar i => node "bvar" [toJson i]
  | .fvar _ => node "UNSUPPORTED_FVAR" []
  | .mvar _ => node "UNSUPPORTED_MVAR" []
  | .sort l => node "sort" [levelJson params l]
  | .const n ls => node "const" [toJson n.toString, toJson (ls.map (levelJson params))]
  | .app f a => node "app" [exprJson params f, exprJson params a]
  | .lam _ t b bi => node "lam" [toJson (reprStr bi), exprJson params t, exprJson params b]
  | .forallE _ t b bi => node "forall" [toJson (reprStr bi), exprJson params t, exprJson params b]
  | .letE _ t v b _ => node "let" [exprJson params t, exprJson params v, exprJson params b]
  | .lit (.natVal n) => node "nat" [toJson n]
  | .lit (.strVal s) => node "str" [toJson s]
  | .mdata _ e => exprJson params e
  | .proj n i e => node "proj" [toJson n.toString, toJson i, exprJson params e]

run_cmd do
  unless levelJson [] (.param `missing) == node "UNSUPPORTED_LEVEL_PARAM" [] do
    throwError "unknown-universe negative control failed"
  unless levelJson [`known] (.param `known) == node "param" [toJson (0 : Nat)] do
    throwError "known-universe control failed"
  let env ← getEnv
  let modules := env.header.moduleNames
  let rows := env.constants.fold (init := #[]) fun acc n ci =>
    match env.getModuleIdxFor? n with
    | some i =>
      if (modules[i.toNat]!).toString.startsWith "Solidity.Semantics.Abi" &&
          !(n.toString.startsWith "_private.") then
        acc.push (Json.mkObj [("name", toJson n.toString),
          ("module", toJson (modules[i.toNat]!).toString),
          ("level_count", toJson ci.levelParams.length),
          ("type", exprJson ci.levelParams ci.type)])
      else acc
    | none => acc
  let some output ← liftIO (IO.getEnv "H62_API_OUTPUT")
    | throwError "H62_API_OUTPUT is required"
  liftIO <| IO.FS.writeFile output (Json.arr rows).compress
end H62SemanticsMigration
