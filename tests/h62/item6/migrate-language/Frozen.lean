import Lean
import Solidity.Language.FeatureInfo
import Solidity.Language.FixedPoint.Conformance
import Solidity.Language.FixedPoint.Storage

/-! Stable structural type transcript. Strip metadata and alpha-normalize binder
names/universe parameter names; retain every type constructor and argument.
This compares expressions, not hashes of pretty-printer output. -/
open Lean Elab Command
namespace H62.Frozen
def level (ps : List Name) : Level → String
  | .zero => "0"
  | .succ a => "s(" ++ level ps a ++ ")"
  | .max a b => "m(" ++ level ps a ++ "," ++ level ps b ++ ")"
  | .imax a b => "i(" ++ level ps a ++ "," ++ level ps b ++ ")"
  | .param n => "p" ++ toString (ps.idxOf n)
  | .mvar _ => "UNRESOLVED_LEVEL"
def binder : BinderInfo → String
  | .default => "d"
  | .implicit => "i"
  | .strictImplicit => "s"
  | .instImplicit => "c"
def expr (ps : List Name) : Expr → String
  | .bvar i => "b" ++ toString i
  | .fvar _ => "UNRESOLVED_FVAR"
  | .mvar _ => "UNRESOLVED_MVAR"
  | .sort l => "S(" ++ level ps l ++ ")"
  | .const n ls => "C(" ++ n.toString ++ ";" ++ String.intercalate "," (ls.map (level ps)) ++ ")"
  | .app f a => "A(" ++ expr ps f ++ ";" ++ expr ps a ++ ")"
  | .lam _ t b bi => "L" ++ binder bi ++ "(" ++ expr ps t ++ ";" ++ expr ps b ++ ")"
  | .forallE _ t b bi => "F" ++ binder bi ++ "(" ++ expr ps t ++ ";" ++ expr ps b ++ ")"
  | .letE _ t v b _ => "E(" ++ expr ps t ++ ";" ++ expr ps v ++ ";" ++ expr ps b ++ ")"
  | .lit (.natVal v) => "N" ++ toString v
  | .lit (.strVal v) => "T" ++ (Json.str v).compress
  | .mdata _ e => expr ps e
  | .proj n i e => "P(" ++ n.toString ++ ";" ++ toString i ++ ";" ++ expr ps e ++ ")"
end H62.Frozen
run_cmd do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc n _ =>
    match env.getModuleIdxFor? n with
    | some i => if (`Solidity.Language).isPrefixOf env.header.moduleNames[i.toNat]!
        then acc.push n else acc
    | none => acc
  for n in names.toList.mergeSort (fun a b => a.toString < b.toString) do
    let some ci := env.find? n | throwError "missing {n}"
    let t := H62.Frozen.expr ci.levelParams ci.type
    if (t.splitOn "UNRESOLVED").length != 1 then throwError "unresolved type {n}"
    let axs ← collectAxioms n
    if axs.contains `sorryAx then throwError "unproved constant {n}"
    let row := Json.mkObj [("name", toJson n.toString), ("levels", toJson ci.levelParams.length),
      ("type", toJson t), ("axioms", toJson (axs.toList.map Name.toString |>.mergeSort (· < ·)))]
    logInfo m!"FROZEN_JSON {row.compress}"
  logInfo m!"FROZEN_COUNT {names.size}"
