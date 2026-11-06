import Solidity.SortCheck.Parser
import Lean.Util.CollectAxioms

/-! Structural interface evidence for Parser/Annotations. Erase binder names
and type metadata; number universe parameters by declaration order. Preserve
binder info, bound-variable indices, constants, levels and every other node.
This is an audit serialization, not cross-toolchain definitional equality. -/
namespace SortCheckCanonical
open Lean Elab Command

def nameJson : Name → Json
  | .anonymous => .arr #[.str "anonymous"]
  | .str p s => .arr #[.str "str", nameJson p, .str s]
  | .num p n => .arr #[.str "num", nameJson p, toJson n]

def levelJson (params : List Name) : Level → Json
  | .zero => .arr #[.str "zero"]
  | .succ u => .arr #[.str "succ", levelJson params u]
  | .max u v => .arr #[.str "max", levelJson params u, levelJson params v]
  | .imax u v => .arr #[.str "imax", levelJson params u, levelJson params v]
  | .param n => .arr #[.str "param", toJson (params.idxOf n)]
  | .mvar _ => .str "unexpected-level-mvar"

def binderJson : BinderInfo → Json
  | .default => toJson (0 : Nat)
  | .implicit => toJson (1 : Nat)
  | .strictImplicit => toJson (2 : Nat)
  | .instImplicit => toJson (3 : Nat)

def exprJson (params : List Name) : Expr → Json
  | .bvar i => .arr #[.str "bvar", toJson i]
  | .fvar _ => .str "unexpected-fvar"
  | .mvar _ => .str "unexpected-mvar"
  | .sort u => .arr #[.str "sort", levelJson params u]
  | .const n us => .arr #[.str "const", nameJson n, toJson (us.map (levelJson params))]
  | .app f a => .arr #[.str "app", exprJson params f, exprJson params a]
  | .lam _ t b bi => .arr #[.str "lam", binderJson bi, exprJson params t, exprJson params b]
  | .forallE _ t b bi => .arr #[.str "forall", binderJson bi, exprJson params t, exprJson params b]
  | .letE _ t v b nondep => .arr #[.str "let", toJson nondep, exprJson params t, exprJson params v, exprJson params b]
  | .lit (.natVal n) => .arr #[.str "nat", toJson n]
  | .lit (.strVal s) => .arr #[.str "string", .str s]
  | .mdata _ b => exprJson params b
  | .proj n i b => .arr #[.str "proj", nameJson n, toJson i, exprJson params b]

def binderNames (path : Array Nat) : Expr → Array Json
  | .forallE n t b _ => #[.arr #[toJson path, nameJson n]] ++ binderNames (path.push 2) t ++ binderNames (path.push 3) b
  | .lam n t b _ => #[.arr #[toJson path, nameJson n]] ++ binderNames (path.push 2) t ++ binderNames (path.push 3) b
  | .letE n t v b _ => #[.arr #[toJson path, nameJson n]] ++ binderNames (path.push 2) t ++ binderNames (path.push 3) v ++ binderNames (path.push 4) b
  | .app f a => binderNames (path.push 1) f ++ binderNames (path.push 2) a
  | .proj _ _ b => binderNames (path.push 3) b
  | .mdata _ b => binderNames path b
  | _ => #[]

run_cmd do
  let env ← getEnv
  let ids := #[`Solidity.SortCheck.Annotations, `Solidity.SortCheck.Parser].map fun m =>
    (env.getModuleIdx? m).get!
  let names := env.constants.fold (init := (#[] : Array Name)) fun acc n _ =>
    if (env.getModuleIdxFor? n).any ids.contains then acc.push n else acc
  let names := names.qsort fun a b => a.toString < b.toString
  logInfo m!"CANONICAL_COUNT {names.size}"
  for n in names do
    let info := (env.find? n).get!
    if info.type.hasExprMVar || info.type.hasLevelMVar || info.type.hasFVar then
      throwError "non-closed type: {n}"
    let axioms ← collectAxioms n
    let row := Json.arr #[.str n.toString, toJson info.levelParams.length,
      exprJson info.levelParams info.type, toJson (axioms.toList.map Name.toString), toJson (binderNames #[] info.type)]
    logInfo m!"CANONICAL {row.compress}"
end SortCheckCanonical
