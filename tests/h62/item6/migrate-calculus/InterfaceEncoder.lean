import Lean

/-! External metadata encoder. It proves no interface-equivalence theorem and
never reads/replaces proof bodies. Types retain exact names, levels and binders;
only nonsemantic Expr.mdata is removed. Output belongs off git. -/
namespace H62.MigrateCalculus.Interfaces
open Lean

def node (tag : String) (xs : Array Json := #[]) : Json := .arr (#[.str tag] ++ xs)
def encodeName : Name → Json
  | .anonymous => node "anonymous"
  | .str p s => node "str" #[encodeName p, toJson s]
  | .num p n => node "num" #[encodeName p, toJson n]

def encodeLevel : Level → Except String Json
  | .zero => pure (node "zero")
  | .succ x => do return node "succ" #[← encodeLevel x]
  | .max x y => do return node "max" #[← encodeLevel x, ← encodeLevel y]
  | .imax x y => do return node "imax" #[← encodeLevel x, ← encodeLevel y]
  | .param n => pure (node "param" #[encodeName n])
  | .mvar _ => .error "Universe metavariable in frozen type"

def encodeBinder : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

partial def encodeExpr : Expr → Except String Json
  | .bvar n => pure (node "bvar" #[toJson n])
  | .fvar _ => .error "Free variable in frozen type"
  | .mvar _ => .error "Metavariable in frozen type"
  | .sort u => do return node "sort" #[← encodeLevel u]
  | .const n us => do return node "const" #[encodeName n, .arr (← us.toArray.mapM encodeLevel)]
  | .app f a => do return node "app" #[← encodeExpr f, ← encodeExpr a]
  | .lam n t b bi => do return node "lam" #[encodeName n, ← encodeExpr t, ← encodeExpr b, toJson (encodeBinder bi)]
  | .forallE n t b bi => do return node "forall" #[encodeName n, ← encodeExpr t, ← encodeExpr b, toJson (encodeBinder bi)]
  | .letE n t v b nd => do return node "let" #[encodeName n, ← encodeExpr t, ← encodeExpr v, ← encodeExpr b, toJson nd]
  | .lit (.natVal n) => pure (node "nat" #[toJson n])
  | .lit (.strVal s) => pure (node "string" #[toJson s])
  | .mdata _ e => encodeExpr e
  | .proj n i e => do return node "proj" #[encodeName n, toJson i, ← encodeExpr e]

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

-- Expected module declarations are inserted by the deterministic generator.
def expectedModules : Array String := #[] -- H62_EXPECTED_MODULES

run_meta do
  if expectedModules.isEmpty then return ()
  let env ← getEnv
  let some output ← IO.getEnv "H62_INTERFACE_OUTPUT"
    | throwError "Set H62_INTERFACE_OUTPUT to an owned off-git output path"
  for expected in expectedModules do
    unless env.header.moduleNames.any (fun name => name.toString == expected) do
      throwError "Missing imported frozen module: {expected}"
  let handle ← IO.FS.Handle.mk output .write
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[index.toNat]!.toString
      if expectedModules.contains moduleName then
        let encoded ← match encodeExpr info.type with
          | .ok value => pure value
          | .error reason => throwError "{name}: {reason}"
        let row := Json.mkObj [("module",toJson moduleName),("name",toJson name.toString),
          ("name_tree",encodeName name),("kind",toJson (kind info)),
          ("level_params",.arr (info.levelParams.toArray.map encodeName)),
          ("unsafe",toJson info.isUnsafe),("type",encoded)]
        handle.putStrLn row.compress
        count := count + 1
  handle.flush
  logInfo m!"Frozen baseline types: {expectedModules.size} modules, {count} declarations"
end H62.MigrateCalculus.Interfaces
