import Lean

/-!
A conservative serialization of an elaborated declaration type. This is
tooling evidence: equal serializations do not prove equal bodies, ownership,
or that moving either declaration is safe. Unsupported forms fail explicitly.
-/

open Lean Elab Command

namespace H62Signature

def node (tag : String) (fields : List Json := []) : Json :=
  Json.arr ((Json.str tag :: fields).toArray)

def encodeName : Name → Json
  | .anonymous => node "anonymous"
  | .str parent s => node "str" [encodeName parent, toJson s]
  | .num parent n => node "num" [encodeName parent, toJson n]

def encodeBinder : BinderInfo → Json
  | .default => node "explicit"
  | .implicit => node "implicit"
  | .strictImplicit => node "strictImplicit"
  | .instImplicit => node "instImplicit"

def encodeLevel (params : List Name) : Level → Except String Json
  | .zero => pure (node "zero")
  | .succ a => do
      pure (node "succ" [(← encodeLevel params a)])
  | .max a b => do
      pure (node "max" [(← encodeLevel params a), (← encodeLevel params b)])
  | .imax a b => do
      pure (node "imax" [(← encodeLevel params a), (← encodeLevel params b)])
  | .param n =>
      match params.idxOf? n with
      | some i => pure (node "param" [toJson i])
      | none => throw "undeclared universe parameter"
  | .mvar _ => throw "universe metavariable"

def encodeExpr (params : List Name) : Expr → Except String Json
  | .bvar n => pure (node "bvar" [toJson n])
  | .fvar _ => throw "free expression variable"
  | .mvar _ => throw "expression metavariable"
  | .sort u => do
      pure (node "sort" [(← encodeLevel params u)])
  | .const n us => do
      let levels ← us.mapM (encodeLevel params)
      pure (node "const" [encodeName n, Json.arr levels.toArray])
  | .app f a => do
      pure (node "app" [(← encodeExpr params f), (← encodeExpr params a)])
  | .lam _ ty body binder => do
      pure (node "lam" [encodeBinder binder, (← encodeExpr params ty), (← encodeExpr params body)])
  | .forallE _ ty body binder => do
      pure (node "forall" [encodeBinder binder, (← encodeExpr params ty), (← encodeExpr params body)])
  | .letE _ ty value body nondep => do
      pure (node "let" [(← encodeExpr params ty), (← encodeExpr params value),
        (← encodeExpr params body), toJson nondep])
  | .lit (.natVal n) => pure (node "nat" [toJson n])
  | .lit (.strVal s) => pure (node "string" [toJson s])
  | .mdata _ _ => throw "expression metadata"
  | .proj n i body => do
      pure (node "proj" [encodeName n, toJson i, (← encodeExpr params body)])

def encodeType (params : List Name) (ty : Expr) : Except String Json := do
  if params.eraseDups.length != params.length then
    throw "duplicate universe parameter"
  if ty.hasFVar || ty.hasMVar || ty.hasLooseBVars then
    throw "type is not closed"
  let encoded ← encodeExpr params ty
  pure (node "declaration-type" [toJson params.length, encoded])

def fingerprint (info : ConstantInfo) : Except String Json :=
  encodeType info.levelParams info.type

/-- Emits a conservative record for an explicitly named elaborated declaration.
The record is not bound to a source or compiled-module hash; callers must pin
those inputs before comparing records from different environments. -/
elab "#h62_signature " id:ident : command => do
  let name ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  let some info := env.find? name | throwError "missing declaration {name}"
  let signature ← match fingerprint info with
    | .ok value => pure value
    | .error reason => throwError "unsupported declaration type {name}: {reason}"
  let origin := match env.getModuleIdxFor? name with
    | some idx => node "imported" [encodeName env.header.moduleNames[idx.toNat]!]
    | none => node "not-in-import-map"
  let record := Json.mkObj [
    ("format", toJson (1 : Nat)),
    ("lean_version", toJson Lean.versionString),
    ("declaration", encodeName name),
    ("origin", origin),
    ("environment_binding", toJson ("unbound" : String)),
    ("signature", signature)]
  logInfo m!"H62_SIGNATURE {record.compress}"

namespace Controls

theorem alphaA (x : Nat) : x = x := rfl
theorem alphaB (y : Nat) : y = y := rfl
theorem differentType (x : Int) : x = x := rfl
theorem differentBinder {x : Nat} : x = x := rfl

universe u v

theorem universeA {α : Type u} (x : α) : x = x := rfl
theorem universeB {β : Type v} (y : β) : y = y := rfl

inductive Indexed : Nat → Type where
  | mk (n : Nat) : Indexed n

theorem indexedOne (x : Indexed 1) : x = x := rfl
theorem indexedTwo (x : Indexed 2) : x = x := rfl

namespace First
def T := Nat
theorem sameSpelling (x : T) : x = x := rfl
end First

namespace Second
def T := Int
theorem sameSpelling (x : T) : x = x := rfl
end Second

end Controls

run_cmd do
  let env ← getEnv
  let controlRoot := (Name.mkSimple "H62Signature").str "Controls"
  let n := fun s => controlRoot.str s
  let cases : List (Name × Name × Bool) := [
    (n "alphaA", n "alphaB", true),
    (n "alphaA", n "differentType", false),
    (n "alphaA", n "differentBinder", false),
    (n "universeA", n "universeB", true),
    (n "indexedOne", n "indexedTwo", false),
    ((n "First").str "sameSpelling", (n "Second").str "sameSpelling", false)]
  for (left, right, expected) in cases do
    let some a := env.find? left | throwError "missing control {left}"
    let some b := env.find? right | throwError "missing control {right}"
    let .ok af := fingerprint a | throwError "unsupported control {left}"
    let .ok bf := fingerprint b | throwError "unsupported control {right}"
    if (af == bf) != expected then
      throwError "signature control failed: {left} / {right}"
  logInfo m!"H62 signature controls: {cases.length} passed"

run_cmd do
  let a := Name.mkSimple "a"
  let b := Name.mkSimple "b"
  let nat := Expr.const (Name.mkSimple "Nat") []
  let s := Expr.sort Level.zero
  let structural : List (Expr × Expr × Bool) := [
    (.lam a nat (.bvar 0) .default, .lam b nat (.bvar 0) .default, true),
    (.forallE a nat (.bvar 0) .default, .forallE b nat (.bvar 0) .implicit, false),
    (.letE a nat (.lit (.natVal 1)) (.bvar 0) false,
      .letE b nat (.lit (.natVal 1)) (.bvar 0) true, false),
    (.proj a 0 (.bvar 0), .proj a 1 (.bvar 0), false),
    (.proj a 0 (.bvar 0), .proj b 0 (.bvar 0), false),
    (.forallE a nat (.bvar 0) .strictImplicit, .forallE a nat (.bvar 0) .instImplicit, false),
    (.sort (.max (.param a) (.param b)), .sort (.imax (.param a) (.param b)), false),
    (.sort (.succ (.param a)), .sort (.param a), false),
    (.const a [], .const a [.zero], false),
    (.lit (.strVal "a b"), .lit (.strVal "a  b"), false),
    (.const (Name.mkSimple "A.B") [], .const ((Name.mkSimple "A").str "B") [], false),
    (.const ((Name.mkSimple "A").str "1") [], .const ((Name.mkSimple "A").num 1) [], false),
    (.const a [Level.param a, Level.param b], .const a [Level.param b, Level.param a], false)]
  for (left, right, expected) in structural do
    let .ok x := encodeExpr [a,b] left | throwError "unexpected structural rejection"
    let .ok y := encodeExpr [a,b] right | throwError "unexpected structural rejection"
    if (x == y) != expected then throwError "structural encoding control failed"
  let rejected : List (Except String Json) := [
    encodeType [] (.bvar 0),
    encodeType [] (.fvar ⟨a⟩),
    encodeType [] (.mvar ⟨a⟩),
    encodeType [] (.mdata default s),
    encodeType [] (.sort (.param a)),
    encodeType [] (.sort (.mvar ⟨a⟩)),
    encodeType [a,a] s]
  for result in rejected do
    if result.isOk then throwError "unsupported encoding was accepted"
  let branches : List (Except String Json × String) := [
    (encodeExpr [] (.fvar ⟨a⟩), "free expression variable"),
    (encodeExpr [] (.mvar ⟨a⟩), "expression metavariable"),
    (encodeExpr [] (.mdata default s), "expression metadata"),
    (encodeLevel [] (.param a), "undeclared universe parameter"),
    (encodeLevel [] (.mvar ⟨a⟩), "universe metavariable"),
    (encodeType [a,a] s, "duplicate universe parameter")]
  for (result, expected) in branches do
    match result with
    | .error actual => if actual != expected then throwError "wrong refusal reason"
    | .ok _ => throwError "unsupported branch was accepted"
  let .ok arityZero := encodeType [] s | throwError "zero arity rejected"
  let .ok arityOne := encodeType [a] s | throwError "one arity rejected"
  if arityZero == arityOne then throwError "universe arity conflated"
  logInfo m!"H62 structural controls: {structural.length} comparisons, {rejected.length} refusals, {branches.length} reasons, arity passed"

#h62_signature Controls.alphaA

end H62Signature
