import SignatureFingerprint

/-!
Guards expression-metadata stripping and cross-version signature promotion.
This additive observation format preserves every supported metadata entry in
list order, including duplicate keys and value constructors. Syntax payloads
remain explicit refusals. V1 and its records are unchanged; this is not a
semantic-equivalence, body-equivalence, ownership or model-witness theorem.
-/

open Lean Elab Command

namespace H62MetadataV2
open H62Signature

def encodeData : DataValue → Except String Json
  | .ofString value => pure (node "ofString" [toJson value])
  | .ofBool value => pure (node "ofBool" [toJson value])
  | .ofName value => pure (node "ofName" [encodeName value])
  | .ofNat value => pure (node "ofNat" [toJson value])
  | .ofInt value => pure (node "ofInt" [toJson value])
  | .ofSyntax _ => throw "metadata syntax payload"

def encodeMetadata (data : MData) : Except String Json := do
  let entries ← data.entries.mapM fun (key, value) => do
    pure (node "entry" [encodeName key, (← encodeData value)])
  pure (node "metadata-entries" entries)

def encodeExpr (params : List Name) : Expr → Except String Json
  | .mdata data body => do
      pure (node "mdata" [(← encodeMetadata data), (← encodeExpr params body)])
  | .app fn arg => do
      pure (node "app" [(← encodeExpr params fn), (← encodeExpr params arg)])
  | .lam _ ty body binder => do
      pure (node "lam" [encodeBinder binder, (← encodeExpr params ty), (← encodeExpr params body)])
  | .forallE _ ty body binder => do
      pure (node "forall" [encodeBinder binder, (← encodeExpr params ty), (← encodeExpr params body)])
  | .letE _ ty value body nondep => do
      pure (node "let" [(← encodeExpr params ty), (← encodeExpr params value),
        (← encodeExpr params body), toJson nondep])
  | .proj name index body => do
      pure (node "proj" [encodeName name, toJson index, (← encodeExpr params body)])
  | leaf => H62Signature.encodeExpr params leaf

def encodeType (params : List Name) (ty : Expr) : Except String Json := do
  if params.eraseDups.length != params.length then throw "duplicate universe parameter"
  if ty.hasFVar || ty.hasMVar || ty.hasLooseBVars then throw "type is not closed"
  pure (node "declaration-type-with-metadata-v2" [toJson params.length, (← encodeExpr params ty)])

def fingerprint (info : ConstantInfo) : Except String Json := encodeType info.levelParams info.type

end H62MetadataV2

run_cmd do
  let key := Name.mkSimple "key"
  let other := Name.mkSimple "other"
  let nat := mkConst ``Nat
  let wrap := fun (entries : List (Name × DataValue)) (body : Expr) => Expr.mdata ⟨entries⟩ body
  let cases : List (Expr × Expr) := [
    (nat, wrap [] nat),
    (wrap [(key, .ofBool true)] nat, wrap [(key, .ofBool false)] nat),
    (wrap [(key, .ofNat 0)] nat, wrap [(key, .ofInt 0)] nat),
    (wrap [(key, .ofString "0")] nat, wrap [(key, .ofNat 0)] nat),
    (wrap [(key, .ofName key)] nat, wrap [(key, .ofString "key")] nat),
    (wrap [(key, .ofBool true)] nat, wrap [(other, .ofBool true)] nat),
    (wrap [(key, .ofBool true), (key, .ofBool false)] nat,
      wrap [(key, .ofBool false), (key, .ofBool true)] nat),
    (wrap [(key, .ofBool true)] (wrap [] nat), wrap [] (wrap [(key, .ofBool true)] nat)),
    (.app (wrap [] nat) nat, .app nat (wrap [] nat)),
    (wrap [(key, .ofName (Name.mkSimple "A.B"))] nat,
      wrap [(key, .ofName ((Name.mkSimple "A").str "B"))] nat)]
  for (left, right) in cases do
    let .ok a := H62MetadataV2.encodeExpr [] left | throwError "metadata control refused"
    let .ok b := H62MetadataV2.encodeExpr [] right | throwError "metadata control refused"
    if a == b then throwError "metadata distinction collapsed"
  let .ok old := H62Signature.encodeExpr [] nat | throwError "legacy leaf refused"
  let .ok current := H62MetadataV2.encodeExpr [] nat | throwError "new leaf refused"
  if old != current then throwError "metadata-free leaf changed"
  let .error _ := H62Signature.encodeType [] (wrap [] nat) | throwError "legacy metadata refusal changed"
  let .error _ := H62MetadataV2.encodeExpr [] (wrap [(key, .ofSyntax Syntax.missing)] nat)
    | throwError "syntax metadata was silently simplified"
  let .ok v1 := H62Signature.encodeType [] nat | throwError "legacy type refused"
  let .ok v2 := H62MetadataV2.encodeType [] nat | throwError "new type refused"
  if v1 == v2 then throwError "observation versions conflated"
  logInfo m!"METADATA_V2_CONTROLS_PASS {cases.length + 4}"
