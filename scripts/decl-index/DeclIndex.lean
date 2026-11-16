/-
DeclIndex: one JSON line per user-facing declaration of the imported `Solidity.*` modules.
Run through scripts/decl-index/decl_index.py, which replaces `import Solidity` with the
modules to index and sets DECLINDEX_OUT (and optionally DECLINDEX_PREFIX, default Solidity).
Needs the imported oleans in .lake/build (`lake env` does not build or fetch them).

Fields: name (private prefix removed), private, module, kind, proj, deprecated, aliasOf
(value is another constant, eta-reduced), typeHash, litHash, typeClass, shapeHash, typeConsts,
valueHash, valueClass, valueDepth. Level params are renamed u_0.. and `mdata` stripped;
`Expr.hash` and `==` ignore binder names and binder info. typeClass/valueClass are
"<hash>.<k>": the hash bucket split by `==` (exact within one run; compare runs by hash).
Value constants named after the declaration (recursion, match_/proof_, `_unsafe_rec`)
become `_self.*`. Shape: constants of `Solidity*` modules become `_S<i>`.
Whole `Solidity`: about 4 min and 5 GB on one thread.
-/
import Lean
import Solidity

open Lean Meta

namespace DeclIndex

partial def stripMData (e : Expr) : Expr :=
  e.replace fun
    | .mdata _ b => some (stripMData b)
    | _ => none

def canonLevels (ps : List Name) (e : Expr) : Expr :=
  if ps.isEmpty then e else
  let us := (List.range ps.length).map fun i => Level.param (Name.mkSimple s!"u_{i}")
  e.instantiateLevelParams ps us

def normType (ci : ConstantInfo) : Expr := stripMData (canonLevels ci.levelParams ci.type)

/-- Replace constants owned by `self` (itself or `self.*`) with `_self.*`. -/
def selfNorm (selfs : List Name) (e : Expr) : Expr :=
  e.replace fun
    | .const c ls =>
      match selfs.find? (fun s => s == c || s.isPrefixOf c) with
      | some s => some (.const (c.replacePrefix s `_self) ls)
      | none => none
    | _ => none

def isSolMod (env : Environment) (pre : Name) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some i => pre.isPrefixOf (env.header.moduleNames[i.toNat]!)
  | none => pre.isPrefixOf (privateToUserName c)  -- declared in the current file

def shapeOf (env : Environment) (pre : Name) (e : Expr) : Expr × Nat :=
  let cs := e.foldConsts (#[] : Array Name) fun c acc => if isSolMod env pre c && !acc.contains c then acc.push c else acc
  let e' := e.replace fun
    | .const c _ => (cs.idxOf? c).map fun i => .const (Name.mkSimple s!"_S{i}") []
    | _ => none
  (e', cs.size)

def kindOf (env : Environment) (n : Name) (ci : ConstantInfo) : Option String :=
  match ci with
  | .thmInfo _ => some "theorem"
  | .axiomInfo _ => some "axiom"
  | .opaqueInfo _ => some (if isInstanceCore env n then "instance" else "opaque")
  | .defnInfo _ =>
    if isInstanceCore env n then some "instance"
    else if getReducibilityStatusCore env n == .reducible then some "abbrev"
    else some "def"
  | .inductInfo _ => some (if isStructure env n then "structure" else "inductive")
  | _ => none

def generatedSuffixes : List String :=
  ["splitter", "congr_simp", "injEq", "inj", "sizeOf_spec", "eq_def", "eq_unfold", "induct", "fun_cases", "mutual_induct",
   "ctorIdx", "toCtorIdx", "noConfusionType", "induct_unfolding", "recOn", "casesOn", "below",
   "brecOn", "binductionOn", "ibelow"]

def skip (env : Environment) (n : Name) (ci : ConstantInfo) : Bool :=
  let u := privateToUserName n
  n.hasMacroScopes || u.isInternalDetail ||
  u.components.any (·.isInternalDetail) ||  -- e.g. `f.match_3.splitter`
  isAuxRecursor env n || isNoConfusion env n ||
  isMatcherCore env n || ci matches .ctorInfo _ || ci matches .recInfo _ || ci matches .quotInfo _ ||
  (match u with | .str _ s => generatedSuffixes.contains s | _ => false)

/-- The expression whose hash stands for a definition's body, if any. -/
def valueExpr? (env : Environment) (n : Name) (ci : ConstantInfo) : Option Expr :=
  let impl := (Compiler.getImplementedBy? env n).orElse fun _ =>
    let u := n ++ `_unsafe_rec; if env.contains u then some u else none
  let body? : Option (List Name × Expr) :=
    match ci with
    | .defnInfo v => some (ci.levelParams, v.value)
    | .opaqueInfo v =>
      match impl.bind env.find? with
      | some (.defnInfo w) => some (w.levelParams, w.value)
      | _ => some (ci.levelParams, v.value)
    | _ => none
  body?.map fun (ps, b) =>
    selfNorm (n :: impl.toList) (stripMData (canonLevels ps b))

def aliasOf? (n : Name) (ci : ConstantInfo) : Option Name :=
  let v? := match ci with
    | .thmInfo v => some v.value
    | .defnInfo v => some v.value
    | _ => none
  v?.bind fun v =>
    match (stripMData v).eta.getAppFn with
    | .const c _ => if c != n && !n.isPrefixOf c && (stripMData v).eta.getAppArgs.all (·.isFVar) then some c else none
    | _ => none

structure Row where
  name : Name
  ci : ConstantInfo
  json : List (String × Json)
  tHash : UInt64
  vHash : Option UInt64
  deriving Inhabited

/-- Split hash buckets by `==`; return class label per row index. -/
def classes (rows : Array Row) (key : Row → Option UInt64) (expr : Row → Option Expr) :
    Std.HashMap Nat String := Id.run do
  let mut buckets : Std.HashMap UInt64 (Array Nat) := {}
  for i in [:rows.size] do
    if let some h := key rows[i]! then
      buckets := buckets.insert h ((buckets.getD h #[]).push i)
  let mut out : Std.HashMap Nat String := {}
  for (h, idxs) in buckets.toList do
    if idxs.size == 1 then
      out := out.insert idxs[0]! s!"{h}.0"
    else
      let mut reps : Array Expr := #[]
      for i in idxs do
        let e := (expr rows[i]!).get!
        match reps.findIdx? (· == e) with
        | some k => out := out.insert i s!"{h}.{k}"
        | none =>
          out := out.insert i s!"{h}.{reps.size}"
          reps := reps.push e
  return out

/-- Hash of the sorted set of literals in `e`: `Expr.hash` collides on statements that differ
only in large numerals. A set, so it does not depend on how subterms are shared. -/
def litKey (e : Expr) : CoreM UInt64 := do
  let r ← IO.mkRef (#[] : Array String)
  e.forEach fun
    | .lit (.natVal n) => r.modify (·.push (toString n))
    | .lit (.strVal v) => r.modify (·.push ("s:" ++ v))
    | _ => pure ()
  let xs := (← r.get).qsort (· < ·)
  let mut h : UInt64 := 7
  let mut last : Option String := none
  for x in xs do
    if last != some x then h := mixHash h (Hashable.hash x)
    last := some x
  return h

def run : CoreM Unit := do
  let env ← getEnv
  let outPath := (← IO.getEnv "DECLINDEX_OUT").getD "decls.jsonl"
  let pre := ((← IO.getEnv "DECLINDEX_PREFIX").getD "Solidity").toName
  let t0 ← IO.monoMsNow
  let mut rows : Array Row := #[]
  let mods := env.header.moduleNames
  let mut srcs : Array (Name × Array Name) := #[]
  for i in [:mods.size] do
    if pre.isPrefixOf mods[i]! then srcs := srcs.push (mods[i]!, env.header.moduleData[i]!.constNames)
  if (← IO.getEnv "DECLINDEX_LOCAL").isSome then
    let local_ := env.constants.map₂.toList.map (·.1) |>.filter (!(`DeclIndex).isPrefixOf ·)
    srcs := srcs.push (`«<local>», local_.toArray)
  for (m, names) in srcs do
    for n in names do
      let some ci := env.find? n | continue
      if skip env n ci then continue
      let some kind := kindOf env n ci | continue
      let ty := normType ci
      let (shape, nSol) := shapeOf env pre ty
      let val? := valueExpr? env n ci
      let lit ← litKey ty
      let json : List (String × Json) := [
        ("name", toJson (privateToUserName n).toString),
        ("private", toJson (isPrivateName n)),
        ("module", toJson m.toString),
        ("kind", toJson kind),
        ("proj", toJson (env.isProjectionFn n)),
        ("deprecated", toJson (Linter.isDeprecated env n)),
        ("aliasOf", match aliasOf? n ci with | some c => toJson (privateToUserName c).toString | none => Json.null),
        ("typeHash", toJson ty.hash),
        ("litHash", toJson lit),
        ("shapeHash", toJson shape.hash),
        ("typeConsts", toJson nSol),
        ("valueHash", match val? with | some v => toJson v.hash | none => Json.null),
        ("valueDepth", match val? with | some v => toJson v.approxDepth.toNat | none => Json.null)]
      rows := rows.push { name := n, ci, json, tHash := ty.hash, vHash := val?.map (·.hash) }
  let t1 ← IO.monoMsNow
  let tc := classes rows (some ·.tHash) (fun r => some (normType r.ci))
  let vc := classes rows (·.vHash) (fun r => valueExpr? env r.name r.ci)
  let t2 ← IO.monoMsNow
  let h ← IO.FS.Handle.mk outPath .write
  for i in [:rows.size] do
    let r := rows[i]!
    let extra := [("typeClass", toJson (tc.getD i "")),
                  ("valueClass", match vc.get? i with | some s => toJson s | none => Json.null)]
    h.putStrLn (Json.mkObj (r.json ++ extra)).compress
  h.flush
  let t3 ← IO.monoMsNow
  IO.println s!"decls={rows.size} modules={mods.size} scan={t1-t0}ms classes={t2-t1}ms write={t3-t2}ms -> {outPath}"

end DeclIndex

#eval DeclIndex.run
