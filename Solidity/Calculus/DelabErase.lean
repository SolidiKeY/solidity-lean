import Solidity.Calculus.Rules
import Solidity.Calculus.RuleKit

/-!
# A scoped term's erasure, with its schema variables

The translation `Calculus/Delab.lean`'s delaborators print through:
the `Expr` of a scoped statement, premise or formula, its schema variables
free, to the `Expr` of its erasure, the `Update.lean`/`Syntax.lean` term
that `Fml.erase` would compute (`Delab.tr`, run under `Delab.withTwins`).

* **Schema variables** get twins: each free variable of a scoped type
  (`v : Idx Γ (.val p)`, `se : Simple C Γ p`, `thenStm : Prog C Γ Γ₁`)
  stands, for the printer, as a local of the erased type with the same name
  (`v : Var`, `se : Simple C p`, `thenStm : Prog C`).
* **Positions** are names: `.here` is the innermost local the term itself
  declared (`T storage sp = nsp;`, `Premise.bind`, `{ x := … }`, `∀`), and
  `.there` steps past one; a schema variable under any number of `.there`
  or `up` is itself, so a rule's weakenings (`v.there`, `Val.up e`) print as
  the rule line writes them.
* **What erasure loses is invisible**, as `Fml.show` has it: a
  capture's scope end, a pop of an update and the hidden binder print as
  nothing; the end of a block in a formula's frames is the local
  `blockEndName`, which the printer turns into `}`.

It imports the scoped rule table and `RuleKit` only, below the
delaborators, the sequent and the strategy, so a reader of the rule table
(the SolKey reader) can erase a constructor without them (decision 53).
-/

namespace Solidity

open Lean Meta

namespace Delab

/-! ## The erased types -/

/-- The erased twins `Solidity.X` may have, in order: a statement or a
block ↦ the one as written (`Solidity.Surface.Stmt`, `Solidity.Surface.Prog`),
a formula ↦ the closer's (`Solidity.NFml`; `trFml` makes it `Surface.Fml`
under a modality), any other family ↦ its twin as written
(`Solidity.Surface.X`) or the closer's (`Solidity.NFml.X`). -/
def legacyNames (n : Lean.Name) : List Lean.Name :=
  if (`Solidity.Stmt).isPrefixOf n then
    [n.replacePrefix `Solidity.Stmt `Solidity.Surface.Stmt]
  else if (`Solidity.Prog).isPrefixOf n then
    [n.replacePrefix `Solidity.Prog `Solidity.Surface.Prog]
  else if (`Solidity.Fml).isPrefixOf n then
    [n.replacePrefix `Solidity.Fml `Solidity.NFml]
  else if (`Solidity).isPrefixOf n then
    let x := n.replacePrefix `Solidity .anonymous
    [`Solidity.Surface ++ x, `Solidity.NFml ++ x]
  else []

/-- The first erased twin of `n` that `env` declares. -/
def legacyName? (env : Environment) (n : Lean.Name) : Option Lean.Name :=
  (legacyNames n).find? env.contains

/-- The scoped families with no erased twin of their name, which
`legacyType?` erases by hand or which carry no context. -/
def untwinnedFamilies : List Lean.Name :=
  [``Idx, ``Args, ``Binders, ``CodeBinder, ``SHole, ``Prog, ``Frames, ``LTy]

/-- Whether `n` names a scoped family, whose values `tr` erases: one with an
erased twin, or one of `untwinnedFamilies`.  (The scoped side once had a
prefix of its own, `Solidity.Core`; no name of the erased side or of the
shared vocabulary has a twin.) -/
def isScopedFamily (env : Environment) (n : Lean.Name) : Bool :=
  (legacyName? env n).isSome || untwinnedFamilies.contains n

/-- Whether an erased formula is one as written: `Surface.Fml`, because a
modality is in it. -/
def isSurface (e : Expr) : Bool :=
  match e.getAppFn with
  | .const n _ => (`Solidity.Surface.Fml).isPrefixOf n || n == ``Solidity.NFml.toSurface
  | _ => false

/-- An erased formula as written (`Fml.toSurface` around one of the
closer's): the parts of a formula with a modality. -/
def asSurface (c e : Expr) : Expr :=
  if isSurface e then e else mkApp2 (mkConst ``Solidity.NFml.toSurface) c e

/-- Whether `ty` is a context. -/
def isCtx (ty : Expr) : MetaM Bool := do
  let ty ← whnfR ty
  return ty.isAppOfArity ``List 1 && (ty.getArg! 0).isConstOf ``LTy

/-- The erased type of a scoped one: `Idx Γ t` is `Var`, a block or frames
`Prog C`, any other family `F C Γ x̄` the family of the same name, its
contexts dropped.  With `schema` (a rule's schema variables, `withTwins`),
the parts of a call that have no family of the same name are their
erasures' types too: `Args C Γ ps` is `List (Arg C)` (`Args.erase`),
`Binders ρ` is `List (PrimTy × Var)`, `CodeBinder κ` is `Option Var`
(`CodeBinder.toOption`). -/
def legacyType? (ty : Expr) (schema : Bool := false) : MetaM (Option Expr) := do
  let ty ← whnfR (← instantiateMVars ty)
  let .const n _ := ty.getAppFn | return none
  let args := ty.getAppArgs
  if n == ``Idx then return some (mkConst ``Solidity.Var)
  if schema then
    if n == ``Args then
      return some (mkApp (mkConst ``List [levelZero]) (mkApp (mkConst ``Solidity.Arg) args[0]!))
    if n == ``Binders then
      return some (mkApp (mkConst ``List [levelZero])
        (mkApp2 (mkConst ``Prod [levelZero, levelZero]) (mkConst ``PrimTy) (mkConst ``Solidity.Var)))
    if n == ``CodeBinder then
      return some (mkApp (mkConst ``Option [levelZero]) (mkConst ``Solidity.Var))
  -- the storage hole is today's `Hole`
  if n == ``SHole then
    return some (mkAppN (mkConst ``Surface.Hole) #[args[0]!, args[2]!])
  if n == ``Prog || n == ``Frames then return some (mkApp (mkConst ``Solidity.Surface.Prog) args[0]!)
  let some n' := legacyName? (← getEnv) n | return none
  let keep ← args.filterM fun a => return !(← isCtx (← inferType a))
  let t := mkAppN (mkConst n') keep
  try
    let s ← inferType t
    unless (← whnf s).isSort do return none
    return some t
  catch _ => return none

/-! ## The translation -/

/-- The twins of the schema variables, and the statement a block's end
prints as (a local, `blockEndName`), when frames are printed. -/
structure Env where
  twins : Std.HashMap FVarId Expr := {}
  blockEnd : Option Expr := none
  /-- A rule's schema variables are being printed: a call or a `try` whose
  parts are schema variables is today's of their twins (`fbs`, `ic`,
  `try call returns (rets) …`). -/
  schema : Bool := false

abbrev TrM := ReaderT Env MetaM

/-- A position that is no local the term declared. -/
def unknownVar : Expr := mkApp (mkConst ``Solidity.Var.user) (toExpr "_")

/-- The twin of `e`, when it is a schema variable that has one. -/
def twin? (e : Expr) : TrM (Option Expr) := do
  let .fvar fv := (← instantiateMVars e).consumeMData | return none
  return (← read).twins.get? fv

/-- The name of a position, from the names `ns` the term declared
(innermost first). -/
partial def trIdx (ns : List Expr) (e : Expr) : TrM Expr := do
  let e := (← instantiateMVars e).consumeMData
  if let .fvar fv := e then return (← read).twins.getD fv unknownVar
  let e ← whnf e
  if e.isAppOf ``Idx.here then return ns.headD unknownVar
  if e.isAppOf ``Idx.there then return ← trIdx ns.tail e.appArg!
  if let .fvar fv := e then return (← read).twins.getD fv unknownVar
  return unknownVar

/-- The names of what a frame end by `h : Thin Γ Δ` keeps, from the names
`ns` of `Δ`; as many as it can read when `h` does not compute. -/
partial def thinNames (ns : List Expr) (h : Expr) : MetaM (List Expr) := do
  let h ← whnf h
  if h.isAppOf ``Thin.keep then return ns.headD unknownVar :: (← thinNames ns.tail h.appArg!)
  if h.isAppOf ``Thin.drop then return ← thinNames ns.tail h.appArg!
  return ns

/-- How many locals a scope end pops, when it computes. -/
partial def extDepth (e : Expr) : MetaM Nat := do
  let e ← whnf e
  if e.isAppOf ``Ext.push then return (← extDepth e.appArg!) + 1
  return 0

/-- The lowering functions, whose erasure is the function of the same
name (`Lower.lean`'s `lower_erase`). -/
def lowerFns : List Lean.Name :=
  [``Simple.lower, ``SPath.lower, ``Loc.lower, ``MPath.lower, ``MLoc.lower, ``Val.lower,
    ``Src.lower, ``MSrc.lower, ``Simple.keyLower, ``Val.keyLower]

/-- A part of the program or a term, read with one local more on top:
`Val.up` and its kin (the one other `Solidity` name ending in `up` is a
theorem, `Wrote.up`, which no term heads). -/
def isUp (n : Lean.Name) : Bool := (`Solidity).isPrefixOf n && n.getString! == "up"

/-- The `fill` of a scoped hole, and today's of the same hole. -/
def holeFills : List (Lean.Name × Lean.Name) :=
  [(``SHole.fill, ``Surface.Hole.fill), (``MHole.fill, ``Surface.MHole.fill),
    (``VHole.fill, ``Surface.VHole.fill), (``NewLhs.fill, ``Surface.NewLhs.fill)]

/-- A hole under any number of `up`s: the hole itself. -/
partial def stripUps (e : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e).consumeMData
  match e.getAppFn.constName? with
  | some n => if isUp n && e.getAppNumArgs > 0 then stripUps e.appArg! else return e
  | none => return e

/-- A piece of a program: one statement, or a program variable spliced in. -/
inductive Piece where
  | one (s : Expr)
  | many (P : Expr)

/-- The list of the pieces, of elements of type `ty` (in `Type`):
`s :: P ++ ω`.  Built unchecked, so that a piece that did not erase stays
in place and prints as `‹…›`. -/
def Piece.buildOf (ty : Expr) (ps : Array Piece) : MetaM Expr := do
  let L := mkApp (mkConst ``List [levelZero]) ty
  let app := mkApp4 (mkConst ``HAppend.hAppend [levelZero, levelZero, levelZero]) L L L
    (← synthInstance (mkApp3 (mkConst ``HAppend [levelZero, levelZero, levelZero]) L L L))
  let mut acc : Option Expr := none
  for p in ps.reverse do
    acc ← match p, acc with
      | .one s, none => mkListLit ty [s]
      | .one s, some r => pure (mkApp3 (mkConst ``List.cons [levelZero]) ty s r)
      | .many P, none => pure P
      | .many P, some r => pure (mkApp2 app P r)
  match acc with
  | some t => return t
  | none => mkListLit ty []

/-- The program of the pieces: `s :: P ++ ω`, as `progTerm` writes it. -/
def Piece.build (c : Expr) (ps : Array Piece) : MetaM Expr :=
  Piece.buildOf (mkApp (mkConst ``Solidity.Surface.Stmt) c) ps

/-- The contract of a scoped term, its type's first argument. -/
def contractOf (e : Expr) : MetaM Expr := do
  let ty ← whnfR (← inferType e)
  return ty.getArg! 0

/-- The names of binders, innermost first (`Binders.names`), when they
compute. -/
partial def bindersNames? (bs : Expr) : MetaM (Option (List Expr)) := do
  let bs ← whnf bs
  if bs.isAppOf ``Binders.nil then return some []
  if bs.isAppOfArity ``Binders.snoc 4 then
    let some xs ← bindersNames? (bs.getArg! 1) | return none
    return some (bs.getArg! 3 :: xs)
  return none

/-- `List (PrimTy × Var)`, the erased binders' type. -/
def pairsTy : Expr :=
  mkApp (mkConst ``List [levelZero])
    (mkApp2 (mkConst ``Prod [levelZero, levelZero]) (mkConst ``PrimTy) (mkConst ``Solidity.Var))

/-- `List (Stmt C)` -/
def stmtsTy (c : Expr) : Expr := mkApp (mkConst ``List [levelZero]) (mkApp (mkConst ``Solidity.Surface.Stmt) c)

/-- Binders as the list `Binders.toList` computes, in the order they are
bound, and their names, innermost first, when they compute. -/
partial def bindersPairs? (bs : Expr) : MetaM (Option (Expr × List Expr)) := do
  let rec go (bs : Expr) : MetaM (Option (Array Expr × List Expr)) := do
    let bs ← whnf bs
    if bs.isAppOf ``Binders.nil then return some (#[], [])
    unless bs.isAppOfArity ``Binders.snoc 4 do return none
    let some (xs, names) ← go (bs.getArg! 1) | return none
    let x := bs.getArg! 3
    return some (xs.push (← mkAppM ``Prod.mk #[bs.getArg! 2, x]), x :: names)
  let some (xs, names) ← go bs | return none
  let ty := mkApp2 (mkConst ``Prod [levelZero, levelZero]) (mkConst ``PrimTy) (mkConst ``Solidity.Var)
  return some (← mkListLit ty xs.toList, names)

/-- A branch's binders as `bindersPairs?` reads them; a schema variable
(`rets`) its twin, the `Panic` code's (`code.binders`) today's
`codeBinders` of its twin, neither naming a local the term reads. -/
def branchBinders? (bs : Expr) : TrM (Option (Expr × List Expr)) := do
  if let some x ← twin? bs then return some (x, [])
  let bs' := (← instantiateMVars bs).consumeMData
  if bs'.isAppOf ``CodeBinder.binders && bs'.getAppNumArgs > 0 then
    if let some x ← twin? bs'.appArg! then
      return some (mkApp (mkConst ``Solidity.codeBinders) x, [])
  bindersPairs? bs

/-- The length of a context, when it computes. -/
partial def ctxLength? (Γ : Expr) : MetaM (Option Nat) := do
  let Γ ← whnf Γ
  if Γ.isAppOf ``List.nil then return some 0
  if Γ.isAppOfArity ``List.cons 3 then return (· + 1) <$> (← ctxLength? Γ.appArg!)
  return none

/-- The names of the context a call leaves its caller in
(`CallRet.outNames`). -/
def callOutNames (ns : List Expr) (ret : Expr) : MetaM (List Expr) := do
  let ret ← whnf ret
  match ret.getAppFn.constName? with
  | some ``CallRet.mem => return ret.getArg! 2 :: ns
  | some ``CallRet.rets => do
    if let some xs ← bindersNames? (ret.getArg! 2) then return xs ++ ns
    match ← ctxLength? (ret.getArg! 1) with
    | some n => return List.replicate n unknownVar ++ ns
    | none => return ns
  | _ => return ns

/-- The names a statement leaves: its declaration's on top. -/
def stmtOutNames (ns : List Expr) (s : Expr) : MetaM (List Expr) := do
  let s ← whnf s
  match s.getAppFn.constName? with
  | some ``Stmt.declLocal | some ``Stmt.declStorage => return s.getArg! 3 :: ns
  | some ``Stmt.declMem => return s.getArg! 3 :: ns
  | some ``Stmt.call => callOutNames ns (s.getArg! 8)
  | _ => return ns

/-- `(Prog.wk up P).2.2`, the unfolding of `Prog.up P` (a block read with
one local more on top), as a projection or an application: `P`. -/
def wkUp? (e : Expr) : Option Expr :=
  let snd? (e : Expr) (s : Lean.Name) (f : Lean.Name) : Option Expr :=
    match e.consumeMData with
    | .proj n 1 x => if n == s then some x.consumeMData else none
    | e => if e.isAppOfArity f 3 then some e.appArg!.consumeMData else none
  match snd? e ``Prod ``Prod.snd with
  | none => none
  | some x => match snd? x ``Sigma ``Sigma.snd with
    | none => none
    | some w =>
      let args := w.getAppArgs
      if w.isAppOf ``Prog.wk && args.size ≥ 3 then
        match args[args.size - 3]?.bind (·.getAppFn.constName?) with
        | some n => if isUp n then args.back? else none
        | none => none
      else none

/-- `n' xs`, each argument that is a proof of the wrong type replaced by a
placeholder of the type `n'` asks (`mkSorry`): printing only, never added
to the environment. -/
def withProofHoles (n' : Lean.Name) (xs : Array Expr) : MetaM (Option Expr) := do
  let mut f := mkConst n'
  let mut ty ← inferType f
  for a in xs do
    let .forallE _ d b _ ← whnf ty | return none
    let a' ← if ← isProp d then
        if ← (try isDefEq (← inferType a) d catch _ => pure false) then pure a
        else mkSorry d false
      else pure a
    f := mkApp f a'
    ty := b.instantiate1 a'
  if ← (try Meta.check f; pure true catch _ => pure false) then return some f
  return none

/-- A print-only proof of a call's `hsep`: `Eq.refl true`, not a proof of
its separation; it prints as `⋯` (proofs are elided) and is no `sorryAx`. -/
def hsepPlaceholder : Expr :=
  mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst ``Bool.true)

mutual

/-- The erasure of a scoped term `e`, read where the term declared the
locals `ns` (innermost first).  What it does not know stays as it is, and
prints as `‹…›`. -/
partial def tr (ns : List Expr) (e : Expr) : TrM Expr := do
  let e := (← instantiateMVars e).consumeMData
  if let .fvar fv := e then return (← read).twins.getD fv e
  if let some P := wkUp? e then return ← tr ns.tail P
  let .const n _ := e.getAppFn | return e
  let args := e.getAppArgs
  if isUp n && args.size > 0 then return ← tr ns.tail args.back!
  if n == ``Prog.nil || n == ``Prog.cons then
    let (ps, _) ← progPieces ns e
    return ← Piece.build (← contractOf e) ps
  if n == ``Stmt.block then
    let (ps, _) ← progPieces ns args.back!
    return ← Piece.build (← contractOf e) ps
  if n == ``Tm.netOf && args.size == 4 then
    return ← mkAppM ``Surface.Tm.app1
      #[mkApp (mkConst ``Solidity.Op1.netOf) (← trIdx ns args[2]!), ← tr ns args[3]!]
  -- a hole that is a schema variable, filled: today's `fill` of its twin,
  -- which `ppStmt` prints as the rule line writes it (`lhs = nsp.fld`)
  if let some (_, n') := holeFills.find? (·.1 == n) then
    if args.size == 5 then
      if let .fvar fv ← stripUps args[3]! then
        if let some h := (← read).twins.get? fv then
          return ← mkAppM n' #[h, ← trArg ns args[4]!]
  -- `t⊕⊕`, the value of an increment on a schema operator: today's
  -- `Term.bumped`, which the conditional on the operator would unfold
  if (n == ``Tm.bumped || n == ``Tms.Term.bumped) && args.size == 5 && args[2]!.isFVar then
    return ← mkAppM ``Solidity.Term.bumped #[args[2]!, args[3]!, ← tr ns args[4]!]
  if n == ``Tm.app1 && args.size == 7 then
    return ← mkAppM ``Surface.Tm.app1 #[args[4]!, ← tr ns args[6]!]
  if n == ``Fml.upd && args.size == 6 then
    let (es, ms) ← updParts ns args[4]!
    let φ ← tr ms args[5]!
    if es.isEmpty then return φ
    -- built unchecked: a blocked update stays scoped, and prints as `‹…›`
    if isSurface φ then
      return mkApp4 (mkConst ``Solidity.Surface.Fml.upd) args[0]! args[3]!
        (← updList args[0]! args[4]! es) φ
    return mkApp4 (mkConst ``Solidity.NFml.upd) args[0]! args[3]! (← updList args[0]! args[4]! es) φ
  if n == ``Fml.modal && args.size == 8 then
    let (ps, ms) ← progPieces ns args[5]!
    let (qs, ms) ← framePieces ms args[6]!
    let P ← Piece.build args[0]! (ps ++ qs)
    return ← mkAppM ``Solidity.Surface.Fml.modal #[args[4]!, P, asSurface args[0]! (← tr ms args[7]!)]
  if n == ``Fml.all && args.size == 5 then
    -- an explicit `∀`'s mark (`Fml.markExplicit`) prints as nothing
    let x := args[2]!.consumeMData
    let φ ← tr (x :: ns) args[4]!
    if isSurface φ then return ← mkAppM ``Solidity.Surface.Fml.all #[x, args[3]!, φ]
    return ← mkAppM ``Solidity.NFml.all #[x, args[3]!, φ]
  if n == ``Fml.bind && args.size == 6 then return ← tr (args[3]! :: ns) args[5]!
  if n == ``Fml.anon && args.size == 4 then
    let some xs ← Solidity.listElems? args[2]! | return e
    let xs ← xs.mapM fun x => do
      let x ← whnf x
      trIdx ns x.appArg!
    let φ ← tr ns args[3]!
    let xs ← mkListLit (mkConst ``Solidity.Var) xs.toList
    if isSurface φ then return ← mkAppM ``Solidity.Surface.Fml.anon #[xs, φ]
    return ← mkAppM ``Solidity.NFml.anon #[xs, φ]
  -- a connective over a formula with a modality is one as written
  if let some k := [(``Fml.not, "not"), (``Fml.and, "and"), (``Fml.imp, "imp"),
      (``Fml.havoc, "havoc")].lookup n then
    let φs ← (args.extract 2 args.size).mapM (tr ns)
    if φs.any isSurface then
      return ← mkAppM (.str `Solidity.Surface.Fml k) (φs.map (asSurface args[0]!))
  if n == ``Premise.update && args.size == 4 then
    let (es, _) ← updParts ns args[3]!
    return mkApp2 (mkConst ``Surface.Premise.update) args[0]! (← updList args[0]! args[3]! es)
  if n == ``Premise.unfold && args.size == 6 then
    return ← mkAppM ``Surface.Premise.unfold #[← tr ns args[4]!]
  if n == ``Premise.bind && args.size == 6 then
    return ← mkAppM ``Surface.Premise.unfold #[← tr (args[3]! :: ns) args[5]!]
  if n == ``Premise.split && args.size == 9 then
    return ← mkAppM ``Surface.Premise.split
      #[← tr ns args[5]!, ← tr ns args[6]!, ← tr ns args[7]!, ← tr ns args[8]!]
  if n == ``Premise.check && args.size == 3 then
    let nil ← mkListLit (mkApp (mkConst ``Solidity.Surface.Stmt) args[0]!) []
    return ← mkAppM ``Surface.Premise.check #[← tr ns args[2]!, nil]
  if n == ``Premise.done && args.size == 4 then
    return mkApp2 (mkConst ``Surface.Premise.done) args[0]! args[3]!
  if n == ``Stmt.call && args.size == 10 then
    if let some r ← callStmt? ns args then return r
  -- `expand_function_body(fbs)`: the statements a call of schema variables
  -- runs, today's `Surface.Stmt.expandBody` of their twins
  if n == ``Premise.expandCall && args.size ≥ 3 then
    if let (some as, some ret, some body) :=
        (← twin? args[args.size - 3]!, ← twin? args[args.size - 2]!, ← twin? args.back!) then
      return ← mkAppM ``Surface.Premise.unfold #[← mkAppM ``Solidity.Surface.Stmt.expandBody #[as, ret, body]]
  if n == ``Stmt.tryCall && args.size == 15 then
    if let some r ← tryStmt? ns args then return r
  if n == ``Premise.branches && args.size == 3 then
    let some bs ← Solidity.listElems? args[2]! | return e
    let c := args[0]!
    let mut out : Array Expr := #[]
    for b in bs do
      let b ← whnf b
      unless b.isAppOfArity ``Branch.mk 6 do return e
      let some (xs, names) ← branchBinders? (b.getArg! 4) | return e
      let (ps, _) ← progPieces (names ++ ns) (b.getArg! 5)
      out := out.push (← mkAppM ``Prod.mk #[xs, ← Piece.build c ps])
    let ty := mkApp2 (mkConst ``Prod [levelZero, levelZero]) (pairsTy) (stmtsTy c)
    return mkApp2 (mkConst ``Surface.Premise.branches) c (← mkListLit ty out.toList)
  if n == ``Premise.cases && args.size == 4 then
    let c := args[0]!
    let some fs ← Solidity.listElems? args[2]! | return e
    let some us ← Solidity.listElems? args[3]! | return e
    let fs ← fs.mapM (tr ns)
    let us ← us.mapM fun U => do
      let (es, _) ← updParts ns U
      updList c U es
    return mkApp3 (mkConst ``Surface.Premise.cases) c
      (← mkListLit (mkApp (mkConst ``Solidity.NFml) c) fs.toList)
      (← mkListLit (mkApp (mkConst ``Surface.Upd) c) us.toList)
  if n == ``Premise.inv && args.size == 15 then
    let c := args[0]!
    let (es, ms) ← updParts ns args[8]!
    let ks := ms.drop (← extDepth args[12]!)
    let (ps, _) ← progPieces ks args[13]!
    return mkAppN (mkConst ``Surface.Premise.inv) #[c, ← tr ns args[5]!, ← updList c args[8]! es,
      ← tr ms args[9]!, ← tr ms args[10]!, ← Piece.build c ps, ← tr ks args[14]!]
  if n == ``Premise.inline && args.size == 6 then
    return ← mkAppM ``Surface.Premise.unfold #[← tr ns args[4]!]
  -- a lowering of a constructor: what it computes to
  if lowerFns.contains n then
    let e' ← match ← unfoldDefinition? e with
      | some e1 => whnfCore e1
      | none => pure e
    if let some c := e'.getAppFn.constName? then
      if c != n && (lowerFns.contains c || (← getEnv).isConstructor c) then return ← tr ns e'
  if let some r ← generic ns e n then return r
  -- a definition: what it computes to
  let e' ← whnf e
  if e' == e then return e
  tr ns e'

/-- A constructor, or a lowering function, as the erased one of the same
name, its explicit arguments erased. -/
partial def generic (ns : List Expr) (e : Expr) (n : Lean.Name) : TrM (Option Expr) := do
  let some n' := legacyName? (← getEnv) n | return none
  let info ← getConstInfo n
  unless info.isCtor || lowerFns.contains n do return none
  let args := e.getAppArgs
  -- the families mirror the erased ones with contexts added: drop the
  -- contexts, erase the rest in place
  let kept ← args.filterM fun a => return !(← isCtx (← inferType a))
  let arity ← forallTelescopeReducing (← getConstInfo n').type fun xs _ => pure xs.size
  if arity == kept.size then
    let kept' ← kept.mapM (trArg ns)
    let r := mkAppN (mkConst n') kept'
    if ← (try Meta.check r; pure true catch _ => pure false) then return some r
    -- a carried proof about the scoped parts (`hs : l.recvSimple = true`)
    -- does not erase; it prints as nothing, so a placeholder of the erased
    -- type stands for it
    if let some r ← withProofHoles n' kept' then return some r
  -- else by the explicit arguments, the implicit ones inferred
  let finfo ← getFunInfoNArgs e.getAppFn args.size
  let mut xs : Array Expr := #[]
  for h : i in [0:args.size] do
    let explicit := match finfo.paramInfo[i]? with
      | some p => p.binderInfo.isExplicit
      | none => true
    if explicit then xs := xs.push (← trArg ns args[i])
  -- the contract given, the explicit arguments in order, the rest inferred
  let c? ← match args[0]? with
    | some a => do
      if (← whnfR (← inferType a)).isConstOf ``Solidity.Contract then pure (some a) else pure none
    | none => pure none
  let slots ← forallTelescopeReducing (← getConstInfo n').type fun bs _ => bs.mapM fun b => do
    let d ← b.fvarId!.getDecl
    return (d.binderInfo.isExplicit, (← whnfR d.type).isConstOf ``Solidity.Contract)
  let mut out : Array (Option Expr) := #[]
  let mut j := 0
  for (ex, isC) in slots do
    if ex then
      out := out.push xs[j]?
      j := j + 1
    else if isC && out.isEmpty then out := out.push c?
    else out := out.push none
  try return some (← mkAppOptM n' out) catch _ => return none

/-- `Stmt.call f args ret body` as `Syntax.lean` writes it
(`Stmt.erase`): the arguments with their parameters, the return as
`CallRet`, a memory return's declaration at the head of the body, the body
read under the return variables and the parameters. -/
partial def callStmt? (ns : List Expr) (args : Array Expr) : TrM (Option Expr) := do
  let c := args[0]!
  let hsep := hsepPlaceholder
  -- KeY's `fbs`/`ic`: a call whose parts are schema variables, today's call
  -- of their twins (its `hsep` a placeholder: it prints as nothing)
  if let (some as, some ret, some body) := (← twin? args[7]!, ← twin? args[8]!, ← twin? args[9]!) then
    return some (mkAppN (mkConst ``Solidity.Surface.Stmt.call) #[c, args[6]!, as, hsep, ret, body])
  let some (as, pNames) ← argsList? ns args[7]! | return none
  let ret ← whnf args[8]!
  let (ret', rNames, pre) ← match ret.getAppFn.constName? with
    | some ``CallRet.none => pure (mkConst ``Surface.CallRet.none, [], #[])
    | some ``CallRet.val => do
      let r := ret.getArg! 2
      pure (mkApp3 (mkConst ``Surface.CallRet.val) (ret.getArg! 1) r (← trArg ns (ret.getArg! 3)),
        [r], #[])
    | some ``CallRet.rets => do
      let some (xs, names) ← bindersPairs? (ret.getArg! 2) | return none
      pure (mkApp (mkConst ``Surface.CallRet.rets) xs, names, #[])
    | some ``CallRet.mem => do
      let r := ret.getArg! 2
      let none' ← mkAppOptM ``Option.none
        #[some (mkApp2 (mkConst ``Surface.MRhs) c (ret.getArg! 1))]
      let d := mkAppN (mkConst ``Solidity.Surface.Stmt.declMem)
        #[c, ret.getArg! 1, r, none', ret.getArg! 3, ret.getArg! 4]
      pure (mkConst ``Surface.CallRet.none, [r], #[Piece.one d])
    | _ => return none
  let (ps, _) ← progPieces (rNames ++ pNames) args[9]!
  let body ← Piece.build c (pre ++ ps)
  let argTy := mkApp (mkConst ``Solidity.Arg) c
  return some (mkAppN (mkConst ``Solidity.Surface.Stmt.call)
    #[c, args[6]!, ← mkListLit argTy as.toList, hsep, ret', body])

/-- `try a.f(e) returns (…) { ok } catch … { … }` as `Syntax.lean` writes
it: `ok` read under the returned values, `panic` under the code. -/
partial def tryStmt? (ns : List Expr) (args : Array Expr) : TrM (Option Expr) := do
  let c := args[0]!
  let some call ← extCall? ns args[8]! | return none
  let some (rets, rNames) ← branchBinders? args[9]! | return none
  let code ← whnf args[12]!
  let (code', cNames) ← if let some x ← twin? args[12]! then pure (x, []) else
      match code.getAppFn.constName? with
      | some ``CodeBinder.none => pure (← mkAppOptM ``Option.none #[mkConst ``Solidity.Var], [])
      | some ``CodeBinder.some => pure (← mkAppM ``Option.some #[code.appArg!], [code.appArg!])
      | _ => return none
  let blk (ms : List Expr) (P : Expr) : TrM Expr := do
    let (ps, _) ← progPieces ms P
    Piece.build c ps
  return some (mkAppN (mkConst ``Solidity.Surface.Stmt.tryCall)
    #[c, call, rets, ← blk (rNames ++ ns) args[10]!, ← blk ns args[11]!, code',
      ← blk (cNames ++ ns) args[13]!, ← blk ns args[14]!])

/-- An external call, its receiver and arguments erased; a schema variable
its twin. -/
partial def extCall? (ns : List Expr) (call : Expr) : TrM (Option Expr) := do
  let call := (← instantiateMVars call).consumeMData
  if let .fvar fv := call then return (← read).twins.get? fv
  let call ← whnf call
  unless call.isAppOfArity ``ExtCall.mk 5 do return none
  let c := call.getArg! 0
  let some xs ← Solidity.listElems? (call.getArg! 4) | return none
  let β := mkLambda `p .default (mkConst ``PrimTy) (mkApp2 (mkConst ``Surface.Simple) c (mkBVar 0))
  let xs ← xs.mapM fun x => do
    let x ← whnf x
    let p := x.getArg! 2
    return mkApp4 (mkConst ``Sigma.mk [levelZero, levelZero]) (mkConst ``PrimTy) β p
      (← tr ns (x.getArg! 3))
  let argTy := mkApp (mkConst ``Surface.ExtArg) c
  return some (mkApp4 (mkConst ``Surface.ExtCall.mk) c (← tr ns (call.getArg! 2)) (call.getArg! 3)
    (← mkListLit argTy xs.toList))

/-- A call's arguments in order, each with its parameter, and the
parameters' names, innermost first (`Args.names`). -/
partial def argsList? (ns : List Expr) (as : Expr) : TrM (Option (Array Expr × List Expr)) := do
  let as ← whnf as
  if as.isAppOf ``Args.nil then return some (#[], [])
  unless as.isAppOfArity ``Args.snoc 7 do return none
  let some (xs, names) ← argsList? ns (as.getArg! 3) | return none
  let x := as.getArg! 5
  let a := mkApp4 (mkConst ``Solidity.Arg.mk) (as.getArg! 0) (as.getArg! 4) x (← tr ns (as.getArg! 6))
  return some (xs.push a, x :: names)

/-- An argument, erased by its type: a position is a name, an option of a
scoped part the option of its erasure, a scoped part its erasure, anything
else (names, types, proofs) itself. -/
partial def trArg (ns : List Expr) (a : Expr) : TrM Expr := do
  let ty ← whnfR (← inferType a)
  let .const n _ := ty.getAppFn | return a
  if n == ``Idx then return ← trIdx ns a
  if n == ``Option then
    let some inner ← legacyType? (ty.getArg! 0) | return a
    let a' ← whnf a
    if a'.isAppOf ``Option.some then return ← mkAppM ``Option.some #[← trArg ns a'.appArg!]
    return ← mkAppOptM ``Option.none #[some inner]
  if isScopedFamily (← getEnv) n then return ← tr ns a
  return a

/-- The pieces of a block, and the names it leaves. -/
partial def progPieces (ns : List Expr) (P : Expr) : TrM (Array Piece × List Expr) := do
  let P := (← instantiateMVars P).consumeMData
  if let .fvar fv := P then return (#[.many ((← read).twins.getD fv P)], ns)
  -- a block read under one local more (`Prog.up`): itself
  if let some n := P.getAppFn.constName? then
    if isUp n && P.getAppNumArgs > 0 && P.appArg!.isFVar then return ← progPieces ns P.appArg!
  -- a block read under one local more (`Prog.up`, unfolded): the block
  if let some P' := wkUp? P then return ((← progPieces ns.tail P').1, ns)
  let P ← whnf P
  if let some P' := wkUp? P then return ((← progPieces ns.tail P').1, ns)
  if P.isAppOf ``Prog.cons then
    let args := P.getAppArgs
    let s := args[4]!
    let (ss, ms) ← stmtPieces ns s
    let (rest, ms) ← progPieces ms args[5]!
    return (ss ++ rest, ms)
  if P.isAppOf ``Prog.nil then return (#[], ns)
  return (#[.many P], ns)

/-- A statement's pieces (a block's statements, spliced) and the names it
leaves. -/
partial def stmtPieces (ns : List Expr) (s : Expr) : TrM (Array Piece × List Expr) := do
  let s := (← instantiateMVars s).consumeMData
  if let .fvar fv := s then return (#[.one ((← read).twins.getD fv s)], ns)
  -- a hole filled declares nothing; read before `whnf` unfolds its `fill`
  if holeFills.any (s.isAppOf ·.1) then return (#[.one (← tr ns s)], ns)
  let s ← whnf s
  if s.isAppOf ``Stmt.block then
    let (ps, _) ← progPieces ns s.appArg!
    return (ps, ns)
  if s.isAppOf ``Stmt.call || s.isAppOf ``Stmt.tryCall then
    if let some P ← closedErase? ns s then return (#[.many P], ← stmtOutNames ns s)
  return (#[.one (← tr ns s)], ← stmtOutNames ns s)

/-- A closed call or `try` (a formula's, no schema variable in it, its
context's names known) erased by `Stmt.erase` itself, run as compiled
code, and quoted back: the callee's body is closed over its own frame, which
`tr`'s names do not reach. -/
partial def closedErase? (ns : List Expr) (s : Expr) : TrM (Option Expr) := do
  if s.hasFVar || s.hasMVar || ns.any (fun n => n.hasFVar || n.hasMVar) then return none
  let c ← contractOf s
  if c.hasFVar || c.hasMVar then return none
  let e ← mkAppM ``Stmt.erase #[← mkListLit (mkConst ``Solidity.Var) ns, s]
  try
    -- the contract is a phantom of the erased syntax: the value's
    -- representation does not depend on it
    let P ← unsafe evalExpr (List (Solidity.Surface.Stmt Solidity.StandardExample)) (← inferType e) e
    return some (Solidity.Surface.Prog.quote c P)
  catch _ => return none

/-- The statements frames hold, `}` where a block ends when `blockEnd` is
set, and the names of the postcondition's context. -/
partial def framePieces (ns : List Expr) (κ : Expr) : TrM (Array Piece × List Expr) := do
  let κ := (← instantiateMVars κ).consumeMData
  if let .fvar fv := κ then return (#[.many ((← read).twins.getD fv κ)], ns)
  let κ ← whnf κ
  let args := κ.getAppArgs
  if κ.isAppOf ``Frames.seq then
    let (ps, ms) ← progPieces ns args[4]!
    let (qs, ms) ← framePieces ms args[5]!
    return (ps ++ qs, ms)
  if κ.isAppOf ``Frames.pop then
    let b ← whnf args[4]!
    let d ← extDepth args[5]!
    let (qs, ms) ← framePieces (ns.drop d) args[6]!
    let close := b.isConstOf ``BlockKind.block
    match (← read).blockEnd, close with
    | some e, true => return (#[.one e] ++ qs, ms)
    | _, _ => return (qs, ms)
  if κ.isAppOf ``Frames.drop then
    return ← framePieces (← thinNames ns args[4]!) args[5]!
  if κ.isAppOf ``Frames.nil then return (#[], ns)
  return (#[.many κ], ns)

/-- An update's pieces, erased, and the names of the context it leaves:
right-hand sides read at `ns`, targets at the names its declarations push;
a pop is nothing.  A schema variable is its twin, spliced in front; any
other blocked update is itself, and prints as `‹…›`. -/
partial def updParts (ns : List Expr) (U : Expr) : TrM (Array Piece × List Expr) := do
  let U ← whnf (← instantiateMVars U)
  let args := U.getAppArgs
  if U.isAppOf ``Upd.snoc then
    let (es, ms) ← updParts ns args[3]!
    return (es.push (.one (← elem ns ms args[4]!)), ms)
  if U.isAppOf ``Upd.decl then
    let (es, ms) ← updParts ns args[4]!
    let x := args[5]!
    return (es.push (.one (← rhs ns x args[6]!)), x :: ms)
  if U.isAppOf ``Upd.pop then
    let (es, ms) ← updParts ns args[4]!
    return (es, ms.drop (← extDepth args[5]!))
  if U.isAppOf ``Upd.drop then
    let (es, ms) ← updParts ns args[4]!
    return (es, ← thinNames ms args[5]!)
  if U.isAppOf ``Upd.nil then return (#[], ns)
  if let .fvar fv := U then return (#[.many ((← read).twins.getD fv U)], ns)
  return (#[.many U], ns)

/-- An assigning element: a local's by its right-hand side, the rest as the
erased element of the same name. -/
partial def elem (ns ms : List Expr) (e : Expr) : TrM Expr := do
  let e ← whnf (← instantiateMVars e)
  if e.isAppOf ``UpdElem.local then
    let args := e.getAppArgs
    return ← rhs ns (← trIdx ms args[4]!) args[5]!
  match ← generic ns e (e.getAppFn.constName?.getD Lean.Name.anonymous) with
  | some r => return r
  | none => return e

/-- `x := r`, the element of `r`'s kind. -/
partial def rhs (ns : List Expr) (x r : Expr) : TrM Expr := do
  let r ← whnf (← instantiateMVars r)
  let args := r.getAppArgs
  match r.getAppFn.constName? with
  | some ``Rhs.val => mkAppM ``Surface.UpdElem.val #[x, ← tr ns args.back!]
  | some ``Rhs.path => mkAppM ``Surface.UpdElem.path #[x, ← tr ns args.back!]
  | some ``Rhs.unset => return mkApp2 (mkConst ``Surface.UpdElem.unset) (← contractOf r) x
  | some ``Rhs.mref => mkAppM ``Surface.UpdElem.mref #[x, ← tr ns args.back!]
  | some ``Rhs.store => mkAppM ``Surface.UpdElem.store #[x, ← tr ns args.back!]
  | some ``Rhs.saveNet => return mkApp2 (mkConst ``Surface.UpdElem.saveNet) (← contractOf r) x
  | some ``Rhs.saveNetMt => return mkApp2 (mkConst ``Surface.UpdElem.saveNetMt) (← contractOf r) x
  | _ => return r

/-- The erased update of the pieces `es`, of the contract `c`: `u ++ [e, …]`;
the scoped update `U` itself (`‹…›`) when it is blocked on a term that is no
schema variable. -/
partial def updList (c U : Expr) (es : Array Piece) : TrM Expr := do
  if es.any (fun | .many P => !P.isFVar | .one _ => false) then return U
  Piece.buildOf (mkApp (mkConst ``Surface.UpdElem) c) es

end

/-! ## Running it -/

/-- The name of the local a block's end prints as, before `fixBlockEnds`
turns it into `}`. -/
def blockEndName : Lean.Name := `core_block_end

/-- The twins of the variables `fvs` from the `i`-th on, then `k`. -/
partial def twinsFrom {α : Type} (fvs : Array FVarId) (i : Nat) (env : Env) (k : Env → MetaM α) :
    MetaM α := do
  let some fv := fvs[i]? | k env
  match ← legacyType? (← fv.getDecl).type env.schema with
  | some ty => withLocalDeclD (← fv.getDecl).userName ty fun x =>
      twinsFrom fvs (i + 1) { env with twins := env.twins.insert fv x } k
  | none => twinsFrom fvs (i + 1) env k

/-- `k` with a twin for every free variable of `e` of a scoped type, and,
when `frames`, the statement `}` prints as; `schema` for a rule's schema
variables (`Env.schema`). -/
def withTwins {α : Type} (e : Expr) (frames : Bool) (k : Env → MetaM α)
    (contract? : Option Expr := none) (schema : Bool := false) : MetaM α := do
  let e ← instantiateMVars e
  let fvs := (collectFVars {} e).fvarIds
  if !frames then return ← twinsFrom fvs 0 { schema } k
  -- the contract, for the type of the `}` statement
  let c? ← match contract? with
    | some c => pure (some c)
    | none => try some <$> contractOf e catch _ => pure none
  match c? with
  | some c => withLocalDeclD blockEndName (mkApp (mkConst ``Solidity.Surface.Stmt) c) fun b =>
      twinsFrom fvs 0 { blockEnd := some b } k
  | none => twinsFrom fvs 0 {} k

/-- The erasure of `e`, run with its twins, then `k` on it. -/
def withErased {α : Type} (e : Expr) (frames : Bool) (k : Expr → MetaM α) : MetaM α :=
  withTwins e frames fun env => do k (← (tr [] e).run env)

end Delab

end Solidity
