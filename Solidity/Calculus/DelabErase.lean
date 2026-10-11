import Solidity.Calculus.Rules
import Solidity.Calculus.RuleKit

/-!
# A scoped term's erasure, with its schema variables

The `Expr` of a scoped term, update or formula with no modality, its schema
variables free, translated to the `Expr` of its erasure, the `Update.lean`
term that `Fml.erase` would compute (`Delab.tr`, run under
`Delab.withTwins`), which `RuleSyntax.lean`'s term printers print.  The
printers no longer read it (W9.1 `print`: `Calculus/PrintTerm.lean` prints
the scoped terms themselves); it stays for the twin check
(`pp.sol.twinCheck`, `Calculus/PrintStmt.lean`) and for the SolKey reader,
which W9.5 ports.

* **Schema variables** get twins: each free variable of a scoped term type
  (`t : Tm C Γ .val`, `U : Upd C Γ Δ`) stands, for the printer, as a local
  of the erased type with the same name (`t : Term C`, `U : Surface.Upd C`).
  A program schema variable lowered to a term (`se.lower`, `sp.lower`) is
  the local of its name (`loweredVar?`): `se`.
* **Positions** are names: `.here` is the innermost local the term itself
  declared (`{ x := … }`, `∀`), and `.there` steps past one; a schema
  variable under any number of `.there` or `up` is itself, so a rule's
  weakenings (`v.there`, `Val.up e`) print as the rule line writes them.
* **What erasure loses is invisible**: a pop of an update and the hidden
  binder print as nothing.

It imports the scoped rule table and `RuleKit` only, below the
delaborators, the sequent and the strategy, so a reader of the rule table
can erase a term without them (decision 53).
-/

namespace Solidity

open Lean Meta

namespace Delab

/-! ## The erased types -/

/-- The erased twins `Solidity.X` may have, in order: a formula ↦ the
closer's (`Solidity.NFml`), any other family ↦ its twin of the closer's
terms (`Solidity.Surface.X`: `Tm`, `Upd`, `UpdElem`) or the closer's
(`Solidity.NFml.X`). -/
def legacyNames (n : Lean.Name) : List Lean.Name :=
  if (`Solidity.Fml).isPrefixOf n then
    [n.replacePrefix `Solidity.Fml `Solidity.NFml]
  else if (`Solidity).isPrefixOf n then
    let x := n.replacePrefix `Solidity .anonymous
    [`Solidity.Surface ++ x, `Solidity.NFml ++ x]
  else []

/-- The first erased twin of `n` that `env` declares. -/
def legacyName? (env : Environment) (n : Lean.Name) : Option Lean.Name :=
  (legacyNames n).find? env.contains

/-- Whether `n` names a scoped family whose values `tr` erases: one with an
erased twin, or a position (`Idx`). -/
def isScopedFamily (env : Environment) (n : Lean.Name) : Bool :=
  (legacyName? env n).isSome || n == ``Idx

/-- Whether `ty` is a context. -/
def isCtx (ty : Expr) : MetaM Bool := do
  let ty ← whnfR ty
  return ty.isAppOfArity ``List 1 && (ty.getArg! 0).isConstOf ``LTy

/-- The erased type of a scoped one: `Idx Γ t` is `Var`, any other family
`F C Γ x̄` with a twin the twin, its contexts dropped. -/
def legacyType? (ty : Expr) : MetaM (Option Expr) := do
  let ty ← whnfR (← instantiateMVars ty)
  let .const n _ := ty.getAppFn | return none
  let args := ty.getAppArgs
  if n == ``Idx then return some (mkConst ``Solidity.Var)
  let some n' := legacyName? (← getEnv) n | return none
  let keep ← args.filterM fun a => return !(← isCtx (← inferType a))
  let t := mkAppN (mkConst n') keep
  try
    let s ← inferType t
    unless (← whnf s).isSort do return none
    return some t
  catch _ => return none

/-! ## The translation -/

/-- The twins of the schema variables. -/
structure Env where
  twins : Std.HashMap FVarId Expr := {}

abbrev TrM := ReaderT Env MetaM

/-- A position that is no local the term declared. -/
def unknownVar : Expr := mkApp (mkConst ``Solidity.Var.user) (toExpr "_")

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

/-- The lowering functions (`Calculus/Lower.lean`). -/
def lowerFns : List Lean.Name :=
  [``Simple.lower, ``SPath.lower, ``Loc.lower, ``MPath.lower, ``MLoc.lower, ``Val.lower,
    ``Src.lower, ``MSrc.lower, ``Simple.keyLower, ``Val.keyLower]

/-- A part of the program or a term, read with one local more on top:
`Val.up` and its kin (the one other `Solidity` name ending in `up` is a
theorem, `Wrote.up`, which no term heads). -/
def isUp (n : Lean.Name) : Bool := (`Solidity).isPrefixOf n && n.getString! == "up"

/-- A part under any number of `up`s: the part itself. -/
partial def stripUps (e : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e).consumeMData
  match e.getAppFn.constName? with
  | some n => if isUp n && e.getAppNumArgs > 0 then stripUps e.appArg! else return e
  | none => return e

/-- A program schema variable `x` lowered to a term (`Simple.lower x`, read
under any number of `up`s), erased: the local of its name at the lowered
sort, `x` (`Term.pv`, `PTerm.pv`, `ITerm.pv`), which prints as the rule line
writes it; a key's (`keyLower`) the same.  None for any other part. -/
def loweredVar? (n : Lean.Name) (args : Array Expr) : MetaM (Option Expr) := do
  let x ← stripUps args.back!
  let .fvar fv := x | return none
  let some c := args[0]? | return none
  let v := mkApp (mkConst ``Solidity.Var.user) (mkStrLit (← fv.getUserName).eraseMacroScopes.toString)
  let tm := mkApp2 (mkConst ``Solidity.Term.pv) c v
  if n == ``Simple.lower || n == ``Val.lower || n == ``Simple.keyLower || n == ``Val.keyLower then
    return some tm
  if n == ``SPath.lower || n == ``Loc.lower then return some (mkApp2 (mkConst ``Solidity.PTerm.pv) c v)
  if n == ``MPath.lower then return some (mkApp2 (mkConst ``Solidity.ITerm.pv) c v)
  if n == ``Src.lower then return some (mkApp2 (mkConst ``Solidity.SValT.val) c tm)
  if n == ``MSrc.lower then return some (mkApp2 (mkConst ``Solidity.MValT.val) c tm)
  return none

/-- A piece of an update: one element, or an update variable spliced in. -/
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

mutual

/-- The erasure of a scoped term `e`, read where the term declared the
locals `ns` (innermost first).  What it does not know stays as it is, and
prints as `‹…›`. -/
partial def tr (ns : List Expr) (e : Expr) : TrM Expr := do
  let e := (← instantiateMVars e).consumeMData
  if let .fvar fv := e then return (← read).twins.getD fv e
  let .const n _ := e.getAppFn | return e
  let args := e.getAppArgs
  if isUp n && args.size > 0 then return ← tr ns.tail args.back!
  if n == ``Tm.netOf && args.size == 4 then
    return ← mkAppM ``Surface.Tm.app1
      #[mkApp (mkConst ``Solidity.Op1.netOf) (← trIdx ns args[2]!), ← tr ns args[3]!]
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
    return mkApp4 (mkConst ``Solidity.NFml.upd) args[0]! args[3]! (← updList args[0]! args[4]! es) φ
  if n == ``Fml.all && args.size == 5 then
    -- an explicit `∀`'s mark (`Fml.markExplicit`) prints as nothing
    let x := args[2]!.consumeMData
    return ← mkAppM ``Solidity.NFml.all #[x, args[3]!, ← tr (x :: ns) args[4]!]
  if n == ``Fml.bind && args.size == 6 then return ← tr (args[3]! :: ns) args[5]!
  if n == ``Fml.anon && args.size == 4 then
    let some xs ← Solidity.listElems? args[2]! | return e
    let xs ← xs.mapM fun x => do
      let x ← whnf x
      trIdx ns x.appArg!
    let xs ← mkListLit (mkConst ``Solidity.Var) xs.toList
    return ← mkAppM ``Solidity.NFml.anon #[xs, ← tr ns args[3]!]
  -- a lowering: of a schema variable, the local of its name; of a
  -- constructor, what it computes to
  if lowerFns.contains n && args.size > 0 then
    if let some r ← loweredVar? n args then return r
    let e' ← match ← unfoldDefinition? e with
      | some e1 => whnfCore e1
      | none => pure e
    if let some c := e'.getAppFn.constName? then
      if c != n && (lowerFns.contains c || (← getEnv).isConstructor c) then return ← tr ns e'
  -- a postcondition `↑φ`: the closer's `↑φ'` of its twin `φ' : NFml.Post C`,
  -- else, for a local `φ`, the coercion itself; `ppFml` prints either as `φ`
  -- (unfolded, it would be the projection `φ.1`).  A defined postcondition
  -- computes, as below.
  if n == `Solidity.Post.fml && args.size == 3 then
    let p ← tr ns args[2]!
    if p == args[2]! then
      if p.getAppFn.isFVar then return e
    else if ← (try return (← whnfR (← inferType p)).isAppOf `Solidity.NFml.Post
        catch _ => return false) then
      return mkApp2 (mkConst `Solidity.NFml.Post.fml) args[0]! p
  if let some r ← generic ns e n then return r
  -- a definition: what it computes to
  let e' ← whnf e
  if e' == e then return e
  tr ns e'

/-- A constructor as the erased one of the same name, its explicit arguments
erased. -/
partial def generic (ns : List Expr) (e : Expr) (n : Lean.Name) : TrM (Option Expr) := do
  let some n' := legacyName? (← getEnv) n | return none
  let info ← getConstInfo n
  unless info.isCtor do return none
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
  match ← legacyType? (← fv.getDecl).type with
  | some ty => withLocalDeclD (← fv.getDecl).userName ty fun x =>
      twinsFrom fvs (i + 1) { env with twins := env.twins.insert fv x } k
  | none => twinsFrom fvs (i + 1) env k

/-- `k` with a twin for every free variable of `e` of a scoped term type. -/
def withTwins {α : Type} (e : Expr) (k : Env → MetaM α) : MetaM α := do
  let e ← instantiateMVars e
  twinsFrom (collectFVars {} e).fvarIds 0 {} k

end Delab

end Solidity
