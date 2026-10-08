import Solidity.Calculus.Core.Taclet
import Solidity.Calculus.Core.Proves

/-!
# Printing scoped taclets and formulas with schema variables

`Calculus/Core/Print.lean` prints a closed formula (`Core.Fml.show`, a value
in `MetaM`).  A taclet is not closed: its schema variables are free (`v`,
`se`, `thenStm`), so it is printed from its `Expr`, as `Rules.lean`'s
delaborators print today's taclets.  This module translates the `Expr` of a
scoped statement, premise or formula into the `Expr` of its erasure, the
`Update.lean`/`Syntax.lean` term that `Fml.erase` would compute, and prints
that with `RuleSyntax.lean`'s printers (`ppStmt`, `ppPremise?`, `ppFml`):
the same KeY text, with no second printer to keep in step.

* **Schema variables** get twins: each free variable of a scoped type
  (`v : Idx Γ (.val p)`, `se : Simple C Γ p`, `thenStm : Prog C Γ Γ₁`)
  stands, for the printer, as a local of the erased type with the same name
  (`v : Var`, `se : Simple C p`, `thenStm : Prog C`).
* **Positions** are names: `.here` is the innermost local the term itself
  declared (`T storage sp = nsp;`, `Premise.bind`, `{ x := … }`, `∀`), and
  `.there` steps past one; a schema variable under any number of `.there`
  or `up` is itself, so a rule's weakenings (`v.there`, `Val.up e`) print as
  the rule line writes them.
* **What erasure loses is invisible**, as `Core.Fml.show` has it: a
  capture's scope end, a pop of an update and the hidden binder print as
  nothing; the end of a block in a formula's frames prints `}`
  (`core_item`, below), the one piece of text today's grammar has no
  production for.

The delaborators: `Core.Taclet C k m s p` as `dl{ ⟨[ s; ]⟩ ⇝ p }` (with
solkey's branch labels), a premise as `dl{ p }`, a formula as `dl{ φ }`; a
taclet's side conditions and carried proofs stay out of sight, as
`delabTacletSide` does for today's.
-/

namespace Solidity.Core

open Lean Meta PrettyPrinter Delaborator SubExpr
open Solidity (ppStmt ppPremise? ppFml ppOn isEscape fullApp)

/-! ## A block's end in a formula

Printing only: no macro reads it.  A modality's program with a `}` in it is
written with at least one `}`, so a program without one parses as today's
production alone. -/

/-- An item of a modality's program: a statement, or a block's end. -/
declare_syntax_cat core_item
syntax sol_stmt "; " : core_item
syntax "} " : core_item

/-- `⟨ s; … } ω ⟩ φ`: the program runs into the end of a block. -/
syntax:max "⟨ " (sol_stmt "; ")* "} " core_item* "⟩ " dl_fml:50 : dl_fml
/-- `[ s; … } ω ] φ` -/
syntax:max "[ " (sol_stmt "; ")* "} " core_item* "] " dl_fml:50 : dl_fml

namespace Delab

/-! ## The erased types -/

/-- `Solidity.Core.X` ↦ `Solidity.X`. -/
def legacyName? (n : Lean.Name) : Option Lean.Name :=
  if (`Solidity.Core).isPrefixOf n then some (n.replacePrefix `Solidity.Core `Solidity) else none

/-- Whether `ty` is a context. -/
def isCtx (ty : Expr) : MetaM Bool := do
  let ty ← whnfR ty
  return ty.isAppOfArity ``List 1 && (ty.getArg! 0).isConstOf ``LTy

/-- The erased type of a scoped one: `Idx Γ t` is `Var`, a block or frames
`Prog C`, any other family `F C Γ x̄` the family of the same name, its
contexts dropped. -/
def legacyType? (ty : Expr) : MetaM (Option Expr) := do
  let ty ← whnfR (← instantiateMVars ty)
  let .const n _ := ty.getAppFn | return none
  let args := ty.getAppArgs
  if n == ``Idx then return some (mkConst ``Solidity.Var)
  if n == ``Prog || n == ``Frames then return some (mkApp (mkConst ``Solidity.Prog) args[0]!)
  let some n' := legacyName? n | return none
  unless (← getEnv).contains n' do return none
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

/-- The lowering functions, whose erasure is the function of the same
name (`Core/Lower.lean`'s `lower_erase`). -/
def lowerFns : List Lean.Name :=
  [``Simple.lower, ``SPath.lower, ``Loc.lower, ``MPath.lower, ``MLoc.lower, ``Val.lower,
    ``Src.lower, ``MSrc.lower, ``Simple.keyLower, ``Val.keyLower]

/-- A part of the program or a term, read with one local more on top:
`Val.up` and its kin. -/
def isUp (n : Lean.Name) : Bool := (`Solidity.Core).isPrefixOf n && n.getString! == "up"

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
  Piece.buildOf (mkApp (mkConst ``Solidity.Stmt) c) ps

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
def stmtsTy (c : Expr) : Expr := mkApp (mkConst ``List [levelZero]) (mkApp (mkConst ``Solidity.Stmt) c)

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
  if n == ``Prog.nil || n == ``Prog.cons then
    let (ps, _) ← progPieces ns e
    return ← Piece.build (← contractOf e) ps
  if n == ``Stmt.block then
    let (ps, _) ← progPieces ns args.back!
    return ← Piece.build (← contractOf e) ps
  if n == ``Tm.netOf && args.size == 4 then
    return ← mkAppM ``Solidity.Tm.app1
      #[mkApp (mkConst ``Solidity.Op1.netOf) (← trIdx ns args[2]!), ← tr ns args[3]!]
  if n == ``Tm.app1 && args.size == 7 then
    return ← mkAppM ``Solidity.Tm.app1 #[args[4]!, ← tr ns args[6]!]
  if n == ``Fml.upd && args.size == 6 then
    let (es, ms) ← updParts ns args[4]!
    let φ ← tr ms args[5]!
    if es.isEmpty then return φ
    -- built unchecked: a stuck update stays scoped, and prints as `‹…›`
    return mkApp4 (mkConst ``Solidity.Fml.upd) args[0]! args[3]! (← updList args[0]! args[4]! es) φ
  if n == ``Fml.modal && args.size == 8 then
    let (ps, ms) ← progPieces ns args[5]!
    let (qs, ms) ← framePieces ms args[6]!
    let P ← Piece.build args[0]! (ps ++ qs)
    return ← mkAppM ``Solidity.Fml.modal #[args[4]!, P, ← tr ms args[7]!]
  if n == ``Fml.all && args.size == 5 then
    -- an explicit `∀`'s mark (`Fml.markExplicit`) prints as nothing
    let x := args[2]!.consumeMData
    return ← mkAppM ``Solidity.Fml.all #[x, args[3]!, ← tr (x :: ns) args[4]!]
  if n == ``Fml.bind && args.size == 6 then return ← tr (args[3]! :: ns) args[5]!
  if n == ``Fml.anon && args.size == 4 then
    let some xs ← Solidity.listElems? args[2]! | return e
    let xs ← xs.mapM fun x => do
      let x ← whnf x
      trIdx ns x.appArg!
    return ← mkAppM ``Solidity.Fml.anon
      #[← mkListLit (mkConst ``Solidity.Var) xs.toList, ← tr ns args[3]!]
  if n == ``Premise.update && args.size == 4 then
    let (es, _) ← updParts ns args[3]!
    return mkApp2 (mkConst ``Solidity.Premise.update) args[0]! (← updList args[0]! args[3]! es)
  if n == ``Premise.unfold && args.size == 6 then
    return ← mkAppM ``Solidity.Premise.unfold #[← tr ns args[4]!]
  if n == ``Premise.bind && args.size == 6 then
    return ← mkAppM ``Solidity.Premise.unfold #[← tr (args[3]! :: ns) args[5]!]
  if n == ``Premise.split && args.size == 9 then
    return ← mkAppM ``Solidity.Premise.split
      #[← tr ns args[5]!, ← tr ns args[6]!, ← tr ns args[7]!, ← tr ns args[8]!]
  if n == ``Premise.check && args.size == 3 then
    let nil ← mkListLit (mkApp (mkConst ``Solidity.Stmt) args[0]!) []
    return ← mkAppM ``Solidity.Premise.check #[← tr ns args[2]!, nil]
  if n == ``Premise.done && args.size == 4 then
    return mkApp2 (mkConst ``Solidity.Premise.done) args[0]! args[3]!
  if n == ``Stmt.call && args.size == 10 then
    if let some r ← callStmt? ns args then return r
  if n == ``Stmt.tryCall && args.size == 15 then
    if let some r ← tryStmt? ns args then return r
  if n == ``Premise.branches && args.size == 3 then
    let some bs ← Solidity.listElems? args[2]! | return e
    let c := args[0]!
    let mut out : Array Expr := #[]
    for b in bs do
      let b ← whnf b
      unless b.isAppOfArity ``Branch.mk 6 do return e
      let some (xs, names) ← bindersPairs? (b.getArg! 4) | return e
      let (ps, _) ← progPieces (names ++ ns) (b.getArg! 5)
      out := out.push (← mkAppM ``Prod.mk #[xs, ← Piece.build c ps])
    let ty := mkApp2 (mkConst ``Prod [levelZero, levelZero]) (pairsTy) (stmtsTy c)
    return mkApp2 (mkConst ``Solidity.Premise.branches) c (← mkListLit ty out.toList)
  if n == ``Premise.cases && args.size == 4 then
    let c := args[0]!
    let some fs ← Solidity.listElems? args[2]! | return e
    let some us ← Solidity.listElems? args[3]! | return e
    let fs ← fs.mapM (tr ns)
    let us ← us.mapM fun U => do
      let (es, _) ← updParts ns U
      updList c U es
    return mkApp3 (mkConst ``Solidity.Premise.cases) c
      (← mkListLit (mkApp (mkConst ``Solidity.Fml) c) fs.toList)
      (← mkListLit (mkApp (mkConst ``Solidity.Upd) c) us.toList)
  if n == ``Premise.inv && args.size == 15 then
    let c := args[0]!
    let (es, ms) ← updParts ns args[8]!
    let ks := ms.drop (← extDepth args[12]!)
    let (ps, _) ← progPieces ks args[13]!
    return mkAppN (mkConst ``Solidity.Premise.inv) #[c, ← tr ns args[5]!, ← updList c args[8]! es,
      ← tr ms args[9]!, ← tr ms args[10]!, ← Piece.build c ps, ← tr ks args[14]!]
  if n == ``Premise.inline && args.size == 6 then
    return ← mkAppM ``Solidity.Premise.unfold #[← tr ns args[4]!]
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
  let some n' := legacyName? n | return none
  unless (← getEnv).contains n' do return none
  let info ← getConstInfo n
  unless info.isCtor || lowerFns.contains n do return none
  let args := e.getAppArgs
  -- the families mirror the erased ones with contexts added: drop the
  -- contexts, erase the rest in place
  let kept ← args.filterM fun a => return !(← isCtx (← inferType a))
  let arity ← forallTelescopeReducing (← getConstInfo n').type fun xs _ => pure xs.size
  if arity == kept.size then
    let r := mkAppN (mkConst n') (← kept.mapM (trArg ns))
    if ← (try Meta.check r; pure true catch _ => pure false) then return some r
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
(`Core.Stmt.erase`): the arguments with their parameters, the return as
`CallRet`, a memory return's declaration at the head of the body, the body
read under the return variables and the parameters. -/
partial def callStmt? (ns : List Expr) (args : Array Expr) : TrM (Option Expr) := do
  let c := args[0]!
  let some (as, pNames) ← argsList? ns args[7]! | return none
  let ret ← whnf args[8]!
  let (ret', rNames, pre) ← match ret.getAppFn.constName? with
    | some ``CallRet.none => pure (mkConst ``Solidity.CallRet.none, [], #[])
    | some ``CallRet.val => do
      let r := ret.getArg! 2
      pure (mkApp3 (mkConst ``Solidity.CallRet.val) (ret.getArg! 1) r (← trArg ns (ret.getArg! 3)),
        [r], #[])
    | some ``CallRet.rets => do
      let some (xs, names) ← bindersPairs? (ret.getArg! 2) | return none
      pure (mkApp (mkConst ``Solidity.CallRet.rets) xs, names, #[])
    | some ``CallRet.mem => do
      let r := ret.getArg! 2
      let none' ← mkAppOptM ``Option.none
        #[some (mkApp2 (mkConst ``Solidity.MRhs) c (ret.getArg! 1))]
      let d := mkAppN (mkConst ``Solidity.Stmt.declMem)
        #[c, ret.getArg! 1, r, none', ret.getArg! 3, ret.getArg! 4]
      pure (mkConst ``Solidity.CallRet.none, [r], #[Piece.one d])
    | _ => return none
  let (ps, _) ← progPieces (rNames ++ pNames) args[9]!
  let body ← Piece.build c (pre ++ ps)
  let hsep := mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst ``Bool.true)
  let argTy := mkApp (mkConst ``Solidity.Arg) c
  return some (mkAppN (mkConst ``Solidity.Stmt.call)
    #[c, args[6]!, ← mkListLit argTy as.toList, hsep, ret', body])

/-- `try a.f(e) returns (…) { ok } catch … { … }` as `Syntax.lean` writes
it: `ok` read under the returned values, `panic` under the code. -/
partial def tryStmt? (ns : List Expr) (args : Array Expr) : TrM (Option Expr) := do
  let c := args[0]!
  let some call ← extCall? ns args[8]! | return none
  let some (rets, rNames) ← bindersPairs? args[9]! | return none
  let code ← whnf args[12]!
  let (code', cNames) ← match code.getAppFn.constName? with
    | some ``CodeBinder.none => pure (← mkAppOptM ``Option.none #[mkConst ``Solidity.Var], [])
    | some ``CodeBinder.some => pure (← mkAppM ``Option.some #[code.appArg!], [code.appArg!])
    | _ => return none
  let blk (ms : List Expr) (P : Expr) : TrM Expr := do
    let (ps, _) ← progPieces ms P
    Piece.build c ps
  return some (mkAppN (mkConst ``Solidity.Stmt.tryCall)
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
  let β := mkLambda `p .default (mkConst ``PrimTy) (mkApp2 (mkConst ``Solidity.Simple) c (mkBVar 0))
  let xs ← xs.mapM fun x => do
    let x ← whnf x
    let p := x.getArg! 2
    return mkApp4 (mkConst ``Sigma.mk [levelZero, levelZero]) (mkConst ``PrimTy) β p
      (← tr ns (x.getArg! 3))
  let argTy := mkApp (mkConst ``Solidity.ExtArg) c
  return some (mkApp4 (mkConst ``Solidity.ExtCall.mk) c (← tr ns (call.getArg! 2)) (call.getArg! 3)
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
  if (`Solidity.Core).isPrefixOf n then return ← tr ns a
  return a

/-- The pieces of a block, and the names it leaves. -/
partial def progPieces (ns : List Expr) (P : Expr) : TrM (Array Piece × List Expr) := do
  let P := (← instantiateMVars P).consumeMData
  if let .fvar fv := P then return (#[.many ((← read).twins.getD fv P)], ns)
  let P ← whnf P
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
    let P ← unsafe evalExpr (List (Solidity.Stmt Solidity.StandardExample)) (← inferType e) e
    return some (Solidity.Prog.quote c P)
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
other stuck update is itself, and prints as `‹…›`. -/
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
  | some ``Rhs.val => mkAppM ``Solidity.UpdElem.val #[x, ← tr ns args.back!]
  | some ``Rhs.path => mkAppM ``Solidity.UpdElem.path #[x, ← tr ns args.back!]
  | some ``Rhs.unset => return mkApp2 (mkConst ``Solidity.UpdElem.unset) (← contractOf r) x
  | some ``Rhs.mref => mkAppM ``Solidity.UpdElem.mref #[x, ← tr ns args.back!]
  | some ``Rhs.store => mkAppM ``Solidity.UpdElem.store #[x, ← tr ns args.back!]
  | some ``Rhs.saveNet => return mkApp2 (mkConst ``Solidity.UpdElem.saveNet) (← contractOf r) x
  | some ``Rhs.saveNetMt => return mkApp2 (mkConst ``Solidity.UpdElem.saveNetMt) (← contractOf r) x
  | _ => return r

/-- The erased update of the pieces `es`, of the contract `c`: `u ++ [e, …]`;
the scoped update `U` itself (`‹…›`) when it is stuck on a term that is no
schema variable. -/
partial def updList (c U : Expr) (es : Array Piece) : TrM Expr := do
  if es.any (fun | .many P => !P.isFVar | .one _ => false) then return U
  Piece.buildOf (mkApp (mkConst ``Solidity.UpdElem) c) es

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

/-- `k` with a twin for every free variable of `e` of a scoped type, and,
when `frames`, the statement `}` prints as. -/
def withTwins {α : Type} (e : Expr) (frames : Bool) (k : Env → MetaM α)
    (contract? : Option Expr := none) : MetaM α := do
  let e ← instantiateMVars e
  let fvs := (collectFVars {} e).fvarIds
  if !frames then return ← twinsFrom fvs 0 {} k
  -- the contract, for the type of the `}` statement
  let c? ← match contract? with
    | some c => pure (some c)
    | none => try some <$> contractOf e catch _ => pure none
  match c? with
  | some c => withLocalDeclD blockEndName (mkApp (mkConst ``Solidity.Stmt) c) fun b =>
      twinsFrom fvs 0 { blockEnd := some b } k
  | none => twinsFrom fvs 0 {} k

/-- The erasure of `e`, run with its twins, then `k` on it. -/
def withErased {α : Type} (e : Expr) (frames : Bool) (k : Expr → MetaM α) : MetaM α :=
  withTwins e frames fun env => do k (← (tr [] e).run env)

/-! ## Printing -/

/-- The statements of a modality's item list, if it is one: `(s ";")*`. -/
def stmtItems (stx : Syntax) : Array Syntax :=
  stx.getArgs.flatMap fun g =>
    if g.isAtom then #[]
    else if g.getKind == groupKind || g.isOfKind nullKind then #[g[0]] else #[g]

/-- Whether a printed statement is a block's end. -/
def isBlockEnd (s : Syntax) : Bool :=
  let x := if s.isIdent then s else s[0]
  x.isIdent && x.getId == blockEndName

/-- `⟨ … ⟩ φ` and `[ … ] φ` with a block's end among its statements, in the
grammar above (`}` without its `;`). -/
partial def fixBlockEnds (stx : Syntax) : MetaM Syntax := do
  let .node info k args := stx | return stx
  let args ← args.mapM fixBlockEnds
  let stx := Syntax.node info k args
  unless args.size == 4 && (args[0]!.isToken "⟨" || args[0]!.isToken "[") do return stx
  let ss := stmtItems args[1]!
  unless ss.any isBlockEnd do return stx
  let some i := ss.findIdx? isBlockEnd | return stx
  let pre : Array (TSyntax `sol_stmt) := (ss.extract 0 i).map (⟨·⟩)
  let rest ← (ss.extract (i + 1) ss.size).mapM fun s =>
    if isBlockEnd s then `(core_item| } ) else `(core_item| $(⟨s⟩):sol_stmt ; )
  let φ : TSyntax `dl_fml := ⟨args[3]!⟩
  if args[0]!.isToken "⟨" then
    return (← `(dl_fml| ⟨ $[$pre;]* } $rest* ⟩ $φ)).raw
  return (← `(dl_fml| [ $[$pre;]* } $rest* ] $φ)).raw

/-- A scoped formula with schema variables in it, in the notation. -/
def ppFmlE (e : Expr) : MetaM (TSyntax `dl_fml) :=
  withErased e true fun l => do return ⟨← fixBlockEnds (← ppFml l)⟩

/-- A scoped formula, one line. -/
def fmtFml (e : Expr) : MetaM String := do
  return (← PrettyPrinter.ppCategory `dl_fml (← ppFmlE e)).pretty 100000

/-! ## The delaborators -/

/-- `Core.Taclet C k m s p`: `dl{ ⟨[ s; ]⟩ ⇝ p }`, as `delabTaclet` prints
today's, its goals labelled by solkey's labels. -/
@[delab app.Solidity.Core.Taclet]
def delabTaclet : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  guard (e.getAppNumArgs == 7)
  let m ← whnf (e.getArg! 2)
  let out? ← withTwins e false fun env => do
      let st ← (tr [] (e.getArg! 5)).run env
      let p ← (tr [] (e.getArg! 6)).run env
      let st' ← whnf st
      let rule? := Solidity.Taclet.labelledBy (st'.getAppFn.constName?.getD Lean.Name.anonymous)
        (m.isConstOf ``Modality.diamond)
      let labels := (do (← Solidity.Taclet.branchLabels.lookup (← rule?))).getD []
      let some p ← ppPremise? p labels (m.isConstOf ``Modality.box) | return none
      return some (← ppStmt st, p)
  let some (s, p) := out? | failure
  if isEscape s then failure
  match_expr m with
  | Modality.box => `(dl{ [ $s:sol_stmt; ] ⇝ $p })
  | Modality.diamond => `(dl{ ⟨ $s:sol_stmt; ⟩ ⇝ $p })
  | _ => `(dl{ ⟨[ $s:sol_stmt; ]⟩ ⇝ $p })

/-- A scoped premise standing alone: `dl{ p }`. -/
def delabPremise : Delab := do
  unless ← ppOn do failure
  fullApp
  let e ← getExpr
  let some p ← withErased e false fun l => ppPremise? l | failure
  `(dl{ $p:dl_premise })

attribute [delab app.Solidity.Core.Premise.update, delab app.Solidity.Core.Premise.unfold,
  delab app.Solidity.Core.Premise.bind, delab app.Solidity.Core.Premise.split,
  delab app.Solidity.Core.Premise.check, delab app.Solidity.Core.Premise.done,
  delab app.Solidity.Core.Premise.branches, delab app.Solidity.Core.Premise.cases,
  delab app.Solidity.Core.Premise.inv, delab app.Solidity.Core.Premise.inline] delabPremise

/-- A scoped formula standing alone: `dl{ φ }`, a block's end `}`. -/
def delabFml : Delab := do
  unless ← ppOn do failure
  fullApp
  let φ ← ppFmlE (← getExpr)
  guard !(isEscape φ)
  `(dl{ $φ:dl_fml })

attribute [delab app.Solidity.Core.Fml.eq, delab app.Solidity.Core.Fml.defined,
  delab app.Solidity.Core.Fml.not, delab app.Solidity.Core.Fml.and,
  delab app.Solidity.Core.Fml.imp, delab app.Solidity.Core.Fml.upd,
  delab app.Solidity.Core.Fml.modal, delab app.Solidity.Core.Fml.all,
  delab app.Solidity.Core.Fml.bind, delab app.Solidity.Core.Fml.havoc,
  delab app.Solidity.Core.Fml.anon] delabFml

/-! ## Sequents -/

/-- A sequent's context, erased: the rest `..H` when it is a variable, the
entries as `Calculus/Hyp.lean`'s `Hyp`s, and the names of the last scope.  What
erasure loses prints as nothing: an update of pops only, and the hidden
binder (it only names the local it puts in scope). -/
partial def hypsParts (c H : Expr) : TrM (Option Lean.Name × Array Expr × List Expr) := do
  let H := (← instantiateMVars H).consumeMData
  let unknown (Γ : Expr) : MetaM (List Expr) := do
    return List.replicate ((← ctxLength? Γ).getD 0) unknownVar
  if let .fvar fv := H then
    let ty ← whnfR (← fv.getType)
    return (some (← fv.getDecl).userName, #[], ← unknown (ty.getArg! 2))
  let H ← whnf H
  let args := H.getAppArgs
  match H.getAppFn.constName? with
  | some ``Hyps.nil => return (none, #[], ← unknown args[1]!)
  | some ``Hyps.pre =>
    let (r, hs, ns) ← hypsParts c args[3]!
    return (r, hs.push (mkApp2 (mkConst ``Solidity.Hyp.pre) c (← tr ns args[4]!)), ns)
  | some ``Hyps.upd =>
    let (r, hs, ns) ← hypsParts c args[4]!
    let (es, ms) ← updParts ns args[6]!
    if es.isEmpty then return (r, hs, ms)
    let U ← updList c args[6]! es
    return (r, hs.push (mkApp3 (mkConst ``Solidity.Hyp.upd) c args[5]! U), ms)
  | some ``Hyps.havoc =>
    let (r, hs, ns) ← hypsParts c args[3]!
    return (r, hs.push (mkApp (mkConst ``Solidity.Hyp.havoc) c), ns)
  | some ``Hyps.all =>
    let (r, hs, ns) ← hypsParts c args[3]!
    return (r, hs.push (mkApp3 (mkConst ``Solidity.Hyp.all) c args[4]! args[5]!), args[4]! :: ns)
  | some ``Hyps.bind =>
    let (r, hs, ns) ← hypsParts c args[3]!
    return (r, hs, args[5]! :: ns)
  | some ``Hyps.anon =>
    let (r, hs, ns) ← hypsParts c args[3]!
    let some xs ← Solidity.listElems? args[4]! | throwError "anon"
    let xs ← xs.mapM fun x => do trIdx ns (← whnf x).appArg!
    let xs ← mkListLit (mkConst ``Solidity.Var) xs.toList
    return (r, hs.push (mkApp2 (mkConst ``Solidity.Hyp.anon) c xs), ns)
  | _ => throwError "not a context"

/-- `Core.Proves C R Γ₀ H φ`: the sequent `dl{ ..H, h₁, … ⟹ φ }`, as
`delabProves` prints today's (`⟹ₖ` for solkey's rules alone, `⟹[R]` over
a variable rule set), its context's entries erased (`hypsParts`). -/
@[delab app.Solidity.Core.Proves]
def delabProves : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  guard (e.getAppNumArgs == 6)
  let c := e.getArg! 0
  let R ← whnf (e.getArg! 1)
  let out? ← withTwins (contract? := some c) e true fun env => do
    let some (rest, hs, ns) ← (try some <$> (hypsParts c (e.getArg! 4)).run env catch _ => pure none)
      | return none
    let φ ← (tr ns (e.getArg! 5)).run env
    let mut out : Array (TSyntax `dl_hyp) := #[]
    if let some r := rest then out := out.push (← `(dl_hyp| ..$(mkIdent r):ident))
    for h in hs do
      let some h ← Solidity.ppHyp? h | return none
      out := out.push ⟨← fixBlockEnds h⟩
    return some (out, (⟨← fixBlockEnds (← ppFml φ)⟩ : TSyntax `dl_fml))
  let some (out, φ) := out? | failure
  guard !(isEscape φ)
  if R.isConstOf ``RuleSet.all then `(dl{ $[$out],* ⟹ $φ:dl_fml })
  else if R.isConstOf ``RuleSet.solkey then `(dl{ $[$out],* ⟹ₖ $φ:dl_fml })
  else if let some r ← Solidity.fvarName? R then `(dl{ $[$out],* ⟹[$(Solidity.nameIdent r)] $φ:dl_fml })
  else failure

/-- A scoped taclet's type: its side conditions and carried proofs out of
sight, as `Rules.lean`'s `delabTacletSide`. -/
@[delab forallE]
def delabTacletSide : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  let b := e.getForallBody
  -- `Core.CallbackTaclet` is declared by a module importing this one (`Core/Callback.lean`)
  unless b.isAppOf ``Core.Taclet || b.isAppOf ``Core.LeanTaclet ||
      b.isAppOf `Solidity.Core.CallbackTaclet do failure
  withTheReader SubExpr (fun s => { s with expr := Solidity.dropSide e })
    (Solidity.delabTacletBinders #[] #[])

end Delab

end Solidity.Core

