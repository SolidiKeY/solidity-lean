import Solidity.Calculus.DelabErase

/-!
# Printing scoped terms and updates

The printers of the scoped terms and updates (`Tm`, `Upd`, `Calculus/Fml.lean`)
read from their `Expr`, schema variables and all, at a name stack `ns` (the
names of the context, innermost first) as `Calculus/PrintStmt.lean` reads
statements: `ppTermS`, `ppPTermS`, …, `ppUpdS`, in the grammar of
`RuleSyntax.lean`, with its builders (`lenTerms`, `elemTerm`, `dotTerm`,
`allocTy?`, `ppVar?`), so the text is the one the closer's printers
(`ppTerm`, `ppUpd`) print of the erasure.  Nothing here erases: a term is
read by its view (`viewTmS`), a position by its name (`idxName`), a symbol by
its constructor (`Op2.find`), and an update by its pieces (`updPiecesS`).

* **Schema variables** are themselves (their user names print); a program
  schema variable lowered to a term (`se.lower`) is the local of its name;
  `up`s and the weakenings of a rule's line are read through.
* **What erasure loses is invisible**: an update's pops and drops print as
  nothing.
* An escape (`‹…›`) shows the scoped `Expr`.
-/

namespace Solidity

open Lean Meta

namespace Delab

section PrintTerm
set_option hygiene false

/-! ## The name stack -/

/-- The name of the position `e` from the names `ns` (innermost first): the
`Var` its binder gave it; a schema variable itself (its user name prints);
`unknownVar` (`_`) for a position past the stack or that does not
compute. -/
partial def idxName (ns : List Expr) (e : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e).consumeMData
  if e.isFVar then return e
  let e ← whnf e
  if e.isAppOf ``Idx.here then return ns.headD unknownVar
  if e.isAppOf ``Idx.there then return ← idxName ns.tail e.appArg!
  if e.isFVar then return e
  return unknownVar

/-! ## A term's view -/

/-- What a scoped term is, for the printers. -/
inductive TmV where
  /-- A schema variable. -/
  | var (x : Expr)
  /-- A local (`pvV`, …, or a program schema variable lowered), by its name. -/
  | pv (x : Expr)
  /-- `net(x, a)`: the ledger bound at the local named `x`. -/
  | netOf (x a : Expr)
  /-- `t⊕⊕`: the value of an increment by a schema operator `op`. -/
  | bumped (op p t : Expr)
  /-- A symbol: its constructor's name (`Op2.find`) and arguments, and the
  terms it is applied to. -/
  | sym (o : Lean.Name) (oargs xs : Array Expr)
  /-- Anything else: it prints as `‹…›`. -/
  | other
  deriving Inhabited

/-- The view of a scoped term read at `ns`: the names its parts are read at
(an `up` steps past one), what it is, and the `Expr` it was read from (what an
escape shows).  Computed (`whnf`) when `red`; else as it is written. -/
partial def viewTmS (red : Bool) (ns : List Expr) (e : Expr) :
    MetaM (List Expr × TmV × Expr) := do
  let e := (← instantiateMVars e).consumeMData
  if e.isFVar then return (ns, .var e, e)
  let .const n _ := e.getAppFn | return (ns, .other, e)
  let args := e.getAppArgs
  if isUp n && args.size > 0 then return ← viewTmS red ns.tail args.back!
  if n == ``Tm.netOf && args.size == 4 then return (ns, .netOf (← idxName ns args[2]!) args[3]!, e)
  if (n == ``Tm.bumped || n == ``Tms.Term.bumped) && args.size == 5 && args[2]!.isFVar then
    return (ns, .bumped args[2]! args[3]! args[4]!, e)
  let sym (o : Expr) (xs : Array Expr) : MetaM (List Expr × TmV × Expr) := do
    let o ← if red then whnf o else pure (← instantiateMVars o).consumeMData
    match o.getAppFn.constName? with
    | some k => return (ns, .sym k o.getAppArgs xs, e)
    | none => return (ns, .other, e)
  if n == ``Tm.app0 && args.size == 4 then return ← sym args[3]! #[]
  if n == ``Tm.app1 && args.size == 7 then return ← sym args[4]! #[args[6]!]
  if n == ``Tm.app2 && args.size == 8 then return ← sym args[5]! #[args[6]!, args[7]!]
  if n == ``Tm.app3 && args.size == 10 then return ← sym args[6]! #[args[7]!, args[8]!, args[9]!]
  if (n == ``Tm.pvV || n == ``Tm.pvP || n == ``Tm.pvI) && args.size == 4 then
    return (ns, .pv (← idxName ns args[3]!), e)
  if n == ``Tm.pvS && args.size == 3 then return (ns, .pv (← idxName ns args[2]!), e)
  -- a lowering: of a schema variable, the local of its name; of a
  -- constructor, what it computes to
  if lowerFns.contains n && args.size > 0 then
    let x ← stripUps args.back!
    if x.isFVar then return (ns, .pv x, e)
    let e' ← match ← unfoldDefinition? e with
      | some e1 => whnfCore e1
      | none => pure e
    if let some c := e'.getAppFn.constName? then
      if c != n && (lowerFns.contains c || (← getEnv).isConstructor c) then
        return ← viewTmS red ns e'
  unless red do return (ns, .other, e)
  let e' ← whnf e
  if e' == e then return (ns, .other, e)
  viewTmS red ns e'

/-- Whether `pp.sol.reduce` is on: the printers compute what they read. -/
def reduceOn : MetaM Bool := return pp.sol.reduce.get (← getOptions)

/-- A part of a symbol that is no term, computed as the printers read it. -/
def whnfV (e : Expr) : MetaM Expr := do
  if ← reduceOn then whnf e else instantiateMVars e

/-- Whether two terms, read at `n₁` and `n₂`, are the same text: the same
symbols on the same arguments, a local by its name. -/
partial def eqTmS (n₁ : List Expr) (x : Expr) (n₂ : List Expr) (y : Expr) : MetaM Bool := do
  let (x, y) := (← instantiateMVars x, ← instantiateMVars y)
  if x == y && n₁ == n₂ then return true
  let (n₁, v₁, x) ← viewTmS true n₁ x
  let (n₂, v₂, y) ← viewTmS true n₂ y
  let same (a b : Expr) : MetaM Bool := return (← instantiateMVars a) == (← instantiateMVars b)
  match v₁, v₂ with
  | .var a, .var b => return a == b
  | .pv a, .pv b => same a b
  | .netOf a s, .netOf b t => return (← same a b) && (← eqTmS n₁ s n₂ t)
  | .bumped o p s, .bumped o' p' t =>
    return (← same o o') && (← same p p') && (← eqTmS n₁ s n₂ t)
  | .sym o oa xs, .sym o' ob ys =>
    unless o == o' && oa.size == ob.size && xs.size == ys.size do return false
    for a in oa, b in ob do
      unless ← same a b do return false
    for s in xs, t in ys do
      unless ← eqTmS n₁ s n₂ t do return false
    return true
  | .other, .other => return x == y && n₁ == n₂
  | _, _ => return false

/-! ## Terms -/

/-- `‹e›`. -/
def escapeS (e : Expr) : MetaM (TSyntax `dl_term) := escapeDl e

mutual

/-- A value term read at `ns`, as `ppTerm` prints the closer's. -/
partial def ppTermS (ns : List Expr) (e : Expr) : MetaM (TSyntax `dl_term) := do
  let (ns, v, e) ← viewTmS (← reduceOn) ns e
  if let .var x := v then
    if let some t ← tmVar? x then return t
  match v with
  | .bumped _ _ t => `(dl_term| $(← ppTermS ns t):dl_term ⊕⊕)
  | .pv x =>
    let some x ← ppVar? x | escapeS e
    `(dl_term| $x:ident)
  | .netOf x a =>
    let some x ← ppVar? x | escapeS e
    `(dl_term| net($x:ident, $(← ppTermS ns a)))
  | .sym ``Op0.lit #[v] _ =>
    match_expr (← whnfV v) with
    | Semantics.PrimVal.int n =>
      let some n ← intOf? n | escapeS e
      `(dl_term| $(Syntax.mkNumLit (toString n)):num)
    | Semantics.PrimVal.bool b =>
      match_expr (← whnfV b) with
      | Bool.true => `(dl_term| true)
      | Bool.false => `(dl_term| false)
      | _ => escapeS e
    | _ =>
      if v.isAppOfArity ``PrimTy.default 1 then
        return ← `(dl_term| defVal(T))
      if let some n ← fvarName? v then return ← `(dl_term| lit($(nameIdent n):ident))
      escapeS e
  | .sym ``Op2.binop #[op, ty] #[a, b] =>
    let some sym ← termOpSym? op | escapeS e
    -- `+ - * /` read back as `uint` arithmetic only (`schemaTerm0`): an
    -- `int` (or unchecked `bool`) one escapes
    unless sym == "⊕" || sym == "±" || (← whnf ty).isConstOf ``PrimTy.uint do return ← escapeS e
    mkBinTerm sym (← ppTermS ns a) (← ppTermS ns b)
  | .sym ``Op1.unop #[op, _] #[a] =>
    if (← fvarName? op).isSome then return ← `(dl_term| ⊖$(← ppTermS ns a))
    if (← whnf op).isConstOf ``UnOp.not then return ← `(dl_term| !$(← ppTermS ns a))
    escapeS e
  | .sym ``Op2.find #[] #[s, p] => `(dl_term| find($(← ppSTermS ns s), $(← ppPTermS ns p)))
  | .sym ``Op2.len #[] #[s, p] =>
    let (lenPath, lenVal, _) ← lenTerms (← ppPTermS ns p)
    if !(← keyOn) && (← isStorageS ns s) then return lenVal
    `(dl_term| find($(← ppSTermS ns s), $lenPath))
  | .sym ``Op1.delValue #[] #[t] => `(dl_term| delValue($(← ppTermS ns t)))
  | .sym ``Op1.wt #[_] #[s] => `(dl_term| wt($(← ppSTermS ns s)))
  | .sym ``Op2.read #[] #[m, a] =>
    if ← keyOn then
      if let some (i, f) ← keyAddrS? ns a then return ← `(dl_term| read($(← ppMTermS ns m), $i, $f))
    `(dl_term| read($(← ppMTermS ns m), $(← ppMAddrS ns a)))
  | .sym ``Op2.mlen #[] #[m, i] =>
    if ← keyOn then return ← `(dl_term| read($(← ppMTermS ns m), $(← ppITermS ns i), size))
    let (_, vm, _) ← viewTmS (← reduceOn) ns m
    unless vm matches .sym ``Op0.memory _ _ do return ← escapeS e
    let `(dl_term| $x:ident) ← ppITermS ns i | escapeS e
    `(dl_term| $(mkIdent (x.getId.str "length")):ident)
  | .sym ``Op0.env #[k] _ =>
    match_expr (← whnf k) with
    | EnvKey.msgSender => `(dl_term| msg.sender)
    | EnvKey.msgValue => `(dl_term| msg.value)
    | EnvKey.timestamp => `(dl_term| block.timestamp)
    | EnvKey.selfBalance => `(dl_term| selfBalance)
    | EnvKey.selfAddress => if ← keyOn then `(dl_term| self) else `(dl_term| this)
    | _ => escapeS e
  | .sym ``Op1.net #[] #[a] =>
    if ← keyOn then return ← `(dl_term| selectSt(net, at($(← ppTermS ns a))))
    `(dl_term| net($(← ppTermS ns a)))
  | .sym ``Op1.netOf #[x] #[a] =>
    let some x ← ppVar? x | escapeS e
    `(dl_term| net($x:ident, $(← ppTermS ns a)))
  | _ => escapeS e

/-- Whether a storage term is `storage`. -/
partial def isStorageS (ns : List Expr) (s : Expr) : MetaM Bool := do
  let (_, v, _) ← viewTmS (← reduceOn) ns s
  return v matches .sym ``Op0.storage _ _

/-- KeY's member or element of a memory location (`read(m, i, f)`,
`read(m, i, at(k))`): the identity and the field. -/
partial def keyAddrS? (ns : List Expr) (a : Expr) :
    MetaM (Option (TSyntax `dl_term × TSyntax `dl_term)) := do
  let (ns, v, _) ← viewTmS (← reduceOn) ns a
  match v with
  | .sym ``Op1.mfield #[f] #[i] =>
    let some f ← nameOf? f | return none
    return some (← ppITermS ns i, ← `(dl_term| $(nameIdent f):ident))
  | .sym ``Op2.mat #[] #[i, k] => return some (← ppITermS ns i, ← `(dl_term| at($(← ppTermS ns k))))
  | _ => return none

/-- A storage path read at `ns` (`ppPTerm`). -/
partial def ppPTermS (ns : List Expr) (e : Expr) : MetaM (TSyntax `dl_term) := do
  let (ns, v, e) ← viewTmS (← reduceOn) ns e
  if let .var x := v then
    if let some t ← tmVar? x then return t
  match v with
  | .sym ``Op0.root #[r] _ =>
    let some r ← nameOf? r | escapeS e
    `(dl_term| $(nameIdent r):ident)
  | .pv x =>
    let some x ← ppVar? x | escapeS e
    `(dl_term| $x:ident)
  | .sym ``Op1.field #[f] #[p] =>
    let some f ← nameOf? f | escapeS e
    if ← keyOn then return ← `(dl_term| consr($(← ppPTermS ns p), $(nameIdent f):ident))
    dotTerm (← ppPTermS ns p) f
  | .sym ``Op2.at #[] #[p, i] => elemTerm (← ppPTermS ns p) (← ppTermS ns i)
  | .sym ``Op1.next #[] #[p] => return (← lenTerms (← ppPTermS ns p)).2.2
  | .sym ``Op3.atIn #[] #[s, p, i] =>
    `(dl_term| $(← recvTerm (← ppPTermS ns p)):dl_term[$(← ppTermS ns i):dl_term]@$(← ppSTermS ns s):dl_term)
  | .sym ``Op2.nextIn #[] #[s, p] =>
    let p ← recvTerm (← ppPTermS ns p)
    let (_, len, _) ← withOptions (fun o => pp.sol.key.set o false) (lenTerms p)
    `(dl_term| $p:dl_term[$len:dl_term]@$(← ppSTermS ns s):dl_term)
  | _ => escapeS e

/-- A storage read at `ns` (`ppSTerm`). -/
partial def ppSTermS (ns : List Expr) (e : Expr) : MetaM (TSyntax `dl_term) := do
  let (ns, v, e) ← viewTmS (← reduceOn) ns e
  if let .var x := v then
    if let some n ← fvarName? x then return ← `(dl_term| $(nameIdent n):ident)
  match v with
  | .sym ``Op0.storage _ _ => `(dl_term| storage)
  | .sym ``Op0.mtSt _ _ => `(dl_term| mtSt)
  | .pv x =>
    let some x ← ppVar? x | escapeS e
    `(dl_term| $x:ident)
  | .sym ``Op3.save #[] #[s, p, v] =>
    `(dl_term| save($(← ppSTermS ns s), $(← ppPTermS ns p), $(← ppSValS ns v)))
  | .sym ``Op2.delAt #[] #[s, p] => `(dl_term| delAt($(← ppSTermS ns s), $(← ppPTermS ns p)))
  | .sym ``Op3.push #[] #[s, p, v] =>
    let (len, val, slot) ← lenTerms (← ppPTermS ns p)
    `(dl_term| save(save($(← ppSTermS ns s), $slot, $(← ppSValS ns v)), $len, $val + 1))
  | .sym ``Op2.pushSlot #[_] #[s, p] =>
    let (len, val, slot) ← lenTerms (← ppPTermS ns p)
    `(dl_term| save(delAt($(← ppSTermS ns s), $slot), $len, $val + 1))
  | .sym ``Op2.pop #[] #[s, p] =>
    let p ← ppPTermS ns p
    let (len, val, _) ← lenTerms p
    `(dl_term| save(delAt($(← ppSTermS ns s), $(← elemTerm p (← `(dl_term| $val - 1)))), $len, $val - 1))
  | .sym ``Op2.extend #[_] #[s, p] =>
    let (len, val, _) ← lenTerms (← ppPTermS ns p)
    `(dl_term| save($(← ppSTermS ns s), $len, $val + 1))
  | .sym ``Op2.shrink #[] #[s, p] =>
    let (len, val, _) ← lenTerms (← ppPTermS ns p)
    `(dl_term| save($(← ppSTermS ns s), $len, $val - 1))
  | .sym ``Op1.select #[r] #[s] =>
    let some r ← nameOf? r | escapeS e
    if ← keyOn then return ← `(dl_term| selectSt($(← ppSTermS ns s), $(nameIdent r):ident))
    `(dl_term| select($(← ppSTermS ns s), $(nameIdent r):ident))
  | _ => escapeS e

/-- What a storage `save` writes, read at `ns` (`ppSVal`). -/
partial def ppSValS (ns : List Expr) (e : Expr) : MetaM (TSyntax `dl_term) := do
  let (ns, v, e) ← viewTmS (← reduceOn) ns e
  if let .var x := v then
    if let some t ← tmVar? x then return t
  match v with
  | .sym ``Op1.sval #[] #[t] =>
    -- `find` here reads back as the copy below, so a value read prints as `select`
    let (nt, vt, _) ← viewTmS (← reduceOn) ns t
    let isVar ← match vt with
      | .var x => pure (← tmVar? x).isSome
      | _ => pure false
    if !isVar then
      if let .sym ``Op2.find #[] #[s, p] := vt then
        return ← `(dl_term| select($(← ppSTermS nt s), $(← ppPTermS nt p)))
    ppTermS ns t
  -- a lowered `Src` schema variable: the value it names
  | .pv x =>
    let some x ← ppVar? x | escapeS e
    `(dl_term| $x:ident)
  | .sym ``Op2.sfind #[] #[s, p] => `(dl_term| find($(← ppSTermS ns s), $(← ppPTermS ns p)))
  | .sym ``Op2.copyMem #[] #[m, i] => `(dl_term| copyMem(mtSt, $(← ppMTermS ns m), $(← ppITermS ns i)))
  | .sym ``Op1.newArr #[R] #[n] =>
    match ← allocTy? R with
    | some T => `(dl_term| newArr($T, $(← ppTermS ns n)))
    | none => `(dl_term| newArr($(← ppTermS ns n)))
  | _ => escapeS e

/-- A memory identity read at `ns` (`ppITerm`). -/
partial def ppITermS (ns : List Expr) (e : Expr) : MetaM (TSyntax `dl_term) := do
  let (ns, v, e) ← viewTmS (← reduceOn) ns e
  if let .var x := v then
    if let some t ← tmVar? x then return t
  match v with
  | .pv x =>
    let some x ← ppVar? x | escapeS e
    `(dl_term| $x:ident)
  | .sym ``Op2.iread #[] #[m, a] =>
    if ← keyOn then
      if let some (i, f) ← keyAddrS? ns a then return ← `(dl_term| read($(← ppMTermS ns m), $i, $f))
    `(dl_term| read($(← ppMTermS ns m), $(← ppMAddrS ns a)))
  | .sym ``Op1.alloc #[R] #[m] =>
    let m ← ppMTermS ns m
    match ← allocTy? R with
    | some T => `(dl_term| freshId(addM($m, $T)))
    | none => `(dl_term| freshId(addM($m)))
  | .sym ``Op2.copy #[] #[m, v] => `(dl_term| freshId(copySt($(← ppMTermS ns m), $(← ppSValS ns v))))
  | _ => escapeS e

/-- A member or an element of a memory object, read at `ns` (`ppMAddr`). -/
partial def ppMAddrS (ns : List Expr) (e : Expr) : MetaM (TSyntax `dl_term) := do
  let (ns, v, e) ← viewTmS (← reduceOn) ns e
  if let .var x := v then
    if let some t ← tmVar? x then return t
  match v with
  | .sym ``Op1.mfield #[f] #[i] =>
    let some f ← nameOf? f | escapeS e
    dotTerm (← ppITermS ns i) f
  | .sym ``Op2.mat #[] #[i, k] => `(dl_term| $(← ppITermS ns i):dl_term[$(← ppTermS ns k):dl_term])
  | _ => escapeS e

/-- A memory read at `ns` (`ppMTerm`). -/
partial def ppMTermS (ns : List Expr) (e : Expr) : MetaM (TSyntax `dl_term) := do
  let (ns, v, e) ← viewTmS (← reduceOn) ns e
  if let .var x := v then
    if let some n ← fvarName? x then return ← `(dl_term| $(nameIdent n):ident)
  match v with
  | .sym ``Op0.memory _ _ => `(dl_term| memory)
  | .sym ``Op3.write #[] #[m, a, v] =>
    if ← keyOn then
      if let some (i, f) ← keyAddrS? ns a then
        return ← `(dl_term| write($(← ppMTermS ns m), $i, $f, $(← ppMValS ns v)))
    `(dl_term| write($(← ppMTermS ns m), $(← ppMAddrS ns a), $(← ppMValS ns v)))
  | .sym ``Op1.addM #[R] #[m] =>
    let m ← ppMTermS ns m
    match ← allocTy? R with
    | some T => `(dl_term| addM($m, $T))
    | none => `(dl_term| addM($m))
  | .sym ``Op2.copySt #[] #[m, v] => `(dl_term| copySt($(← ppMTermS ns m), $(← ppSValS ns v)))
  | _ => escapeS e

/-- What a memory `write` writes, read at `ns` (`ppMVal`). -/
partial def ppMValS (ns : List Expr) (e : Expr) : MetaM (TSyntax `dl_term) := do
  let (ns, v, e) ← viewTmS (← reduceOn) ns e
  if let .var x := v then
    if let some t ← tmVar? x then return t
  match v with
  | .sym ``Op1.mval #[] #[t] => ppTermS ns t
  | .sym ``Op1.ref #[] #[i] => ppITermS ns i
  -- a lowered `MSrc` schema variable: the value it names
  | .pv x =>
    let some x ← ppVar? x | escapeS e
    `(dl_term| $x:ident)
  | _ => escapeS e

end

/-- A scoped term of any sort read at `ns`, by its sort's printer. -/
def ppTmAnyS (ns : List Expr) (e : Expr) : MetaM (TSyntax `dl_term) := do
  let ty ← whnfR (← inferType e)
  let some srt := (← whnf (ty.getArg! 2)).constName? | escapeS e
  match srt with
  | ``Srt.val => ppTermS ns e
  | ``Srt.path => ppPTermS ns e
  | ``Srt.st => ppSTermS ns e
  | ``Srt.sv => ppSValS ns e
  | ``Srt.ident => ppITermS ns e
  | ``Srt.addr => ppMAddrS ns e
  | ``Srt.mem => ppMTermS ns e
  | ``Srt.mv => ppMValS ns e
  | _ => escapeS e

/-- `a < b = true`, a comparison as the specification writes one, read at
`na` and `nb`: its operator and operands, with their names. -/
def cmpPartsS (na : List Expr) (a : Expr) (nb : List Expr) (b : Expr) :
    MetaM (Option (String × (List Expr × Expr) × (List Expr × Expr))) := do
  let (_, vb, _) ← viewTmS true nb b
  let .sym ``Op0.lit #[v] _ := vb | return none
  let v ← whnf v
  unless v.isAppOfArity ``Semantics.PrimVal.bool 1 && (← whnf v.appArg!).isConstOf ``Bool.true do
    return none
  let (na, va, _) ← viewTmS true na a
  let .sym ``Op2.binop #[op, _] #[l, r] := va | return none
  let sym ← match_expr (← whnf op) with
    | BinOp.lt => pure "<"
    | BinOp.le => pure "<="
    | BinOp.gt => pure ">"
    | BinOp.ge => pure ">="
    | _ => return none
  return some (sym, (na, l), (na, r))

/-! ## Updates -/

/-- A piece of an update. -/
inductive UPiece where
  /-- An assigning element, its right-hand sides read at `ns`, its target
  at `ms`. -/
  | elem (ns ms : List Expr) (e : Expr)
  /-- `x := r`, a local declared, `r` read at `ns`. -/
  | decl (ns : List Expr) (x r : Expr)
  /-- An update variable spliced in. -/
  | var (U : Expr)
  /-- An update that does not compute. -/
  | stuck
  deriving Inhabited

/-- An update's pieces read at `ns`, in order, and the names of the context it
leaves: a pop or a drop is nothing. -/
partial def updPiecesS (ns : List Expr) (U : Expr) : MetaM (Array UPiece × List Expr) := do
  let U ← whnf (← instantiateMVars U)
  let args := U.getAppArgs
  if U.isAppOf ``Upd.snoc then
    let (es, ms) ← updPiecesS ns args[3]!
    return (es.push (.elem ns ms args[4]!), ms)
  if U.isAppOf ``Upd.decl then
    let (es, ms) ← updPiecesS ns args[4]!
    let x := args[5]!
    return (es.push (.decl ns x args[6]!), x :: ms)
  if U.isAppOf ``Upd.pop then
    let (es, ms) ← updPiecesS ns args[4]!
    return (es, ms.drop (← extDepth args[5]!))
  if U.isAppOf ``Upd.drop then
    let (es, ms) ← updPiecesS ns args[4]!
    return (es, ← thinNames ms args[5]!)
  if U.isAppOf ``Upd.nil then return (#[], ns)
  if U.isFVar then return (#[.var U], ns)
  return (#[.stuck], ns)

/-- `x := r`, the element of `r`'s kind, `r` read at `ns`; none where it does
not print. -/
def rhsElemS (ns : List Expr) (x r : Expr) : MetaM (Option (TSyntax `dl_upd_elem)) := do
  let some xi ← ppVar? x | return none
  let x : TSyntax `dl_term ← `(dl_term| $xi:ident)
  let r ← whnf (← instantiateMVars r)
  let t := r.getAppArgs.back?.getD r
  match r.getAppFn.constName? with
  | some ``Rhs.val =>
    let (nt, vt, _) ← viewTmS true ns t
    if let .sym ``Op2.binop #[op, ty] #[a, b] := vt then
      let a ← ppTermS nt a
      let b ← ppTermS nt b
      match_expr (← whnf op) with
      | BinOp.le => return some (← `(dl_upd_elem| $x:dl_term := $a:dl_term <= $b:dl_term))
      | BinOp.lt => return some (← `(dl_upd_elem| $x:dl_term := $a:dl_term < $b:dl_term))
      | BinOp.gt => return some (← `(dl_upd_elem| $x:dl_term := $a:dl_term > $b:dl_term))
      | BinOp.ge => return some (← `(dl_upd_elem| $x:dl_term := $a:dl_term >= $b:dl_term))
      | BinOp.eqB =>
        if (← whnf ty).isConstOf ``PrimTy.uint then
          return some (← `(dl_upd_elem| $x:dl_term := $a:dl_term == $b:dl_term))
      | BinOp.neB =>
        if (← whnf ty).isConstOf ``PrimTy.uint then
          return some (← `(dl_upd_elem| $x:dl_term := $a:dl_term != $b:dl_term))
      | _ => pure ()
    return some (← `(dl_upd_elem| $x:dl_term := $(← ppTermS ns t):dl_term))
  | some ``Rhs.path => return some (← `(dl_upd_elem| $x:dl_term := $(← ppPTermS ns t):dl_term))
  | some ``Rhs.unset => return some (← `(dl_upd_elem| $x:dl_term := unset))
  | some ``Rhs.mref => return some (← `(dl_upd_elem| $x:dl_term := $(← ppITermS ns t):dl_term))
  | some ``Rhs.store => return some (← `(dl_upd_elem| $x:dl_term := $(← ppSTermS ns t):dl_term))
  | some ``Rhs.saveNet => return some (← `(dl_upd_elem| $x:dl_term := net))
  | some ``Rhs.saveNetMt => return some (← `(dl_upd_elem| $x:dl_term := mtSt))
  | _ => return none

/-- An assigning element, its right-hand sides read at `ns` and its target at
`ms` (`ppUpdElem?`); none where it does not print. -/
def updElemS (ns ms : List Expr) (e : Expr) : MetaM (Option (TSyntax `dl_upd_elem)) := do
  let e ← whnf (← instantiateMVars e)
  let args := e.getAppArgs
  match e.getAppFn.constName? with
  | some ``UpdElem.local => rhsElemS ns (← idxName ms args[4]!) args[5]!
  | some ``UpdElem.storage => return some (← `(dl_upd_elem| storage := $(← ppSTermS ns args[3]!):dl_term))
  | some ``UpdElem.memory => return some (← `(dl_upd_elem| memory := $(← ppMTermS ns args[3]!):dl_term))
  | some ``UpdElem.selfBalance =>
    let a ← ppTermS ns args[4]!
    match_expr (← whnf args[3]!) with
    | IntOp.sub => return some (← `(dl_upd_elem| selfBalance := selfBalance - $a))
    | IntOp.add => return some (← `(dl_upd_elem| selfBalance := selfBalance + $a))
    | _ => return none
  | some ``UpdElem.net =>
    let r ← ppTermS ns args[3]!
    let a ← ppTermS ns args[5]!
    let key ← keyOn
    match_expr (← whnf args[4]!) with
    | IntOp.sub =>
      if key then return some (← `(dl_upd_elem| net := storeSt(net, at($r), selectSt(net, at($r)) - $a)))
      return some (← `(dl_upd_elem| net := store(net, at($r), net($r) - $a)))
    | IntOp.add =>
      if key then return some (← `(dl_upd_elem| net := storeSt(net, at($r), selectSt(net, at($r)) + $a)))
      return some (← `(dl_upd_elem| net := store(net, at($r), net($r) + $a)))
    | _ => return none
  | some ``UpdElem.pay =>
    let r ← ppTermS ns args[3]!
    let a ← ppTermS ns args[4]!
    if ← keyOn then
      return some (← `(dl_upd_elem|
        net := if($r = $(mkIdent `self):ident) then $(mkIdent `net):ident
          else storeSt(net, at($r), selectSt(net, at($r)) - $a)))
    return some (← `(dl_upd_elem|
      net := if($r = $(mkIdent `this):ident) then $(mkIdent `net):ident
        else store(net, at($r), net($r) - $a)))
  | some ``UpdElem.netMt =>
    let r ← ppTermS ns args[3]!
    let a ← ppTermS ns args[4]!
    if ← keyOn then return some (← `(dl_upd_elem| net := storeSt(mtSt, at($r), $a)))
    return some (← `(dl_upd_elem| net := store(mtSt, at($r), $a)))
  | some ``UpdElem.setBalance =>
    return some (← `(dl_upd_elem| selfBalance := $(← ppTermS ns args[3]!)))
  | _ => return none

/-- The elements of an update's pieces, as `{u ‖ x := t}` reads them: a
variable first, then elements; none where that is not their shape or an
element does not print. -/
def updElemsS (ps : Array UPiece) : MetaM (Option (Array (TSyntax `dl_upd_elem))) := do
  let mut out := #[]
  let mut elems := false
  for p in ps do
    match p with
    | .var U =>
      -- a variable after an element: no list the notation reads
      if elems then return none
      let some n ← fvarName? U | return none
      out := out.push (← `(dl_upd_elem| $(nameIdent n):ident))
    | .elem ns ms e =>
      elems := true
      let some u ← updElemS ns ms e | return none
      out := out.push u
    | .decl ns x r =>
      elems := true
      let some u ← rhsElemS ns x r | return none
      out := out.push u
    | .stuck => return none
  return some out

/-- The update `U`, of pieces `ps`, as `ppUpd` prints the closer's: `‹U›`
where it does not print. -/
def ppUpdPiecesS (U : Expr) (ps : Array UPiece) : MetaM (TSyntax `dl_upd) := do
  if ps.isEmpty then return ← `(dl_upd| ‹$(← `([])):term›)
  let some out ← updElemsS ps | `(dl_upd| ‹$(← escapeTerm U):term›)
  `(dl_upd| { $[$out]‖* })

/-- An update read at `ns`, and the names of the context it leaves. -/
def ppUpdS (ns : List Expr) (U : Expr) : MetaM (TSyntax `dl_upd × List Expr) := do
  let (ps, ms) ← updPiecesS ns U
  return (← ppUpdPiecesS U ps, ms)

/-- Whether an update has a schema variable in what it prints: a free
variable that is no context, scope end or proof. -/
def updHasSchemaVar (U : Expr) : MetaM Bool := do
  let U ← instantiateMVars U
  (collectFVars {} U).fvarIds.anyM fun fv => do
    let ty ← whnfR (← instantiateMVars (← fv.getType))
    if ← isProp ty then return false
    if ty.isAppOfArity ``List 1 && (ty.getArg! 0).isConstOf ``LTy then return false
    return !(ty.isAppOf ``Ext || ty.isAppOf ``Thin)

end PrintTerm

end Delab

end Solidity
