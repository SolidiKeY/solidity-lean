import Solidity.Update.SequentSyntax

/-!
# Printing a derivation line back in the calculus's notation

`seq!` reads `Γ => {U} <[ π ]>(φ)`; nothing read it back.  A goal in the middle
of a derivation therefore printed as the data it is --

```
[{ goal := SeqGoal.prog { modality := SolidityModality.both,
     stmts := [Stmt.assign { expr := Typed.WrappedExpr.field Kind.storage … } … ] } φ }]
```

-- which is unreadable at exactly the moment a reader wants to read it: between
two steps of a chain whose intermediate lines are *not* written out
(`Examples/Derivations/StorageSteps.lean`).  This module is the delaborator
that prints such a term as the line the calculus draws.

## It is not an inverse of the parser, and it does not pretend to be

`expandUpd` is lossy: `x := p` on a place builds a `UpdElem.bind`, but `x := e` goes
through `Rules.writeBack`, a *function* that dispatches on the data location,
so there is no constructor left to match on the way back.  Several surface
forms also build the same term -- `alice`, `alice@Person` and `alice@@Person`
are all a `WrappedExpr.var`.

So where a term is ambiguous this **builds the candidate and checks it**:
`rootExpr "alice"` is elaborated and compared with `isDefEq` against the term
in hand, and the spelling is used only if it reproduces it.  That is what makes
the output re-parse to what it came from rather than merely look like it.

## Failure is per line, and silent

Any node the walk does not handle fails, and the whole `Sequent` falls back to
Lean's own printing.  A partial printer that showed a line it could not account
for would be worse than none: a derivation is read to be checked.  `set_option
pp.solidity.seq false` turns it off entirely.
-/

namespace Solidity.SequentPP

open Lean Lean.PrettyPrinter.Delaborator Lean.Meta

register_option pp.solidity.seq : Bool := {
  defValue := true
  descr := "print Solidity derivation lines in the `seq!` notation \
            they are written in, rather than as constructor applications"
}

/-! ## Small readers over the term -/

private def strLit? (e : Lean.Expr) : Option String :=
  match e.consumeMData with
  | .lit (.strVal s) => some s
  | _ => none

private def ident! (s : String) : Ident := mkIdent (Lean.Name.mkSimple s)

/-- The elements of a literal list, or `none` if the spine is not literal. -/
private partial def listElems? (es : Lean.Expr) : MetaM (Option (Array Lean.Expr)) := do
  let mut out := #[]
  let mut cur ← whnf es
  repeat
    if cur.isAppOfArity ``List.nil 1 then return some out
    unless cur.isAppOfArity ``List.cons 3 do return none
    let args := cur.getAppArgs
    out := out.push args[1]!
    cur ← whnf args[2]!
  return some out

/-- The constructor name and explicit-looking arguments of an application. -/
private def appOf? (e : Lean.Expr) (n : Lean.Name) (arity : Nat) : Option (Array Lean.Expr) :=
  if e.isAppOfArity n arity then some e.getAppArgs else none

/-- The names `SoliditySyntax.declTy` answers to, in its own order.  A type
outside this list has no spelling in `name@Type`, so a line that mentions one
falls back rather than inventing one. -/
def declaredTyNames : List String :=
  ["Person", "Account", "Token", "PersonArray", "UintMatrix", "Basket",
   "Ledger", "LedgerUse", "TokenBucket", "Toggle", "Pair", "S", "Sub",
   "WithSub", "Inner", "Outer", "Simple", "WithArray", "Triple",
   "UintArray", "BoolArray", "TokenArray", "TokenBucketArray", "PairArray",
   "InnerArray", "LedgerUseArray", "UintMap", "UintArrayMap", "AccountMap",
   "SMap", "WithSubMap", "SimpleMap", "bool", "uint", "int"]

/-! ## Types

The name a type is *written* under, which is `SoliditySyntax.declTy` read
backwards.  Only the vocabulary of the worked examples is here, because that is
the vocabulary `declTy` has; a type outside it fails and the line falls back. -/

private partial def tyName? (e : Lean.Expr) : MetaM (Option String) := do
  let e ← whnf e
  if let some #[p] := appOf? e ``Ty.prim 1 then
    let p ← whnf p
    if p.isConstOf ``PrimTy.uint then return some "uint"
    if p.isConstOf ``PrimTy.int then return some "int"
    if p.isConstOf ``PrimTy.bool then return some "bool"
    return none
  let some #[r] := appOf? e ``Ty.ref 1 | return none
  let r ← whnf r
  if let some #[s] := appOf? r ``RefTy.struct 1 then return strLit? s
  -- Arrays and mappings are written under their declared names, so ask
  -- `declTy` which name builds this type rather than inverting its table.
  for cand in declaredTyNames do
    let built ← reduce (mkApp (mkConst ``SoliditySyntax.declTy) (mkStrLit cand))
    if ← isDefEq built e then return some cand
  return none

/-! ## Expressions -/

/-- Does `cand` -- the term some surface spelling builds -- denote `e`? -/
private def denotes (cand e : Lean.Expr) : MetaM Bool :=
  try isDefEq (← reduce cand) e catch _ => pure false

/-- A binary operator between two already-printed operands.  The comparisons
are the parenthesised productions of `sol_expr`; the rest are its infixes. -/
private def ppBinop (op : Lean.Expr) (l r : TSyntax `sol_expr) :
    MetaM (Option (TSyntax `sol_expr)) := do
  let op ← whnf op
  let res : Option (TSyntax `sol_expr) ←
    if op.isConstOf ``BinOp.add then return some (← `(sol_expr| $l + $r))
    else if op.isConstOf ``BinOp.sub then return some (← `(sol_expr| $l - $r))
    else if op.isConstOf ``BinOp.mul then return some (← `(sol_expr| $l * $r))
    else if op.isConstOf ``BinOp.div then return some (← `(sol_expr| $l / $r))
    else if op.isConstOf ``BinOp.mod then return some (← `(sol_expr| $l % $r))
    else if op.isConstOf ``BinOp.pow then return some (← `(sol_expr| $l ** $r))
    else if op.isConstOf ``BinOp.lt then return some (← `(sol_expr| ($l < $r)))
    else if op.isConstOf ``BinOp.gt then return some (← `(sol_expr| ($l > $r)))
    else if op.isConstOf ``BinOp.le then return some (← `(sol_expr| ($l <= $r)))
    else if op.isConstOf ``BinOp.ge then return some (← `(sol_expr| ($l >= $r)))
    else if op.isConstOf ``BinOp.eqB then return some (← `(sol_expr| ($l == $r)))
    else if op.isConstOf ``BinOp.neB then return some (← `(sol_expr| ($l != $r)))
    else if op.isConstOf ``BinOp.and then return some (← `(sol_expr| $l && $r))
    else if op.isConstOf ``BinOp.or then return some (← `(sol_expr| $l || $r))
    else pure none
  return res

private partial def ppExpr (e : Lean.Expr) : MetaM (Option (TSyntax `sol_expr)) := do
  let e ← whnf e
  -- A variable: a root, a scratch alias, or a contract's state variable.  All
  -- three are one constructor, so try each spelling and keep the one that
  -- reproduces the term.
  if let some #[_, ty, fld] := appOf? e ``Typed.WrappedExpr.var 3 then
    let fld ← whnf fld
    let some #[nameE, _, _] := appOf? fld ``Field.mk 3 | return none
    let some name := strLit? nameE | return none
    if ← denotes (mkApp (mkConst ``SoliditySyntax.rootExpr) (mkStrLit name)) e then
      return some (← `(sol_expr| $(ident! name):ident))
    let some tn ← tyName? ty | return none
    let args := #[mkStrLit name, ty]
    if ← denotes (mkAppN (mkConst ``SoliditySyntax.aliasExpr) args) e then
      return some (← `(sol_expr| $(ident! name):ident@$(ident! tn):ident))
    if ← denotes (mkAppN (mkConst ``SoliditySyntax.globalExpr) args) e then
      return some (← `(sol_expr| $(ident! name):ident@@$(ident! tn):ident))
    return none
  if let some #[_, _, base, fld] := appOf? e ``Typed.WrappedExpr.field 4 then
    let fld ← whnf fld
    let some #[nameE, _, _] := appOf? fld ``Field.mk 3 | return none
    let some name := strLit? nameE | return none
    let some b ← ppExpr base | return none
    return some (← `(sol_expr| $b.$(ident! name)))
  if let some #[_, _, base, idx] := appOf? e ``Typed.WrappedExpr.index 4 then
    let some b ← ppExpr base | return none
    let some i ← ppExpr idx | return none
    return some (← `(sol_expr| $b[$i]))
  if let some #[tgt] := appOf? e ``Typed.WrappedExpr.pushPlace 1 then
    let some t ← ppExpr tgt | return none
    return some (← `(sol_expr| $t .push()))
  if let some #[b] := appOf? e ``Typed.WrappedExpr.bool 1 then
    let b ← whnf b
    if b.isConstOf ``Bool.true then return some (← `(sol_expr| true))
    if b.isConstOf ``Bool.false then return some (← `(sol_expr| false))
    return none
  if let some #[_, v] := appOf? e ``Typed.WrappedExpr.intLit 2 then
    let some n ← natOf? v | return none
    return some (← `(sol_expr| $(Syntax.mkNumLit (toString n)):num))
  if let some #[op, lhs, rhs] := appOf? e ``Typed.WrappedExpr.mkBinop 3 then
    let some l ← ppExpr lhs | return none
    let some r ← ppExpr rhs | return none
    return (← ppBinop op l r)
  if let some #[op, arg] := appOf? e ``Typed.WrappedExpr.mkUnop 2 then
    let some a ← ppExpr arg | return none
    let op ← whnf op
    if op.isConstOf ``UnOp.not then return some (← `(sol_expr| !$a))
    if op.isConstOf ``UnOp.neg then return some (← `(sol_expr| -$a))
    return none
  if let some #[op, tgt] := appOf? e ``Typed.WrappedExpr.mkIncDec 2 then
    let some t ← ppExpr tgt | return none
    let op ← whnf op
    if op.isConstOf ``IncDec.preInc then return some (← `(sol_expr| ++$t))
    if op.isConstOf ``IncDec.postInc then return some (← `(sol_expr| $t++))
    if op.isConstOf ``IncDec.preDec then return some (← `(sol_expr| predec($t)))
    if op.isConstOf ``IncDec.postDec then return some (← `(sol_expr| postdec($t)))
    return none
  if let some #[_, _, nameE, args] := appOf? e ``Typed.WrappedExpr.mkCall 4 then
    let some name := strLit? nameE | return none
    let some as ← ppExprList args | return none
    return some (← `(sol_expr| $(ident! name):ident($as,*)))
  return none
where
  natOf? (v : Lean.Expr) : MetaM (Option Nat) := do
    let v ← whnf v
    if let some #[n] := appOf? v ``Int.ofNat 1 then
      return (← whnf n).rawNatLit?
    return none
  ppExprList (es : Lean.Expr) : MetaM (Option (Array (TSyntax `sol_expr))) := do
    let some xs ← listElems? es | return none
    let mut out := #[]
    for x in xs do
      let some s ← ppExpr x | return none
      out := out.push s
    return some out

/-! ## Statements -/

/-- A `PlaceExpr` is its expression; the assignability proof is not drawn. -/
private def ppPlace (e : Lean.Expr) : MetaM (Option (TSyntax `sol_expr)) := do
  let e ← whnf e
  let some #[x, _] := appOf? e ``PlaceExpr.mk 2 | ppExpr e
  ppExpr x

/-- The `Ty name` and `Ty loc name` heads of a declaration. -/
private def ppDecl (loc : Option String) (ty nameE init : Lean.Expr) :
    MetaM (Option (TSyntax `sol_stmt)) := do
  let some tn ← tyName? ty | return none
  let some nm := strLit? (← whnf nameE) | return none
  let t := ident! tn
  let n := ident! nm
  let init ← whnf init
  let some e? ← optionOf? init | return none
  match loc, e? with
  | none, none => return some (← `(sol_stmt| $t:ident $n:ident))
  | none, some v =>
      let some r ← ppExpr v | return none
      return some (← `(sol_stmt| $t:ident $n:ident = $r:sol_expr))
  | some l, none => return some (← `(sol_stmt| $t:ident $(ident! l):ident $n:ident))
  | some l, some v =>
      let some r ← ppExpr v | return none
      return some (← `(sol_stmt| $t:ident $(ident! l):ident $n:ident = $r:sol_expr))
where
  optionOf? (o : Lean.Expr) : MetaM (Option (Option Lean.Expr)) := do
    if o.isAppOfArity ``Option.none 1 then return some none
    let some #[_, v] := appOf? o ``Option.some 2 | return none
    return some (some v)

private partial def ppStmt (e : Lean.Expr) : MetaM (Option (TSyntax `sol_stmt)) := do
  let e ← whnf e
  if let some #[lhs, rhs] := appOf? e ``Stmt.assign 2 then
    let some l ← ppPlace lhs | return none
    let some r ← ppExpr rhs | return none
    return some (← `(sol_stmt| $l:sol_expr = $r:sol_expr))
  if let some #[ty, n, init] := appOf? e ``Stmt.stackDecl 3 then
    return (← ppDecl none ty n init)
  if let some #[ty, n, init] := appOf? e ``Stmt.storageDecl 3 then
    return (← ppDecl (some "storage") ty n init)
  if let some #[ty, n, init] := appOf? e ``Stmt.memoryDecl 3 then
    return (← ppDecl (some "memory") ty n init)
  if let some #[ty, n, init] := appOf? e ``Stmt.storagePlaceAlias 3 then
    return (← ppDecl (some "storage") ty n (← mkAppOptM ``Option.some #[none, init]))
  if let some #[t] := appOf? e ``Stmt.delete 1 then
    let some p ← ppPlace t | return none
    return some (← `(sol_stmt| delete $p:sol_expr))
  if let some #[t] := appOf? e ``Stmt.pop 1 then
    let some p ← ppPlace t | return none
    return some (← `(sol_stmt| $p:sol_expr .pop()))
  if let some #[t, v] := appOf? e ``Stmt.push 2 then
    let some p ← ppPlace t | return none
    let v ← whnf v
    if v.isAppOfArity ``Option.none 1 then
      return some (← `(sol_stmt| $p:sol_expr .push()))
    let some #[_, x] := appOf? v ``Option.some 2 | return none
    let some a ← ppExpr x | return none
    return some (← `(sol_stmt| $p:sol_expr .push($a)))
  if let some #[t, v] := appOf? e ``Stmt.pushAssign 2 then
    let some p ← ppPlace t | return none
    let some a ← ppExpr v | return none
    return some (← `(sol_stmt| $p:sol_expr .push() = $a:sol_expr))
  if let some #[c] := appOf? e ``Stmt.assertStmt 1 then
    let some a ← ppExpr c | return none
    return some (← `(sol_stmt| assert($a)))
  if let some #[c] := appOf? e ``Stmt.requireStmt 1 then
    let some a ← ppExpr c | return none
    return some (← `(sol_stmt| require($a)))
  if let some #[m] := appOf? e ``Stmt.revert 1 then
    unless (← whnf m).isAppOfArity ``Option.none 1 do return none
    return some (← `(sol_stmt| revert()))
  if let some #[to, amt] := appOf? e ``Stmt.transfer 2 then
    let some t ← ppExpr to | return none
    let some a ← ppExpr amt | return none
    return some (← `(sol_stmt| $t:sol_expr .transfer($a)))
  if let some #[op, lhs, rhs] := appOf? e ``Stmt.compoundAssign 3 then
    let some l ← ppPlace lhs | return none
    let some r ← ppExpr rhs | return none
    let op ← whnf op
    if op.isConstOf ``BinOp.add then return some (← `(sol_stmt| $l:sol_expr += $r:sol_expr))
    if op.isConstOf ``BinOp.sub then return some (← `(sol_stmt| $l:sol_expr -= $r:sol_expr))
    if op.isConstOf ``BinOp.mul then return some (← `(sol_stmt| $l:sol_expr *= $r:sol_expr))
    if op.isConstOf ``BinOp.div then return some (← `(sol_stmt| $l:sol_expr /= $r:sol_expr))
    if op.isConstOf ``BinOp.mod then return some (← `(sol_stmt| $l:sol_expr %= $r:sol_expr))
    return none
  if let some #[c, thn, els] := appOf? e ``Stmt.ite 3 then
    let some cs ← ppExpr c | return none
    let some ts ← ppStmts thn | return none
    let some es ← ppStmts els | return none
    return some (← `(sol_stmt| if ($cs) { $ts;* } else { $es;* }))
  if let some #[x] := appOf? e ``Stmt.expr 1 then
    let some a ← ppExpr x | return none
    return some (← `(sol_stmt| $a:sol_expr))
  return none
where
  ppStmts (es : Lean.Expr) : MetaM (Option (Array (TSyntax `sol_stmt))) := do
    let some xs ← listElems? es | return none
    let mut out := #[]
    for x in xs do
      let some st ← ppStmt x | return none
      out := out.push st
    return some out

/-! ## Updates

An elementary update is `lhs := rhs`.  `Rules.writeBack` means the left-hand
side's *spelling* does not survive into the term, so the spellings are built
and checked back: whichever of `n`, `n@T`, `n@@T` reproduces the update is the
one written. -/

/-- Every way a variable named `n` can be spelled, with the term it builds. -/
private def lhsSpellings (n : String) :
    MetaM (Array (Lean.Expr × TSyntax `sol_expr)) := do
  -- `n@T` first: it is the spelling the worked examples use, and a scratch
  -- name that happens to sit in `rootExpr`'s table would otherwise lose its
  -- type annotation.  The bare root and `n@@T` follow.
  let mut out := #[]
  for t in declaredTyNames do
    let ty := mkApp (mkConst ``SoliditySyntax.declTy) (mkStrLit t)
    out := out.push
      (mkAppN (mkConst ``SoliditySyntax.aliasExpr) #[mkStrLit n, ty],
       ← `(sol_expr| $(ident! n):ident@$(ident! t):ident))
  out := out.push (mkApp (mkConst ``SoliditySyntax.rootExpr) (mkStrLit n),
                   ← `(sol_expr| $(ident! n):ident))
  for t in declaredTyNames do
    let ty := mkApp (mkConst ``SoliditySyntax.declTy) (mkStrLit t)
    out := out.push
      (mkAppN (mkConst ``SoliditySyntax.globalExpr) #[mkStrLit n, ty],
       ← `(sol_expr| $(ident! n):ident@@$(ident! t):ident))
  return out

/-- A `Rules.Sym`, as the right-hand side of an update. -/
private def ppSym (e : Lean.Expr) : MetaM (Option (TSyntax `sol_expr)) := do
  let e ← whnf e
  if let some #[x] := appOf? e ``Sym.read 1 then return (← ppExpr x)
  if let some #[x] := appOf? e ``Sym.current 1 then
    let some a ← ppExpr x | return none
    return some (← `(sol_expr| $(ident! "current"):ident($a)))
  if let some #[x] := appOf? e ``Sym.length 1 then
    let some a ← ppExpr x | return none
    return some (← `(sol_expr| $(ident! "length"):ident($a)))
  if let some #[x] := appOf? e ``Sym.netOf 1 then
    let some a ← ppExpr x | return none
    return some (← `(sol_expr| $(ident! "net"):ident($a)))
  if let some #[ty] := appOf? e ``Sym.deflt 1 then
    let some tn ← tyName? ty | return none
    return some (← `(sol_expr| $(ident! "defVal"):ident($(ident! tn):ident)))
  return none

/-- A `save`'s value slot.  A storage source prints as the paper's
`find(storage, q)`, a memory one as `copyMem(mtSt, memory, q)` -- the sorts
KeY's two copy taclets differ in. -/
private def ppStVal (e : Lean.Expr) : MetaM (Option (TSyntax `sol_expr)) := do
  let e ← whnf e
  let st : TSyntax `sol_expr := ← `(sol_expr| $(ident! "storage"):ident)
  let mem : TSyntax `sol_expr := ← `(sol_expr| $(ident! "memory"):ident)
  let mt : TSyntax `sol_expr := ← `(sol_expr| $(ident! "mtSt"):ident)
  if let some #[q] := appOf? e ``StVal.find 1 then
    let some qe ← ppExpr q | return none
    return some (← `(sol_expr| $(ident! "find"):ident($st, $qe)))
  if let some #[q] := appOf? e ``StVal.copyMem 1 then
    let some qe ← ppExpr q | return none
    return some (← `(sol_expr| $(ident! "copyMem"):ident($mt, $mem, $qe)))
  if let some #[v] := appOf? e ``StVal.sym 1 then
    return (← ppSym v)
  if let some #[v] := appOf? e ``StVal.pushed 1 then
    let v ← whnf v
    let some #[_, x] := appOf? v ``Option.some 2 | return none
    return (← ppExpr x)
  return none

/-- A `Rules.StTerm`, printed as the nested writes it is. -/
private partial def ppStTerm (e : Lean.Expr) : MetaM (Option (TSyntax `sol_expr)) := do
  let e ← whnf e
  if e.isConstOf ``StTerm.cur then
    return some (← `(sol_expr| $(ident! "storage"):ident))
  if let some #[t, p, v] := appOf? e ``StTerm.save 3 then
    let some te ← ppStTerm t | return none
    let some pe ← ppExpr p | return none
    let some ve ← ppStVal v | return none
    -- The paper's two names for one write: `store` at a root, `save` at a
    -- path.  A save target that is a *variable* is a global root -- a local
    -- alias is stuck in `locPath` -- so the shape decides it.
    let isRoot := (appOf? (← whnf p) ``Typed.WrappedExpr.var 3).isSome
    if isRoot then
      return some (← `(sol_expr| $(ident! "store"):ident($te, $pe, $ve)))
    return some (← `(sol_expr| $(ident! "save"):ident($te, $pe, $ve)))
  if let some #[t, p] := appOf? e ``StTerm.delAt 2 then
    let some te ← ppStTerm t | return none
    let some pe ← ppExpr p | return none
    return some (← `(sol_expr| $(ident! "delAt"):ident($te, $pe)))
  -- The push and pop writes print in the paper's spelling they were read in.
  if let some #[t, a, n] := appOf? e ``StTerm.setSize 3 then
    let some te ← ppStTerm t | return none
    let some ae ← ppExpr a | return none
    let some ne ← ppSym n | return none
    return some (← `(sol_expr| $(ident! "save"):ident($te, $ae, $ne)))
  if let some #[t, a, v] := appOf? e ``StTerm.pushAt 3 then
    let some te ← ppStTerm t | return none
    let some ae ← ppExpr a | return none
    let v ← whnf v
    if v.isAppOfArity ``Option.none 1 then
      return some (← `(sol_expr| $(ident! "delAt"):ident($te, $ae)))
    let some #[_, x] := appOf? v ``Option.some 2 | return none
    let some xe ← ppStVal x | return none
    return some (← `(sol_expr| $(ident! "save"):ident($te, $ae, $xe)))
  return none

private def ppStorageUpd (e : Lean.Expr) : MetaM (Option (TSyntax `sol_upd)) := do
  let st : TSyntax `sol_expr := ← `(sol_expr| $(ident! "storage"):ident)
  let some te ← ppStTerm e | return none
  return some (← `(sol_upd| $st:sol_expr := $te:sol_expr))

private def ppUpdElem (e : Lean.Expr) : MetaM (Option (TSyntax `sol_upd)) := do
  let e ← whnf e
  if e.isConstOf ``UpdElem.havoc then
    return some (← `(sol_upd| $(ident! "havoc"):ident))
  if let some #[u] := appOf? e ``UpdElem.storage 1 then
    return (← ppStorageUpd u)
  if let some #[to, amt] := appOf? e ``UpdElem.transfer 2 then
    let some t ← ppExpr to | return none
    let some a ← ppExpr amt | return none
    return some (← `(sol_upd| $(ident! "transfer"):ident($t, $a)))
  if let some #[x] := appOf? e ``UpdElem.bumpOf 1 then
    let some a ← ppExpr x | return none
    return some (← `(sol_upd| $(ident! "bump"):ident($a)))
  let some #[nameE, rhs] := appOf? e ``UpdElem.bind 2 | return none
  let some n := strLit? (← whnf nameE) | return none
  let rhs ← whnf rhs
  -- The named right-hand sides keep their spelling, so only the name is
  -- needed; `Rules.varName` of any expression called `n` is `n`.
  let bare : TSyntax `sol_expr := ← `(sol_expr| $(ident! n):ident)
  -- A path alias prints bare: the paper marks the *value* side instead.
  if let some #[p] := appOf? rhs ``BindRhs.path 1 then
    let some pe ← ppExpr p | return none
    return some (← `(sol_upd| $bare:sol_expr := $pe:sol_expr))
  if let some #[p] := appOf? rhs ``BindRhs.mref 1 then
    let some pe ← ppExpr p | return none
    return some (← `(sol_upd| $bare:sol_expr := $(ident! "ref"):ident($pe)))
  if let some #[p] := appOf? rhs ``BindRhs.pushSlot 1 then
    let some pe ← ppExpr p | return none
    return some (← `(sol_upd| $bare:sol_expr := $pe:sol_expr))
  -- A value binding came from `Rules.writeBack`, which ate the left-hand
  -- side's type annotation.  Find the spelling that rebuilds this update.
  let some #[v] := appOf? rhs ``BindRhs.val 1 | return none
  let some ve ← ppSym v | return none
  for (cand, stx) in ← lhsSpellings n do
    let built ← mkAppM ``Rules.writeBack #[cand, v]
    if ← denotes built e then
      return some (← `(sol_upd| $stx:sol_expr := $ve:sol_expr))
  return some (← `(sol_upd| $bare:sol_expr := $ve))

/-! ## Formulas, goals, lines -/

private partial def ppFormula (e : Lean.Expr) : MetaM (Option (TSyntax `sol_formula)) := do
  let e ← whnf e
  if e.isConstOf ``SideFormula.cinv then return some (← `(sol_formula| CInv))
  if let some #[b] := appOf? e ``SideFormula.const 1 then
    let b ← whnf b
    if b.isConstOf ``Bool.true then return some (← `(sol_formula| ⊤))
    if b.isConstOf ``Bool.false then return some (← `(sol_formula| ⊥))
    return none
  if let some #[f] := appOf? e ``SideFormula.neg 1 then
    let some g ← ppFormula f | return none
    return some (← `(sol_formula| ¬$g))
  if let some #[c] := appOf? e ``SideFormula.holds 1 then
    let some a ← ppExpr c | return none
    return some (← `(sol_formula| $a:sol_expr))
  if let some #[c] := appOf? e ``SideFormula.inBounds 1 then
    let some a ← ppExpr c | return none
    return some (← `(sol_formula| $(ident! "inBounds"):ident($a)))
  if let some #[c] := appOf? e ``SideFormula.nonEmpty 1 then
    let some a ← ppExpr c | return none
    return some (← `(sol_formula| $(ident! "nonEmpty"):ident($a)))
  if let some #[c] := appOf? e ``SideFormula.nonZero 1 then
    let some a ← ppExpr c | return none
    return some (← `(sol_formula| $(ident! "nonZero"):ident($a)))
  if let some #[c] := appOf? e ``SideFormula.rhsNonZero 1 then
    let some a ← ppExpr c | return none
    return some (← `(sol_formula| $(ident! "rhsNonZero"):ident($a)))
  if let some #[c] := appOf? e ``SideFormula.funded 1 then
    let some a ← ppExpr c | return none
    return some (← `(sol_formula| $(ident! "funded"):ident($a)))
  return none

/-- One parallel update `{a ‖ b}`. -/
private def ppParUpd (e : Lean.Expr) : MetaM (Option (TSyntax `sol_par_upd)) := do
  let some xs ← listElems? e | return none
  let mut out : Array (TSyntax `sol_upd) := #[]
  for x in xs do
    let some u ← ppUpdElem x | return none
    out := out.push u
  `(sol_par_upd| { $[$out]‖* })

/-- A stack of parallel updates, `{U₁}{U₂}`. -/
private def ppUpdStack (e : Lean.Expr) : MetaM (Option (Array (TSyntax `sol_par_upd))) := do
  let some xs ← listElems? e | return none
  let mut out := #[]
  for x in xs do
    let some u ← ppParUpd x | return none
    out := out.push u
  return some out

/-- The postcondition slot.  The calculus's opaque `φ` is a free variable, and
`(φ)` -- a bare atomic identifier in parentheses -- is exactly the production
`sol_seq_post` reads as a Lean term, so it round-trips. -/
private def ppSeqPost (e : Lean.Expr) : MetaM (Option (TSyntax `sol_seq_post)) := do
  if let .fvar fv := e.consumeMData then
    let n := (← fv.getUserName).eraseMacroScopes
    if n.isAtomic then
      return some (← `(sol_seq_post| ($(mkIdent n))))
    return none
  let some a ← ppExpr e | return none
  return some (← `(sol_seq_post| $a:sol_expr))

private def ppSeqGoal (e : Lean.Expr) : MetaM (Option (TSyntax `sol_seq_goal)) := do
  let e ← whnf e
  if let some #[f] := appOf? e ``SeqGoal.obl 1 then
    let some g ← ppFormula f | return none
    return some (← `(sol_seq_goal| $g:sol_formula))
  let some #[blk, post] := appOf? e ``SeqGoal.prog 2 | return none
  let blk ← whnf blk
  let some #[modeE, stmtsE] := appOf? blk ``SolidityBlock.mk 2 | return none
  let mode ← whnf modeE
  let some xs ← listElems? stmtsE | return none
  let mut ss : Array (TSyntax `sol_stmt) := #[]
  for x in xs do
    let some st ← ppStmt x | return none
    ss := ss.push st
  let some p ← ppSeqPost post | return none
  -- The paper drops the modality once no program is left, and a standalone
  -- line reads that back as the combined one -- so write it that way only
  -- when that is what it is.
  if xs.isEmpty && mode.isConstOf ``SolidityModality.both then
    if let `(sol_seq_post| ($x:ident)) := p then
      return some (← `(sol_seq_goal| ($x:ident)))
  if mode.isConstOf ``SolidityModality.both then
    return some (← `(sol_seq_goal| <[ $ss;* ]> $p:sol_seq_post))
  if mode.isConstOf ``SolidityModality.box then
    return some (← `(sol_seq_goal| [ $ss;* ] $p:sol_seq_post))
  if mode.isConstOf ``SolidityModality.diamond then
    return some (← `(sol_seq_goal| < $ss;* > $p:sol_seq_post))
  return none

/-- One antecedent formula with the update stack it is read under. -/
private def ppAnte (e : Lean.Expr) : MetaM (Option (TSyntax `sol_ante)) := do
  let e ← whnf e
  let some #[_, _, u, f] := appOf? e ``Prod.mk 4 | return none
  let some us ← ppUpdStack u | return none
  let some g ← ppFormula f | return none
  return some (← `(sol_ante| $[$us]* $g:sol_formula))

/-- `Γ => {U₁}…{Uₙ} goal` -- the whole line. -/
def ppLine (e : Lean.Expr) : MetaM (Option (TSyntax `sol_line)) := do
  let e ← whnf e
  let some #[anteE, updsE, goalE] := appOf? e ``Sequent.mk 3 | return none
  let some as ← listElems? anteE | return none
  let mut ante : Array (TSyntax `sol_ante) := #[]
  for a in as do
    let some x ← ppAnte a | return none
    ante := ante.push x
  let some us ← ppUpdStack updsE | return none
  let some g ← ppSeqGoal goalE | return none
  `(sol_line| $[$ante],* => $[$us]* $g:sol_seq_goal)

/-! ## The delaborator -/

open Lean.PrettyPrinter.Delaborator in
/-- Print a `Sequent` as the `seq!` line it was written as.  Anything the walk
cannot account for fails, and Lean's own printer takes over for that line. -/
@[delab app.Solidity.Sequent.mk]
def delabSequent : Delab := do
  unless pp.solidity.seq.get (← getOptions) do failure
  let some line ← ppLine (← SubExpr.getExpr) | failure
  `(seq!{ $line:sol_line })

/-! ## Round-trip tests

`Update/SequentSyntax.lean` ends with a `#check` per production of the grammar.
These are the same lines read the other way: what this module prints for them
has to *denote* what they were written as.  `rfl` is the assertion, so a
regression is a failed proof rather than a whitespace diff -- the printer is
allowed to lay a line out differently, not to mean something else.

The left-hand side of each is the spelling this module emits, transcribed;
the right-hand side is the paper's own.  Where they differ it is because a
surface annotation did not survive into the term (`se@uint` is a
`Rules.writeBack` whose left-hand side is gone by the time the update exists),
and the point of the test is exactly that the two are the same line. -/

section
open Solidity.Examples StandardExample SoliditySyntax
variable (φ : WrappedExpr)

example :
    seq!{ => {se := 10 ‖ sp := alice.account
              ‖ storage := save(storage, alice.account.balance, 10)} (φ) }
      = seq!{ => { se@uint := 10 ‖ sp@Account := alice.account
                   ‖ storage := save(storage, alice.account.balance, 10) } (φ) } := rfl

example : seq!{ => {se := defVal(uint)} <[ alice.age = 10 ]>(φ) }
    = seq!{ => { se@uint := defVal(uint) } <[ alice.age = 10 ]>(φ) } := rfl

/-- A line with nothing left to execute prints without its modality, the way
the paper draws it; a standalone line reads that back as the combined one. -/
example : seq!{ => (φ) } = seq!{ => <[ ]> ‹φ› } := rfl

/-- Guards print as the formulas they are, under the stack they are read
under. -/
example : seq!{ inBounds(values[i]), ¬nonEmpty(values) => (φ) }
    = seq!{ inBounds(values[i]), ¬nonEmpty(values) => <[ ]> ‹φ› } := rfl

example : seq!{ {storage := save(storage, pv@uint, 3)} funded(pv@uint)
                => {storage := save(storage, pv@uint, 3)} (φ) }
    = seq!{ { pv@uint := 3 } funded(pv@uint) => { pv@uint := 3 } <[ ]> ‹φ› } := rfl

/-- The box and diamond modalities keep their brackets, since a program is
still there to draw them around. -/
example : seq!{ => [ alice.age = ageVal ](φ) }
    = seq!{ ⟹ [ alice.age = ageVal ] ‹φ› } := rfl

example : seq!{ => < result = alice.age >(result == 0) }
    = seq!{ ⟹ < result = alice.age > (result == 0) } := rfl

example : seq!{ => {storage := save(storage, alice.account, find(storage, bob.account))} (φ) }
    = seq!{ ⟹ { storage := save(storage, alice.account, find(storage, bob.account)) } <[ ]> ‹φ› } := rfl

example : seq!{ => {storage := save(save(storage, values[values.length], 42), values.length, values.length + 1)} (φ) }
    = seq!{ ⟹ { storage := save(save(storage, values[values.length], 42), values.length, values.length + 1) } <[ ]> ‹φ› } := rfl

example : seq!{ => {sp := values.push()} (φ) }
    = seq!{ ⟹ { sp@UintArray := values.push() } <[ ]> ‹φ› } := rfl

example : seq!{ => {v := length(values)} (φ) }
    = seq!{ ⟹ { v := length(values) } <[ ]> ‹φ› } := rfl

/-- And the derivation this was written for: the frontier `deepFieldWrite`
stands at after two steps (`Examples/Derivations/StorageSteps.lean`). -/
example : seq!{ => {se := defVal(uint)}
                   <[ se@uint = 10; Account storage sp = alice.account;
                      sp@Account.balance = se@uint ]>(φ) }
    = seq!{ => { se@uint := defVal(uint) }
              <[ se@uint = 10; Account storage sp = alice.account;
                 sp@Account.balance = se@uint ]>(φ) } := rfl

end

end Solidity.SequentPP
