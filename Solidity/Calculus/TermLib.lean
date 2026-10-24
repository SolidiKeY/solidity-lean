import Solidity.Calculus.TermLib.Rules
import Solidity.Calculus.PrintTerm

/-!
# Term taclets on scoped terms, printed

The term taclets, their side conditions and their soundness are
`Calculus/TermLib/Rules.lean`'s, in the core; this module adds what reads
them back, above it (`docs/parallelism.md`).  A scoped term over schema
variables prints back as `tm{ … }` through the scoped term printers
(`delabTmS`, `Delab.ppTermS`), and the rules, stated over the `Tms`
symbols, print so.
-/

namespace Solidity

open Semantics
open Theory (lengthSeg)
open Solidity (Srt Op0 Op1 Op2 Op3)

variable {C : Contract}

/-! ### Printing a scoped term as `tm{ … }` -/

section Print
open Lean Meta PrettyPrinter Delaborator SubExpr

/-- Whether `n` is a scoped term symbol a rule line writes (`Tms.Term.find`,
`Tm.lit`, …): an abbreviation of a constructor application (`Tm.app2
Op2.find …`).  `Tm.bumped` is no symbol: it computes, so the printers
read it whole (`t⊕⊕`), its operand unfolded. -/
def isTmsSym (n : Lean.Name) : Bool :=
  n == ``Tm.lit || n == ``Tm.storage || n == ``Tm.memory ||
    ((`Solidity.Tms).isPrefixOf n && n != ``Tms.Term.bumped)

/-- A scoped term with its symbols (`isTmsSym`) unfolded to the constructor
applications they abbreviate, down through the terms it is applied to: what
the scoped printers read of a term they do not compute (`viewTmS`,
`pp.sol.reduce false`).  Anything else (a variable, `K.fill t`) is left as
it is. -/
partial def unfoldTmsSyms (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← instantiateMVars e
  let .const n _ := e.getAppFn | return e
  if isTmsSym n then
    match ← unfoldDefinition? e with
    | some e' => return ← unfoldTmsSyms (← whnfCore e')
    | none => return e
  let terms : List Nat :=
    if n == ``Tm.netOf then [3] else if n == ``Tm.bumped || n == ``Tms.Term.bumped then [5]
    else if n == ``Tm.app1 then [5]
    else if n == ``Tm.app2 then [6, 7] else if n == ``Tm.app3 then [7, 8, 9] else []
  let mut args := e.getAppArgs
  for i in terms do
    if h : i < args.size then args := args.set i (← unfoldTmsSyms args[i])
  return mkAppN e.getAppFn args

/-- Whether `ty` is a contract or a context: no schema variable of a term. -/
def isContractOrCtx (ty : Lean.Expr) : MetaM Bool := do
  let ty ← whnfR ty
  return ty.isConstOf ``Contract || (ty.isAppOfArity ``List 1 && (ty.getArg! 0).isConstOf ``LTy)

/-- The sort a family of scoped term symbols is at (`Tms.STerm` ↦ `.st`). -/
def tmsFamilySort? : Lean.Name → Option Lean.Name
  | `Term => some ``Srt.val
  | `PTerm => some ``Srt.path
  | `STerm => some ``Srt.st
  | `SValT => some ``Srt.sv
  | `ITerm => some ``Srt.ident
  | `MAddr => some ``Srt.addr
  | `MTerm => some ``Srt.mem
  | `MValT => some ``Srt.mv
  | _ => none

/-- A scoped term symbol inside a `‹…›` of `tm{ … }` (`pp.sol.tmField`):
`Tms.STerm.save s p v` as `s.save p v`, its first explicit argument the
receiver when that is a term of the family's sort, else `STerm.save s p v`. -/
def delabTmsField : Delab := do
  unless pp.sol.tmField.get (← getOptions) do failure
  let e ← getExpr
  let .const n _ := e.getAppFn | failure
  let [`Solidity, `Tms, fam, f] := n.components | failure
  let some srt := tmsFamilySort? fam | failure
  let args := e.getAppArgs
  guard (args.size == (← getConstInfo n).type.getNumHeadForalls)
  let bis ← forallTelescope (← inferType e.getAppFn) fun xs _ => xs.mapM fun x => x.fvarId!.getBinderInfo
  let expl := (List.range args.size).filter fun i => bis[i]! == .default
  let some i₀ := expl.head? | failure
  let stxs ← expl.toArray.mapM fun i => withNaryArg i delab
  let recv? ← do
    let ty ← whnfR (← inferType args[i₀]!)
    let_expr Solidity.Tm _ _ s := ty | pure false
    pure ((← whnf s).getAppFn.isConstOf srt)
  if recv? then
    let rest := stxs.extract 1 stxs.size
    let fld : Lean.Term ← `($(stxs[0]!).$(mkIdent f):ident)
    if rest.isEmpty then return fld
    `($fld $rest*)
  else
    `($(mkIdent (fam ++ f)) $stxs*)

/-- A scoped term over schema variables, as `tm{ t }`: printed by the
scoped term printers (`Delab.ppTermS`, `Calculus/PrintTerm.lean`) as
written (`pp.sol.reduce false`, its symbols unfolded, `unfoldTmsSyms`), a
schema variable by its name, and only up to `tmCutoff` nodes. -/
def delabTmS : Delab := do
  unless ← ppOn do return ← delabTmsField
  let e ← getExpr
  let some c := e.getAppFn.constName? | failure
  guard (e.getAppNumArgs == (← getConstInfo c).type.getNumHeadForalls)
  guard (sizeAtMost tmCutoff e)
  let e' ← instantiateMVars e
  guard e'.hasFVar
  let fvs := (collectFVars {} e').fvarIds
  guard (← fvs.anyM fun fv => return !(← isContractOrCtx (← fv.getType)))
  let_expr Solidity.Tm _ _ s := (← whnfR (← inferType e)) | failure
  let some srt := (← whnf s).getAppFn.constName? | failure
  let printer : Lean.Expr → MetaM (TSyntax `dl_term) ← match srt with
    | ``Srt.val => pure (Delab.ppTermS [])
    | ``Srt.path | ``Srt.spath => pure (Delab.ppPTermS [])
    | ``Srt.st | ``Srt.sts => pure (Delab.ppSTermS [])
    | ``Srt.sv => pure (Delab.ppSValS [])
    | ``Srt.ident => pure (Delab.ppITermS [])
    | ``Srt.addr => pure (Delab.ppMAddrS [])
    | ``Srt.mem => pure (Delab.ppMTermS [])
    | ``Srt.mv => pure (Delab.ppMValS [])
    | ``Srt.kint => pure (Delab.ppTermS [])
    | _ => failure
  let t ← withOptions (fun o => pp.sol.tmField.set (pp.sol.reduce.set o false) true)
    (printer (← unfoldTmsSyms e'))
  guard !(isEscape t)
  `(tm{ $t })

/-- A closed scoped term as `tm{ t }`, where `pp.sol.closedTm` asks (a law's
side condition, `lawAt`): read as the closer's terms are (`pp.sol.reduce`),
an escape refused. -/
def delabTmClosed : Delab := do
  unless pp.sol.closedTm.get (← getOptions) do failure
  let e ← instantiateMVars (← getExpr)
  let some c := e.getAppFn.constName? | failure
  guard (e.getAppNumArgs == (← getConstInfo c).type.getNumHeadForalls)
  guard (sizeAtMost tmCutoff e)
  let_expr Solidity.Tm _ _ s := (← whnfR (← inferType e)) | failure
  let some srt := (← whnf s).getAppFn.constName? | failure
  let printer : Lean.Expr → MetaM (TSyntax `dl_term) ← match srt with
    | ``Srt.val | ``Srt.kint => pure (Delab.ppTermS [])
    | ``Srt.path | ``Srt.spath => pure (Delab.ppPTermS [])
    | ``Srt.st | ``Srt.sts => pure (Delab.ppSTermS [])
    | ``Srt.sv => pure (Delab.ppSValS [])
    | _ => failure
  let t ← withOptions (fun o => pp.sol.reduce.set o true) (printer e)
  guard !(isEscape t)
  `(tm{ $t })

attribute [delab app.Solidity.Tm.app0, delab app.Solidity.Tm.app1, delab app.Solidity.Tm.app2,
  delab app.Solidity.Tm.app3] delabTmClosed

attribute [delab app.Solidity.Tms.Term.lit, delab app.Solidity.Tms.Term.binop,
  delab app.Solidity.Tms.Term.unop, delab app.Solidity.Tms.Term.find,
  delab app.Solidity.Tms.Term.len, delab app.Solidity.Tms.Term.read,
  delab app.Solidity.Tms.Term.mlen, delab app.Solidity.Tms.Term.env,
  delab app.Solidity.Tms.Term.net, delab app.Solidity.Tms.Term.delValue,
  delab app.Solidity.Tms.Term.bumped,
  delab app.Solidity.Tms.PTerm.root, delab app.Solidity.Tms.PTerm.field,
  delab app.Solidity.Tms.PTerm.at, delab app.Solidity.Tms.PTerm.next,
  delab app.Solidity.Tms.STerm.storage, delab app.Solidity.Tms.STerm.save,
  delab app.Solidity.Tms.STerm.delAt, delab app.Solidity.Tms.STerm.push,
  delab app.Solidity.Tms.STerm.pushSlot, delab app.Solidity.Tms.STerm.pop,
  delab app.Solidity.Tms.STerm.shrink, delab app.Solidity.Tms.STerm.extend,
  delab app.Solidity.Tms.STerm.select,
  delab app.Solidity.Tms.SValT.val, delab app.Solidity.Tms.SValT.find,
  delab app.Solidity.Tms.SValT.copyMem, delab app.Solidity.Tms.SValT.newArr,
  delab app.Solidity.Tms.ITerm.read, delab app.Solidity.Tms.ITerm.alloc,
  delab app.Solidity.Tms.ITerm.copy, delab app.Solidity.Tms.MAddr.field,
  delab app.Solidity.Tms.MAddr.at,
  delab app.Solidity.Tms.MTerm.memory, delab app.Solidity.Tms.MTerm.write,
  delab app.Solidity.Tms.MTerm.addM, delab app.Solidity.Tms.MTerm.copySt,
  delab app.Solidity.Tms.MValT.val, delab app.Solidity.Tms.MValT.ref] delabTmS

end Print

/-! ## Pins -/

section Pins

section Printed

variable {Γ : Ctx}

/- `tm{ … }` writes a scoped rule and prints it back as it was written; an
escape's term prints as the closer's does. -/
/--
info: @TermTaclet.findOnSave : ∀ {C : Contract} {Γ : Ctx} {s : Tm C Γ Srt.st} {P : PrimTy}
  {p q : Tm C Γ (Srt.path (Ty.prim P))} {v : P.Denote},
  autoParam (p.hasSeg = true) _auto✝ →
    autoParam (p.sameSegs q = true) _auto✝¹ → TermTaclet tm{ find(save(s, p, lit(v)), q) } tm{ lit(v) }
-/
#guard_msgs in
#check @TermTaclet.findOnSave

/--
info: @TermTaclet.findOnPushFrame : ∀ {C : Contract} {Γ : Ctx} {s : Tm C Γ Srt.st} {E : Ty}
  {p : Tm C Γ (Srt.path (Ty.ref (RefTy.array E)))} {v : Tm C Γ (Srt.sv E)} {P : PrimTy}
  {q : Tm C Γ (Srt.path (Ty.prim P))},
  autoParam (p.diverges q = true) _auto✝ →
    TermTaclet tm{ find(save(save(s, p[p.length], v), p.length, p.length + 1), q) } tm{ find(s, q) }
-/
#guard_msgs in
#check @TermTaclet.findOnPushFrame

/--
info: @TermTaclet.selectOnSaveMemberIn : ∀ {C : Contract} {Γ : Ctx} {s : Tm C Γ Srt.st} {T : Ty} {p : Tm C Γ (Srt.path T)}
  {v : Tm C Γ (Srt.sv T)} {r sn : Name} {hr : C.rootType r = some (Ty.ref (RefTy.struct sn))}
  {p' : Tm C Γ (Srt.spath sn T)} {sn₁ : Name} (K : SCtxS C Γ sn sn₁) {P : PrimTy}
  {q : Tm C Γ (Srt.spath sn₁ (Ty.prim P))},
  autoParam (p.shift? = some { r := r, sn := sn, h := hr, p := p' }) _auto✝ →
    TermTaclet (Tm.app2 Op2.findIn (K.fill tm{ select(save(s, p, v), r) }) q)
      (Tm.app2 Op2.findIn (K.fill (Tm.app3 Op3.saveIn tm{ select(s, r) } p' v)) q)
-/
#guard_msgs in
#check @TermTaclet.selectOnSaveMemberIn

/-- `t⊕⊕` prints with its operand's symbols unfolded (W9.6 review). -/
theorem bumped_pin (op : IncDec) (hp : PrimTy.uint.isNumeric = true) (s : Tm C Γ .st)
    (q : Tm C Γ (.path (.prim .uint))) :
    (tm{ find(s, q)⊕⊕ + 1 } : Tm C Γ (.val .uint)) = tm{ find(s, q)⊕⊕ + 1 } := rfl

/--
info: Solidity.bumped_pin {C : Contract} {Γ : Ctx} (op : IncDec) (hp : PrimTy.uint.isNumeric = true) (s : Tm C Γ Srt.st)
  (q : Tm C Γ (Srt.path (Ty.prim PrimTy.uint))) : tm{ find(s, q)⊕⊕ + 1 } = tm{ find(s, q)⊕⊕ + 1 }
-/
#guard_msgs in
#check bumped_pin

end Printed

/-- `bob.age`. -/
private def bobAge : Tm StandardExample [] (.path (.prim .uint)) :=
  .app1 (.field (s := "Person") (f := "age") rfl) (.app0 (.root "bob" rfl))

/-- The side conditions close by `rfl` on closed paths. -/
example (s : Tm StandardExample [] .st) (v : Tm StandardExample [] (.sv (.prim .uint))) :
    TermTaclet (Tms.Term.find (Tms.STerm.save s Tm.aliceAge v) bobAge)
      (Tms.Term.find s bobAge) :=
  .findOnSaveFrame

example (s : Tm StandardExample [] .st) :
    TermTaclet (Tms.Term.find (Tms.STerm.save s Tm.aliceAge (Tms.SValT.val (Tms.Term.lit ⟨7, rfl⟩)))
      Tm.aliceAge) (Tms.Term.lit ⟨7, rfl⟩) :=
  .findOnSave

/-- `findMemberCons` reads `alice.age` from its head. -/
example (s : Tm StandardExample [] .st) :
    TermTaclet (Tms.Term.find s Tm.aliceAge)
      (.app2 .findIn (Tms.STerm.select s "alice" rfl) (.app0 (.member "Person" "age" rfl))) :=
  .findMemberCons

/-- The recursors reduce in the kernel. -/
example : (Tm.aliceAge.shift?).isSome = true := by decide +kernel

end Pins

end Solidity
