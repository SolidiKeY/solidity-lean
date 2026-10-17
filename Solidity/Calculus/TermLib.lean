import Solidity.Calculus.Logic
import Solidity.Calculus.TermEq
import Solidity.Calculus.Rules
import Solidity.Calculus.StateFacts
import Solidity.Calculus.PrintTerm

/-!
# Term taclets on scoped terms

The Theory's rules on terms, KeY's term taclets, stated on the
scoped terms `Tm C Γ (.val P)` (`Calculus/Fml.lean`), with what they need:
the side conditions read off a scoped path.  The Theory equality of two
terms (`Tm.Theq`) and the term functions a closer compares terms with
(`Tm.beqR`, `Tm.litVarsS`) are `Calculus/TermEq.lean`'s.  Soundness is over
the scoped `Tm.denote` (`Calculus/Lands.lean`).

**Typed sorts** (W9.8.3c).  A path is at its type, so a law reads a word
at the type it is written at: `findOnSave`'s `v` is a `P.Denote`, a
delete's default `defVal(P)`.  `select(s, r)` is a storage of the members
of `r`'s struct and its paths are member paths (`findIn`, `saveIn`,
`delAtIn`, `Tm.shift?`), and an array's push and pop are their symbols
(`push`, `pop`), the typed signature having no write to `p.length`.

**Notation.** `tm{ … }` writes the scoped term: the text is read as a rule
line reads a term (`RuleSyntax.schemaTerm`), its symbols the scoped ones
(`Tms`, `Calculus/Rules.lean`; `RuleSyntax.coreNames`).  A scoped term over
schema variables prints back as `tm{ … }` through the scoped term printers
(`delabTmS`, `Delab.ppTermS`).  The rules are stated over the `Tms`
symbols, which print so.

`holds_eqD_iffS` is in `Calculus/SoundLoops.lean`, with the term bridge
`Tm.denote_eval` (`Calculus/Lands.lean`).
-/

namespace Solidity

open Semantics
open Theory (lengthSeg)
open Solidity (Srt Op0 Op1 Op2 Op3)

variable {C : Contract}

/-! ## `tm{ … }` at a scoped term type -/

section Notation
open Lean Elab Term Meta

/-- `tm{ t }`, the scoped term `Tm C Γ s`. -/
syntax (name := tmAt) "tm_at% " dl_term : term

macro_rules
  | `(tm{ $t:dl_term }) => `(tm_at% $t)

/-- `tm{ t }` read as the scoped term: the text read as a rule line reads a
term (`RuleSyntax.schemaTerm`), its symbols the scoped ones (`Tms`,
`RuleSyntax.coreNames`), elaborated once its expected type is known. -/
@[term_elab tmAt] def elabTmAt : TermElab := fun stx expectedType? => do
  let t : TSyntax `dl_term := ⟨stx[1]⟩
  match expectedType? with
  | some ety => if (← instantiateMVars ety).getAppFn.isMVar then tryPostpone
  | none => tryPostpone
  let out ← liftMacroM (coreNames (← liftMacroM (schemaTerm rawScope (tmSort t) t)))
  withMacroExpansion stx out (elabTerm out expectedType?)

end Notation

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

/-! ## The side conditions, on scoped paths

The term taclets', read off a scoped path: the syntactic forms
of the Theory's `p ≠ []`, `diverges p q`, `p = q` and `q = p ++ r`.  The
shapes are `SegT`'s.  A path is at its type (`Tm C Γ (.path T)`); two paths
compared may be at two types, the Theory reading their segments alone. -/

section Side

variable {Γ : Ctx}

/-! The functions on terms are generic in the sort, by `match` on the term
alone, and read a symbol by a `match` on the symbol alone (`Op1.shapeStep`
…), whose sorts are variables: a pattern nesting a symbol under a term of
a fixed sort compiles to casts its equations and `rfl` cannot see
through. -/

/-- The path is never empty: anything but a bare alias. -/
def Tm.hasSeg {u : Srt} : Tm C Γ u → Bool
  | .pvP _ => false
  | _ => true

/-- A literal, at its type. -/
def Op0.litW? {s : Srt} : Op0 C s → Option ((p : PrimTy) × p.Denote)
  | .lit v => some ⟨_, v⟩
  | _ => none

/-- A literal term, at its type. -/
def Tm.litW? {u : Srt} : Tm C Γ u → Option ((p : PrimTy) × p.Denote)
  | .app0 o => o.litW?
  | _ => none

/-- A root's segment. -/
def Op0.shapeLeaf? {s : Srt} : Op0 C s → Option (List SegT)
  | .root r _ => some [.root r]
  | .member _ f _ => some [.root f]
  | _ => none

/-- An index's shape, by how the reference is indexed: a mapping's key, an
array's index, at the literal it is (`some`) or not. -/
def IndexTy.segT {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V)
    (w : Option ((K : PrimTy) × K.Denote)) : SegT :=
  @IndexTy.casesOn (fun _ _ _ _ => SegT) R k V it (fun {_} {_} => .key w)
    (fun {_} {_} _ => .idx w)

/-- A member or an element after a path's shape. -/
def Op1.shapeStep {a s : Srt} : Op1 C a s → Option (List SegT) → Option (List SegT)
  | .field (f := f) _, ih => ih.map (· ++ [.field f])
  | .fieldIn (f := f) _, ih => ih.map (· ++ [.field f])
  | .next, ih => ih.map (· ++ [.idx none])
  | _, _ => none

/-- An element after a path's shape, at a literal index or not. -/
def Op2.shapeStep {a b s : Srt} : Op2 C a b s → Tm C Γ b → Option (List SegT) →
    Option (List SegT) → Option (List SegT)
  | .at it, i, ihx, _ => ihx.map (· ++ [it.segT i.litW?])
  | .nextIn, _, _, ihy => ihy.map (· ++ [.idx none])
  | _, _, _, _ => none

/-- A checked element after a path's shape. -/
def Op3.shapeStep {a b c s : Srt} : Op3 C a b c s → Tm C Γ c → Option (List SegT) →
    Option (List SegT)
  | .atIn it, i, ihy => ihy.map (· ++ [it.segT i.litW?])
  | _, _, _ => none

/-- A path's shape, read off its syntax: `none` through an alias.  Generic
in the sort. -/
def Tm.shape? : {u : Srt} → Tm C Γ u → Option (List SegT)
  | _, .app0 o => o.shapeLeaf?
  | _, .app1 o x => o.shapeStep x.shape?
  | _, .app2 o x y => o.shapeStep y x.shape? y.shape?
  | _, .app3 o _ y z => o.shapeStep z y.shape?
  | _, _ => none

/-- The two paths leave each other. -/
def Tm.diverges {T U : Ty} (p : Tm C Γ (.path T)) (q : Tm C Γ (.path U)) : Bool :=
  match p.shape?, q.shape? with
  | some a, some b => SegT.diverges a b
  | _, _ => false

/-- `q` leaves `p.length`. -/
def Tm.divergesLen {T U : Ty} (q : Tm C Γ (.path T)) (p : Tm C Γ (.path U)) : Bool :=
  match q.shape?, p.shape? with
  | some a, some b => SegT.diverges a (b ++ [.len])
  | _, _ => false

/-- A member or an element, its path's checks erased. -/
def Op1.eraseStep {a s : Srt} : Op1 C a s → Tm C Γ a → Tm C Γ a → Tm C Γ s
  | .field h, _, x' => .app1 (.field h) x'
  | .next, _, x' => .app1 .next x'
  | o, x, _ => .app1 o x

/-- An element, its path's checks erased. -/
def Op2.eraseStep {a b s : Srt} : Op2 C a b s → Tm C Γ a → Tm C Γ b → Tm C Γ a → Tm C Γ b →
    Tm C Γ s
  | .at it, _, y, x', _ => .app2 (.at it) x' y
  | .nextIn, x, _, _, y' => .app2 .nextIn x y'
  | o, x, y, _, _ => .app2 o x y

/-- A checked element, its check erased. -/
def Op3.eraseStep {a b c s : Srt} : Op3 C a b c s → Tm C Γ a → Tm C Γ b → Tm C Γ c → Tm C Γ b →
    Tm C Γ s
  | .atIn it, _, _, z, y' => .app2 (.at it) y' z
  | o, x, y, z, _ => .app3 o x y z

/-- The path its checks aside: `p[i]@S` is `p[i]`.  Generic in the sort. -/
def Tm.eraseChecks : {u : Srt} → Tm C Γ u → Tm C Γ u
  | _, .app1 o x => o.eraseStep x x.eraseChecks
  | _, .app2 o x y => o.eraseStep x y x.eraseChecks y.eraseChecks
  | _, .app3 o x y z => o.eraseStep x y z y.eraseChecks
  | _, p => p

/-- The two paths have the same segments in every state, their checks aside
compared by `Tm.beqR` (and so their types). -/
def Tm.sameSegs {T U : Ty} (p : Tm C Γ (.path T)) (q : Tm C Γ (.path U)) : Bool :=
  p.eraseChecks.beqR q.eraseChecks

theorem Tm.sameSegs_refl {T : Ty} (p : Tm C Γ (.path T)) : p.sameSegs p = true := Tm.beqR_self _

/-- `f` of the path a member is of, or on the way down from it. -/
def Op1.extStep (f : {T : Ty} → Tm C Γ (.path T) → Bool) {a s : Srt} :
    Op1 C a s → Tm C Γ a → Bool → Bool
  | .field _, x, ih => f x || ih
  | _, _, _ => false

/-- `f` of the path an element is of, or on the way down from it. -/
def Op2.extStep (f : {T : Ty} → Tm C Γ (.path T) → Bool) {a b s : Srt} :
    Op2 C a b s → Tm C Γ a → Bool → Bool
  | .at _, x, ih => f x || ih
  | _, _, _ => false

/-- `f` of the path a checked element is of, or on the way down from it. -/
def Op3.extStep (f : {T : Ty} → Tm C Γ (.path T) → Bool) {a b c s : Srt} :
    Op3 C a b c s → Tm C Γ b → Bool → Bool
  | .atIn _, y, ih => f y || ih
  | _, _, _ => false

/-- `f` of some path on the way down to `t`'s root.  Generic in the sort. -/
def Tm.extendsAny (f : {T : Ty} → Tm C Γ (.path T) → Bool) : {u : Srt} → Tm C Γ u → Bool
  | _, .app1 o x => o.extStep f x (x.extendsAny f)
  | _, .app2 o x _ => o.extStep f x (x.extendsAny f)
  | _, .app3 o _ y _ => o.extStep f y (y.extendsAny f)
  | _, _ => false

/-- `q` goes on below `p`. -/
def Tm.extends {T U : Ty} (q : Tm C Γ (.path T)) (p : Tm C Γ (.path U)) : Bool :=
  q.extendsAny (·.beqR p)

/-- A path read from its head: the root `r` (a struct `sn`), and the rest,
a path in the frame of `sn` (`select(s, r)`'s members, solkey's
`findMemberCons`). -/
structure Shifted (C : Contract) (Γ : Ctx) (T : Ty) where
  r : Name
  sn : Name
  h : C.rootType r = some (.ref (.struct sn))
  p : Tm C Γ (.spath sn T)

/-- What `Tm.shift?` gives at a sort: a path's head and rest. -/
@[reducible] def Srt.ShiftD (C : Contract) (Γ : Ctx) : Srt → Type
  | .path T => Shifted C Γ T
  | _ => PUnit

/-- What `Tm.rootOf?` gives at a sort: a root and its type's proof. -/
@[reducible] def Srt.RootOf (C : Contract) : Srt → Type
  | .path T => (r : Name) ×' C.rootType r = some T
  | _ => PUnit

/-- A root, with its type's proof. -/
def Op0.rootOf? {s : Srt} : Op0 C s → Option (s.RootOf C)
  | .root r h => some ⟨r, h⟩
  | _ => none

/-- The state variable a path is, if it is one alone. -/
def Tm.rootOf? {u : Srt} : Tm C Γ u → Option (u.RootOf C)
  | .app0 o => o.rootOf?
  | _ => none

/-- A member after a path, read from its head. -/
def Op1.shiftStep {a s : Srt} : Op1 C a s → Tm C Γ a → Option (a.ShiftD C Γ) →
    Option (s.ShiftD C Γ)
  | .field (s := sn) (f := f) hf, x, ih => match x.rootOf? with
    | some ⟨r, hr⟩ => some ⟨r, sn, hr, .app0 (.member sn f hf)⟩
    | none => ih.map fun sh => ⟨sh.r, sh.sn, sh.h, .app1 (.fieldIn hf) sh.p⟩
  | _, _, _ => none

/-- A path of members read from its head (`alice.account.balance` as
`alice` and `account.balance` under it).  An index under a `select` has no
typed symbol (`docs/intrinsic.md`, W9.8.2), so a path through one is not
shifted. -/
def Tm.shift? : {u : Srt} → Tm C Γ u → Option (u.ShiftD C Γ)
  | _, .app1 o x => o.shiftStep x x.shift?
  | _, _ => none

/-- A member path read from its head under a `select`: the member `f` (a
struct `sn`), and the rest, a member path in the frame of `sn` (solkey's
`findMemberCons` in a storage of members). -/
structure ShiftedIn (C : Contract) (Γ : Ctx) (s : Name) (T : Ty) where
  f : Name
  sn : Name
  h : C.fieldType s f = some (.ref (.struct sn))
  p : Tm C Γ (.spath sn T)

/-- What `Tm.shiftIn?` gives at a sort: a member path's head and rest. -/
@[reducible] def Srt.ShiftInD (C : Contract) (Γ : Ctx) : Srt → Type
  | .spath s T => ShiftedIn C Γ s T
  | _ => PUnit

/-- What `Tm.memberOf?` gives at a sort: a member and its type's proof. -/
@[reducible] def Srt.MemberOf (C : Contract) : Srt → Type
  | .spath s T => (f : Name) ×' C.fieldType s f = some T
  | _ => PUnit

/-- A member, with its type's proof. -/
def Op0.memberOf? {s : Srt} : Op0 C s → Option (s.MemberOf C)
  | .member _ f h => some ⟨f, h⟩
  | _ => none

/-- The member a member path is, if it is one alone. -/
def Tm.memberOf? {u : Srt} : Tm C Γ u → Option (u.MemberOf C)
  | .app0 o => o.memberOf?
  | _ => none

/-- A member after a member path, read from its head. -/
def Op1.shiftInStep {a s : Srt} : Op1 C a s → Tm C Γ a → Option (a.ShiftInD C Γ) →
    Option (s.ShiftInD C Γ)
  | .fieldIn (s' := sn') (f := g) hg, x, ih => match x.memberOf? with
    | some ⟨f, hf⟩ => some ⟨f, sn', hf, .app0 (.member sn' g hg)⟩
    | none => ih.map fun sh => ⟨sh.f, sh.sn, sh.h, .app1 (.fieldIn hg) sh.p⟩
  | _, _, _ => none

/-- A member path read from its head (`account.balance` under `select(s,
alice)` as `account` and `balance` under it). -/
def Tm.shiftIn? : {u : Srt} → Tm C Γ u → Option (u.ShiftInD C Γ)
  | _, .app1 o x => o.shiftInStep x x.shiftIn?
  | _, _ => none

/-- A written value's word. -/
def Op1.svStep {a s : Srt} : Op1 C a s → Tm C Γ a → Option ((p : PrimTy) × p.Denote)
  | .sval, x => x.litW?
  | _, _ => none

/-- The word a written value is, at its type, if it is a literal. -/
def Tm.svLit? {u : Srt} : Tm C Γ u → Option ((p : PrimTy) × p.Denote)
  | .app1 o x => o.svStep x
  | _ => none

/-- A save's word where it writes the path, past it where it leaves it. -/
def Op3.findStep (eq div : {T : Ty} → Tm C Γ (.path T) → Bool) {a b c s : Srt} :
    Op3 C a b c s → Tm C Γ b → Tm C Γ c → Option ((p : PrimTy) × p.Denote) →
      Option ((p : PrimTy) × p.Denote)
  | .save, y, z, ih => if eq y then z.svLit? else if div y then ih else none
  | _, _, _, _ => none

/-- The word a storage term reads at a path, read off its writes.  Generic
in the sort. -/
def Tm.findLitBy (eq div : {T : Ty} → Tm C Γ (.path T) → Bool) :
    {u : Srt} → Tm C Γ u → Option ((p : PrimTy) × p.Denote)
  | _, .app3 o x y z => o.findStep eq div y z (x.findLitBy eq div)
  | _, _ => none

/-- The word `s` reads at `q`, read off its writes. -/
def Tm.findLit? {P : PrimTy} (s : Tm C Γ .st) (q : Tm C Γ (.path (.prim P))) :
    Option P.Denote :=
  if q.hasSeg then
    (s.findLitBy (·.sameSegs q) (·.diverges q)).bind fun w =>
      if h : w.1 = P then some (h ▸ w.2) else none
  else none

/-- The two paths, of any sorts, leave each other: `Tm.diverges` for two
member paths under a `select`. -/
def Tm.divergesU {u v : Srt} (p : Tm C Γ u) (q : Tm C Γ v) : Bool :=
  match p.shape?, q.shape? with
  | some a, some b => SegT.diverges a b
  | _, _ => false

/-- A member-wise save's word where it writes the path, past it where it
leaves it. -/
def Op3.findStepIn (eq div : {u : Srt} → Tm C Γ u → Bool) {a b c s : Srt} :
    Op3 C a b c s → Tm C Γ b → Tm C Γ c → Option ((p : PrimTy) × p.Denote) →
      Option ((p : PrimTy) × p.Denote)
  | .saveIn, y, z, ih => if eq y then z.svLit? else if div y then ih else none
  | _, _, _, _ => none

/-- The word a storage of members reads at a path, read off its writes.
Generic in the sort. -/
def Tm.findLitInBy (eq div : {u : Srt} → Tm C Γ u → Bool) :
    {u : Srt} → Tm C Γ u → Option ((p : PrimTy) × p.Denote)
  | _, .app3 o x y z => o.findStepIn eq div y z (x.findLitInBy eq div)
  | _, _ => none

/-- The word the storage of members `s` reads at the member path `q`, read
off its writes (`Tm.findLit?` under a `select`). -/
def Tm.findLitIn? {sn : Name} {P : PrimTy} (s : Tm C Γ (.sts sn))
    (q : Tm C Γ (.spath sn (.prim P))) : Option P.Denote :=
  (s.findLitInBy (·.beqR q) (·.divergesU q)).bind fun w =>
    if h : w.1 = P then some (h ▸ w.2) else none

/-- `f` of the member path a member is of, or on the way down from it. -/
def Op1.extStepIn (f : {u : Srt} → Tm C Γ u → Bool) {a s : Srt} :
    Op1 C a s → Tm C Γ a → Bool → Bool
  | .fieldIn _, x, ih => f x || ih
  | _, _, _ => false

/-- `f` of some member path on the way down to `t`'s member.  Generic in
the sort. -/
def Tm.extendsAnyIn (f : {u : Srt} → Tm C Γ u → Bool) : {u : Srt} → Tm C Γ u → Bool
  | _, .app1 o x => o.extStepIn f x (x.extendsAnyIn f)
  | _, _ => false

/-- `q` goes on below `p`, two member paths under a `select` (members only:
a member path has no index). -/
def Tm.extendsIn {sn : Name} {T U : Ty} (q : Tm C Γ (.spath sn T)) (p : Tm C Γ (.spath sn U)) :
    Bool :=
  q.extendsAnyIn (·.beqR p)

end Side

/-! ## The side conditions in the Theory

A path term denotes a storage location (`SLoc`); the side conditions are
read off its segments (`SLoc.labels`: the root, then the path), which the
shapes match, and give the Theory's location facts: two paths that part
are not below one another (`ObsLoc.strip? … = none`), a path that extends
another is it followed by a path. -/

/-- A storage reference's segments: the state variable, then its path. -/
def RefSegments.labels {C : Contract} {T : Ty} (r : RefSegments C T) : List Selector :=
  .root r.root :: r.tail.labels

def SRef.labels {C : Contract} {T : Ty} (r : SRef C T) : List Selector := r.segments.labels

theorem SRef.labels_eq {C : Contract} {T : Ty} (r : SRef C T) :
    r.labels = .root r.root :: r.path.labels := by
  unfold SRef.labels SRef.segments RefSegments.labels Path.labels
  rfl

attribute [irreducible] SRef.labels
attribute [eqns SRef.labels_eq] SRef.labels

/-- A storage location's segments: a reference's, a dangling location's
path alone. -/
def SLoc.labels {C : Contract} {T : Ty} : SLoc C T → List Selector
  | .ref r => r.labels
  | .dangling _ p => p.labels

theorem SLoc.labels_app {C : Contract} {T U : Ty} (l : SLoc C T) (p : Path T U) :
    (ObsLoc.app l p).labels = l.labels ++ p.labels := by
  cases l <;> simp only [ObsLoc.app, SLoc.app, SLoc.labels, SRef.labels, SRef.append,
    Path.labels_append, List.cons_append]

/-- Two lists that part are not one the other's prefix, either way. -/
theorem diverges_append_ne : (a b : List Selector) → Theory.diverges a b = true →
    ∀ x y : List Selector, a ++ x ≠ b ++ y
  | [], _, h, _, _, _ => by simp only [Theory.diverges, Bool.false_eq_true] at h
  | _ :: _, [], h, _, _, _ => by simp only [Theory.diverges, Bool.false_eq_true] at h
  | a :: p, b :: q, h, x, y, e => by
    simp only [List.cons_append, List.cons.injEq] at e
    obtain ⟨rfl, e⟩ := e
    simp only [Theory.diverges, if_true] at h
    exact diverges_append_ne p q h x y e

/-- **Locations whose segments part**: neither is below the other. -/
theorem SLoc.strip?_none_of_diverges {C : Contract} {U W : Ty} {p : SLoc C U} {q : SLoc C W}
    (h : Theory.diverges p.labels q.labels = true) :
    ∀ {V : Ty} (r : Path W V), ObsLoc.strip? p (ObsLoc.app q r) = none := by
  intro V r
  cases hs : ObsLoc.strip? p (ObsLoc.app q r) with
  | none => rfl
  | some r' =>
    exfalso
    have e := congrArg SLoc.labels (ObsLoc.eq_of_strip? p _ hs)
    rw [SLoc.labels_app, SLoc.labels_app] at e
    exact diverges_append_ne _ _ h _ _ e.symm

/-- **A location that parts from an array's length** is not at or above
the array. -/
theorem SLoc.strip?_none_of_divergesLen {C : Contract} {U E : Ty} {q : SLoc C U}
    {p : SLoc C (.ref (.array E))}
    (h : Theory.diverges q.labels (p.labels ++ [lengthSeg]) = true) :
    ObsLoc.strip? q p = none := by
  cases hs : ObsLoc.strip? q p with
  | none => rfl
  | some r =>
    exfalso
    have e := congrArg SLoc.labels (ObsLoc.eq_of_strip? q p hs)
    rw [SLoc.labels_app] at e
    refine diverges_append_ne _ _ h (r.labels ++ [lengthSeg]) [] ?_
    rw [e, List.append_nil, List.append_assoc]

/-- A sort's Theory denotation as segments: a path's, `[]` for the rest. -/
def Srt.labels : (u : Srt) → u.TDen C → List Selector
  | .path _, d => d.labels
  | .spath _ _, d => d.labels
  | _, _ => []

/-- The sort of a path below a storage sort's roots: from the contract's
roots for a storage, from the members under a `select`. -/
@[reducible] def Srt.pathAt : Srt → Ty → Srt
  | .sts sn, T => .spath sn T
  | _, T => .path T

/-- **A delete at `p` resets every word below it**, in every state: no
mapping's entry and no slot past an array's live end below `p` in `s`
(both of which a delete keeps; `TVal.delR`).  `s` a storage, or a storage of
members (`select`) and `p` a member path. -/
def Tm.KindFreeAt {Γ : Ctx} {u : Srt} {T : Ty} (s : Tm C Γ u) (p : Tm C Γ (u.pathAt T)) : Prop :=
  match u, s, p with
  | .st, s, p => ∀ (σ : State C Γ) {P : PrimTy} (r : Path T (.prim P)),
      TVal.delR (Comp.word P) ((s.denote σ).find (p.denote σ)) r = PrimTy.dflt P
  | .sts _, s, p => ∀ (σ : State C Γ) {P : PrimTy} (r : Path T (.prim P)),
      TVal.delR (Comp.word P) ((s.denote σ).find (p.denote σ)) r = PrimTy.dflt P
  | _, _, _ => True

section SideDenote

variable {Γ : Ctx} (σ : State C Γ)

/-- A literal reads its word in the Theory. -/
theorem Tm.litW?_denote {p : PrimTy} {t : Tm C Γ (.val p)} {w : (p : PrimTy) × p.Denote}
    (h : t.litW? = some w) : ∃ e : w.1 = p, t.denote σ = some (e ▸ w.2) := by
  cases t with
  | app0 o =>
    cases o with
    | lit v => cases h; exact ⟨rfl, rfl⟩
    | _ => cases h
  | _ => cases h

theorem Path.labels_index' {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) (i : k.Denote) :
    (Path.index it i).labels = [it.label i] := Path.labels_index it i

/-- An index's shape fits its label in every state. -/
theorem IndexTy.segT_fits {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V)
    (y : Tm C Γ (.val k)) :
    (it.segT y.litW?).fits (it.label ((y.denote σ).getD (PrimTy.dflt _))) = true := by
  cases hw : y.litW? with
  | none => cases it <;> rfl
  | some w =>
    obtain ⟨e, hd⟩ := Tm.litW?_denote σ hw
    obtain ⟨P, w⟩ := w
    dsimp only at e
    subst e
    rw [hd, Option.getD_some]
    cases it <;> simp only [IndexTy.segT, IndexTy.label, SegT.fits, beq_self_eq_true]

/-- A path has its shape in every state; generic in the sort, a path's
segments read by `Srt.labels`. -/
theorem Tm.shape?_matches' {u : Srt} (p : Tm C Γ u) :
    ∀ {a : List SegT}, p.shape? = some a → SegT.matches a (u.labels (p.denote σ)) = true := by
  induction p with
  | app0 o =>
    intro a h
    cases o with
    | root r hr =>
      cases h
      simp only [Srt.labels, Tm.denote, Op0.denote, SLoc.labels, SRef.labels, SRef.ofRoot, Path.labels,
        SegT.matches, SegT.fits, beq_self_eq_true, Bool.and_self]
    | member sn f hf =>
      cases h
      simp only [Srt.labels, Tm.denote, Op0.denote, SLoc.labels, SRef.labels, SRef.ofRoot, Path.labels,
        SegT.matches, SegT.fits, beq_self_eq_true, Bool.and_self]
    | _ => cases h
  | app1 o x ih =>
    intro a h
    cases o with
    | field hf =>
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      show SegT.matches _ (SLoc.labels (ObsLoc.app (x.denote σ) _)) = true
      rw [SLoc.labels_app]
      exact SegT.matches_append _ _ _ _ (ih ha)
        (by simp only [Path.labels, SegT.matches, SegT.fits, beq_self_eq_true, Bool.and_self])
    | fieldIn hf =>
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      show SegT.matches _ (SLoc.labels (ObsLoc.app (x.denote σ) _)) = true
      rw [SLoc.labels_app]
      exact SegT.matches_append _ _ _ _ (ih ha)
        (by simp only [Path.labels, SegT.matches, SegT.fits, beq_self_eq_true, Bool.and_self])
    | next =>
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      show SegT.matches _ (SLoc.labels (ObsLoc.app (x.denote σ) _)) = true
      rw [SLoc.labels_app]
      exact SegT.matches_append _ _ _ _ (ih ha)
        (by simp only [Path.labels, SegT.matches, SegT.fits, Bool.and_self])
    | _ => cases h
  | app2 o x y ihx ihy =>
    intro a h
    cases o with
    | «at» it =>
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      show SegT.matches _ (SLoc.labels (ObsLoc.app (x.denote σ) _)) = true
      rw [SLoc.labels_app, Path.labels_index']
      refine SegT.matches_append _ _ _ _ (ihx ha) ?_
      simp only [SegT.matches, IndexTy.segT_fits σ it y, Bool.and_self]
    | nextIn =>
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      show SegT.matches _ (SLoc.labels (ObsLoc.app (y.denote σ) _)) = true
      rw [SLoc.labels_app]
      exact SegT.matches_append _ _ _ _ (ihy ha)
        (by simp only [Path.labels, SegT.matches, SegT.fits, Bool.and_self])
    | _ => cases h
  | app3 o x y z _ ihy _ =>
    intro a h
    cases o with
    | atIn it =>
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      show SegT.matches _ (SLoc.labels (ObsLoc.app (y.denote σ) _)) = true
      rw [SLoc.labels_app, Path.labels_index']
      refine SegT.matches_append _ _ _ _ (ihy ha) ?_
      simp only [SegT.matches, IndexTy.segT_fits σ it z, Bool.and_self]
    | _ => cases h
  | _ => intro a h; cases h

/-- A path has its shape in every state. -/
theorem Tm.shape?_matches {T : Ty} (p : Tm C Γ (.path T)) {a : List SegT}
    (h : p.shape? = some a) : SegT.matches a (p.denote σ).labels = true :=
  Tm.shape?_matches' σ p h

/-- `Tm.diverges` gives the Theory's `diverges` on the locations' segments. -/
theorem Tm.diverges_segs {T U : Ty} {p : Tm C Γ (.path T)} {q : Tm C Γ (.path U)}
    (h : p.diverges q = true) :
    Theory.diverges (p.denote σ).labels (q.denote σ).labels = true := by
  unfold Tm.diverges at h
  split at h
  · rename_i a b ha hb
    exact SegT.diverges_sound a b _ _ h (p.shape?_matches σ ha) (q.shape?_matches σ hb)
  · exact absurd h Bool.false_ne_true

/-- `Tm.divergesLen` gives the Theory's `diverges q (p ++ [lengthSeg])` on
the segments. -/
theorem Tm.divergesLen_segs {T U : Ty} {q : Tm C Γ (.path T)} {p : Tm C Γ (.path U)}
    (h : q.divergesLen p = true) :
    Theory.diverges (q.denote σ).labels ((p.denote σ).labels ++ [lengthSeg]) = true := by
  unfold Tm.divergesLen at h
  split at h
  · rename_i a b ha hb
    exact SegT.diverges_sound _ _ _ _ h (q.shape?_matches σ ha)
      (SegT.matches_append _ _ _ _ (p.shape?_matches σ hb) (by decide))
  · exact absurd h Bool.false_ne_true

/-- `Tm.diverges` gives two locations neither below the other, in every
state. -/
theorem Tm.diverges_denote {T U : Ty} {p : Tm C Γ (.path T)} {q : Tm C Γ (.path U)}
    (h : p.diverges q = true) :
    ∀ {V : Ty} (r : Path U V), ObsLoc.strip? (p.denote σ) (ObsLoc.app (q.denote σ) r) = none := by
  unfold Tm.diverges at h
  split at h
  · rename_i a b ha hb
    exact SLoc.strip?_none_of_diverges
      (SegT.diverges_sound a b _ _ h (p.shape?_matches σ ha) (q.shape?_matches σ hb))
  · exact absurd h Bool.false_ne_true

/-- `Tm.diverges` read at the location itself. -/
theorem Tm.diverges_denote_nil {T U : Ty} {p : Tm C Γ (.path T)} {q : Tm C Γ (.path U)}
    (h : p.diverges q = true) : ObsLoc.strip? (p.denote σ) (q.denote σ) = none := by
  have e := Tm.diverges_denote σ h .nil
  rwa [ObsLoc.app_nil] at e

/-- `Tm.divergesLen` gives a location not at or above the array. -/
theorem Tm.divergesLen_denote {T E : Ty} {q : Tm C Γ (.path T)} {p : Tm C Γ (.path (.ref (.array E)))}
    (h : q.divergesLen p = true) : ObsLoc.strip? (q.denote σ) (p.denote σ) = none := by
  unfold Tm.divergesLen at h
  split at h
  · rename_i a b ha hb
    exact SLoc.strip?_none_of_divergesLen (SegT.diverges_sound _ _ _ _ h (q.shape?_matches σ ha)
      (SegT.matches_append _ _ _ _ (p.shape?_matches σ hb) (by decide)))
  · exact absurd h Bool.false_ne_true

/-- A check erased leaves the Theory's location, in every state; generic in
the sort. -/
theorem Tm.eraseChecks_denote' {u : Srt} (p : Tm C Γ u) :
    p.eraseChecks.denote σ = p.denote σ := by
  induction p with
  | app1 o x ih =>
    cases o <;> first
      | rfl
      | (show ObsLoc.app (x.eraseChecks.denote σ) _ = ObsLoc.app (x.denote σ) _; rw [ih])
      | (show ObsLoc.app (x.eraseChecks.denote σ) (.at (uintOfNat (σ.glob.storage.obs.len
            (x.eraseChecks.denote σ))) .nil) = ObsLoc.app (x.denote σ)
            (.at (uintOfNat (σ.glob.storage.obs.len (x.denote σ))) .nil); rw [ih])
  | app2 o x y ihx ihy =>
    cases o <;>
      first
      | rfl
      | (show ObsLoc.app (x.eraseChecks.denote σ) _ = ObsLoc.app (x.denote σ) _; rw [ihx])
      | (show ObsLoc.app (y.eraseChecks.denote σ) (.at (uintOfNat (Obs.len (x.denote σ)
            (y.eraseChecks.denote σ))) .nil) = ObsLoc.app (y.denote σ) (.at (uintOfNat (Obs.len
            (x.denote σ) (y.denote σ))) .nil); rw [ihy])
  | app3 o x y z _ ihy _ =>
    cases o <;> first | rfl | (show ObsLoc.app (y.eraseChecks.denote σ) _ = ObsLoc.app (y.denote σ) _; rw [ihy])
  | _ => rfl

theorem Tm.eraseChecks_denote {T : Ty} (p : Tm C Γ (.path T)) :
    p.eraseChecks.denote σ = p.denote σ :=
  Tm.eraseChecks_denote' σ p

/-- `sameSegs` gives one location in every state, at one type. -/
theorem Tm.sameSegs_heq {T U : Ty} {p : Tm C Γ (.path T)} {q : Tm C Γ (.path U)}
    (h : p.sameSegs q = true) : T = U ∧ HEq (p.denote σ) (q.denote σ) := by
  rw [← Tm.eraseChecks_denote σ p, ← Tm.eraseChecks_denote σ q]
  have e := Tm.sigma_eq_of_beqR h
  generalize p.eraseChecks = p' at e
  generalize q.eraseChecks = q' at e
  cases e
  exact ⟨rfl, HEq.rfl⟩

theorem Tm.sameSegs_denote {T : Ty} {p q : Tm C Γ (.path T)} (h : p.sameSegs q = true) :
    p.denote σ = q.denote σ :=
  eq_of_heq (Tm.sameSegs_heq σ h).2

/-- A location below another: it followed by a path that goes somewhere. -/
def Srt.Below {U : Ty} (l : SLoc C U) : (u : Srt) → u.TDen C → Prop
  | .path T, d => ∃ r : Path U T, r.labels ≠ [] ∧ d = ObsLoc.app l r
  | _, _ => False

/-- A member location below another under a `select` of `s`. -/
def Srt.BelowIn {s : Name} {U : Ty} (l : SLoc (Contract.ofStruct s) U) :
    (u : Srt) → u.TDen C → Prop
  | .spath s' T, d => ∀ e : s' = s, ∃ r : Path U T, r.labels ≠ [] ∧
      (e ▸ d : SLoc (Contract.ofStruct s) T) = ObsLoc.app l r
  | _, _ => False

/-- `q.extends p` gives `q`'s location `p`'s followed by a path, in every
state; generic in the sort. -/
theorem Tm.extends_denote' {U : Ty} {p : Tm C Γ (.path U)} {u : Srt} (q : Tm C Γ u) :
    q.extendsAny (·.beqR p) = true → Srt.Below (p.denote σ) u (q.denote σ) := by
  induction q with
  | app1 o x ih =>
    intro h
    cases o with
    | field hf =>
      rcases Bool.or_eq_true_iff.mp h with h | h
      · cases Tm.sigma_eq_of_beqR h
        exact ⟨.field hf .nil, by simp only [Path.labels, ne_eq, reduceCtorEq,
          not_false_eq_true], rfl⟩
      · obtain ⟨r, hr, hq⟩ := ih h
        refine ⟨r.append (.field hf .nil), ?_, ?_⟩
        · rw [Path.labels_append]; exact List.append_ne_nil_of_left_ne_nil hr _
        · show ObsLoc.app (x.denote σ) _ = _
          rw [hq, ObsLoc.app_app]
    | _ => cases h
  | app2 o x y ihx _ =>
    intro h
    cases o with
    | «at» it =>
      rcases Bool.or_eq_true_iff.mp h with h | h
      · cases Tm.sigma_eq_of_beqR h
        exact ⟨_, by rw [Path.labels_index']; simp only [ne_eq, reduceCtorEq,
          not_false_eq_true], rfl⟩
      · obtain ⟨r, hr, hq⟩ := ihx h
        refine ⟨r.append (Path.index it ((y.denote σ).getD (PrimTy.dflt _))), ?_, ?_⟩
        · rw [Path.labels_append]; exact List.append_ne_nil_of_left_ne_nil hr _
        · show ObsLoc.app (x.denote σ) _ = _
          rw [hq, ObsLoc.app_app]
    | _ => cases h
  | app3 o x y z _ ihy _ =>
    intro h
    cases o with
    | atIn it =>
      rcases Bool.or_eq_true_iff.mp h with h | h
      · cases Tm.sigma_eq_of_beqR h
        exact ⟨_, by rw [Path.labels_index']; simp only [ne_eq, reduceCtorEq,
          not_false_eq_true], rfl⟩
      · obtain ⟨r, hr, hq⟩ := ihy h
        refine ⟨r.append (Path.index it ((z.denote σ).getD (PrimTy.dflt _))), ?_, ?_⟩
        · rw [Path.labels_append]; exact List.append_ne_nil_of_left_ne_nil hr _
        · show ObsLoc.app (y.denote σ) _ = _
          rw [hq, ObsLoc.app_app]
    | _ => cases h
  | _ => intro h; cases h

theorem Tm.extends_denote {T U : Ty} {p : Tm C Γ (.path U)} (q : Tm C Γ (.path T))
    (h : q.extends p = true) :
    ∃ r : Path U T, r.labels ≠ [] ∧ q.denote σ = ObsLoc.app (p.denote σ) r := by
  exact Tm.extends_denote' σ q h

/-- What `shift?` gives splits the location at its head: the member path
under the root. -/
def Srt.ShiftOK' (σ : State C Γ) : (u : Srt) → u.ShiftD C Γ → u.TDen C → Prop
  | .path _, sh, d => d = (sh.p.denote σ).under sh.h
  | _, _, _ => True

/-- What `shift?` gives, if anything, splits the path; generic in the sort. -/
def Srt.ShiftOK (σ : State C Γ) (u : Srt) (o : Option (u.ShiftD C Γ)) (d : u.TDen C) : Prop :=
  ∀ sh, o = some sh → Srt.ShiftOK' σ u sh d

theorem Tm.shift?_ok {u : Srt} (p : Tm C Γ u) : Srt.ShiftOK σ u p.shift? (p.denote σ) := by
  induction p with
  | app1 o x ih =>
    cases o with
    | field hf =>
      rename_i sn f T
      intro sh h
      have h : (match x.rootOf? with
        | some ⟨r, hr⟩ => some ⟨r, sn, hr, .app0 (.member sn f hf)⟩
        | none => x.shift?.map fun sh => ⟨sh.r, sh.sn, sh.h, .app1 (.fieldIn hf) sh.p⟩) =
          some sh := h
      cases hx : x.rootOf? with
      | some rr =>
        rw [hx] at h
        obtain ⟨r, hr⟩ := rr
        cases h
        have hd : x.denote σ = .ref (SRef.ofRoot r hr) := by
          cases x with
          | app0 o =>
            cases o with
            | root r' hr' => cases hx; rfl
            | _ => cases hx
          | _ => cases hx
        show ObsLoc.app (x.denote σ) _ = _
        rw [hd]
        simp only [ObsLoc.app, SLoc.app, SRef.ofRoot, SRef.append, Path.append_nil, Tm.denote,
          Op0.denote, SLoc.under, SRef.under]
      | none =>
        rw [hx] at h
        obtain ⟨sh', hs, rfl⟩ := Option.map_eq_some_iff.1 h
        have ih' : x.denote σ = (sh'.p.denote σ).under sh'.h := ih sh' hs
        show ObsLoc.app (x.denote σ) _ = (ObsLoc.app (sh'.p.denote σ) _).under sh'.h
        rw [ih', SLoc.under_app]
    | _ => intro sh h; cases h
  | _ => intro sh h; cases h

/-- `shift?` splits the location at its head, in every state. -/
theorem Tm.shift?_denote {T : Ty} (p : Tm C Γ (.path T)) {sh : Shifted C Γ T}
    (h : p.shift? = some sh) : p.denote σ = (sh.p.denote σ).under sh.h :=
  Tm.shift?_ok σ p sh h

/-- What `shiftIn?` gives splits the member location at its head. -/
def Srt.ShiftInOK (σ : State C Γ) : (u : Srt) → u.ShiftInD C Γ → u.TDen C → Prop
  | .spath _ _, sh, d => d = SLoc.under (C := Contract.ofStruct _) sh.h (sh.p.denote σ)
  | _, _, _ => True

theorem Tm.shiftIn?_ok {u : Srt} (p : Tm C Γ u) :
    ∀ sh, p.shiftIn? = some sh → Srt.ShiftInOK σ u sh (p.denote σ) := by
  induction p with
  | app1 o x ih =>
    cases o with
    | fieldIn hg =>
      rename_i s sn' g T
      intro sh h
      have h : (match x.memberOf? with
        | some ⟨f, hf⟩ => some ⟨f, sn', hf, .app0 (.member sn' g hg)⟩
        | none => x.shiftIn?.map fun sh => ⟨sh.f, sh.sn, sh.h, .app1 (.fieldIn hg) sh.p⟩) =
          some sh := h
      cases hx : x.memberOf? with
      | some mm =>
        rw [hx] at h
        obtain ⟨f, hf⟩ := mm
        cases h
        have hd : x.denote σ = .ref (SRef.ofRoot (C := Contract.ofStruct s) f hf) := by
          cases x with
          | app0 o =>
            cases o with
            | member _ f' hf' => cases hx; rfl
            | _ => cases hx
          | _ => cases hx
        show ObsLoc.app (x.denote σ) _ = _
        rw [hd]
        simp only [ObsLoc.app, SLoc.app, SRef.ofRoot, SRef.append, Path.append_nil, Tm.denote,
          Op0.denote, SLoc.under, SRef.under]
      | none =>
        rw [hx] at h
        obtain ⟨sh', hs, rfl⟩ := Option.map_eq_some_iff.1 h
        have ih' : x.denote σ = SLoc.under (C := Contract.ofStruct _) sh'.h (sh'.p.denote σ) :=
          ih sh' hs
        show ObsLoc.app (x.denote σ) _ =
          SLoc.under (C := Contract.ofStruct _) sh'.h (ObsLoc.app (sh'.p.denote σ) _)
        rw [ih', SLoc.under_app]
    | _ => intro sh h; cases h
  | _ => intro sh h; cases h

/-- A member path denotes a state variable's path, never a dangling one;
generic in the sort. -/
def Srt.IsRef : (u : Srt) → u.TDen C → Prop
  | .spath _ _, d => ∃ q, d = .ref q
  | _, _ => True

theorem Tm.spath_isRef' {u : Srt} (p : Tm C Γ u) : Srt.IsRef u (p.denote σ) := by
  induction p with
  | app0 o => cases o <;> first | trivial | exact ⟨_, rfl⟩
  | app1 o x ih =>
    cases o with
    | fieldIn h =>
      obtain ⟨q, hq⟩ := ih
      exact ⟨_, show ObsLoc.app (x.denote σ) _ = _ by rw [hq]; rfl⟩
    | _ => trivial
  | app2 o => cases o <;> trivial
  | app3 o => cases o <;> trivial
  | _ => trivial

theorem Tm.spath_isRef {s : Name} {T : Ty} (p : Tm C Γ (.spath s T)) :
    ∃ q, p.denote σ = .ref q :=
  Tm.spath_isRef' σ p

end SideDenote

section SideSyntax

variable {Γ : Ctx}

/-- A check erased leaves a segment where there was one. -/
theorem Tm.eraseChecks_hasSeg {T : Ty} (p : Tm C Γ (.path T)) :
    p.eraseChecks.hasSeg = p.hasSeg := by
  cases p with
  | app1 o _ | app2 o _ _ | app3 o _ _ _ => cases o <;> rfl
  | _ => rfl

/-- Paths of the same segments are both bare aliases or neither. -/
theorem Tm.sameSegs_hasSeg {T U : Ty} {p : Tm C Γ (.path T)} {q : Tm C Γ (.path U)}
    (h : p.sameSegs q = true) : p.hasSeg = q.hasSeg := by
  rw [← Tm.eraseChecks_hasSeg p, ← Tm.eraseChecks_hasSeg q]
  have e := Tm.sigma_eq_of_beqR h
  generalize p.eraseChecks = p' at e
  generalize q.eraseChecks = q' at e
  cases e
  rfl

end SideSyntax

/-! ## A storage of members with a hole

`select`'s storage of members, down to the hole: saves, deletes and selects
of members (`saveIn`, `delAtIn`, `selectIn`), from the struct `s₀` the hole
is at to the struct `sn` the context reads. -/

/-- A context over storages of members (`SCtx`, scoped and typed). -/
inductive SCtxS (C : Contract) (Γ : Ctx) (s₀ : Name) : Name → Type where
  | hole : SCtxS C Γ s₀ s₀
  | save {sn : Name} {T : Ty} (K : SCtxS C Γ s₀ sn) (p : Tm C Γ (.spath sn T))
      (v : Tm C Γ (.sv T)) : SCtxS C Γ s₀ sn
  | delAt {sn : Name} {T : Ty} (K : SCtxS C Γ s₀ sn) (p : Tm C Γ (.spath sn T)) : SCtxS C Γ s₀ sn
  | select {sn sn' f : Name} (K : SCtxS C Γ s₀ sn)
      (h : C.fieldType sn f = some (.ref (.struct sn'))) : SCtxS C Γ s₀ sn'

section Ctx

variable {Γ : Ctx} {s₀ : Name}

/-- The hole filled. -/
def SCtxS.fill : {sn : Name} → SCtxS C Γ s₀ sn → Tm C Γ (.sts s₀) → Tm C Γ (.sts sn)
  | _, .hole, s => s
  | _, .save K p v, s => .app3 .saveIn (K.fill s) p v
  | _, .delAt K p, s => .app2 .delAtIn (K.fill s) p
  | _, .select K h, s => .app1 (.selectIn h) (K.fill s)

/-- Two storages that denote alike fill a context alike. -/
theorem SCtxS.fill_denote {s s' : Tm C Γ (.sts s₀)}
    (h : ∀ σ : State C Γ, s.denote σ = s'.denote σ) :
    {sn : Name} → (K : SCtxS C Γ s₀ sn) → ∀ σ : State C Γ, (K.fill s).denote σ = (K.fill s').denote σ
  | _, .hole, σ => h σ
  | _, .save K p v, σ => by
    show Op3.denote .saveIn ((K.fill s).denote σ) _ _ = Op3.denote .saveIn ((K.fill s').denote σ) _ _
    rw [SCtxS.fill_denote h K σ]
  | _, .delAt K p, σ => by
    show Op2.denote σ.glob .delAtIn _ _ ((K.fill s).denote σ) _ =
      Op2.denote σ.glob .delAtIn _ _ ((K.fill s').denote σ) _
    simp only [Op2.denote, SCtxS.fill_denote h K σ]
  | _, .select K hf, σ => by
    show Op1.denote σ.glob (.selectIn hf) ((K.fill s).denote σ) =
      Op1.denote σ.glob (.selectIn hf) ((K.fill s').denote σ)
    rw [SCtxS.fill_denote h K σ]

end Ctx

/-! ## The rules

Typed (W9.8.3c): each side is a term of the value's type; a select reads
its member paths in the struct's frame (`findIn`, `saveIn`, `delAtIn`;
`Tm.shift?`), and an array's push and pop are their symbols (`push`,
`pop`), which the typed signature has in place of a write to the length
path (`p.length`).  -/

/-- `t ⇝ t'` on scoped terms: a rule of the Theory rewrites `t` to `t'`,
each constructor named as its solkey taclet. -/
inductive TermTaclet {Γ : Ctx} : {P : PrimTy} → Tm C Γ (.val P) → Tm C Γ (.val P) → Prop
  /-- **`findOnSave`**: `find(save(s, p, v), q) ⇝ v` for a word `v`, `q` the
  path `p` its checks aside (`Obs.findOnSave`). -/
  | findOnSave {s : Tm C Γ .st} {P : PrimTy} {p q : Tm C Γ (.path (.prim P))} {v : P.Denote}
      (hp : p.hasSeg = true := by rfl)
      (hq : p.sameSegs q = true := by first | rfl | exact Tm.sameSegs_refl _) :
      TermTaclet (Tms.Term.find (Tms.STerm.save s p (Tms.SValT.val (Tms.Term.lit v))) q)
        (Tms.Term.lit v)
  /-- **`findOnSaveFrame`**: a read at a path that leaves the written one does
  not see the write (`Obs.findOnSaveFrame`). -/
  | findOnSaveFrame {s : Tm C Γ .st} {T : Ty} {P : PrimTy} {p : Tm C Γ (.path T)}
      {q : Tm C Γ (.path (.prim P))} {v : Tm C Γ (.sv T)} (h : p.diverges q = true := by rfl) :
      TermTaclet (Tms.Term.find (Tms.STerm.save s p v) q) (Tms.Term.find s q)
  /-- **`findMemberCons`**: `find(s, r.p) ⇝ find(select(s, r), p)`, the path
  read from its head (`Obs.select_find`). -/
  | findMemberCons {s : Tm C Γ .st} {P : PrimTy} {p : Tm C Γ (.path (.prim P))} {r sn : Name}
      {hr : C.rootType r = some (.ref (.struct sn))} {p' : Tm C Γ (.spath sn (.prim P))}
      (h : p.shift? = some ⟨r, sn, hr, p'⟩ := by rfl) :
      TermTaclet (Tms.Term.find s p) (.app2 .findIn (Tms.STerm.select s r hr) p')
  /-- **`findMemberCons`** in a storage of members: `findIn(s, f.p) ⇝
  findIn(select(s, f), p)` (`Obs.select_find`). -/
  | findMemberConsIn {sn : Name} {s : Tm C Γ (.sts sn)} {P : PrimTy}
      {p : Tm C Γ (.spath sn (.prim P))} {f sn' : Name}
      {hf : C.fieldType sn f = some (.ref (.struct sn'))} {p' : Tm C Γ (.spath sn' (.prim P))}
      (h : p.shiftIn? = some ⟨f, sn', hf, p'⟩ := by rfl) :
      TermTaclet (.app2 .findIn s p) (.app2 .findIn (.app1 (.selectIn hf) s) p')
  /-- **`findOnSave`** in a storage of members: `findIn(saveIn(s, p, v), p) ⇝ v`
  for a word `v` (`Obs.findOnSave`). -/
  | findOnSaveIn {sn : Name} {s : Tm C Γ (.sts sn)} {P : PrimTy}
      {p q : Tm C Γ (.spath sn (.prim P))} {v : P.Denote}
      (hq : p.beqR q = true := by first | rfl | exact Tm.beqR_self _) :
      TermTaclet (.app2 .findIn (.app3 .saveIn s p (Tms.SValT.val (Tms.Term.lit v))) q)
        (Tms.Term.lit v)
  /-- **`selectOnSaveMember`**: solkey's `selectOnSaveCons` at `a1 = a2`. -/
  | selectOnSaveMember {s : Tm C Γ .st} {T : Ty} {p : Tm C Γ (.path T)} {v : Tm C Γ (.sv T)}
      {r sn : Name} {hr : C.rootType r = some (.ref (.struct sn))} {p' : Tm C Γ (.spath sn T)}
      {P : PrimTy} {q : Tm C Γ (.spath sn (.prim P))}
      (h : p.shift? = some ⟨r, sn, hr, p'⟩ := by rfl) :
      TermTaclet (.app2 .findIn (Tms.STerm.select (Tms.STerm.save s p v) r hr) q)
        (.app2 .findIn (.app3 .saveIn (Tms.STerm.select s r hr) p' v) q)
  /-- **`selectOnSaveFrame`**: solkey's `selectOnSaveCons` at `a1 ≠ a2`. -/
  | selectOnSaveFrame {s : Tm C Γ .st} {T : Ty} {p : Tm C Γ (.path T)} {v : Tm C Γ (.sv T)}
      {r sn r' sn' : Name} {hr : C.rootType r = some (.ref (.struct sn))}
      {hr' : C.rootType r' = some (.ref (.struct sn'))} {p' : Tm C Γ (.spath sn' T)}
      {P : PrimTy} {q : Tm C Γ (.spath sn (.prim P))}
      (h : p.shift? = some ⟨r', sn', hr', p'⟩ := by rfl) (hne : r' ≠ r := by decide) :
      TermTaclet (.app2 .findIn (Tms.STerm.select (Tms.STerm.save s p v) r hr) q)
        (.app2 .findIn (Tms.STerm.select s r hr) q)
  /-- **`selectOnDelAtMember`**: the delete at `r.p`, seen from `r`, is a
  delete at `p`. -/
  | selectOnDelAtMember {s : Tm C Γ .st} {T : Ty} {p : Tm C Γ (.path T)}
      {r sn : Name} {hr : C.rootType r = some (.ref (.struct sn))} {p' : Tm C Γ (.spath sn T)}
      {P : PrimTy} {q : Tm C Γ (.spath sn (.prim P))}
      (h : p.shift? = some ⟨r, sn, hr, p'⟩ := by rfl) :
      TermTaclet (.app2 .findIn (Tms.STerm.select (Tms.STerm.delAt s p) r hr) q)
        (.app2 .findIn (.app2 .delAtIn (Tms.STerm.select s r hr) p') q)
  /-- **`selectOnDelAtFrame`**: a delete under another root is not seen from
  `r`. -/
  | selectOnDelAtFrame {s : Tm C Γ .st} {T : Ty} {p : Tm C Γ (.path T)}
      {r sn r' sn' : Name} {hr : C.rootType r = some (.ref (.struct sn))}
      {hr' : C.rootType r' = some (.ref (.struct sn'))} {p' : Tm C Γ (.spath sn' T)}
      {P : PrimTy} {q : Tm C Γ (.spath sn (.prim P))}
      (h : p.shift? = some ⟨r', sn', hr', p'⟩ := by rfl) (hne : r' ≠ r := by decide) :
      TermTaclet (.app2 .findIn (Tms.STerm.select (Tms.STerm.delAt s p) r hr) q)
        (.app2 .findIn (Tms.STerm.select s r hr) q)
  /-- **`selectOnSaveMemberIn`**: `selectOnSaveMember` in a storage of
  members. -/
  | selectOnSaveMemberIn {s : Tm C Γ .st} {T : Ty} {p : Tm C Γ (.path T)} {v : Tm C Γ (.sv T)}
      {r sn : Name} {hr : C.rootType r = some (.ref (.struct sn))} {p' : Tm C Γ (.spath sn T)}
      {sn₁ : Name} (K : SCtxS C Γ sn sn₁) {P : PrimTy} {q : Tm C Γ (.spath sn₁ (.prim P))}
      (h : p.shift? = some ⟨r, sn, hr, p'⟩ := by rfl) :
      TermTaclet (.app2 .findIn (K.fill (Tms.STerm.select (Tms.STerm.save s p v) r hr)) q)
        (.app2 .findIn (K.fill (.app3 .saveIn (Tms.STerm.select s r hr) p' v)) q)
  /-- **`selectOnSaveFrameIn`**: `selectOnSaveFrame` in a storage of
  members. -/
  | selectOnSaveFrameIn {s : Tm C Γ .st} {T : Ty} {p : Tm C Γ (.path T)} {v : Tm C Γ (.sv T)}
      {r sn r' sn' : Name} {hr : C.rootType r = some (.ref (.struct sn))}
      {hr' : C.rootType r' = some (.ref (.struct sn'))} {p' : Tm C Γ (.spath sn' T)}
      {sn₁ : Name} (K : SCtxS C Γ sn sn₁) {P : PrimTy} {q : Tm C Γ (.spath sn₁ (.prim P))}
      (h : p.shift? = some ⟨r', sn', hr', p'⟩ := by rfl) (hne : r' ≠ r := by decide) :
      TermTaclet (.app2 .findIn (K.fill (Tms.STerm.select (Tms.STerm.save s p v) r hr)) q)
        (.app2 .findIn (K.fill (Tms.STerm.select s r hr)) q)
  /-- **`selectOnDelAtMemberIn`**: `selectOnDelAtMember` in a storage of
  members. -/
  | selectOnDelAtMemberIn {s : Tm C Γ .st} {T : Ty} {p : Tm C Γ (.path T)}
      {r sn : Name} {hr : C.rootType r = some (.ref (.struct sn))} {p' : Tm C Γ (.spath sn T)}
      {sn₁ : Name} (K : SCtxS C Γ sn sn₁) {P : PrimTy} {q : Tm C Γ (.spath sn₁ (.prim P))}
      (h : p.shift? = some ⟨r, sn, hr, p'⟩ := by rfl) :
      TermTaclet (.app2 .findIn (K.fill (Tms.STerm.select (Tms.STerm.delAt s p) r hr)) q)
        (.app2 .findIn (K.fill (.app2 .delAtIn (Tms.STerm.select s r hr) p')) q)
  /-- **`selectOnDelAtFrameIn`**: `selectOnDelAtFrame` in a storage of
  members. -/
  | selectOnDelAtFrameIn {s : Tm C Γ .st} {T : Ty} {p : Tm C Γ (.path T)}
      {r sn r' sn' : Name} {hr : C.rootType r = some (.ref (.struct sn))}
      {hr' : C.rootType r' = some (.ref (.struct sn'))} {p' : Tm C Γ (.spath sn' T)}
      {sn₁ : Name} (K : SCtxS C Γ sn sn₁) {P : PrimTy} {q : Tm C Γ (.spath sn₁ (.prim P))}
      (h : p.shift? = some ⟨r', sn', hr', p'⟩ := by rfl) (hne : r' ≠ r := by decide) :
      TermTaclet (.app2 .findIn (K.fill (Tms.STerm.select (Tms.STerm.delAt s p) r hr)) q)
        (.app2 .findIn (K.fill (Tms.STerm.select s r hr)) q)
  /-- **`selectOnSaveMember`** at a member under a `select`: the write at
  `f.p` in a storage of members, seen from `f`, is a write at `p`. -/
  | selectOnSaveMemberAt {sn sn' f : Name} {s : Tm C Γ (.sts sn)} {T : Ty}
      {p : Tm C Γ (.spath sn T)} {v : Tm C Γ (.sv T)}
      {hf : C.fieldType sn f = some (.ref (.struct sn'))} {p' : Tm C Γ (.spath sn' T)}
      {sn₁ : Name} (K : SCtxS C Γ sn' sn₁) {P : PrimTy} {q : Tm C Γ (.spath sn₁ (.prim P))}
      (h : p.shiftIn? = some ⟨f, sn', hf, p'⟩ := by rfl) :
      TermTaclet (.app2 .findIn (K.fill (.app1 (.selectIn hf) (.app3 .saveIn s p v))) q)
        (.app2 .findIn (K.fill (.app3 .saveIn (.app1 (.selectIn hf) s) p' v)) q)
  /-- **`selectOnSaveFrame`** at a member under a `select`: a write under
  another member is not seen from `f`. -/
  | selectOnSaveFrameAt {sn sn' sn'' f f' : Name} {s : Tm C Γ (.sts sn)} {T : Ty}
      {p : Tm C Γ (.spath sn T)} {v : Tm C Γ (.sv T)}
      {hf : C.fieldType sn f = some (.ref (.struct sn'))}
      {hf' : C.fieldType sn f' = some (.ref (.struct sn''))} {p' : Tm C Γ (.spath sn'' T)}
      {sn₁ : Name} (K : SCtxS C Γ sn' sn₁) {P : PrimTy} {q : Tm C Γ (.spath sn₁ (.prim P))}
      (h : p.shiftIn? = some ⟨f', sn'', hf', p'⟩ := by rfl) (hne : f' ≠ f := by decide) :
      TermTaclet (.app2 .findIn (K.fill (.app1 (.selectIn hf) (.app3 .saveIn s p v))) q)
        (.app2 .findIn (K.fill (.app1 (.selectIn hf) s)) q)
  /-- **`selectOnDelAtMember`** at a member under a `select`. -/
  | selectOnDelAtMemberAt {sn sn' f : Name} {s : Tm C Γ (.sts sn)} {T : Ty}
      {p : Tm C Γ (.spath sn T)} {hf : C.fieldType sn f = some (.ref (.struct sn'))}
      {p' : Tm C Γ (.spath sn' T)}
      {sn₁ : Name} (K : SCtxS C Γ sn' sn₁) {P : PrimTy} {q : Tm C Γ (.spath sn₁ (.prim P))}
      (h : p.shiftIn? = some ⟨f, sn', hf, p'⟩ := by rfl) :
      TermTaclet (.app2 .findIn (K.fill (.app1 (.selectIn hf) (.app2 .delAtIn s p))) q)
        (.app2 .findIn (K.fill (.app2 .delAtIn (.app1 (.selectIn hf) s) p')) q)
  /-- **`selectOnDelAtFrame`** at a member under a `select`. -/
  | selectOnDelAtFrameAt {sn sn' sn'' f f' : Name} {s : Tm C Γ (.sts sn)} {T : Ty}
      {p : Tm C Γ (.spath sn T)} {hf : C.fieldType sn f = some (.ref (.struct sn'))}
      {hf' : C.fieldType sn f' = some (.ref (.struct sn''))} {p' : Tm C Γ (.spath sn'' T)}
      {sn₁ : Name} (K : SCtxS C Γ sn' sn₁) {P : PrimTy} {q : Tm C Γ (.spath sn₁ (.prim P))}
      (h : p.shiftIn? = some ⟨f', sn'', hf', p'⟩ := by rfl) (hne : f' ≠ f := by decide) :
      TermTaclet (.app2 .findIn (K.fill (.app1 (.selectIn hf) (.app2 .delAtIn s p))) q)
        (.app2 .findIn (K.fill (.app1 (.selectIn hf) s)) q)
  /-- **`findOnDelAt`**: where `s` reads the word `w` at `p`, the delete
  leaves its default (`Obs.findOnDelAt`). -/
  | findOnDelAt {s : Tm C Γ .st} {P : PrimTy} {p q : Tm C Γ (.path (.prim P))} {w : P.Denote}
      (hw : TermTaclet (Tms.Term.find s p) (Tms.Term.lit w)) (hp : p.hasSeg = true := by rfl)
      (hq : p.sameSegs q = true := by first | rfl | exact Tm.sameSegs_refl _) :
      TermTaclet (Tms.Term.find (Tms.STerm.delAt s p) q) (Tms.Term.dflt P)
  /-- **`findOnDelAtValue`**: the delete leaves at its path the default of
  what was there (`Obs.findOnDelAt`). -/
  | findOnDelAtValue {s : Tm C Γ .st} {T : Ty} {p : Tm C Γ (.path T)} {P : PrimTy}
      {q : Tm C Γ (.path (.prim P))} (hp : p.hasSeg = true := by rfl)
      (hq : p.sameSegs q = true := by first | rfl | exact Tm.sameSegs_refl _) :
      TermTaclet (Tms.Term.find (Tms.STerm.delAt s p) q) (Tms.Term.delValue (Tms.Term.find s q))
  /-- **`delValueLit`**: the default of a word (`delValue`'s denotation). -/
  | delValueLit {P : PrimTy} {w : P.Denote} :
      TermTaclet (Tms.Term.delValue (Tms.Term.lit w)) (Tms.Term.dflt P)
  /-- **`findOnDelAtBelow`**: below a deleted node that is not a mapping,
  every word reads its default (`Obs.delAt_word_below`). -/
  | findOnDelAtBelow {s : Tm C Γ .st} {T : Ty} {p : Tm C Γ (.path T)} {P : PrimTy}
      {q : Tm C Γ (.path (.prim P))} {w : P.Denote} (hk : s.KindFreeAt p)
      (hw : s.findLit? q = some w := by rfl) (hp : p.hasSeg = true := by rfl)
      (hq : q.extends p = true := by rfl) :
      TermTaclet (Tms.Term.find (Tms.STerm.delAt s p) q) (Tms.Term.dflt P)
  /-- **`findOnDelAtBelow`** in a storage of members:
  `findIn(delAtIn(s, p), q) ⇝ defVal` below a deleted member that is not a
  mapping, `q` going on below `p` by members (`Tm.extendsIn`) and `s`
  writing the word there (`Tm.findLitIn?`) (`Obs.delAt_word_below`). -/
  | findOnDelAtBelowIn {sn : Name} {s : Tm C Γ (.sts sn)} {T : Ty} {p : Tm C Γ (.spath sn T)}
      {P : PrimTy} {q : Tm C Γ (.spath sn (.prim P))} {w : P.Denote} (hk : s.KindFreeAt p)
      (hw : s.findLitIn? q = some w := by rfl) (hq : q.extendsIn p = true := by rfl) :
      TermTaclet (.app2 .findIn (.app2 .delAtIn s p) q) (Tms.Term.dflt P)
  /-- **`findOnDelAtFrame`**: a read off the deleted path does not see the
  delete (`Obs.findOnDelAtFrame`). -/
  | findOnDelAtFrame {s : Tm C Γ .st} {T : Ty} {p : Tm C Γ (.path T)} {P : PrimTy}
      {q : Tm C Γ (.path (.prim P))} (h : p.diverges q = true := by rfl) :
      TermTaclet (Tms.Term.find (Tms.STerm.delAt s p) q) (Tms.Term.find s q)
  /-- **`findOnPushFrame`**: a read off the array's path does not see a push
  (`Obs.findOnPushFrame`). -/
  | findOnPushFrame {s : Tm C Γ .st} {E : Ty} {p : Tm C Γ (.path (.ref (.array E)))}
      {v : Tm C Γ (.sv E)} {P : PrimTy} {q : Tm C Γ (.path (.prim P))}
      (h : p.diverges q = true := by rfl) :
      TermTaclet (Tms.Term.find (Tms.STerm.push s p v) q) (Tms.Term.find s q)
  /-- **`findOnPopFrame`**: a read off the array's path does not see a pop
  (`Obs.findOnPopFrame`). -/
  | findOnPopFrame {s : Tm C Γ .st} {E : Ty} {p : Tm C Γ (.path (.ref (.array E)))}
      {P : PrimTy} {q : Tm C Γ (.path (.prim P))} (h : p.diverges q = true := by rfl) :
      TermTaclet (Tms.Term.find (Tms.STerm.pop s p) q) (Tms.Term.find s q)
  /-- **`lenOnSaveFrame`**: a length read off the written path does not see
  the write (`Obs.lenOnSaveFrame`). -/
  | lenOnSaveFrame {s : Tm C Γ .st} {T : Ty} {q : Tm C Γ (.path T)} {v : Tm C Γ (.sv T)}
      {E : Ty} {p : Tm C Γ (.path (.ref (.array E)))} (h : q.divergesLen p = true := by rfl) :
      TermTaclet (Tms.Term.len (Tms.STerm.save s q v) p) (Tms.Term.len s p)
  /-- **`lenOnDelAtFrame`**: a length read off the deleted path does not see
  the delete (`Obs.lenOnDelAtFrame`). -/
  | lenOnDelAtFrame {s : Tm C Γ .st} {T : Ty} {q : Tm C Γ (.path T)}
      {E : Ty} {p : Tm C Γ (.path (.ref (.array E)))} (h : q.divergesLen p = true := by rfl) :
      TermTaclet (Tms.Term.len (Tms.STerm.delAt s q) p) (Tms.Term.len s p)
  /-- Any law of the Theory: `t` and `t'` have one Theory value in every
  state. -/
  | theory {P : PrimTy} {t t' : Tm C Γ (.val P)} (h : Tm.Theq t t') : TermTaclet t t'
  /-- A rule read right to left, `rw [← r]`. -/
  | symm {P : PrimTy} {t t' : Tm C Γ (.val P)} (r : TermTaclet t t') : TermTaclet t' t

section Rules

variable {Γ : Ctx}

/-- **`findOnDelAtSave`**: a delete over a written word reads the word's
default: `findOnDelAt` with `findOnSave` as its premise. -/
theorem TermTaclet.findOnDelAtSave {s : Tm C Γ .st} {P : PrimTy} {p' p q : Tm C Γ (.path (.prim P))}
    {v : P.Denote} (hp : p.hasSeg = true := by rfl)
    (hp' : p'.sameSegs p = true := by first | rfl | exact Tm.sameSegs_refl _)
    (hq : p.sameSegs q = true := by first | rfl | exact Tm.sameSegs_refl _) :
    TermTaclet (Tms.Term.find (Tms.STerm.delAt (Tms.STerm.save s p' (Tms.SValT.val (Tms.Term.lit v))) p) q)
      (Tms.Term.dflt P) :=
  .findOnDelAt (.findOnSave ((Tm.sameSegs_hasSeg hp').trans hp) hp') hp hq

end Rules

/-! ## Soundness -/

section Sound

variable {Γ : Ctx}

theorem Tm.selectOnSaveMember_denote {s : Tm C Γ .st} {T : Ty} {p : Tm C Γ (.path T)}
    {v : Tm C Γ (.sv T)} {r sn : Name} {hr : C.rootType r = some (.ref (.struct sn))}
    {p' : Tm C Γ (.spath sn T)} (h : p.shift? = some ⟨r, sn, hr, p'⟩) (σ : State C Γ) :
    (Tms.STerm.select (Tms.STerm.save s p v) r hr).denote σ =
      (.app3 .saveIn (Tms.STerm.select s r hr) p' v : Tm C Γ (.sts sn)).denote σ := by
  have hd := Tm.shift?_denote σ p h
  show ((s.denote σ).copyTo (p.denote σ) (v.denote σ)).select hr =
    ((s.denote σ).select hr).copyTo (p'.denote σ) (v.denote σ)
  rw [hd, Obs.select_copyTo]

theorem Tm.selectOnSaveFrame_denote {s : Tm C Γ .st} {T : Ty} {p : Tm C Γ (.path T)}
    {v : Tm C Γ (.sv T)} {r sn r' sn' : Name} {hr : C.rootType r = some (.ref (.struct sn))}
    {hr' : C.rootType r' = some (.ref (.struct sn'))} {p' : Tm C Γ (.spath sn' T)}
    (h : p.shift? = some ⟨r', sn', hr', p'⟩) (hne : r' ≠ r) (σ : State C Γ) :
    (Tms.STerm.select (Tms.STerm.save s p v) r hr).denote σ =
      (Tms.STerm.select s r hr).denote σ := by
  have hd := Tm.shift?_denote σ p h
  obtain ⟨q', hq'⟩ := Tm.spath_isRef σ p'
  show ((s.denote σ).copyTo (p.denote σ) (v.denote σ)).select hr = (s.denote σ).select hr
  rw [hd, hq']
  exact Obs.select_copyTo_ne _ hr hr' hne q' _

theorem Tm.selectOnDelAtMember_denote {s : Tm C Γ .st} {T : Ty} {p : Tm C Γ (.path T)}
    {r sn : Name} {hr : C.rootType r = some (.ref (.struct sn))}
    {p' : Tm C Γ (.spath sn T)} (h : p.shift? = some ⟨r, sn, hr, p'⟩) (σ : State C Γ) :
    (Tms.STerm.select (Tms.STerm.delAt s p) r hr).denote σ =
      (.app2 .delAtIn (Tms.STerm.select s r hr) p' : Tm C Γ (.sts sn)).denote σ := by
  have hd := Tm.shift?_denote σ p h
  show ((s.denote σ).delAt (p.denote σ)).select hr = ((s.denote σ).select hr).delAt (p'.denote σ)
  rw [hd, Obs.select_delAt]

theorem Tm.selectOnDelAtFrame_denote {s : Tm C Γ .st} {T : Ty} {p : Tm C Γ (.path T)}
    {r sn r' sn' : Name} {hr : C.rootType r = some (.ref (.struct sn))}
    {hr' : C.rootType r' = some (.ref (.struct sn'))} {p' : Tm C Γ (.spath sn' T)}
    (h : p.shift? = some ⟨r', sn', hr', p'⟩) (hne : r' ≠ r) (σ : State C Γ) :
    (Tms.STerm.select (Tms.STerm.delAt s p) r hr).denote σ =
      (Tms.STerm.select s r hr).denote σ := by
  have hd := Tm.shift?_denote σ p h
  obtain ⟨q', hq'⟩ := Tm.spath_isRef σ p'
  show ((s.denote σ).delAt (p.denote σ)).select hr = (s.denote σ).select hr
  rw [hd, hq']
  exact Obs.select_delAt_ne _ hr hr' hne q'

theorem Tm.selectOnSaveMemberAt_denote {sn sn' f : Name} {s : Tm C Γ (.sts sn)} {T : Ty}
    {p : Tm C Γ (.spath sn T)} {v : Tm C Γ (.sv T)}
    {hf : C.fieldType sn f = some (.ref (.struct sn'))} {p' : Tm C Γ (.spath sn' T)}
    (h : p.shiftIn? = some ⟨f, sn', hf, p'⟩) (σ : State C Γ) :
    (.app1 (.selectIn hf) (.app3 .saveIn s p v) : Tm C Γ (.sts sn')).denote σ =
      (.app3 .saveIn (.app1 (.selectIn hf) s) p' v : Tm C Γ (.sts sn')).denote σ := by
  have hd : p.denote σ = SLoc.under (C := Contract.ofStruct sn) hf (p'.denote σ) :=
    Tm.shiftIn?_ok σ p _ h
  show Obs.select (C := Contract.ofStruct sn) ((s.denote σ).copyTo (p.denote σ) (v.denote σ)) hf =
    (Obs.select (C := Contract.ofStruct sn) (s.denote σ) hf).copyTo (p'.denote σ) (v.denote σ)
  rw [hd, Obs.select_copyTo]

theorem Tm.selectOnSaveFrameAt_denote {sn sn' sn'' f f' : Name} {s : Tm C Γ (.sts sn)} {T : Ty}
    {p : Tm C Γ (.spath sn T)} {v : Tm C Γ (.sv T)}
    {hf : C.fieldType sn f = some (.ref (.struct sn'))}
    {hf' : C.fieldType sn f' = some (.ref (.struct sn''))} {p' : Tm C Γ (.spath sn'' T)}
    (h : p.shiftIn? = some ⟨f', sn'', hf', p'⟩) (hne : f' ≠ f) (σ : State C Γ) :
    (.app1 (.selectIn hf) (.app3 .saveIn s p v) : Tm C Γ (.sts sn')).denote σ =
      (.app1 (.selectIn hf) s : Tm C Γ (.sts sn')).denote σ := by
  have hd : p.denote σ = SLoc.under (C := Contract.ofStruct sn) hf' (p'.denote σ) :=
    Tm.shiftIn?_ok σ p _ h
  obtain ⟨q', hq'⟩ := Tm.spath_isRef σ p'
  show Obs.select (C := Contract.ofStruct sn) ((s.denote σ).copyTo (p.denote σ) (v.denote σ)) hf =
    Obs.select (C := Contract.ofStruct sn) (s.denote σ) hf
  rw [hd, hq']
  exact Obs.select_copyTo_ne (C := Contract.ofStruct sn) _ hf hf' hne q' _

theorem Tm.selectOnDelAtMemberAt_denote {sn sn' f : Name} {s : Tm C Γ (.sts sn)} {T : Ty}
    {p : Tm C Γ (.spath sn T)} {hf : C.fieldType sn f = some (.ref (.struct sn'))}
    {p' : Tm C Γ (.spath sn' T)} (h : p.shiftIn? = some ⟨f, sn', hf, p'⟩) (σ : State C Γ) :
    (.app1 (.selectIn hf) (.app2 .delAtIn s p) : Tm C Γ (.sts sn')).denote σ =
      (.app2 .delAtIn (.app1 (.selectIn hf) s) p' : Tm C Γ (.sts sn')).denote σ := by
  have hd : p.denote σ = SLoc.under (C := Contract.ofStruct sn) hf (p'.denote σ) :=
    Tm.shiftIn?_ok σ p _ h
  show Obs.select (C := Contract.ofStruct sn) ((s.denote σ).delAt (p.denote σ)) hf =
    (Obs.select (C := Contract.ofStruct sn) (s.denote σ) hf).delAt (p'.denote σ)
  rw [hd, Obs.select_delAt]

theorem Tm.selectOnDelAtFrameAt_denote {sn sn' sn'' f f' : Name} {s : Tm C Γ (.sts sn)} {T : Ty}
    {p : Tm C Γ (.spath sn T)} {hf : C.fieldType sn f = some (.ref (.struct sn'))}
    {hf' : C.fieldType sn f' = some (.ref (.struct sn''))} {p' : Tm C Γ (.spath sn'' T)}
    (h : p.shiftIn? = some ⟨f', sn'', hf', p'⟩) (hne : f' ≠ f) (σ : State C Γ) :
    (.app1 (.selectIn hf) (.app2 .delAtIn s p) : Tm C Γ (.sts sn')).denote σ =
      (.app1 (.selectIn hf) s : Tm C Γ (.sts sn')).denote σ := by
  have hd : p.denote σ = SLoc.under (C := Contract.ofStruct sn) hf' (p'.denote σ) :=
    Tm.shiftIn?_ok σ p _ h
  obtain ⟨q', hq'⟩ := Tm.spath_isRef σ p'
  show Obs.select (C := Contract.ofStruct sn) ((s.denote σ).delAt (p.denote σ)) hf =
    Obs.select (C := Contract.ofStruct sn) (s.denote σ) hf
  rw [hd, hq']
  exact Obs.select_delAt_ne (C := Contract.ofStruct sn) _ hf hf' hne q'

/-- Two storages of members that denote alike are read alike, in any
context. -/
theorem Tm.findIn_fill_theq {sn sn₁ : Name} {s s' : Tm C Γ (.sts sn)}
    (h : ∀ σ : State C Γ, s.denote σ = s'.denote σ) (K : SCtxS C Γ sn sn₁) {P : PrimTy}
    (q : Tm C Γ (.spath sn₁ (.prim P))) :
    Tm.Theq (.app2 .findIn (K.fill s) q) (.app2 .findIn (K.fill s') q) := fun σ => by
  show some (((K.fill s).denote σ).word (q.denote σ)) = some (((K.fill s').denote σ).word (q.denote σ))
  rw [SCtxS.fill_denote h K σ]

/-- `q.extendsIn p` gives `q`'s location `p`'s followed by a path. -/
theorem Tm.extendsIn_denote (σ : State C Γ) {sn : Name} {T U : Ty} {p : Tm C Γ (.spath sn U)}
    (q : Tm C Γ (.spath sn T)) (h : q.extendsIn p = true) :
    ∃ r : Path U T, r.labels ≠ [] ∧ q.denote σ = ObsLoc.app (p.denote σ) r := by
  have key : ∀ {u : Srt} (q : Tm C Γ u), q.extendsAnyIn (·.beqR p) = true →
      Srt.BelowIn (p.denote σ) u (q.denote σ) := by
    intro u q
    induction q with
    | app1 o x ih =>
      intro h
      cases o with
      | fieldIn hf =>
        intro e
        subst e
        rcases Bool.or_eq_true_iff.mp h with h | h
        · have e2 := Tm.sigma_eq_of_beqR h
          simp only [Sigma.mk.injEq, Srt.spath.injEq] at e2
          obtain ⟨⟨-, rfl⟩, hh⟩ := e2
          refine ⟨.field hf .nil, by simp only [Path.labels, ne_eq, reduceCtorEq,
            not_false_eq_true], ?_⟩
          show ObsLoc.app (x.denote σ) _ = _
          rw [eq_of_heq hh]
        · obtain ⟨r, hr, hq⟩ := ih h rfl
          refine ⟨r.append (.field hf .nil), ?_, ?_⟩
          · rw [Path.labels_append]; exact List.append_ne_nil_of_left_ne_nil hr _
          · show ObsLoc.app (x.denote σ) _ = _
            rw [show x.denote σ = _ from hq, ObsLoc.app_app]
      | _ => cases h
    | _ => intro h; cases h
  exact key q h rfl

/-- **Each scoped term taclet is sound**: its two terms have one Theory value
in every state (`TermTaclet.sound`). -/
theorem TermTaclet.sound {P : PrimTy} {t t' : Tm C Γ (.val P)} : TermTaclet t t' → Tm.Theq t t'
  | @findOnSave _ _ s _ p q v hp hq => fun σ => by
    show some (((s.denote σ).copyTo (p.denote σ) (TVal.ofWord v)).word (q.denote σ)) = some v
    rw [← Tm.sameSegs_denote σ hq, Obs.copyTo_word_same]
    rfl
  | @findOnSaveFrame _ _ s _ _ p q v h => fun σ => by
    show some (((s.denote σ).copyTo (p.denote σ) (v.denote σ)).word (q.denote σ)) =
      some ((s.denote σ).word (q.denote σ))
    rw [Obs.copyTo, Obs.save_word_frame _ _ (Tm.diverges_denote_nil σ h)]
  | @findMemberCons _ _ s _ p r sn hr p' h => fun σ => by
    show some ((s.denote σ).word (p.denote σ)) = some (((s.denote σ).select hr).word (p'.denote σ))
    rw [Tm.shift?_denote σ p h]
    rfl
  | @findMemberConsIn _ _ sn s _ p f sn' hf p' h => fun σ => by
    have hd : p.denote σ = SLoc.under (C := Contract.ofStruct sn) hf (p'.denote σ) :=
      Tm.shiftIn?_ok σ p _ h
    show some ((s.denote σ).word (p.denote σ)) =
      some ((Obs.select (C := Contract.ofStruct sn) (s.denote σ) hf).word (p'.denote σ))
    rw [hd]
    rfl
  | @findOnSaveIn _ _ sn s _ p q v hq => fun σ => by
    obtain rfl := Tm.eq_of_beqR hq
    show some (((s.denote σ).copyTo (p.denote σ) (TVal.ofWord v)).word (p.denote σ)) = some v
    rw [Obs.copyTo_word_same]
    rfl
  | @selectOnSaveMember _ _ s _ p v r sn hr p' _ q h =>
    Tm.findIn_fill_theq (Tm.selectOnSaveMember_denote h) .hole q
  | @selectOnSaveFrame _ _ s _ p v r sn r' sn' hr hr' p' _ q h hne =>
    Tm.findIn_fill_theq (Tm.selectOnSaveFrame_denote h hne) .hole q
  | @selectOnDelAtMember _ _ s _ p r sn hr p' _ q h =>
    Tm.findIn_fill_theq (Tm.selectOnDelAtMember_denote h) .hole q
  | @selectOnDelAtFrame _ _ s _ p r sn r' sn' hr hr' p' _ q h hne =>
    Tm.findIn_fill_theq (Tm.selectOnDelAtFrame_denote h hne) .hole q
  | @selectOnSaveMemberIn _ _ s _ p v r sn hr p' _ K _ q h =>
    Tm.findIn_fill_theq (Tm.selectOnSaveMember_denote h) K q
  | @selectOnSaveFrameIn _ _ s _ p v r sn r' sn' hr hr' p' _ K _ q h hne =>
    Tm.findIn_fill_theq (Tm.selectOnSaveFrame_denote h hne) K q
  | @selectOnDelAtMemberIn _ _ s _ p r sn hr p' _ K _ q h =>
    Tm.findIn_fill_theq (Tm.selectOnDelAtMember_denote h) K q
  | @selectOnDelAtFrameIn _ _ s _ p r sn r' sn' hr hr' p' _ K _ q h hne =>
    Tm.findIn_fill_theq (Tm.selectOnDelAtFrame_denote h hne) K q
  | @selectOnSaveMemberAt _ _ sn sn' f s _ p v hf p' _ K _ q h =>
    Tm.findIn_fill_theq (Tm.selectOnSaveMemberAt_denote h) K q
  | @selectOnSaveFrameAt _ _ sn sn' sn'' f f' s _ p v hf hf' p' _ K _ q h hne =>
    Tm.findIn_fill_theq (Tm.selectOnSaveFrameAt_denote h hne) K q
  | @selectOnDelAtMemberAt _ _ sn sn' f s _ p hf p' _ K _ q h =>
    Tm.findIn_fill_theq (Tm.selectOnDelAtMemberAt_denote h) K q
  | @selectOnDelAtFrameAt _ _ sn sn' sn'' f f' s _ p hf hf' p' _ K _ q h hne =>
    Tm.findIn_fill_theq (Tm.selectOnDelAtFrameAt_denote h hne) K q
  | @findOnDelAt _ _ s P p q w hw hp hq => fun σ => by
    show some (((s.denote σ).delAt (p.denote σ)).word (q.denote σ)) = some (PrimTy.dflt P)
    rw [← Tm.sameSegs_denote σ hq, Obs.delAt_word_same]
  | @findOnDelAtValue _ _ s _ p _ q hp hq => fun σ => by
    obtain ⟨rfl, hh⟩ := Tm.sameSegs_heq σ hq
    show some (((s.denote σ).delAt (p.denote σ)).word (q.denote σ)) =
      (some ((s.denote σ).word (q.denote σ))).map fun _ => PrimTy.dflt _
    rw [← eq_of_heq hh, Obs.delAt_word_same]
    rfl
  | @delValueLit _ _ P w => fun σ => rfl
  | @findOnDelAtBelow _ _ s _ p P q w hk hw hp hq => fun σ => by
    obtain ⟨r, -, hqr⟩ := Tm.extends_denote σ q hq
    show some (((s.denote σ).delAt (p.denote σ)).word (q.denote σ)) = some (PrimTy.dflt P)
    rw [hqr, Obs.delAt_word_below]
    exact congrArg some (hk σ r)
  | @findOnDelAtBelowIn _ _ sn s _ p P q w hk hw hq => fun σ => by
    obtain ⟨r, -, hqr⟩ := Tm.extendsIn_denote σ q hq
    show some (((s.denote σ).delAt (p.denote σ)).word (q.denote σ)) = some (PrimTy.dflt P)
    rw [hqr, Obs.delAt_word_below]
    exact congrArg some (hk σ r)
  | @findOnDelAtFrame _ _ s _ p _ q h => fun σ => by
    show some (((s.denote σ).delAt (p.denote σ)).word (q.denote σ)) =
      some ((s.denote σ).word (q.denote σ))
    rw [Obs.delAt, Obs.save_word_frame _ _ (Tm.diverges_denote_nil σ h)]
  | @findOnPushFrame _ _ s _ p v _ q h => fun σ => by
    show some (((s.denote σ).push (p.denote σ) (TVal.strip (v.denote σ))).word (q.denote σ)) =
      some ((s.denote σ).word (q.denote σ))
    rw [Obs.push, Obs.save_word_frame _ _ (Tm.diverges_denote_nil σ h)]
  | @findOnPopFrame _ _ s _ p _ q h => fun σ => by
    show some (((s.denote σ).pop false (p.denote σ)).word (q.denote σ)) =
      some ((s.denote σ).word (q.denote σ))
    rw [Obs.pop, Obs.save_word_frame _ _ (Tm.diverges_denote_nil σ h)]
  | @lenOnSaveFrame _ _ s _ q v _ p h => fun σ => by
    show lenW (((s.denote σ).copyTo (q.denote σ) (v.denote σ)).len (p.denote σ)) =
      lenW ((s.denote σ).len (p.denote σ))
    rw [Obs.copyTo, Obs.save_len_frame _ _ (Tm.divergesLen_denote σ h)]
  | @lenOnDelAtFrame _ _ s _ q _ p h => fun σ => by
    show lenW (((s.denote σ).delAt (q.denote σ)).len (p.denote σ)) =
      lenW ((s.denote σ).len (p.denote σ))
    rw [Obs.delAt, Obs.save_len_frame _ _ (Tm.divergesLen_denote σ h)]
  | .theory h => h
  | .symm r => r.sound.symm

end Sound

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
