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

open Semantics Theory Theory.StValue
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
    | _ => failure
  let t ← withOptions (fun o => pp.sol.tmField.set (pp.sol.reduce.set o false) true)
    (printer (← unfoldTmsSyms e'))
  guard !(isEscape t)
  `(tm{ $t })

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

/-- An index literal, as the integer it is hashed as. -/
def Tm.litInt? {u : Srt} (t : Tm C Γ u) : Option Int :=
  t.litW?.map fun w => asInt (.prim (PrimTy.erase w.2))

/-- A root's segment. -/
def Op0.shapeLeaf? {s : Srt} : Op0 C s → Option (List SegT)
  | .root r _ => some [.field r]
  | _ => none

/-- A member or an element after a path's shape. -/
def Op1.shapeStep {a s : Srt} : Op1 C a s → Option (List SegT) → Option (List SegT)
  | .field (f := f) _, ih => ih.map (· ++ [.field f])
  | .next, ih => ih.map (· ++ [.at none])
  | _, _ => none

/-- An element after a path's shape, at a literal index or not. -/
def Op2.shapeStep {a b s : Srt} : Op2 C a b s → Tm C Γ b → Option (List SegT) →
    Option (List SegT) → Option (List SegT)
  | .at _, i, ihx, _ => ihx.map (· ++ [.at i.litInt?])
  | .nextIn, _, _, ihy => ihy.map (· ++ [.at none])
  | _, _, _, _ => none

/-- A checked element after a path's shape. -/
def Op3.shapeStep {a b c s : Srt} : Op3 C a b c s → Tm C Γ c → Option (List SegT) →
    Option (List SegT)
  | .atIn _, i, ihy => ihy.map (· ++ [.at i.litInt?])
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
  | some a, some b => SegT.diverges a (b ++ [.field "length"])
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

/-- The node at `p` in `s` is not a mapping, in every state. -/
def Tm.KindFreeAt {T : Ty} (s : Tm C Γ .st) (p : Tm C Γ (.path T)) : Prop :=
  ∀ σ : State C Γ, (findSt (s.denote σ) (p.denote σ)).kindFree = true

end Side

/-! ## The side conditions in the Theory -/

/-- A sort's Theory denotation as segments: a path's, `[]` for the rest. -/
def Srt.segs : (u : Srt) → u.TDen → List Seg
  | .path _, d => d
  | .spath _ _, d => d
  | _, _ => []

/-- A sort's Theory denotation as a storage: a storage's, `mtSt` for the
rest. -/
def Srt.stDen : (u : Srt) → u.TDen → Struct
  | .st, d => d
  | _, _ => .mtSt

section SideDenote

variable {Γ : Ctx} (σ : State C Γ)

/-- `hasSeg` gives the Theory's `p ≠ []` in every state. -/
theorem Tm.denote_ne_nil {T : Ty} {p : Tm C Γ (.path T)} (hp : p.hasSeg = true) :
    p.denote σ ≠ [] := by
  cases p with
  | pvP _ => exact absurd hp Bool.false_ne_true
  | app0 o => cases o; exact List.cons_ne_nil _ _
  | app1 o _ => cases o <;> exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
  | app2 o _ _ => cases o <;> exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
  | app3 o _ _ _ => cases o; exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)

/-- A literal reads its word in the Theory. -/
theorem Tm.litW?_denote {p : PrimTy} {t : Tm C Γ (.val p)} {w : (p : PrimTy) × p.Denote}
    (h : t.litW? = some w) : t.denote σ = .prim (PrimTy.erase w.2) := by
  cases t with
  | app0 o =>
    cases o with
    | lit v => cases h; rfl
    | _ => cases h
  | _ => cases h

/-- An index literal reads its integer in the Theory. -/
theorem Tm.litInt?_denote {p : PrimTy} {t : Tm C Γ (.val p)} {i : Int} (h : t.litInt? = some i) :
    asInt (t.denote σ) = i := by
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [Tm.litW?_denote σ hw]

/-- A path has its shape in every state; generic in the sort, a path's
segments read by `Srt.segs`. -/
theorem Tm.shape?_matches' {u : Srt} (p : Tm C Γ u) :
    ∀ {a : List SegT}, p.shape? = some a → SegT.matches a (u.segs (p.denote σ)) = true := by
  induction p with
  | app0 o =>
    intro a h
    cases o with
    | root r hr =>
      cases h
      simp only [Srt.segs, Tm.denote, Op0.denote, rootPath, SegT.matches, SegT.fits,
        beq_self_eq_true, Bool.and_self]
    | _ => cases h
  | app1 o x ih =>
    intro a h
    cases o with
    | field hf =>
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      exact SegT.matches_append _ _ _ _ (ih ha)
        (by simp only [SegT.matches, SegT.fits, beq_self_eq_true, Bool.and_self])
    | next =>
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      exact SegT.matches_append _ _ _ _ (ih ha) rfl
    | _ => cases h
  | app2 o x y ihx ihy =>
    intro a h
    cases o with
    | «at» it =>
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      refine SegT.matches_append _ _ _ _ (ihx ha) ?_
      cases hi : Tm.litInt? y with
      | none => rfl
      | some k =>
        have hk := Tm.litInt?_denote σ hi
        show SegT.matches [.at (some k)] [.at (asInt (y.denote σ))] = true
        simp only [hk, SegT.matches, SegT.fits, beq_self_eq_true, Bool.and_self]
    | nextIn =>
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      exact SegT.matches_append _ _ _ _ (ihy ha) rfl
    | _ => cases h
  | app3 o x y z _ ihy _ =>
    intro a h
    cases o with
    | atIn it =>
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      refine SegT.matches_append _ _ _ _ (ihy ha) ?_
      cases hi : Tm.litInt? z with
      | none => rfl
      | some k =>
        have hk := Tm.litInt?_denote σ hi
        show SegT.matches [.at (some k)] [.at (asInt (z.denote σ))] = true
        simp only [hk, SegT.matches, SegT.fits, beq_self_eq_true, Bool.and_self]
    | _ => cases h
  | _ => intro a h; cases h

/-- A path has its shape in every state. -/
theorem Tm.shape?_matches {T : Ty} (p : Tm C Γ (.path T)) {a : List SegT}
    (h : p.shape? = some a) : SegT.matches a (p.denote σ) = true :=
  Tm.shape?_matches' σ p h

/-- `Tm.diverges` gives the Theory's `diverges` in every state. -/
theorem Tm.diverges_denote {T U : Ty} {p : Tm C Γ (.path T)} {q : Tm C Γ (.path U)}
    (h : p.diverges q = true) : Theory.StValue.diverges (p.denote σ) (q.denote σ) = true := by
  unfold Tm.diverges at h
  split at h
  · rename_i a b ha hb
    exact SegT.diverges_sound a b _ _ h (p.shape?_matches σ ha) (q.shape?_matches σ hb)
  · exact absurd h Bool.false_ne_true

/-- `Tm.divergesLen` gives the Theory's `diverges q (p ++ [lengthSeg])`. -/
theorem Tm.divergesLen_denote {T U : Ty} {q : Tm C Γ (.path T)} {p : Tm C Γ (.path U)}
    (h : q.divergesLen p = true) :
    Theory.StValue.diverges (q.denote σ) (p.denote σ ++ [lengthSeg]) = true := by
  unfold Tm.divergesLen at h
  split at h
  · rename_i a b ha hb
    exact SegT.diverges_sound _ _ _ _ h (q.shape?_matches σ ha)
      (SegT.matches_append _ _ _ _ (p.shape?_matches σ hb) (by decide))
  · exact absurd h Bool.false_ne_true

/-- A check erased leaves the Theory's path, in every state; generic in the
sort. -/
theorem Tm.eraseChecks_denote' {u : Srt} (p : Tm C Γ u) :
    p.eraseChecks.denote σ = p.denote σ := by
  induction p with
  | app1 o x ih =>
    cases o <;> first | rfl | (show x.eraseChecks.denote σ ++ _ = x.denote σ ++ _; rw [ih])
  | app2 o x y ihx ihy =>
    cases o <;>
      first
      | rfl
      | (show x.eraseChecks.denote σ ++ _ = x.denote σ ++ _; rw [ihx])
      | (show y.eraseChecks.denote σ ++ _ = y.denote σ ++ _; rw [ihy])
  | app3 o x y z _ ihy _ =>
    cases o <;> first | rfl | (show y.eraseChecks.denote σ ++ _ = y.denote σ ++ _; rw [ihy])
  | _ => rfl

theorem Tm.eraseChecks_denote {T : Ty} (p : Tm C Γ (.path T)) :
    p.eraseChecks.denote σ = p.denote σ :=
  Tm.eraseChecks_denote' σ p

/-- `sameSegs` gives one Theory path in every state. -/
theorem Tm.sameSegs_denote {T U : Ty} {p : Tm C Γ (.path T)} {q : Tm C Γ (.path U)}
    (h : p.sameSegs q = true) : p.denote σ = q.denote σ := by
  rw [← Tm.eraseChecks_denote σ p, ← Tm.eraseChecks_denote σ q]
  have e := Tm.sigma_eq_of_beqR h
  generalize p.eraseChecks = p' at e
  generalize q.eraseChecks = q' at e
  cases e
  rfl

/-- `q.extends p` gives the Theory's `q = p ++ r`, `r ≠ []`, in every
state; generic in the sort. -/
theorem Tm.extends_denote' {U : Ty} {p : Tm C Γ (.path U)} {u : Srt} (q : Tm C Γ u) :
    q.extendsAny (·.beqR p) = true →
      ∃ r, r ≠ [] ∧ u.segs (q.denote σ) = p.denote σ ++ r := by
  induction q with
  | app1 o x ih =>
    intro h
    cases o with
    | field hf =>
      rename_i f _
      rcases Bool.or_eq_true_iff.mp h with h | h
      · cases Tm.sigma_eq_of_beqR h
        exact ⟨[.field f], List.cons_ne_nil _ _, rfl⟩
      · obtain ⟨r, -, hq⟩ := ih h
        refine ⟨r ++ [.field f], List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _), ?_⟩
        show x.denote σ ++ _ = _
        rw [show x.denote σ = _ from hq, List.append_assoc]
    | _ => cases h
  | app2 o x y ihx _ =>
    intro h
    cases o with
    | «at» it =>
      rcases Bool.or_eq_true_iff.mp h with h | h
      · cases Tm.sigma_eq_of_beqR h
        exact ⟨[.at (asInt (y.denote σ))], List.cons_ne_nil _ _, rfl⟩
      · obtain ⟨r, -, hq⟩ := ihx h
        refine ⟨r ++ [.at (asInt (y.denote σ))],
          List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _), ?_⟩
        show x.denote σ ++ _ = _
        rw [show x.denote σ = _ from hq, List.append_assoc]
    | _ => cases h
  | app3 o x y z _ ihy _ =>
    intro h
    cases o with
    | atIn it =>
      rcases Bool.or_eq_true_iff.mp h with h | h
      · cases Tm.sigma_eq_of_beqR h
        exact ⟨[.at (asInt (z.denote σ))], List.cons_ne_nil _ _, rfl⟩
      · obtain ⟨r, -, hq⟩ := ihy h
        refine ⟨r ++ [.at (asInt (z.denote σ))],
          List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _), ?_⟩
        show y.denote σ ++ _ = _
        rw [show y.denote σ = _ from hq, List.append_assoc]
    | _ => cases h
  | _ => intro h; cases h

theorem Tm.extends_denote {T U : Ty} {p : Tm C Γ (.path U)} (q : Tm C Γ (.path T))
    (h : q.extends p = true) : ∃ r, r ≠ [] ∧ q.denote σ = p.denote σ ++ r :=
  Tm.extends_denote' σ q h

/-- What `shift?` gives splits the Theory's path at its head. -/
def Srt.ShiftOK' (σ : State C Γ) : (u : Srt) → u.ShiftD C Γ → u.TDen → Prop
  | .path _, sh, d => d = .field sh.r :: sh.p.denote σ ∧ sh.p.denote σ ≠ []
  | _, _, _ => True

/-- What `shift?` gives, if anything, splits the path; generic in the sort. -/
def Srt.ShiftOK (σ : State C Γ) (u : Srt) (o : Option (u.ShiftD C Γ)) (d : u.TDen) : Prop :=
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
        have hd : x.denote σ = [.field r] := by
          cases x with
          | app0 o =>
            cases o with
            | root r' hr' => cases hx; rfl
            | _ => cases hx
          | _ => cases hx
        exact ⟨by show x.denote σ ++ _ = _; rw [hd]; rfl, List.cons_ne_nil _ _⟩
      | none =>
        rw [hx] at h
        obtain ⟨sh', hs, rfl⟩ := Option.map_eq_some_iff.1 h
        obtain ⟨ih, -⟩ := ih sh' hs
        exact ⟨by show x.denote σ ++ _ = _; rw [ih]; rfl,
          List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)⟩
    | _ => intro sh h; cases h
  | _ => intro sh h; cases h

/-- `shift?` splits the Theory's path at its head, in every state; the rest
has a segment. -/
theorem Tm.shift?_denote {T : Ty} (p : Tm C Γ (.path T)) {sh : Shifted C Γ T}
    (h : p.shift? = some sh) : p.denote σ = .field sh.r :: sh.p.denote σ ∧ sh.p.denote σ ≠ [] := by
  exact Tm.shift?_ok σ p sh h

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

/-- A literal written value reads its word in the Theory. -/
theorem Tm.svLit?_denote (σ : State C Γ) {T : Ty} {v : Tm C Γ (.sv T)}
    {w : (p : PrimTy) × p.Denote} (h : v.svLit? = some w) :
    v.denote σ = .prim (PrimTy.erase w.2) := by
  cases v with
  | app1 o x =>
    cases o with
    | sval => exact Tm.litW?_denote σ (t := x) h
    | _ => cases h
  | _ => cases h

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
  path `p` its checks aside (`find_copyTo_same`). -/
  | findOnSave {s : Tm C Γ .st} {P : PrimTy} {p q : Tm C Γ (.path (.prim P))} {v : P.Denote}
      (hp : p.hasSeg = true := by rfl)
      (hq : p.sameSegs q = true := by first | rfl | exact Tm.sameSegs_refl _) :
      TermTaclet (Tms.Term.find (Tms.STerm.save s p (Tms.SValT.val (Tms.Term.lit v))) q)
        (Tms.Term.lit v)
  /-- **`findOnSaveFrame`**: a read at a path that leaves the written one does
  not see the write (`find_copyTo_frame`). -/
  | findOnSaveFrame {s : Tm C Γ .st} {T : Ty} {P : PrimTy} {p : Tm C Γ (.path T)}
      {q : Tm C Γ (.path (.prim P))} {v : Tm C Γ (.sv T)} (h : p.diverges q = true := by rfl) :
      TermTaclet (Tms.Term.find (Tms.STerm.save s p v) q) (Tms.Term.find s q)
  /-- **`findMemberCons`**: `find(s, r.p) ⇝ find(select(s, r), p)`, the path
  read from its head (`find_cons`). -/
  | findMemberCons {s : Tm C Γ .st} {P : PrimTy} {p : Tm C Γ (.path (.prim P))} {r sn : Name}
      {hr : C.rootType r = some (.ref (.struct sn))} {p' : Tm C Γ (.spath sn (.prim P))}
      (h : p.shift? = some ⟨r, sn, hr, p'⟩ := by rfl) :
      TermTaclet (Tms.Term.find s p) (.app2 .findIn (Tms.STerm.select s r hr) p')
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
  /-- **`findOnDelAt`**: where `s` reads the word `w` at `p`, the delete
  leaves its default (`find_delAt_same`, `delValueDefault`). -/
  | findOnDelAt {s : Tm C Γ .st} {P : PrimTy} {p q : Tm C Γ (.path (.prim P))} {w : P.Denote}
      (hw : TermTaclet (Tms.Term.find s p) (Tms.Term.lit w)) (hp : p.hasSeg = true := by rfl)
      (hq : p.sameSegs q = true := by first | rfl | exact Tm.sameSegs_refl _) :
      TermTaclet (Tms.Term.find (Tms.STerm.delAt s p) q) (Tms.Term.dflt P)
  /-- **`findOnDelAtValue`**: the delete leaves at its path the default of
  what was there (`find_delAt_same`). -/
  | findOnDelAtValue {s : Tm C Γ .st} {T : Ty} {p : Tm C Γ (.path T)} {P : PrimTy}
      {q : Tm C Γ (.path (.prim P))} (hp : p.hasSeg = true := by rfl)
      (hq : p.sameSegs q = true := by first | rfl | exact Tm.sameSegs_refl _) :
      TermTaclet (Tms.Term.find (Tms.STerm.delAt s p) q) (Tms.Term.delValue (Tms.Term.find s q))
  /-- **`delValueLit`**: the default of a word (`delValueDefault`). -/
  | delValueLit {P : PrimTy} {w : P.Denote} :
      TermTaclet (Tms.Term.delValue (Tms.Term.lit w)) (Tms.Term.dflt P)
  /-- **`findOnDelAtBelow`**: below a deleted node that is not a mapping,
  every word reads its default (`find_delAt_below`, `delValueDefault`). -/
  | findOnDelAtBelow {s : Tm C Γ .st} {T : Ty} {p : Tm C Γ (.path T)} {P : PrimTy}
      {q : Tm C Γ (.path (.prim P))} {w : P.Denote} (hk : s.KindFreeAt p)
      (hw : s.findLit? q = some w := by rfl) (hp : p.hasSeg = true := by rfl)
      (hq : q.extends p = true := by rfl) :
      TermTaclet (Tms.Term.find (Tms.STerm.delAt s p) q) (Tms.Term.dflt P)
  /-- **`findOnDelAtFrame`**: a read off the deleted path does not see the
  delete (`find_delAt_frame`). -/
  | findOnDelAtFrame {s : Tm C Γ .st} {T : Ty} {p : Tm C Γ (.path T)} {P : PrimTy}
      {q : Tm C Γ (.path (.prim P))} (h : p.diverges q = true := by rfl) :
      TermTaclet (Tms.Term.find (Tms.STerm.delAt s p) q) (Tms.Term.find s q)
  /-- **`findOnPushFrame`**: a read off the array's path does not see a push
  (`find_pushT_frame`). -/
  | findOnPushFrame {s : Tm C Γ .st} {E : Ty} {p : Tm C Γ (.path (.ref (.array E)))}
      {v : Tm C Γ (.sv E)} {P : PrimTy} {q : Tm C Γ (.path (.prim P))}
      (h : p.diverges q = true := by rfl) :
      TermTaclet (Tms.Term.find (Tms.STerm.push s p v) q) (Tms.Term.find s q)
  /-- **`findOnPopFrame`**: a read off the array's path does not see a pop
  (`find_popT_frame`). -/
  | findOnPopFrame {s : Tm C Γ .st} {E : Ty} {p : Tm C Γ (.path (.ref (.array E)))}
      {P : PrimTy} {q : Tm C Γ (.path (.prim P))} (h : p.diverges q = true := by rfl) :
      TermTaclet (Tms.Term.find (Tms.STerm.pop s p) q) (Tms.Term.find s q)
  /-- **`lenOnSaveFrame`**: a length read off the written path does not see
  the write (`find_copyTo_frame`). -/
  | lenOnSaveFrame {s : Tm C Γ .st} {T : Ty} {q : Tm C Γ (.path T)} {v : Tm C Γ (.sv T)}
      {E : Ty} {p : Tm C Γ (.path (.ref (.array E)))} (h : q.divergesLen p = true := by rfl) :
      TermTaclet (Tms.Term.len (Tms.STerm.save s q v) p) (Tms.Term.len s p)
  /-- **`lenOnDelAtFrame`**: a length read off the deleted path does not see
  the delete (`find_delAt_frame`). -/
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

/-- A word's default, erased, is the Theory's default of the word. -/
theorem primDefault_erase {P : PrimTy} (w : P.Denote) :
    primDefault (PrimTy.erase w) = PrimTy.erase (PrimTy.dflt P) := by
  cases P <;> rfl

theorem Tm.selectOnSaveMember_denote {s : Tm C Γ .st} {T : Ty} {p : Tm C Γ (.path T)}
    {v : Tm C Γ (.sv T)} {r sn : Name} {hr : C.rootType r = some (.ref (.struct sn))}
    {p' : Tm C Γ (.spath sn T)} (h : p.shift? = some ⟨r, sn, hr, p'⟩) (σ : State C Γ) :
    (Tms.STerm.select (Tms.STerm.save s p v) r hr).denote σ =
      (.app3 .saveIn (Tms.STerm.select s r hr) p' v : Tm C Γ (.sts sn)).denote σ := by
  obtain ⟨hd, hne⟩ := Tm.shift?_denote σ p h
  show asStruct (selectSt (copyTo (s.denote σ) (p.denote σ) (v.denote σ)) (.field r)) =
    copyTo (asStruct (selectSt (s.denote σ) (.field r))) (p'.denote σ) (v.denote σ)
  simp only [hd, copyTo, StValue.selectOnSaveCons, if_true, List.isEmpty_iff, hne, if_false,
    asStruct_st, find_cons _ _ hne]

theorem Tm.selectOnSaveFrame_denote {s : Tm C Γ .st} {T : Ty} {p : Tm C Γ (.path T)}
    {v : Tm C Γ (.sv T)} {r sn r' sn' : Name} {hr : C.rootType r = some (.ref (.struct sn))}
    {hr' : C.rootType r' = some (.ref (.struct sn'))} {p' : Tm C Γ (.spath sn' T)}
    (h : p.shift? = some ⟨r', sn', hr', p'⟩) (hne : r' ≠ r) (σ : State C Γ) :
    (Tms.STerm.select (Tms.STerm.save s p v) r hr).denote σ =
      (Tms.STerm.select s r hr).denote σ := by
  obtain ⟨hd, -⟩ := Tm.shift?_denote σ p h
  show asStruct (selectSt (copyTo (s.denote σ) (p.denote σ) (v.denote σ)) (.field r)) =
    asStruct (selectSt (s.denote σ) (.field r))
  simp only [hd, copyTo, StValue.selectOnSaveCons]
  rw [if_neg (fun e => hne (Seg.field.inj e))]

theorem Tm.selectOnDelAtMember_denote {s : Tm C Γ .st} {T : Ty} {p : Tm C Γ (.path T)}
    {r sn : Name} {hr : C.rootType r = some (.ref (.struct sn))}
    {p' : Tm C Γ (.spath sn T)} (h : p.shift? = some ⟨r, sn, hr, p'⟩) (σ : State C Γ) :
    (Tms.STerm.select (Tms.STerm.delAt s p) r hr).denote σ =
      (.app2 .delAtIn (Tms.STerm.select s r hr) p' : Tm C Γ (.sts sn)).denote σ := by
  obtain ⟨hd, hne⟩ := Tm.shift?_denote σ p h
  show asStruct (selectSt (Theory.StValue.delAt (s.denote σ) (p.denote σ)) (.field r)) =
    Theory.StValue.delAt (asStruct (selectSt (s.denote σ) (.field r))) (p'.denote σ)
  simp only [hd, Theory.StValue.delAt, StValue.selectOnSaveCons, if_true, List.isEmpty_iff, hne,
    if_false, asStruct_st, find_cons _ _ hne]

theorem Tm.selectOnDelAtFrame_denote {s : Tm C Γ .st} {T : Ty} {p : Tm C Γ (.path T)}
    {r sn r' sn' : Name} {hr : C.rootType r = some (.ref (.struct sn))}
    {hr' : C.rootType r' = some (.ref (.struct sn'))} {p' : Tm C Γ (.spath sn' T)}
    (h : p.shift? = some ⟨r', sn', hr', p'⟩) (hne : r' ≠ r) (σ : State C Γ) :
    (Tms.STerm.select (Tms.STerm.delAt s p) r hr).denote σ =
      (Tms.STerm.select s r hr).denote σ := by
  obtain ⟨hd, -⟩ := Tm.shift?_denote σ p h
  show asStruct (selectSt (Theory.StValue.delAt (s.denote σ) (p.denote σ)) (.field r)) =
    asStruct (selectSt (s.denote σ) (.field r))
  simp only [hd, Theory.StValue.delAt, StValue.selectOnSaveCons]
  rw [if_neg (fun e => hne (Seg.field.inj e))]

/-- Two storages of members that denote alike are read alike, in any
context. -/
theorem Tm.findIn_fill_theq {sn sn₁ : Name} {s s' : Tm C Γ (.sts sn)}
    (h : ∀ σ : State C Γ, s.denote σ = s'.denote σ) (K : SCtxS C Γ sn sn₁) {P : PrimTy}
    (q : Tm C Γ (.spath sn₁ (.prim P))) :
    Tm.Theq (.app2 .findIn (K.fill s) q) (.app2 .findIn (K.fill s') q) := fun σ => by
  show Equiv (findSt ((K.fill s).denote σ) (q.denote σ)) (findSt ((K.fill s').denote σ) (q.denote σ))
  rw [SCtxS.fill_denote h K σ]
  exact Equiv.refl _

/-- The word read off the writes is the word read; generic in the sort, a
storage read by `Srt.stDen`. -/
theorem Tm.findLitBy_theq {P : PrimTy} {q : Tm C Γ (.path (.prim P))} (hq : q.hasSeg = true)
    (σ : State C Γ) {u : Srt} (s : Tm C Γ u) : ∀ {w : (p : PrimTy) × p.Denote},
      s.findLitBy (·.sameSegs q) (·.diverges q) = some w →
      Equiv (findSt (u.stDen (s.denote σ)) (q.denote σ)) (.prim (PrimTy.erase w.2)) := by
  induction s with
  | app3 o x y z ihx _ _ =>
    intro w h
    cases o with
    | save =>
      have h : (if y.sameSegs q then z.svLit? else if y.diverges q then
          x.findLitBy (·.sameSegs q) (·.diverges q) else none) = some w := h
      show Equiv (findSt (copyTo (x.denote σ) (y.denote σ) (z.denote σ)) (q.denote σ)) _
      split at h
      · rename_i hpq
        have hp : y.hasSeg = true := (Tm.sameSegs_hasSeg hpq).trans hq
        rw [← Tm.sameSegs_denote σ hpq, find_copyTo_same _ (Tm.denote_ne_nil σ hp),
          Tm.svLit?_denote σ h]
        exact Equiv.refl _
      · split at h
        · rename_i hd
          rw [find_copyTo_frame _ _ _ _ (Tm.diverges_denote σ hd)]
          exact ihx h
        · cases h
    | _ => cases h
  | _ => intro w h; cases h

/-- `findLit?` reads the word the storage holds there. -/
theorem Tm.findLit?_theq {s : Tm C Γ .st} {P : PrimTy} {q : Tm C Γ (.path (.prim P))}
    {w : P.Denote} (h : s.findLit? q = some w) :
    Tm.Theq (Tms.Term.find s q) (Tms.Term.lit w) := fun σ => by
  unfold Tm.findLit? at h
  split at h
  · rename_i hq
    obtain ⟨w', hw', h⟩ := Option.bind_eq_some_iff.1 h
    split at h
    · rename_i e
      obtain ⟨P', w'⟩ := w'
      dsimp only at e
      subst e
      cases h
      exact Tm.findLitBy_theq hq σ s hw'
    · cases h
  · cases h

/-- **Each scoped term taclet is sound**: its two terms have one Theory value
in every state (`TermTaclet.sound`). -/
theorem TermTaclet.sound {P : PrimTy} {t t' : Tm C Γ (.val P)} : TermTaclet t t' → Tm.Theq t t'
  | @findOnSave _ _ s _ p q v hp hq => fun σ => by
    show Equiv (findSt (copyTo (s.denote σ) (p.denote σ) (.prim (PrimTy.erase v))) (q.denote σ))
      (.prim (PrimTy.erase v))
    rw [← Tm.sameSegs_denote σ hq, find_copyTo_same _ (Tm.denote_ne_nil σ hp)]
    exact Equiv.refl _
  | @findOnSaveFrame _ _ s _ _ p q v h => fun σ => by
    show Equiv (findSt (copyTo (s.denote σ) (p.denote σ) (v.denote σ)) (q.denote σ))
      (findSt (s.denote σ) (q.denote σ))
    rw [find_copyTo_frame _ _ _ _ (Tm.diverges_denote σ h)]
    exact Equiv.refl _
  | @findMemberCons _ _ s _ p r sn hr p' h => fun σ => by
    obtain ⟨hd, hne⟩ := Tm.shift?_denote σ p h
    show Equiv (findSt (s.denote σ) (p.denote σ))
      (findSt (asStruct (selectSt (s.denote σ) (.field r))) (p'.denote σ))
    rw [hd, find_cons _ _ hne]
    exact Equiv.refl _
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
  | @findOnDelAt _ _ s P p q w hw hp hq => fun σ => by
    have hr : findSt (s.denote σ) (p.denote σ) = .prim (PrimTy.erase w) :=
      Equiv.prim_iff.1 (hw.sound σ)
    show Equiv (findSt (Theory.StValue.delAt (s.denote σ) (p.denote σ)) (q.denote σ))
      (.prim (PrimTy.erase (PrimTy.dflt P)))
    rw [← Tm.sameSegs_denote σ hq, find_delAt_same _ (Tm.denote_ne_nil σ hp), hr,
      delValueDefault, primDefault_erase]
    exact Equiv.refl _
  | @findOnDelAtValue _ _ s _ p _ q hp hq => fun σ => by
    show Equiv (findSt (Theory.StValue.delAt (s.denote σ) (p.denote σ)) (q.denote σ))
      (StValue.delValue (findSt (s.denote σ) (q.denote σ)))
    rw [← Tm.sameSegs_denote σ hq, find_delAt_same _ (Tm.denote_ne_nil σ hp)]
    exact Equiv.refl _
  | @delValueLit _ _ P w => fun σ => by
    show Equiv (StValue.delValue (.prim (PrimTy.erase w))) (.prim (PrimTy.erase (PrimTy.dflt P)))
    rw [delValueDefault, primDefault_erase]
    exact Equiv.refl _
  | @findOnDelAtBelow _ _ s _ p P q w hk hw hp hq => fun σ => by
    obtain ⟨r, hr, hqr⟩ := Tm.extends_denote σ q hq
    have hw' := Tm.findLit?_theq hw σ
    have hw'' : findSt (s.denote σ) (q.denote σ) = .prim (PrimTy.erase w) := Equiv.prim_iff.1 hw'
    show Equiv (findSt (Theory.StValue.delAt (s.denote σ) (p.denote σ)) (q.denote σ))
      (.prim (PrimTy.erase (PrimTy.dflt P)))
    rw [hqr, find_delAt_below _ (Tm.denote_ne_nil σ hp) hr (hk σ), ← hqr, hw'', delValueDefault,
      primDefault_erase]
    exact Equiv.refl _
  | @findOnDelAtFrame _ _ s _ p _ q h => fun σ => by
    show Equiv (findSt (Theory.StValue.delAt (s.denote σ) (p.denote σ)) (q.denote σ))
      (findSt (s.denote σ) (q.denote σ))
    rw [find_delAt_frame _ (Tm.diverges_denote σ h)]
    exact Equiv.refl _
  | @findOnPushFrame _ _ s _ p v _ q h => fun σ => by
    show Equiv (findSt (pushT (s.denote σ) (p.denote σ) (stripVal (v.denote σ))) (q.denote σ))
      (findSt (s.denote σ) (q.denote σ))
    rw [find_pushT_frame _ _ (Tm.diverges_denote σ h)]
    exact Equiv.refl _
  | @findOnPopFrame _ _ s _ p _ q h => fun σ => by
    show Equiv (findSt (popT (s.denote σ) (p.denote σ)) (q.denote σ))
      (findSt (s.denote σ) (q.denote σ))
    rw [find_popT_frame _ (Tm.diverges_denote σ h)]
    exact Equiv.refl _
  | @lenOnSaveFrame _ _ s _ q v _ p h => fun σ => by
    show Equiv (findSt (copyTo (s.denote σ) (q.denote σ) (v.denote σ)) (p.denote σ ++ [lengthSeg]))
      (findSt (s.denote σ) (p.denote σ ++ [lengthSeg]))
    rw [find_copyTo_frame _ _ _ _ (Tm.divergesLen_denote σ h)]
    exact Equiv.refl _
  | @lenOnDelAtFrame _ _ s _ q _ p h => fun σ => by
    show Equiv (findSt (Theory.StValue.delAt (s.denote σ) (q.denote σ)) (p.denote σ ++ [lengthSeg]))
      (findSt (s.denote σ) (p.denote σ ++ [lengthSeg]))
    rw [find_delAt_frame _ (Tm.divergesLen_denote σ h)]
    exact Equiv.refl _
  | .theory h => h
  | .symm r => r.sound.symm

end Sound

/-! ## Pins -/

section Pins

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
