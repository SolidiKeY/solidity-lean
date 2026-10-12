import Solidity.Calculus.Logic
import Solidity.Calculus.Rules
import Solidity.Calculus.StateFacts
import Solidity.Calculus.PrintTerm

/-!
# Term taclets on scoped terms

The Theory's rules on terms, KeY's term taclets, stated on the
scoped terms `Tm C Γ .val` (`Calculus/Fml.lean`), with what they need: the
Theory equality of two terms (`Tm.Theq`), the side conditions read off a
scoped path, and the term functions a scoped closer compares terms with.
Soundness is over the scoped `Tm.denote` (`Calculus/Lands.lean`).

**Notation.** `tm{ … }` writes the scoped term: the text is read as a rule
line reads a term (`RuleSyntax.schemaTerm`), its symbols the scoped ones
(`Tms`, `Calculus/Rules.lean`; `RuleSyntax.coreNames`).  A scoped term over
schema variables prints back as `tm{ … }` through the scoped term printers
(`delabTmS`, `Delab.ppTermS`).

**Sort-generic recursion.**  A recursive function on `Tm` is generic in the
sort: on one fixed sort it compiles by well-founded recursion and stops
reducing by `rfl` and `decide`.  The ones a kernel check evaluates
(`Tm.litVarsS`, `Tm.beqR`) are written by the recursor, each
with its `match` form as the compiled twin (`…M`) and a link theorem
(`…_eq_…M`), as Gate G0 asks (`Calculus/DecideScoped.lean`).

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
    if n == ``Tm.netOf then [3] else if n == ``Tm.bumped || n == ``Tms.Term.bumped then [4]
    else if n == ``Tm.app1 then [6]
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
    pure ((← whnf s).isConstOf srt)
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
  let some srt := (← whnf s).constName? | failure
  let printer : Lean.Expr → MetaM (TSyntax `dl_term) ← match srt with
    | ``Srt.val => pure (Delab.ppTermS [])
    | ``Srt.path => pure (Delab.ppPTermS [])
    | ``Srt.st => pure (Delab.ppSTermS [])
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

/-! ## Terms equal in the Theory -/

section Theq

variable {Γ : Ctx}

/-- The two terms have the same Theory value in every state: what a law of the Theory says about the terms that denote its
sides. -/
def Tm.Theq (t t' : Tm C Γ .val) : Prop :=
  ∀ σ : State C Γ, Theory.StValue.Equiv (t.denote σ) (t'.denote σ)

theorem Tm.Theq.refl (t : Tm C Γ .val) : Tm.Theq t t := fun _ => StValue.Equiv.refl _

theorem Tm.Theq.symm {t t' : Tm C Γ .val} (h : Tm.Theq t t') : Tm.Theq t' t :=
  fun σ => (h σ).symm

theorem Tm.Theq.trans {t₁ t₂ t₃ : Tm C Γ .val} (h₁ : Tm.Theq t₁ t₂) (h₂ : Tm.Theq t₂ t₃) :
    Tm.Theq t₁ t₃ :=
  fun σ => (h₁ σ).trans (h₂ σ)

/-- Terms whose Theory values are equal are equal in the Theory. -/
theorem Tm.Theq.of_eq {t t' : Tm C Γ .val} (h : ∀ σ : State C Γ, t.denote σ = t'.denote σ) :
    Tm.Theq t t' :=
  fun σ => h σ ▸ StValue.Equiv.refl _

instance : Trans (@Tm.Theq C Γ) (@Tm.Theq C Γ) (@Tm.Theq C Γ) := ⟨Tm.Theq.trans⟩

end Theq

/-! ## Sort-generic term functions -/

section Generic

variable {Γ : Ctx}

/-- A local of the context, at its type. -/
abbrev AnyIdx (Γ : Ctx) : Type := (t : LTy) × Idx Γ t

/-- `Tm.litVarsS`' compiled twin. -/
def Tm.litVarsSM : {s : Srt} → Tm C Γ s → Option (List (AnyIdx Γ))
  | _, .pvV i => some [⟨_, i⟩]
  | _, .app0 (.lit _) => some []
  | _, .app1 (.unop _ _) _ a => a.litVarsSM
  | _, .app2 (.binop _ _) a b =>
    match a.litVarsSM, b.litVarsSM with
    | some u, some v => some (u ++ v)
    | _, _ => none
  | _, _ => none

/-- **The locals a value term reads when it is built from literals and value
operators alone**, by position; `none` when it reads
anything else.  By the recursor. -/
@[implemented_by Tm.litVarsSM]
def Tm.litVarsS {s : Srt} (t : Tm C Γ s) : Option (List (AnyIdx Γ)) :=
  Tm.rec (motive := fun _ _ => Option (List (AnyIdx Γ)))
    (fun i => some [⟨_, i⟩]) (fun _ => none) (fun _ => none) (fun _ => none)
    (fun _ _ _ => none)
    (@fun s o => match s, o with
      | _, .lit _ => some []
      | _, _ => none)
    (@fun a s o _ _ ih => match a, s, o with
      | _, _, .unop _ _ => ih
      | _, _, _ => none)
    (@fun a b s o _ _ iha ihb => match a, b, s, o with
      | _, _, _, .binop _ _ =>
        match iha, ihb with
        | some u, some v => some (u ++ v)
        | _, _ => none
      | _, _, _, _ => none)
    (fun _ _ _ _ _ _ _ => none) t

theorem Tm.litVarsS_eq_litVarsSM {s : Srt} (t : Tm C Γ s) : t.litVarsS = t.litVarsSM := by
  induction t with
  | pvV _ | pvP _ | pvS _ | pvI _ | netOf _ _ | app3 _ _ _ _ => rfl
  | app0 o => cases o <;> rfl
  | app1 o _ x ih => cases o <;> first | rfl | (simp only [Tm.litVarsSM, ← ih]; rfl)
  | app2 o x y ihx ihy => cases o <;> first | rfl | (simp only [Tm.litVarsSM, ← ihx, ← ihy]; rfl)

/-- Two values of a family at two indices are one: the indices are equal,
and so are the values once they are. -/
def hbeqAt {ι : Type} [DecidableEq ι] (F : ι → Type) [∀ i, DecidableEq (F i)] {i j : ι}
    (x : F i) (y : F j) : Bool :=
  if h : i = j then decide (h ▸ x = y) else false

theorem eq_of_hbeqAt {ι : Type} [DecidableEq ι] {F : ι → Type} [∀ i, DecidableEq (F i)]
    {i j : ι} {x : F i} {y : F j} (h : hbeqAt F x y = true) : (⟨i, x⟩ : Sigma F) = ⟨j, y⟩ := by
  unfold hbeqAt at h
  split at h
  · rename_i e
    subst e
    exact congrArg (Sigma.mk i) (of_decide_eq_true h)
  · cases h

theorem hbeqAt_self {ι : Type} [DecidableEq ι] {F : ι → Type} [∀ i, DecidableEq (F i)] {i : ι}
    (x : F i) : hbeqAt F x x = true := by
  simp only [hbeqAt, ↓reduceDIte, decide_true]

/-- Two positions of one context are one local, their types compared too. -/
def Idx.hbeq {t t' : LTy} (i : Idx Γ t) (j : Idx Γ t') : Bool := hbeqAt (Idx Γ) i j

/-- Two constants are one, their sorts compared too. -/
def Op0.hbeq {s s' : Srt} (o : Op0 s) (o' : Op0 s') : Bool := hbeqAt Op0 o o'

/-- Two unary symbols are one, their sorts compared too. -/
def Op1.hbeq {a s a' s' : Srt} (o : Op1 a s) (o' : Op1 a' s') : Bool :=
  hbeqAt (fun q : Srt × Srt => Op1 q.1 q.2) (i := (a, s)) (j := (a', s')) o o'

/-- Two binary symbols are one, their sorts compared too. -/
def Op2.hbeq {a b s a' b' s' : Srt} (o : Op2 a b s) (o' : Op2 a' b' s') : Bool :=
  hbeqAt (fun q : Srt × Srt × Srt => Op2 q.1 q.2.1 q.2.2) (i := (a, b, s)) (j := (a', b', s')) o o'

/-- Two ternary symbols are one, their sorts compared too. -/
def Op3.hbeq {a b c s a' b' c' s' : Srt} (o : Op3 a b c s) (o' : Op3 a' b' c' s') : Bool :=
  hbeqAt (fun q : Srt × Srt × Srt × Srt => Op3 q.1 q.2.1 q.2.2.1 q.2.2.2)
    (i := (a, b, c, s)) (j := (a', b', c', s')) o o'

/-- `Tm.beqR`'s compiled twin. -/
def Tm.beqM : {s s' : Srt} → Tm C Γ s → Tm C Γ s' → Bool
  | _, _, .pvV i, t' => match t' with
    | .pvV j => Idx.hbeq i j
    | _ => false
  | _, _, .pvP i, t' => match t' with
    | .pvP j => Idx.hbeq i j
    | _ => false
  | _, _, .pvS i, t' => match t' with
    | .pvS j => Idx.hbeq i j
    | _ => false
  | _, _, .pvI i, t' => match t' with
    | .pvI j => Idx.hbeq i j
    | _ => false
  | _, _, .netOf i a, t' => match t' with
    | .netOf j a' => Idx.hbeq i j && a.beqM a'
    | _ => false
  | _, _, .app0 o, t' => match t' with
    | .app0 o' => Op0.hbeq o o'
    | _ => false
  | _, _, .app1 o _ x, t' => match t' with
    | .app1 o' _ x' => Op1.hbeq o o' && x.beqM x'
    | _ => false
  | _, _, .app2 o x y, t' => match t' with
    | .app2 o' x' y' => Op2.hbeq o o' && x.beqM x' && y.beqM y'
    | _ => false
  | _, _, .app3 o x y z, t' => match t' with
    | .app3 o' x' y' z' => Op3.hbeq o o' && x.beqM x' && y.beqM y' && z.beqM z'
    | _ => false

/-- **Structural equality of two terms**, their sorts compared too, by the
recursor. -/
@[implemented_by Tm.beqM]
def Tm.beqR {s s' : Srt} (t : Tm C Γ s) (t' : Tm C Γ s') : Bool :=
  Tm.rec (motive := fun _ _ => {s' : Srt} → Tm C Γ s' → Bool)
    (@fun _ i _ t' => match t' with
      | .pvV j => Idx.hbeq i j
      | _ => false)
    (@fun _ i _ t' => match t' with
      | .pvP j => Idx.hbeq i j
      | _ => false)
    (@fun i _ t' => match t' with
      | .pvS j => Idx.hbeq i j
      | _ => false)
    (@fun _ i _ t' => match t' with
      | .pvI j => Idx.hbeq i j
      | _ => false)
    (@fun i _ ih _ t' => match t' with
      | .netOf j a' => Idx.hbeq i j && ih a'
      | _ => false)
    (@fun _ o _ t' => match t' with
      | .app0 o' => Op0.hbeq o o'
      | _ => false)
    (@fun _ _ o _ _ ih _ t' => match t' with
      | .app1 o' _ x' => Op1.hbeq o o' && ih x'
      | _ => false)
    (@fun _ _ _ o _ _ ihx ihy _ t' => match t' with
      | .app2 o' x' y' => Op2.hbeq o o' && ihx x' && ihy y'
      | _ => false)
    (@fun _ _ _ _ o _ _ _ ihx ihy ihz _ t' => match t' with
      | .app3 o' x' y' z' => Op3.hbeq o o' && ihx x' && ihy y' && ihz z'
      | _ => false) t t'

theorem Tm.beqR_eq_beqM {s s' : Srt} (t : Tm C Γ s) (t' : Tm C Γ s') : t.beqR t' = t.beqM t' := by
  induction t generalizing s' with
  | pvV _ | pvP _ | pvS _ | pvI _ | app0 _ => cases t' <;> rfl
  | netOf i a ih => cases t' <;> first | rfl | (simp only [Tm.beqM, ← ih]; rfl)
  | app1 o _ x ih => cases t' <;> first | rfl | (simp only [Tm.beqM, ← ih]; rfl)
  | app2 o x y ihx ihy => cases t' <;> first | rfl | (simp only [Tm.beqM, ← ihx, ← ihy]; rfl)
  | app3 o x y z ihx ihy ihz =>
    cases t' <;> first | rfl | (simp only [Tm.beqM, ← ihx, ← ihy, ← ihz]; rfl)

/-- What `beqM` accepts is one term, its sort and all. -/
theorem Tm.eq_of_beqM {s s' : Srt} (t : Tm C Γ s) (t' : Tm C Γ s') (h : t.beqM t' = true) :
    (⟨s, t⟩ : (s : Srt) × Tm C Γ s) = ⟨s', t'⟩ := by
  induction t generalizing s' with
  | pvV i | pvP i | pvS i | pvI i | app0 i =>
    cases t' <;> simp only [Tm.beqM, Bool.false_eq_true] at h
    cases eq_of_hbeqAt h
    rfl
  | netOf i a ih =>
    cases t' <;> simp only [Tm.beqM, Bool.false_eq_true, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases eq_of_hbeqAt h1
    cases ih _ h2
    rfl
  | app1 o _ x ih =>
    cases t' <;> simp only [Tm.beqM, Bool.false_eq_true, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases eq_of_hbeqAt h1
    cases ih _ h2
    rfl
  | app2 o x y ihx ihy =>
    cases t' <;> simp only [Tm.beqM, Bool.false_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases eq_of_hbeqAt h1
    cases ihx _ h2
    cases ihy _ h3
    rfl
  | app3 o x y z ihx ihy ihz =>
    cases t' <;> simp only [Tm.beqM, Bool.false_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    cases eq_of_hbeqAt h1
    cases ihx _ h2
    cases ihy _ h3
    cases ihz _ h4
    rfl

theorem Tm.beqM_self {s : Srt} (t : Tm C Γ s) : t.beqM t = true := by
  induction t with
  | pvV i | pvP i | pvS i | pvI i | app0 i => simp only [Tm.beqM, Idx.hbeq, Op0.hbeq, hbeqAt_self]
  | netOf i a ih => simp only [Tm.beqM, Idx.hbeq, hbeqAt_self, ih, Bool.and_self]
  | app1 o _ x ih => simp only [Tm.beqM, Op1.hbeq, hbeqAt_self, ih, Bool.and_self]
  | app2 o x y ihx ihy => simp only [Tm.beqM, Op2.hbeq, hbeqAt_self, ihx, ihy, Bool.and_self]
  | app3 o x y z ihx ihy ihz =>
    simp only [Tm.beqM, Op3.hbeq, hbeqAt_self, ihx, ihy, ihz, Bool.and_self]

/-- **`beqR` is equality**: what it accepts is one term. -/
theorem Tm.eq_of_beqR {s : Srt} {t t' : Tm C Γ s} (h : t.beqR t' = true) : t = t' :=
  eq_of_heq (Sigma.mk.inj (Tm.eq_of_beqM t t' ((Tm.beqR_eq_beqM t t').symm.trans h))).2

theorem Tm.beqR_self {s : Srt} (t : Tm C Γ s) : t.beqR t = true :=
  (Tm.beqR_eq_beqM t t).trans (Tm.beqM_self t)

theorem Tm.beqR_iff {s : Srt} {t t' : Tm C Γ s} : t.beqR t' = true ↔ t = t' :=
  ⟨Tm.eq_of_beqR, fun h => h ▸ Tm.beqR_self t⟩

end Generic


/-! ## The side conditions, on scoped paths

The term taclets', read off a scoped path: the syntactic forms
of the Theory's `p ≠ []`, `diverges p q`, `p = q` and `q = p ++ r`.  The
shapes are `SegT`'s. -/

section Side

variable {Γ : Ctx}

/-- The path is never empty: anything but a bare alias. -/
def Tm.hasSeg : Tm C Γ .path → Bool
  | .pvP _ => false
  | _ => true

/-- An integer literal. -/
def Tm.litInt? : Tm C Γ .val → Option Int
  | .app0 (.lit (.int i)) => some i
  | _ => none

theorem Tm.eq_of_litInt? {t : Tm C Γ .val} {i : Int} (h : t.litInt? = some i) :
    t = Tm.lit (.int i) := by
  unfold Tm.litInt? at h
  split at h
  · cases h; rfl
  · cases h

/-- A path's shape, read off its syntax: `none` through an alias.  Generic in the sort. -/
def Tm.shape? : {u : Srt} → Tm C Γ u → Option (List SegT)
  | _, .app0 (.root r) => some [.field r]
  | _, .app1 (.field f) _ p => p.shape?.map (· ++ [.field f])
  | _, .app1 .next _ p => p.shape?.map (· ++ [.at none])
  | _, .app2 .at p i => p.shape?.map (· ++ [.at i.litInt?])
  | _, .app2 .nextIn _ p => p.shape?.map (· ++ [.at none])
  | _, .app3 .atIn _ p i => p.shape?.map (· ++ [.at i.litInt?])
  | _, _ => none

/-- The two paths leave each other. -/
def Tm.diverges (p q : Tm C Γ .path) : Bool :=
  match p.shape?, q.shape? with
  | some a, some b => SegT.diverges a b
  | _, _ => false

/-- `q` leaves `p.length`. -/
def Tm.divergesLen (q p : Tm C Γ .path) : Bool :=
  match q.shape?, p.shape? with
  | some a, some b => SegT.diverges a (b ++ [.field "length"])
  | _, _ => false

/-- The path its checks aside: `p[i]@S` is `p[i]`.  Generic in the sort. -/
def Tm.eraseChecks : {u : Srt} → Tm C Γ u → Tm C Γ u
  | _, .app1 (.field f) h p => .app1 (.field f) h p.eraseChecks
  | _, .app1 .next h p => .app1 .next h p.eraseChecks
  | _, .app2 .at p i => .app2 .at p.eraseChecks i
  | _, .app2 .nextIn S p => .app2 .nextIn S p.eraseChecks
  | _, .app3 .atIn _ p i => .app2 .at p.eraseChecks i
  | _, p => p

/-- The two paths have the same segments in every state, their checks aside
compared by `Tm.beqR`. -/
def Tm.sameSegs (p q : Tm C Γ .path) : Bool := p.eraseChecks.beqR q.eraseChecks

theorem Tm.sameSegs_refl (p : Tm C Γ .path) : p.sameSegs p = true := Tm.beqR_self _

/-- `f` of some path on the way down to `t`'s root.
Generic in the sort. -/
def Tm.extendsAny (f : Tm C Γ .path → Bool) : {u : Srt} → Tm C Γ u → Bool
  | _, .app1 (.field _) _ q => f q || q.extendsAny f
  | _, .app2 .at q _ => f q || q.extendsAny f
  | _, .app3 .atIn _ q _ => f q || q.extendsAny f
  | _, _ => false

/-- `q` goes on below `p`. -/
def Tm.extends (q p : Tm C Γ .path) : Bool := q.extendsAny (·.beqR p)

/-- The state variable a path is, if it is one alone. -/
def Tm.root? : {u : Srt} → Tm C Γ u → Option Name
  | _, .app0 (.root r) => some r
  | _, _ => none

/-- A path read from its head: the root, and the rest rooted at its first
member.  Generic in the sort. -/
def Tm.shift? : {u : Srt} → Tm C Γ u → Option (Name × Tm C Γ .path)
  | _, .app1 (.field f) _ p => match p.root? with
    | some r => some (r, .app0 (.root f))
    | none => p.shift?.map fun (r, p') => (r, .app1 (.field f) rfl p')
  | _, .app2 .at p i => match p.root? with
    | some _ => none
    | none => p.shift?.map fun (r, p') => (r, .app2 .at p' i)
  | _, .app3 .atIn S p i => match p.root? with
    | some _ => none
    | none => p.shift?.map fun (r, p') => (r, .app3 .atIn S p' i)
  | _, _ => none

/-- The word a written value is, if it is a literal. -/
def Tm.svLit? : Tm C Γ .sv → Option Value
  | .app1 .sval _ (.app0 (.lit v)) => some v
  | _ => none

/-- The word a storage term reads at a path, read off its writes.  Generic in the sort. -/
def Tm.findLitBy (eq div : Tm C Γ .path → Bool) : {u : Srt} → Tm C Γ u → Option Value
  | _, .app3 .save s p v => if eq p then v.svLit? else if div p then s.findLitBy eq div else none
  | _, _ => none

/-- The word `s` reads at `q`, read off its writes. -/
def Tm.findLit? (s : Tm C Γ .st) (q : Tm C Γ .path) : Option Value :=
  if q.hasSeg then s.findLitBy (·.sameSegs q) (·.diverges q) else none

/-- The node at `p` in `s` is not a mapping, in every state. -/
def Tm.KindFreeAt (s : Tm C Γ .st) (p : Tm C Γ .path) : Prop :=
  ∀ σ : State C Γ, (findSt (s.denote σ) (p.denote σ)).kindFree = true

end Side

/-! ## The side conditions in the Theory -/

section SideDenote

variable {Γ : Ctx} (σ : State C Γ)

/-- `hasSeg` gives the Theory's `p ≠ []` in every state. -/
theorem Tm.denote_ne_nil {p : Tm C Γ .path} (hp : p.hasSeg = true) : p.denote σ ≠ [] := by
  match p, hp with
  | .pvP _, hp => nomatch hp
  | .app0 (.root _), _ => simp only [Tm.denote, Op0.denote, ne_eq, List.cons_ne_nil, not_false_eq_true]
  | .app1 (.field _) _ _, _ | .app1 .next _ _, _ | .app2 .at _ _, _ | .app2 .nextIn _ _, _
  | .app3 .atIn _ _ _, _ =>
    simp only [Tm.denote, Op1.denote, Op2.denote, Op3.denote, ne_eq, List.append_eq_nil_iff,
      List.cons_ne_nil, and_false, not_false_eq_true]

/-- A path has its shape in every state. -/
theorem Tm.shape?_matches : (p : Tm C Γ .path) → {a : List SegT} →
    p.shape? = some a → SegT.matches a (p.denote σ) = true
  | .pvP _, _, h => nomatch h
  | .app0 (.root _), _, h => by
    simp only [Tm.shape?, Option.some.injEq] at h
    subst h
    simp only [Tm.denote, Op0.denote, SegT.matches, SegT.fits, BEq.rfl, Bool.and_self]
  | .app1 (.field _) _ p, _, h => by
    simp only [Tm.shape?, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [Tm.denote, Op1.denote]
    exact SegT.matches_append _ _ _ _ (Tm.shape?_matches p ha)
      (by simp only [SegT.matches, SegT.fits, BEq.rfl, Bool.and_self])
  | .app1 .next _ p, _, h | .app2 .nextIn _ p, _, h => by
    simp only [Tm.shape?, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [Tm.denote, Op1.denote, Op2.denote]
    exact SegT.matches_append _ _ _ _ (Tm.shape?_matches p ha) rfl
  | .app2 .at p i, _, h | .app3 .atIn _ p i, _, h => by
    simp only [Tm.shape?, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [Tm.denote, Op2.denote, Op3.denote]
    refine SegT.matches_append _ _ _ _ (Tm.shape?_matches p ha) ?_
    cases hi : Tm.litInt? i with
    | none => rfl
    | some k =>
      rw [Tm.eq_of_litInt? hi]
      simp only [Tm.denote, Op0.denote, asInt, SegT.matches, SegT.fits, BEq.rfl, Bool.and_self]

/-- `Tm.diverges` gives the Theory's `diverges` in every state. -/
theorem Tm.diverges_denote {p q : Tm C Γ .path} (h : p.diverges q = true) :
    Theory.StValue.diverges (p.denote σ) (q.denote σ) = true := by
  unfold Tm.diverges at h
  split at h
  · rename_i a b ha hb
    exact SegT.diverges_sound a b _ _ h (p.shape?_matches σ ha) (q.shape?_matches σ hb)
  · exact absurd h Bool.false_ne_true

/-- `Tm.divergesLen` gives the Theory's `diverges q (p ++ [lengthSeg])`. -/
theorem Tm.divergesLen_denote {q p : Tm C Γ .path} (h : q.divergesLen p = true) :
    Theory.StValue.diverges (q.denote σ) (p.denote σ ++ [lengthSeg]) = true := by
  unfold Tm.divergesLen at h
  split at h
  · rename_i a b ha hb
    exact SegT.diverges_sound _ _ _ _ h (q.shape?_matches σ ha)
      (SegT.matches_append _ _ _ _ (p.shape?_matches σ hb) (by decide))
  · exact absurd h Bool.false_ne_true

/-- A check erased leaves the Theory's path, in every state. -/
theorem Tm.eraseChecks_denote : (p : Tm C Γ .path) → p.eraseChecks.denote σ = p.denote σ
  | .pvP _ | .app0 (.root _) => rfl
  | .app1 (.field _) _ p | .app1 .next _ p | .app2 .at p _ | .app2 .nextIn _ p
  | .app3 .atIn _ p _ => by
    simp only [Tm.eraseChecks, Tm.denote, Op1.denote, Op2.denote, Op3.denote,
      Tm.eraseChecks_denote p]

/-- A check erased leaves a segment where there was one. -/
theorem Tm.eraseChecks_hasSeg : (p : Tm C Γ .path) → p.eraseChecks.hasSeg = p.hasSeg
  | .pvP _ | .app0 (.root _) | .app1 (.field _) _ _ | .app1 .next _ _ | .app2 .at _ _
  | .app2 .nextIn _ _ | .app3 .atIn _ _ _ => rfl

/-- `sameSegs` gives one Theory path in every state. -/
theorem Tm.sameSegs_denote {p q : Tm C Γ .path} (h : p.sameSegs q = true) :
    p.denote σ = q.denote σ := by
  rw [← Tm.eraseChecks_denote σ p, ← Tm.eraseChecks_denote σ q, Tm.eq_of_beqR h]

/-- Paths of the same segments are both bare aliases or neither. -/
theorem Tm.sameSegs_hasSeg {p q : Tm C Γ .path} (h : p.sameSegs q = true) :
    p.hasSeg = q.hasSeg := by
  rw [← Tm.eraseChecks_hasSeg p, ← Tm.eraseChecks_hasSeg q, Tm.eq_of_beqR h]

/-- `q.extends p` gives the Theory's `q = p ++ r`, `r ≠ []`, in every state. -/
theorem Tm.extends_denote {p : Tm C Γ .path} :
    (q : Tm C Γ .path) → q.extends p = true → ∃ r, r ≠ [] ∧ q.denote σ = p.denote σ ++ r
  | .app1 (.field f) _ q, h => by
    simp only [Tm.extends, Tm.extendsAny, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain rfl := Tm.eq_of_beqR h
      exact ⟨[.field f], List.cons_ne_nil _ _, by simp only [Tm.denote, Op1.denote]⟩
    · obtain ⟨r, -, hq⟩ := Tm.extends_denote q h
      exact ⟨r ++ [.field f], by simp only [ne_eq, List.append_eq_nil_iff, List.cons_ne_nil, and_false,
        not_false_eq_true],
        by simp only [Tm.denote, Op1.denote, hq, List.append_assoc]⟩
  | .app2 .at q i, h | .app3 .atIn _ q i, h => by
    simp only [Tm.extends, Tm.extendsAny, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain rfl := Tm.eq_of_beqR h
      exact ⟨[.at (asInt (i.denote σ))], List.cons_ne_nil _ _,
        by simp only [Tm.denote, Op2.denote, Op3.denote]⟩
    · obtain ⟨r, -, hq⟩ := Tm.extends_denote q h
      exact ⟨r ++ [.at (asInt (i.denote σ))], by simp only [ne_eq, List.append_eq_nil_iff, List.cons_ne_nil, and_false,
        not_false_eq_true],
        by simp only [Tm.denote, Op2.denote, Op3.denote, hq, List.append_assoc]⟩
  | .pvP _, h | .app0 (.root _), h | .app1 .next _ _, h | .app2 .nextIn _ _, h => nomatch h

theorem Tm.eq_root_of_root? : (p : Tm C Γ .path) → {r : Name} → p.root? = some r →
    p = .app0 (.root r)
  | .app0 (.root _), _, h => by
    simp only [Tm.root?, Option.some.injEq] at h
    subst h
    rfl
  | .pvP _, _, h | .app1 (.field _) _ _, _, h | .app1 .next _ _, _, h | .app2 .at _ _, _, h
  | .app2 .nextIn _ _, _, h | .app3 .atIn _ _ _, _, h => nomatch h

/-- `shift?` splits the Theory's path at its head, in every state. -/
theorem Tm.shift?_denote : (p : Tm C Γ .path) → {r : Name} → {p' : Tm C Γ .path} →
    p.shift? = some (r, p') → p.denote σ = .field r :: p'.denote σ
  | .app1 (.field f) _ p, _, _, h => by
    simp only [Tm.shift?] at h
    split at h
    · rename_i r hr
      obtain rfl := Tm.eq_root_of_root? p hr
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Tm.denote, Op0.denote, Op1.denote, List.singleton_append]
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨r, p'⟩, hp, h⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have ih := Tm.shift?_denote p hp
      simp only [Tm.denote, Op1.denote, ih, List.cons_append]
  | .app2 .at p i, _, _, h => by
    simp only [Tm.shift?] at h
    split at h
    · nomatch h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨r, p'⟩, hp, h⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have ih := Tm.shift?_denote p hp
      simp only [Tm.denote, Op2.denote, ih, List.cons_append]
  | .app3 .atIn _ p i, _, _, h => by
    simp only [Tm.shift?] at h
    split at h
    · nomatch h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨r, p'⟩, hp, h⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have ih := Tm.shift?_denote p hp
      simp only [Tm.denote, Op3.denote, ih, List.cons_append]
  | .pvP _, _, _, h | .app0 (.root _), _, _, h | .app1 .next _ _, _, _, h
  | .app2 .nextIn _ _, _, _, h => nomatch h

end SideDenote

section SideSyntax

variable {Γ : Ctx}

/-- The rest `shift?` leaves has a segment: it is rooted at the first member. -/
theorem Tm.shift?_hasSeg : (p : Tm C Γ .path) → {r : Name} → {p' : Tm C Γ .path} →
    p.shift? = some (r, p') → p'.hasSeg = true
  | .app1 (.field _) _ p, _, _, h => by
    simp only [Tm.shift?] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨r, p'⟩, -, h⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | .app2 .at p _, _, _, h | .app3 .atIn _ p _, _, _, h => by
    simp only [Tm.shift?] at h
    split at h
    · nomatch h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨r, p'⟩, -, h⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | .pvP _, _, _, h | .app0 (.root _), _, _, h | .app1 .next _ _, _, _, h
  | .app2 .nextIn _ _, _, _, h => nomatch h

theorem Tm.svLit?_eq {v : Tm C Γ .sv} {w : Value} (h : v.svLit? = some w) :
    v = .app1 .sval rfl (.app0 (.lit w)) := by
  unfold Tm.svLit? at h
  split at h
  · cases h; rfl
  · cases h

end SideSyntax

/-! ## A storage term with a hole -/

/-- A storage term with a hole (`SCtx`, scoped): the storage argument of
saves, deletes and selects, down to the hole. -/
inductive SCtxS (C : Contract) (Γ : Ctx) where
  | hole
  | save (K : SCtxS C Γ) (p : Tm C Γ .path) (v : Tm C Γ .sv)
  | delAt (K : SCtxS C Γ) (p : Tm C Γ .path)
  | select (K : SCtxS C Γ) (r : Name)

section Ctx

variable {Γ : Ctx}

/-- The hole filled. -/
def SCtxS.fill : SCtxS C Γ → Tm C Γ .st → Tm C Γ .st
  | .hole, s => s
  | .save K p v, s => .app3 .save (K.fill s) p v
  | .delAt K p, s => .app2 .delAt (K.fill s) p
  | .select K r, s => .app1 (.select r) rfl (K.fill s)

/-- Two storages that denote alike fill a context alike. -/
theorem SCtxS.fill_denote {s s' : Tm C Γ .st} (h : ∀ σ : State C Γ, s.denote σ = s'.denote σ) :
    (K : SCtxS C Γ) → ∀ σ : State C Γ, (K.fill s).denote σ = (K.fill s').denote σ
  | .hole, σ => h σ
  | .save K p v, σ => by simp only [SCtxS.fill, Tm.denote, Op3.denote, SCtxS.fill_denote h K σ]
  | .delAt K p, σ => by simp only [SCtxS.fill, Tm.denote, Op2.denote, SCtxS.fill_denote h K σ]
  | .select K r, σ => by simp only [SCtxS.fill, Tm.denote, Op1.denote, SCtxS.fill_denote h K σ]

end Ctx

/-! ## The rules -/

/-- `t ⇝ t'` on scoped terms: a rule of the Theory rewrites `t` to `t'`,
each constructor named as its solkey taclet. -/
inductive TermTaclet {Γ : Ctx} : Tm C Γ .val → Tm C Γ .val → Prop
  /-- **`findOnSave`**: `find(save(s, p, v), q) ⇝ v` for a word `v`, `q` the
  path `p` its checks aside (`find_copyTo_same`). -/
  | findOnSave {s : Tm C Γ .st} {p q : Tm C Γ .path} {v : Value} (hp : p.hasSeg = true := by rfl)
      (hq : p.sameSegs q = true := by first | rfl | exact Tm.sameSegs_refl _) :
      TermTaclet tm{ find(save(s, p, lit(v)), q) } tm{ lit(v) }
  /-- **`findOnSaveFrame`**: a read at a path that leaves the written one does
  not see the write (`find_copyTo_frame`). -/
  | findOnSaveFrame {s : Tm C Γ .st} {p q : Tm C Γ .path} {v : Tm C Γ .sv}
      (h : p.diverges q = true := by rfl) :
      TermTaclet tm{ find(save(s, p, v), q) } tm{ find(s, q) }
  /-- **`findMemberCons`**: `find(s, r.p) ⇝ find(select(s, r), p)`, the path
  read from its head (`find_cons`). -/
  | findMemberCons {s : Tm C Γ .st} {p : Tm C Γ .path} {r : Name} {p' : Tm C Γ .path}
      (h : p.shift? = some (r, p') := by rfl) :
      TermTaclet tm{ find(s, p) } tm{ find(select(s, r), p') }
  /-- **`selectOnSaveMember`**: solkey's `selectOnSaveCons` at `a1 = a2`. -/
  | selectOnSaveMember {s : Tm C Γ .st} {p : Tm C Γ .path} {r : Name} {p' : Tm C Γ .path}
      {v : Tm C Γ .sv} {q : Tm C Γ .path} (h : p.shift? = some (r, p') := by rfl) :
      TermTaclet tm{ find(select(save(s, p, v), r), q) } tm{ find(save(select(s, r), p', v), q) }
  /-- **`selectOnSaveFrame`**: solkey's `selectOnSaveCons` at `a1 ≠ a2`. -/
  | selectOnSaveFrame {s : Tm C Γ .st} {p : Tm C Γ .path} {r r' : Name} {p' : Tm C Γ .path}
      {v : Tm C Γ .sv} {q : Tm C Γ .path} (h : p.shift? = some (r', p') := by rfl)
      (hr : r' ≠ r := by decide) :
      TermTaclet tm{ find(select(save(s, p, v), r), q) } tm{ find(select(s, r), q) }
  /-- **`selectOnDelAtMember`**: the delete at `r.p`, seen from `r`, is a
  delete at `p`. -/
  | selectOnDelAtMember {s : Tm C Γ .st} {p : Tm C Γ .path} {r : Name} {p' : Tm C Γ .path}
      {q : Tm C Γ .path} (h : p.shift? = some (r, p') := by rfl) :
      TermTaclet tm{ find(select(delAt(s, p), r), q) } tm{ find(delAt(select(s, r), p'), q) }
  /-- **`selectOnDelAtFrame`**: a delete under another root is not seen from
  `r`. -/
  | selectOnDelAtFrame {s : Tm C Γ .st} {p : Tm C Γ .path} {r r' : Name} {p' : Tm C Γ .path}
      {q : Tm C Γ .path} (h : p.shift? = some (r', p') := by rfl) (hr : r' ≠ r := by decide) :
      TermTaclet tm{ find(select(delAt(s, p), r), q) } tm{ find(select(s, r), q) }
  /-- **`selectOnSaveMemberIn`**: `selectOnSaveMember` in a storage context. -/
  | selectOnSaveMemberIn (K : SCtxS C Γ) {s : Tm C Γ .st} {p : Tm C Γ .path} {r : Name}
      {p' : Tm C Γ .path} {v : Tm C Γ .sv} {q : Tm C Γ .path}
      (h : p.shift? = some (r, p') := by rfl) :
      TermTaclet tm{ find(‹K.fill tm{ select(save(s, p, v), r) }›, q) }
        tm{ find(‹K.fill tm{ save(select(s, r), p', v) }›, q) }
  /-- **`selectOnSaveFrameIn`**: `selectOnSaveFrame` in a storage context. -/
  | selectOnSaveFrameIn (K : SCtxS C Γ) {s : Tm C Γ .st} {p : Tm C Γ .path} {r r' : Name}
      {p' : Tm C Γ .path} {v : Tm C Γ .sv} {q : Tm C Γ .path}
      (h : p.shift? = some (r', p') := by rfl) (hr : r' ≠ r := by decide) :
      TermTaclet tm{ find(‹K.fill tm{ select(save(s, p, v), r) }›, q) }
        tm{ find(‹K.fill tm{ select(s, r) }›, q) }
  /-- **`selectOnDelAtMemberIn`**: `selectOnDelAtMember` in a storage context. -/
  | selectOnDelAtMemberIn (K : SCtxS C Γ) {s : Tm C Γ .st} {p : Tm C Γ .path} {r : Name}
      {p' : Tm C Γ .path} {q : Tm C Γ .path} (h : p.shift? = some (r, p') := by rfl) :
      TermTaclet tm{ find(‹K.fill tm{ select(delAt(s, p), r) }›, q) }
        tm{ find(‹K.fill tm{ delAt(select(s, r), p') }›, q) }
  /-- **`selectOnDelAtFrameIn`**: `selectOnDelAtFrame` in a storage context. -/
  | selectOnDelAtFrameIn (K : SCtxS C Γ) {s : Tm C Γ .st} {p : Tm C Γ .path} {r r' : Name}
      {p' : Tm C Γ .path} {q : Tm C Γ .path} (h : p.shift? = some (r', p') := by rfl)
      (hr : r' ≠ r := by decide) :
      TermTaclet tm{ find(‹K.fill tm{ select(delAt(s, p), r) }›, q) }
        tm{ find(‹K.fill tm{ select(s, r) }›, q) }
  /-- **`findOnDelAt`**: where `s` reads the word `w` at `p`, the delete
  leaves its default (`find_delAt_same`, `delValueDefault`). -/
  | findOnDelAt {s : Tm C Γ .st} {p q : Tm C Γ .path} {w : Value}
      (hw : TermTaclet tm{ find(s, p) } tm{ lit(w) }) (hp : p.hasSeg = true := by rfl)
      (hq : p.sameSegs q = true := by first | rfl | exact Tm.sameSegs_refl _) :
      TermTaclet tm{ find(delAt(s, p), q) } tm{ lit(‹primDefault w›) }
  /-- **`findOnDelAtValue`**: the delete leaves at its path the default of
  what was there (`find_delAt_same`). -/
  | findOnDelAtValue {s : Tm C Γ .st} {p q : Tm C Γ .path} (hp : p.hasSeg = true := by rfl)
      (hq : p.sameSegs q = true := by first | rfl | exact Tm.sameSegs_refl _) :
      TermTaclet tm{ find(delAt(s, p), q) } tm{ delValue(find(s, q)) }
  /-- **`delValueLit`**: the default of a word (`delValueDefault`). -/
  | delValueLit {w : Value} : TermTaclet tm{ delValue(lit(w)) } tm{ lit(‹primDefault w›) }
  /-- **`findOnDelAtBelow`**: below a deleted node that is not a mapping,
  every word reads its default (`find_delAt_below`, `delValueDefault`). -/
  | findOnDelAtBelow {s : Tm C Γ .st} {p q : Tm C Γ .path} {w : Value} (hk : s.KindFreeAt p)
      (hw : s.findLit? q = some w := by rfl) (hp : p.hasSeg = true := by rfl)
      (hq : q.extends p = true := by rfl) :
      TermTaclet tm{ find(delAt(s, p), q) } tm{ lit(‹primDefault w›) }
  /-- **`findOnDelAtFrame`**: a read off the deleted path does not see the
  delete (`find_delAt_frame`). -/
  | findOnDelAtFrame {s : Tm C Γ .st} {p q : Tm C Γ .path} (h : p.diverges q = true := by rfl) :
      TermTaclet tm{ find(delAt(s, p), q) } tm{ find(s, q) }
  /-- **`findOnPushFrame`**: a read off the array's path does not see a push
  (`find_pushT_frame`). -/
  | findOnPushFrame {s : Tm C Γ .st} {p q : Tm C Γ .path} {v : Tm C Γ .sv}
      (h : p.diverges q = true := by rfl) :
      TermTaclet tm{ find(save(save(s, p[p.length], v), p.length, p.length + 1), q) }
        tm{ find(s, q) }
  /-- **`findOnPopFrame`**: a read off the array's path does not see a pop
  (`find_popT_frame`). -/
  | findOnPopFrame {s : Tm C Γ .st} {p q : Tm C Γ .path} (h : p.diverges q = true := by rfl) :
      TermTaclet tm{ find(save(delAt(s, p[p.length - 1]), p.length, p.length - 1), q) }
        tm{ find(s, q) }
  /-- **`lenOnSaveFrame`**: a length read off the written path does not see
  the write (`find_copyTo_frame`). -/
  | lenOnSaveFrame {s : Tm C Γ .st} {q p : Tm C Γ .path} {v : Tm C Γ .sv}
      (h : q.divergesLen p = true := by rfl) :
      TermTaclet tm{ find(save(s, q, v), p.length) } tm{ find(s, p.length) }
  /-- **`lenOnDelAtFrame`**: a length read off the deleted path does not see
  the delete (`find_delAt_frame`). -/
  | lenOnDelAtFrame {s : Tm C Γ .st} {q p : Tm C Γ .path} (h : q.divergesLen p = true := by rfl) :
      TermTaclet tm{ find(delAt(s, q), p.length) } tm{ find(s, p.length) }
  /-- Any law of the Theory: `t` and `t'` have one Theory value in every
  state. -/
  | theory {t t' : Tm C Γ .val} (h : Tm.Theq t t') : TermTaclet t t'
  /-- A rule read right to left, `rw [← r]`. -/
  | symm {t t' : Tm C Γ .val} (r : TermTaclet t t') : TermTaclet t' t

section Rules

variable {Γ : Ctx}

/-- **`findOnDelAtSave`**: a delete over a written word reads the word's
default: `findOnDelAt` with `findOnSave` as its premise. -/
theorem TermTaclet.findOnDelAtSave {s : Tm C Γ .st} {p' p q : Tm C Γ .path} {v : Value}
    (hp : p.hasSeg = true := by rfl)
    (hp' : p'.sameSegs p = true := by first | rfl | exact Tm.sameSegs_refl _)
    (hq : p.sameSegs q = true := by first | rfl | exact Tm.sameSegs_refl _) :
    TermTaclet tm{ find(delAt(save(s, p', lit(v)), p), q) } tm{ lit(‹primDefault v›) } :=
  .findOnDelAt (.findOnSave ((Tm.sameSegs_hasSeg hp').trans hp) hp') hp hq

end Rules

/-! ## Soundness -/

section Sound

variable {Γ : Ctx}

theorem Tm.selectOnSaveMember_denote {s : Tm C Γ .st} {p : Tm C Γ .path} {r : Name}
    {p' : Tm C Γ .path} {v : Tm C Γ .sv} (h : p.shift? = some (r, p')) (σ : State C Γ) :
    (tm{ select(save(s, p, v), r) } : Tm C Γ .st).denote σ =
      (tm{ save(select(s, r), p', v) } : Tm C Γ .st).denote σ := by
  have hne := Tm.denote_ne_nil σ (Tm.shift?_hasSeg p h)
  simp only [Tm.denote, Op1.denote, Op3.denote, Tm.shift?_denote σ p h, copyTo,
    StValue.selectOnSaveCons, if_true, List.isEmpty_iff, hne, if_false, asStruct_st,
    find_cons _ _ hne]

theorem Tm.selectOnSaveFrame_denote {s : Tm C Γ .st} {p : Tm C Γ .path} {r r' : Name}
    {p' : Tm C Γ .path} {v : Tm C Γ .sv} (h : p.shift? = some (r', p')) (hr : r' ≠ r)
    (σ : State C Γ) :
    (tm{ select(save(s, p, v), r) } : Tm C Γ .st).denote σ =
      (tm{ select(s, r) } : Tm C Γ .st).denote σ := by
  simp only [Tm.denote, Op1.denote, Op3.denote, Tm.shift?_denote σ p h, copyTo,
    StValue.selectOnSaveCons]
  rw [if_neg (fun e => hr (Seg.field.inj e))]

theorem Tm.selectOnDelAtMember_denote {s : Tm C Γ .st} {p : Tm C Γ .path} {r : Name}
    {p' : Tm C Γ .path} (h : p.shift? = some (r, p')) (σ : State C Γ) :
    (tm{ select(delAt(s, p), r) } : Tm C Γ .st).denote σ =
      (tm{ delAt(select(s, r), p') } : Tm C Γ .st).denote σ := by
  have hne := Tm.denote_ne_nil σ (Tm.shift?_hasSeg p h)
  simp only [Tm.denote, Op1.denote, Op2.denote, Tm.shift?_denote σ p h, Theory.StValue.delAt,
    StValue.selectOnSaveCons, if_true, List.isEmpty_iff, hne, if_false, asStruct_st,
    find_cons _ _ hne]

theorem Tm.selectOnDelAtFrame_denote {s : Tm C Γ .st} {p : Tm C Γ .path} {r r' : Name}
    {p' : Tm C Γ .path} (h : p.shift? = some (r', p')) (hr : r' ≠ r) (σ : State C Γ) :
    (tm{ select(delAt(s, p), r) } : Tm C Γ .st).denote σ =
      (tm{ select(s, r) } : Tm C Γ .st).denote σ := by
  simp only [Tm.denote, Op1.denote, Op2.denote, Tm.shift?_denote σ p h, Theory.StValue.delAt,
    StValue.selectOnSaveCons]
  rw [if_neg (fun e => hr (Seg.field.inj e))]

/-- Two storages that denote alike are read alike, in any context. -/
theorem Tm.find_fill_theq {s s' : Tm C Γ .st} (h : ∀ σ : State C Γ, s.denote σ = s'.denote σ)
    (K : SCtxS C Γ) (q : Tm C Γ .path) :
    Tm.Theq tm{ find(‹K.fill s›, q) } tm{ find(‹K.fill s'›, q) } := fun σ => by
  simp only [Tm.denote, Op2.denote, SCtxS.fill_denote h K σ]
  exact Equiv.refl _

/-- The word read off the writes is the word read. -/
theorem Tm.findLitBy_theq {q : Tm C Γ .path} (hq : q.hasSeg = true) :
    (s : Tm C Γ .st) → {w : Value} → s.findLitBy (·.sameSegs q) (·.diverges q) = some w →
      Tm.Theq tm{ find(s, q) } tm{ lit(w) }
  | .app3 .save s p v, w, h => fun σ => by
    simp only [Tm.findLitBy] at h
    split at h
    · rename_i hpq
      obtain rfl := Tm.svLit?_eq h
      have hp : p.hasSeg = true := (Tm.sameSegs_hasSeg hpq).trans hq
      simp only [Tm.denote, Op0.denote, Op1.denote, Op2.denote, Op3.denote,
        ← Tm.sameSegs_denote σ hpq, find_copyTo_same _ (Tm.denote_ne_nil σ hp), copyVal]
      exact Equiv.refl _
    · split at h
      · rename_i hd
        have ih := Tm.findLitBy_theq hq s h σ
        simp only [Tm.denote, Op0.denote, Op2.denote, Op3.denote] at ih ⊢
        rw [find_copyTo_frame _ _ _ _ (Tm.diverges_denote σ hd)]
        exact ih
      · nomatch h
  | .pvS _, _, h | .app0 _, _, h | .app1 _ _ _, _, h | .app2 _ _ _, _, h => nomatch h
  | .app3 .push _ _ _, _, h => nomatch h

theorem Tm.findLit?_theq {s : Tm C Γ .st} {q : Tm C Γ .path} {w : Value}
    (h : s.findLit? q = some w) : Tm.Theq tm{ find(s, q) } tm{ lit(w) } := by
  unfold Tm.findLit? at h
  split at h
  · exact Tm.findLitBy_theq ‹_› s h
  · nomatch h

/-- **Each scoped term taclet is sound**: its two terms have one Theory value
in every state (`TermTaclet.sound`). -/
theorem TermTaclet.sound {t t' : Tm C Γ .val} : TermTaclet t t' → Tm.Theq t t'
  | @findOnSave _ _ s p q v hp hq => fun σ => by
    simp only [Tm.denote, Op0.denote, Op1.denote, Op2.denote, Op3.denote,
      ← Tm.sameSegs_denote σ hq, find_copyTo_same _ (Tm.denote_ne_nil σ hp), copyVal]
    exact Equiv.refl _
  | .findOnSaveFrame h => fun σ => by
    simp only [Tm.denote, Op2.denote, Op3.denote, find_copyTo_frame _ _ _ _ (Tm.diverges_denote σ h)]
    exact Equiv.refl _
  | @findMemberCons _ _ s p r p' h => fun σ => by
    simp only [Tm.denote, Op1.denote, Op2.denote, Tm.shift?_denote σ p h,
      find_cons _ _ (Tm.denote_ne_nil σ (Tm.shift?_hasSeg p h))]
    exact Equiv.refl _
  | @selectOnSaveMember _ _ s p r p' v q h =>
    Tm.find_fill_theq (Tm.selectOnSaveMember_denote h) .hole q
  | @selectOnSaveFrame _ _ s p r r' p' v q h hr =>
    Tm.find_fill_theq (Tm.selectOnSaveFrame_denote h hr) .hole q
  | @selectOnDelAtMember _ _ s p r p' q h =>
    Tm.find_fill_theq (Tm.selectOnDelAtMember_denote h) .hole q
  | @selectOnDelAtFrame _ _ s p r r' p' q h hr =>
    Tm.find_fill_theq (Tm.selectOnDelAtFrame_denote h hr) .hole q
  | @selectOnSaveMemberIn _ _ K s p r p' v q h =>
    Tm.find_fill_theq (Tm.selectOnSaveMember_denote h) K q
  | @selectOnSaveFrameIn _ _ K s p r r' p' v q h hr =>
    Tm.find_fill_theq (Tm.selectOnSaveFrame_denote h hr) K q
  | @selectOnDelAtMemberIn _ _ K s p r p' q h =>
    Tm.find_fill_theq (Tm.selectOnDelAtMember_denote h) K q
  | @selectOnDelAtFrameIn _ _ K s p r r' p' q h hr =>
    Tm.find_fill_theq (Tm.selectOnDelAtFrame_denote h hr) K q
  | @findOnDelAt _ _ s p q w hw hp hq => fun σ => by
    have hr : findSt (s.denote σ) (p.denote σ) = .prim w := Equiv.prim_iff.1 (hw.sound σ)
    simp only [Tm.denote, Op0.denote, Op2.denote, ← Tm.sameSegs_denote σ hq,
      find_delAt_same _ (Tm.denote_ne_nil σ hp), hr, delValueDefault]
    exact Equiv.refl _
  | @findOnDelAtValue _ _ s p q hp hq => fun σ => by
    simp only [Tm.denote, Op1.denote, Op2.denote, ← Tm.sameSegs_denote σ hq,
      find_delAt_same _ (Tm.denote_ne_nil σ hp)]
    exact Equiv.refl _
  | .delValueLit => fun σ => by
    simp only [Tm.denote, Op0.denote, Op1.denote, delValueDefault]
    exact Equiv.refl _
  | @findOnDelAtBelow _ _ s p q w hk hw hp hq => fun σ => by
    obtain ⟨r, hr, hqr⟩ := Tm.extends_denote σ q hq
    have hw' := Tm.findLit?_theq hw σ
    simp only [Tm.denote, Op0.denote, Op2.denote] at hw' ⊢
    rw [hqr, find_delAt_below _ (Tm.denote_ne_nil σ hp) hr (hk σ), ← hqr,
      Equiv.prim_iff.1 hw', delValueDefault]
    exact Equiv.refl _
  | .findOnDelAtFrame h => fun σ => by
    simp only [Tm.denote, Op2.denote, find_delAt_frame _ (Tm.diverges_denote σ h)]
    exact Equiv.refl _
  | .findOnPushFrame h => fun σ => by
    simp only [Tm.denote, Op2.denote, Op3.denote, find_pushT_frame _ _ (Tm.diverges_denote σ h)]
    exact Equiv.refl _
  | .findOnPopFrame h => fun σ => by
    simp only [Tm.denote, Op2.denote, find_popT_frame _ (Tm.diverges_denote σ h)]
    exact Equiv.refl _
  | .lenOnSaveFrame h => fun σ => by
    simp only [Tm.denote, Op2.denote, Op3.denote,
      find_copyTo_frame _ _ _ _ (Tm.divergesLen_denote σ h)]
    exact Equiv.refl _
  | .lenOnDelAtFrame h => fun σ => by
    simp only [Tm.denote, Op2.denote, find_delAt_frame _ (Tm.divergesLen_denote σ h)]
    exact Equiv.refl _
  | .theory h => h
  | .symm r => r.sound.symm

end Sound

/-! ## Pins -/

section Pins

variable {Γ : Ctx}

/- `tm{ … }` writes a scoped rule and prints it back as it was written; an
escape's term prints as the closer's does. -/
/--
info: @TermTaclet.findOnSave : ∀ {C : Contract} {Γ : Ctx} {s : Tm C Γ Srt.st} {p q : Tm C Γ Srt.path} {v : Value},
  autoParam (p.hasSeg = true) _auto✝ →
    autoParam (p.sameSegs q = true) _auto✝¹ → TermTaclet tm{ find(save(s, p, lit(v)), q) } tm{ lit(v) }
-/
#guard_msgs in
#check @TermTaclet.findOnSave

/--
info: @TermTaclet.findOnPushFrame : ∀ {C : Contract} {Γ : Ctx} {s : Tm C Γ Srt.st} {p q : Tm C Γ Srt.path}
  {v : Tm C Γ Srt.sv},
  autoParam (p.diverges q = true) _auto✝ →
    TermTaclet tm{ find(save(save(s, p[p.length], v), p.length, p.length + 1), q) } tm{ find(s, q) }
-/
#guard_msgs in
#check @TermTaclet.findOnPushFrame

/--
info: @TermTaclet.selectOnSaveMemberIn : ∀ {C : Contract} {Γ : Ctx} (K : SCtxS C Γ) {s : Tm C Γ Srt.st} {p : Tm C Γ Srt.path}
  {r : Name} {p' : Tm C Γ Srt.path} {v : Tm C Γ Srt.sv} {q : Tm C Γ Srt.path},
  autoParam (p.shift? = some (r, p')) _auto✝ →
    TermTaclet tm{ find(‹K.fill ((s.save p v).select r)›, q) } tm{ find(‹K.fill ((s.select r).save p' v)›, q) }
-/
#guard_msgs in
#check @TermTaclet.selectOnSaveMemberIn

/-- `t⊕⊕` prints with its operand's symbols unfolded (W9.6 review). -/
theorem bumped_pin (op : IncDec) (p : PrimTy) (s : Tm C Γ .st) (q : Tm C Γ .path) :
    (tm{ find(s, q)⊕⊕ + 1 } : Tm C Γ .val) = tm{ find(s, q)⊕⊕ + 1 } := rfl

/--
info: Solidity.bumped_pin {C : Contract} {Γ : Ctx} (op : IncDec) (p : PrimTy) (s : Tm C Γ Srt.st) (q : Tm C Γ Srt.path) :
  tm{ find(s, q)⊕⊕ + 1 } = tm{ find(s, q)⊕⊕ + 1 }
-/
#guard_msgs in
#check bumped_pin

/-- The side conditions close by `rfl` on closed paths. -/
example (s : Tm C Γ .st) (v : Tm C Γ .sv) :
    TermTaclet (tm{ find(save(s, ‹.app1 (.field "age") rfl (.app0 (.root "alice"))›, v),
      ‹.app1 (.field "name") rfl (.app0 (.root "alice"))›) } : Tm C Γ .val)
      tm{ find(s, ‹.app1 (.field "name") rfl (.app0 (.root "alice"))›) } :=
  .findOnSaveFrame

example (s : Tm C Γ .st) (w : Value) :
    TermTaclet
      (tm{ find(save(s, ‹.app2 .at (.app0 (.root "xs")) (.app0 (.lit (.int 2)))›, lit(w)),
        ‹.app3 .atIn s (.app0 (.root "xs")) (.app0 (.lit (.int 2)))›) } : Tm C Γ .val) tm{ lit(w) } :=
  .findOnSave

/-- The recursors reduce in the kernel. -/
example : (Tm.app2 (.binop .add .uint) (.pvV (.here (Γ := []))) (.app0 (.lit (.int 1))) :
    Tm C [.val .uint] .val).litVarsS = some [⟨_, .here⟩] := rfl

example : (Tm.app2 .at (.app0 (.root "xs")) (.pvV .here) : Tm C [.val .uint] .path).beqR
    (Tm.app2 .at (.app0 (.root "xs")) (.pvV .here) : Tm C [.val .uint] .path) = true := rfl

example : (Tm.app2 .at (.app0 (.root "xs")) (.pvV .here) : Tm C [.val .uint] .path).beqR
    (Tm.app2 .at (.app0 (.root "ys")) (.pvV .here) : Tm C [.val .uint] .path) = false := rfl

end Pins

end Solidity
