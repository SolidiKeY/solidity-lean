import Solidity.Calculus.UpdateRules
import Solidity.Calculus.WalkSyntax
import Solidity.Calculus.Rewrite
import Solidity.Calculus.ProvesDerive

/-!
# Today's steps after the program, on a scoped goal

Under `open scoped Solidity.Scoped` the lines that finish a goal keep
today's text (`Calculus/Rewrite.lean`): `refine merge rfl ?_` and
`refine Proves.mergeStorage ?_` (`sequentialToParallel`), `refine simplify
?_`, `refine Proves.eqDSplit ?_ ?_ ?_`, `exact Proves.definedWritten`,
`exact Proves.definedLit`, `exact Proves.eqRefl`, `exact Proves.eqDClose`,
`sol_apply_upd`, and `rw [r]`/`sol_rw [r, …]`.  On a scoped goal
(`Proves`) each is the scoped rule of `Calculus/Proves.lean` or
`Calculus/UpdateRules.lean`; on today's goal, today's.

The scoped context has what today's does not show: hidden binders (a
declaration's local) and scope ends (an update that only pops).  So a merge
line takes the scope ends under the last update into it first, then merges
the last update with the one before it past the hidden binders between them
(`Proves.merge`'s `bs`): one line, one merge of updates that print.

What a step computes (the merged update, the goal with an update applied, a
rewritten update) is computed by the compiled code and quoted back
(`Upd.quote`, `Fml.quote`), so that the next line, and the printer, see its
terms; the kernel checks it (`rfl`).
-/

namespace Solidity

open Lean Elab Tactic Meta

/-! ## Computing and quoting -/

/-- The contract's name of a scoped goal. -/
def Walk.contractName (C : Expr) : MetaM Lean.Name := do
  let some n := (← whnfR C).constName? | throwError "not a named contract: {C}"
  return n

/-- `e : Option T`, computed by the compiled code, each value quoted back by
`quote` (`Upd.quote`, `Fml.quote`: its explicit arguments the contract's
name and the value). -/
unsafe def Walk.evalQuoteOptImpl (C : Expr) (quote : Lean.Name) (e : Expr) : MetaM (Option Expr) := do
  let c := quoteConstName (← Walk.contractName C)
  let T := (← whnf (← inferType e)).appArg!
  let qf ← withLocalDeclD `x T fun x => do mkLambdaFVars #[x] (← mkAppM quote #[c, x])
  let ty := mkApp (mkConst ``Option [levelZero]) (mkConst ``Expr)
  evalExpr (Option Expr) ty (← mkAppM ``Option.map #[qf, e])

@[implemented_by Walk.evalQuoteOptImpl]
opaque Walk.evalQuoteOpt (C : Expr) (quote : Lean.Name) (e : Expr) : MetaM (Option Expr)

/-- The parts of a scoped sequent `Proves C R Γ₀ H φ`. -/
def Walk.provesParts (ty : Expr) : MetaM (Expr × Expr × Expr) := do
  let ty ← instantiateMVars ty
  unless ty.isAppOfArity ``Proves 6 do throwError "not a scoped sequent"
  return (ty.getArg! 0, ty.getArg! 4, ty.getArg! 5)

/-- The top update of a context, `H.upd m V`: `(H, m, V)`. -/
def Walk.updTop? (H : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let H ← whnf H
  unless H.isAppOfArity ``Hyps.upd 7 do return none
  return some (H.getArg! 4, H.getArg! 5, H.getArg! 6)

/-! ## `sequentialToParallel` -/

/-- The update below the top one, past the hidden binders between: the
binders (top first) and the update. -/
def Walk.below (H₁ : Expr) : MetaM (Option (Array Expr × Expr)) := do
  let mut bsRev : Array Expr := #[]
  let mut cur ← whnf H₁
  while cur.isAppOfArity ``Hyps.bind 7 do
    let tr ← mkAppM ``Prod.mk #[cur.getArg! 4, ← mkAppM ``Prod.mk #[cur.getArg! 5, cur.getArg! 6]]
    bsRev := bsRev.push tr
    cur ← whnf (cur.getArg! 3)
  unless cur.isAppOfArity ``Hyps.upd 7 do return none
  return some (bsRev, cur.getArg! 6)

/-- One `Proves.merge` on the main goal: the top update with the update
below the hidden binders under it.  Fails where there is none. -/
def Walk.mergeOnce : TacticM Unit := withMainContext do
  let (C, H, _) ← Walk.provesParts (← getMainTarget)
  let some (H₁, _, V) ← Walk.updTop? H | throwError "merge: no update at the top of the context"
  let some (bsRev, U) ← Walk.below H₁ | throwError "merge: no update before the last one"
  let elemTy ← mkAppM ``Prod #[mkConst ``Modality, ← mkAppM ``Prod #[mkConst ``Var, mkConst ``LTy]]
  let bs ← mkListLit elemTy bsRev.reverse.toList
  let some U' ← Walk.evalQuoteOpt C ``Upd.quote (← mkAppM ``Upd.liftBinds? #[bs, U])
    | throwError "merge: the update before the binders cannot move under them"
  let some W ← Walk.evalQuoteOpt C ``Upd.quote (← mkAppM ``Upd.seqPar #[U', V])
    | throwError "merge: the last update reads a global part the one before it writes"
  let bsS ← Term.exprToSyntax bs
  let U'S ← Term.exprToSyntax U'
  let WS ← Term.exprToSyntax W
  evalTactic (← `(tactic|
    refine Solidity.Proves.merge (bs := $bsS) (U' := $U'S) (W := $WS) rfl rfl ?_))

/-- `core_merge`: the scope ends under the last update merged into it,
silently, then one merge (`Proves.merge`, past the hidden binders). -/
elab "core_merge" : tactic => withMainContext do
  for _ in [0:64] do
    let (_, H, _) ← withMainContext do Walk.provesParts (← getMainTarget)
    let some (H₁, _, V) ← Walk.updTop? H | break
    let some (bsRev, U) ← Walk.below H₁ | break
    -- a scope end at the top, or below the binders, is merged silently
    unless (← Walk.popsOnly V) && bsRev.isEmpty || (← Walk.popsOnly U) do break
    Walk.mergeOnce
  Walk.mergeOnce

/-! ## The steps that finish a goal -/

/-- `core_simplify`: `Proves.simplify'`, the simplified update computed. -/
elab "core_simplify" : tactic => withMainContext do
  let (C, H, _) ← Walk.provesParts (← getMainTarget)
  let some (_, _, U) ← Walk.updTop? H | throwError "simplify: no update at the top of the context"
  let some U₂ ← Walk.evalQuoteOpt C ``Upd.quote (← mkAppM ``Option.some #[
      ← mkAppM ``Upd.simp #[mkNatLit 0, U]]) | throwError "simplify: internal error"
  let U₂S ← Term.exprToSyntax U₂
  evalTactic (← `(tactic| refine Solidity.Proves.simplify' (U₂ := $U₂S) rfl ?_))

/-- `core_apply_upd`: `Proves.applyOnRigidBox`, the goal with the last
update applied computed. -/
elab "core_apply_upd" : tactic => withMainContext do
  let (C, H, φ) ← Walk.provesParts (← getMainTarget)
  let some (_, _, W) ← Walk.updTop? H | throwError "sol_apply_upd: no update at the top of the context"
  let some φ' ← Walk.evalQuoteOpt C ``Fml.quote (← mkAppM ``Fml.substU #[W, φ])
    | throwError "sol_apply_upd: the goal reads a global part the update writes, or is not \
        first-order"
  let φ'S ← Term.exprToSyntax φ'
  evalTactic (← `(tactic| refine Solidity.Proves.applyOnRigidBox (φ' := $φ'S) rfl ?_))

/-! ## A Theory lemma as a rewrite rule, on scoped terms

`theoryRewrite` (`Calculus/TheoryRewrite.lean`) on a scoped closed term
`u : Tm C [] .val`: `u.denote σ` unfolded by the denotation of its symbols
(the `Tm.denote_*S` lemmas, `rfl`), rewritten by the laws, and read back as a
scoped term (`reifyTermS`).  The two `simp` runs prove
`∀ σ, u.denote σ = u'.denote σ`, which `Tm.Theq.of_eq` makes a Theory
equation. -/

section TheoryS

open Theory Theory.StValue

variable {C : Contract} {Γ : Ctx}

theorem Tm.denote_litS (σ : EState C Γ) (v : Semantics.Value) :
    (Tm.app0 (.lit v) : Tm C Γ .val).denote σ = .prim v := rfl
theorem Tm.denote_findS (σ : EState C Γ) (s : Tm C Γ .st) (p : Tm C Γ .path) :
    (Tm.app2 .find s p : Tm C Γ .val).denote σ = findSt (s.denote σ) (p.denote σ) := rfl
theorem Tm.denote_lenS (σ : EState C Γ) (s : Tm C Γ .st) (p : Tm C Γ .path) :
    (Tm.app2 .len s p : Tm C Γ .val).denote σ = findSt (s.denote σ) (p.denote σ ++ [lengthSeg]) :=
  rfl
theorem Tm.denote_storageS (σ : EState C Γ) : (Tm.app0 .storage : Tm C Γ .st).denote σ = σ.glob.abs :=
  rfl
theorem Tm.denote_saveS (σ : EState C Γ) (s : Tm C Γ .st) (p : Tm C Γ .path) (v : Tm C Γ .sv) :
    (Tm.app3 .save s p v : Tm C Γ .st).denote σ = copyTo (s.denote σ) (p.denote σ) (v.denote σ) :=
  rfl
theorem Tm.denote_delAtS (σ : EState C Γ) (s : Tm C Γ .st) (p : Tm C Γ .path) :
    (Tm.app2 .delAt s p : Tm C Γ .st).denote σ = StValue.delAt (s.denote σ) (p.denote σ) := rfl
theorem Tm.denote_svalS (σ : EState C Γ) (h : Op1.sval.named = false) (t : Tm C Γ .val) :
    (Tm.app1 .sval h t : Tm C Γ .sv).denote σ = t.denote σ := rfl
theorem Tm.denote_sfindS (σ : EState C Γ) (s : Tm C Γ .st) (p : Tm C Γ .path) :
    (Tm.app2 .sfind s p : Tm C Γ .sv).denote σ = findSt (s.denote σ) (p.denote σ) := rfl
theorem Tm.denote_rootS (σ : EState C Γ) (r : Name) :
    (Tm.app0 (.root r) : Tm C Γ .path).denote σ = [.field r] := rfl
theorem Tm.denote_fieldS (σ : EState C Γ) (f : Name) (h : (Op1.field f).named = false)
    (p : Tm C Γ .path) : (Tm.app1 (.field f) h p : Tm C Γ .path).denote σ = p.denote σ ++ [.field f] :=
  rfl
theorem Tm.denote_atS (σ : EState C Γ) (p : Tm C Γ .path) (i : Tm C Γ .val) :
    (Tm.app2 .at p i : Tm C Γ .path).denote σ = p.denote σ ++ [.at (asInt (i.denote σ))] := rfl

end TheoryS

open Theory Theory.StValue in
/-- The denotation lemmas `theoryRewriteS` unfolds with. -/
def theoryUnfoldLemmasS : List Lean.Name :=
  [``Tm.denote_litS, ``Tm.denote_findS, ``Tm.denote_lenS, ``Tm.denote_storageS,
    ``Tm.denote_saveS, ``Tm.denote_delAtS, ``Tm.denote_svalS, ``Tm.denote_sfindS,
    ``Tm.denote_rootS, ``Tm.denote_fieldS, ``Tm.denote_atS]

/-- `e`, a `denote` of a scoped term of the sort `srt` at `σ`, is that term. -/
def reifyFoldedS? (srt : Lean.Name) (σ e : Expr) : MetaM (Option Expr) := do
  unless e.isAppOfArity ``Tm.denote 5 do return none
  unless (← whnf (e.getArg! 3)).isConstOf srt do return none
  if ← isDefEq (e.getArg! 2) σ then return some e.appArg! else return none

open Theory Theory.StValue in
mutual

/-- A value of the Theory, written as a scoped term of the context `Γ`: the
inverse of `Tm.denote σ`, for the values it gives (`reifyTerm`'s twin). -/
partial def reifyTermS (C Γ σ e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if let some t ← reifyFoldedS? ``Srt.val σ e then return t
  let lit (v : Expr) : MetaM Expr := mkAppOptM ``Tms.Term.lit #[C, Γ, v]
  match_expr e with
  | StValue.prim v => lit v
  | StValue.int n => lit (mkApp (mkConst ``Semantics.PrimVal.int) n)
  | StValue.bool b => lit (mkApp (mkConst ``Semantics.PrimVal.bool) b)
  | findSt s p =>
    let s ← reifySTermS C Γ σ s
    if let some p' ← lengthOf? p then
      return ← mkAppOptM ``Tms.Term.len #[C, Γ, s, ← reifyPTermS C Γ σ p']
    mkAppOptM ``Tms.Term.find #[C, Γ, s, ← reifyPTermS C Γ σ p]
  | _ => throwError "not a term: {e}"

/-- A storage node, written as a scoped storage term. -/
partial def reifySTermS (C Γ σ e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if let some s ← reifyFoldedS? ``Srt.st σ e then return s
  match_expr e with
  | Semantics.State.abs g =>
    unless ← isDefEq g (← mkAppM ``EState.glob #[σ]) do throwError "not a storage term: {e}"
    mkAppOptM ``Tms.STerm.storage #[C, Γ]
  | copyTo s p v =>
    mkAppOptM ``Tms.STerm.save #[C, Γ, ← reifySTermS C Γ σ s, ← reifyPTermS C Γ σ p,
      ← reifySValTS C Γ σ v]
  | StValue.delAt s p =>
    mkAppOptM ``Tms.STerm.delAt #[C, Γ, ← reifySTermS C Γ σ s, ← reifyPTermS C Γ σ p]
  | _ => throwError "not a storage term: {e}"

/-- A value stored by a `save`, written as its right-hand side. -/
partial def reifySValTS (C Γ σ e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if let some v ← reifyFoldedS? ``Srt.sv σ e then return v
  match_expr e with
  | findSt s p =>
    mkAppOptM ``Tms.SValT.find #[C, Γ, ← reifySTermS C Γ σ s, ← reifyPTermS C Γ σ p]
  | _ => mkAppOptM ``Tms.SValT.val #[C, Γ, ← reifyTermS C Γ σ e]

/-- A list of segments, written as a scoped path term. -/
partial def reifyPTermS (C Γ σ e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if let some p ← reifyFoldedS? ``Srt.path σ e then return p
  if let some (p, q) := append? e then
    let some segs := listLit? q | throwError "not a path term: {e}"
    return ← segs.foldlM (extendS C Γ σ) (← reifyPTermS C Γ σ p)
  let some (a :: segs) := listLit? e | throwError "not a path term: {e}"
  let_expr Semantics.Seg.field r := a | throwError "not a path term: {e}"
  segs.foldlM (extendS C Γ σ) (← mkAppOptM ``Tms.PTerm.root #[C, Γ, r])

/-- The scoped path `p` one segment further. -/
partial def extendS (C Γ σ : Expr) (p a : Expr) : MetaM Expr := do
  match_expr a with
  | Semantics.Seg.field f => mkAppOptM ``Tms.PTerm.field #[C, Γ, p, f]
  | Semantics.Seg.at i =>
    let i ← match_expr i with
      | asInt t => reifyTermS C Γ σ t
      | _ => mkAppOptM ``Tms.Term.lit #[C, Γ, mkApp (mkConst ``Semantics.PrimVal.int) i]
    mkAppOptM ``Tms.PTerm.at #[C, Γ, p, i]
  | _ => throwError "not a segment: {a}"

end

/-- The scoped term `u : Tm C Γ .val` rewritten by the laws `thms` in the
Theory: the term `u'` and a proof of `Tm.Theq u u'`, if a law applies and
the result is a term. -/
def theoryRewriteS (thms : SimpTheorems) (C u : Expr) : MetaM (Option (Expr × Expr)) := do
  let ty ← whnf (← inferType u)
  unless ty.isAppOfArity ``Tm 3 do return none
  let Γ := ty.getArg! 1
  withLocalDeclD `σ (mkApp2 (mkConst ``EState) C Γ) fun σ => do
    let denote (t : Expr) : Expr := mkAppN (mkConst ``Tm.denote) #[C, Γ, σ, mkConst ``Srt.val, t]
    let lhs := denote u
    let mut unfold : SimpTheorems := {}
    for n in theoryUnfoldLemmasS do unfold ← unfold.addConst n
    let (r₁, _) ← simp lhs (← Simp.mkContext (simpTheorems := #[unfold]))
    let (r₂, _) ← simp r₁.expr (← Simp.mkContext (simpTheorems := #[thms]))
      (discharge? := dischargeTheory)
    if r₂.expr == r₁.expr then return none
    let some u' ← (try some <$> reifyTermS C Γ σ r₂.expr catch _ => pure none) | return none
    if ← isDefEq u' u then return none
    let ty ← mkEq lhs (denote u')
    let pf ← mkEqTrans (← r₁.getProof) (← r₂.getProof)
    unless ← isDefEq (← inferType pf) ty do return none
    let h ← mkLambdaFVars #[σ] (← mkExpectedTypeHint pf ty)
    return some (u', mkAppN (mkConst ``Tm.Theq.of_eq) #[C, Γ, u, u', h])

/-! ## Rewriting with a term taclet or the Theory's laws -/

/-- The sides of a formula's equations (`Fml.eq`), at any depth: through
the connectives, updates, quantifiers, hidden binders and an open
modality's postcondition, as `Fml.rwEqC` rewrites them. -/
partial def Walk.eqSides (φ : Expr) : MetaM (Array Expr) := do
  let φ ← whnf φ
  if φ.isAppOfArity ``Fml.eq 4 then return #[φ.getArg! 2, φ.getArg! 3]
  if φ.isAppOfArity ``Fml.and 4 || φ.isAppOfArity ``Fml.imp 4 then
    return (← Walk.eqSides (φ.getArg! 2)) ++ (← Walk.eqSides (φ.getArg! 3))
  if φ.isAppOfArity ``Fml.not 3 || φ.isAppOfArity ``Fml.havoc 3 ||
      φ.isAppOfArity ``Fml.upd 6 || φ.isAppOfArity ``Fml.modal 8 ||
      φ.isAppOfArity ``Fml.all 5 || φ.isAppOfArity ``Fml.bind 6 ||
      φ.isAppOfArity ``Fml.anon 4 then
    return ← Walk.eqSides φ.appArg!
  return #[]

/-- The sides of the equations of a context's preconditions (`Hyps.rwEqC`). -/
partial def Walk.hypSides (H : Expr) : MetaM (Array Expr) := do
  let H ← whnf H
  if H.isAppOfArity ``Hyps.pre 5 then
    return (← Walk.hypSides (H.getArg! 3)) ++ (← Walk.eqSides (H.getArg! 4))
  if H.isAppOfArity ``Hyps.upd 7 then return ← Walk.hypSides (H.getArg! 4)
  if H.isAppOfArity ``Hyps.havoc 4 || H.isAppOfArity ``Hyps.all 6 ||
      H.isAppOfArity ``Hyps.bind 7 || H.isAppOfArity ``Hyps.anon 5 then
    return ← Walk.hypSides (H.getArg! 3)
  return #[]

/-- A formula rewritten by `q` (`Fml.rwEqC`), computed and quoted back; the
formula as written where nothing in it is rewritten, its explicit `∀`s
marked again otherwise (`Symex.restoreMarks`). -/
def Walk.rwFml (C q a : Expr) : MetaM Expr := do
  let some a₀ ← Walk.evalQuoteOpt C ``Fml.quote (← mkAppM ``Option.some #[a])
    | throwError "rw: internal error"
  let some a' ← Walk.evalQuoteOpt C ``Fml.quote (← mkAppM ``Option.some #[← mkAppM ``Fml.rwEqC #[q, a]])
    | throwError "rw: internal error"
  return if a' == a₀ then a else Symex.restoreMarks a a'

/-- A context rewritten by `q` (`Hyps.rwEqC`): each precondition by
`Walk.rwFml`, every other entry kept as written, so that the marks of
explicit `∀`s (`Fml.markExplicitVar`), which `Seq.paramCount` reads, stay
(decision 28); `none` where the context is not written out. -/
partial def Walk.rwHyps (C q H : Expr) : MetaM (Option Expr) := do
  let H ← whnfR (← instantiateMVars H)
  let below (i : Nat) (f : Array Expr → MetaM (Array Expr) := pure) : MetaM (Option Expr) := do
    let some H₁ ← Walk.rwHyps C q (H.getArg! i) | return none
    let args ← f (H.getAppArgs.set! i H₁)
    return some (mkAppN H.getAppFn args)
  if H.isAppOfArity ``Hyps.nil 2 then return some H
  if H.isAppOfArity ``Hyps.pre 5 then
    return ← below 3 fun args => do return args.set! 4 (← Walk.rwFml C q (H.getArg! 4))
  if H.isAppOfArity ``Hyps.upd 7 then return ← below 4
  if H.isAppOfArity ``Hyps.havoc 4 || H.isAppOfArity ``Hyps.all 6 ||
      H.isAppOfArity ``Hyps.bind 7 || H.isAppOfArity ``Hyps.anon 5 then
    return ← below 3
  return none

/-- Rewrite the main goal by `q = (t, t')`, two closed terms at the empty
scope: in the sides of the sequent's equations (`Proves.rewrite'`,
`hq : Tm.Theq t t'`), the context's preconditions and the goal, a modality
still open or not, when one reads `t`; else in the last box update's
right-hand sides (`Proves.updRw'`) when `t'` is a literal.  The context
keeps what it does not rewrite as written, its marks of explicit `∀`s with
it (`Walk.rwHyps`). -/
def Walk.rwWith (C q hq : Expr) (inGoal : Bool) : TacticM Unit := withMainContext do
  let (_, H, φ) ← Walk.provesParts (← getMainTarget)
  let qS ← Term.exprToSyntax q
  let hqS ← Term.exprToSyntax hq
  if inGoal then
    let φ' ← Walk.rwFml C q φ
    let H' ← match ← Walk.rwHyps C q H with
      | some H' => pure H'
      | none =>
        let some H' ← Walk.evalQuoteOpt C ``Hyps.quote
            (← mkAppM ``Option.some #[← mkAppM ``Hyps.rwEqC #[q, H]])
          | throwError "rw: internal error"
        pure H'
    let φ'S ← Term.exprToSyntax φ'
    let H'S ← Term.exprToSyntax H'
    evalTactic (← `(tactic|
      refine Solidity.Proves.rewrite' ($qS) ($hqS) (H' := $H'S) (φ' := $φ'S) rfl rfl ?_))
  else
    let some (_, _, U) ← Walk.updTop? H | throwError "rw: no update at the top of the context"
    let some U₂ ← Walk.evalQuoteOpt C ``Upd.quote (← mkAppM ``Option.some #[← mkAppM ``Upd.rwC #[q, U]])
      | throwError "rw: internal error"
    let U₂S ← Term.exprToSyntax U₂
    evalTactic (← `(tactic|
      refine Solidity.Proves.updRw' ($qS)
        (Solidity.Tm.EvalRefines.of_theq ($hqS) (by first | rfl | decide)) (U₂ := $U₂S) rfl ?_))

/-- The value subterms of the closed term `t` (at the empty scope), `t`
first. -/
partial def Walk.valSubterms (t : Expr) (acc : Array Expr := #[]) : MetaM (Array Expr) := do
  let mut acc := acc
  if !acc.contains t && t.getAppFn.constName?.any (·.getPrefix == ``Tm) then
    let ty ← whnf (← inferType t)
    if ty.isAppOfArity ``Tm 3 && (← whnf (ty.getArg! 2)).isConstOf ``Srt.val then
      acc := acc.push t
  for a in t.getAppArgs do acc ← Walk.valSubterms a acc
  return acc

/-- The places a rewrite of the main goal may reach: the sides of its
equations, then the closed value terms of the last box update's right-hand
sides; each read at the empty scope (`Tm.toNilQ?`), and whether it is in the
goal. -/
def Walk.rwCandidates : TacticM (Array (Expr × Bool)) := withMainContext do
  let (_, H, φ) ← Walk.provesParts (← getMainTarget)
  let mut out : Array (Expr × Bool) := #[]
  for side in (← Walk.hypSides H) ++ (← Walk.eqSides φ) do
    if let some t ← Tm.toNilQ? side then out := out.push (t, true)
  if let some (_, m, U) ← Walk.updTop? H then
    if (← whnf m).isConstOf ``Modality.box then
      for t in ← Tm.closedNilVals U do
        for u in ← Walk.valSubterms t do out := out.push (u, false)
  return out

/-- `h`, a term taclet's name, as the scoped one (`TermTacletS.h`). -/
def qualifyTacletS (h : Lean.Term) : TermElabM Lean.Term := do
  let qual (id : Syntax) : TermElabM (Option Syntax) := do
    unless id.isIdent do return none
    let n := ``TermTacletS ++ id.getId
    if (← getEnv).contains n then return some (mkCIdentFrom id n) else return none
  if let some q ← qual h.raw then return ⟨q⟩
  if h.raw.isOfKind ``Lean.Parser.Term.app then
    if let some q ← qual h.raw[0] then return ⟨h.raw.setArg 0 q⟩
  return h

/-- `pf` as a scoped term taclet: itself, or, for a Theory equation
`Tm.Theq t t'`, the rule `TermTacletS.theory` makes of it. -/
def asTacletS (pf : Expr) : MetaM Expr := do
  if (← whnfR (← instantiateMVars (← inferType pf))).isAppOf ``Tm.Theq then
    mkAppM ``TermTacletS.theory #[pf]
  else pure pf

/-- `rw [r]` with a term taclet (`TermTacletS`) or a Theory equation
(`Tm.Theq`) `r` on a scoped goal: its left side matched against each place
a rewrite may reach, in turn. -/
def Walk.rwTaclet (h : Lean.Term) (symm : Bool) : TacticM Unit := withMainContext do
  let (C, _, _) ← Walk.provesParts (← getMainTarget)
  for (t₀, inGoal) in ← Walk.rwCandidates do
    let saved ← saveState
    try
      let h' ← qualifyTacletS h
      let pf ← match h' with
        | `($id:ident) => elabTerm (← `(@$id)) none (mayPostpone := true)
        | _ => elabTerm h' none (mayPostpone := true)
      let (args, _, _) ← forallMetaTelescope (← instantiateMVars (← inferType pf))
      let pf ← asTacletS (mkAppN pf args)
      let pf ← if symm then mkAppM ``TermTacletS.symm #[pf] else pure pf
      let_expr TermTacletS _ _ lhs rhs ← (← whnfR (← instantiateMVars (← inferType pf)))
        | throwError "rw: {h} is not a term taclet or a Theory equation"
      unless ← isDefEq lhs t₀ do throwError "no match"
      for a in args do
        let g := a.mvarId!
        if !(← g.isAssigned) && (← isProp (← g.getType)) then solRwSide h g
      Term.synthesizeSyntheticMVarsNoPostponing
      let pf ← instantiateMVars pf
      let rhs ← instantiateMVars rhs
      if pf.hasExprMVar || rhs.hasExprMVar then throwError "rw: could not instantiate {pf}"
      if !inGoal then
        unless (← whnfR rhs).isAppOf ``Tm.app0 do throwError "not a literal"
      let q ← mkAppM ``Prod.mk #[t₀, rhs]
      Walk.rwWith C q (← mkAppM ``TermTacletS.sound #[pf]) inGoal
      return
    catch _ => saved.restore
  throwError "rw: {h} rewrites nothing in the sequent"

/-- `sol_rw [l₁, …]` with Theory laws on a scoped goal: each read of a closed
term they turn into a term rewritten (`theoryRewriteS`), until none is. -/
def Walk.rwTheory (thms : SimpTheorems) (names : Array Lean.Term) : TacticM Unit := do
  let mut rounds := 0
  let mut progress := true
  while progress && rounds < 32 do
    progress := false
    let (C, _, _) ← withMainContext do Walk.provesParts (← getMainTarget)
    for (t₀, inGoal) in ← Walk.rwCandidates do
      unless t₀.isAppOfArity ``Tm.app2 8 &&
          ((t₀.getArg! 5).isConstOf ``Op2.find || (t₀.getArg! 5).isConstOf ``Op2.len) do continue
      let some (u', pf) ← withMainContext (theoryRewriteS thms C t₀) | continue
      let saved ← saveState
      try
        if !inGoal then
          unless (← whnfR u').isAppOf ``Tm.app0 do throwError "not a literal"
        Walk.rwWith C (← mkAppM ``Prod.mk #[t₀, u']) pf inGoal
        progress := true
        break
      catch _ => saved.restore
    if progress then rounds := rounds + 1
  if rounds == 0 then
    throwError "sol_rw: no term of the sequent is rewritten to a term by {names}"

/-- `core_rw [r, …]`: `sol_rw`'s rules on a scoped goal, in order (a term
taclet (`TermTacletS`) or Theory equation by `Walk.rwTaclet`, a run of Theory laws by
`Walk.rwTheory`).  It fails on a goal that is not a scoped sequent. -/
def Walk.rwRules (rs : Array Syntax) : TacticM Unit := do
  unless (← instantiateMVars (← getMainTarget)).isAppOf ``Proves do
    throwError "core_rw: not a scoped sequent"
  let mut thms : SimpTheorems := {}
  let mut names : Array Lean.Term := #[]
  for r in rs do
    let h : Lean.Term := ⟨r[1]⟩
    let symm := !r[0].isNone
    let isTheq ← withMainContext do
      unless h.raw.isIdent do return true
      if (← getEnv).contains (``TermTacletS ++ h.raw.getId) ||
          (← getEnv).contains (``TermTaclet ++ h.raw.getId) then return true
      let some n ← (try some <$> realizeGlobalConstNoOverloadWithInfo h
          catch _ => pure none) | return true
      forallTelescope (← getConstInfo n).type fun _ ty => do
        let ty ← whnfR ty
        return ty.isAppOf ``Solidity.Term.Theq || ty.isAppOf ``Solidity.TermTaclet ||
          ty.isAppOf ``Solidity.Tm.Theq || ty.isAppOf ``Solidity.TermTacletS
    if isTheq then
      unless names.isEmpty do
        Walk.rwTheory thms names
        thms := {}; names := #[]
      withRef r <| Walk.rwTaclet h symm
    else
      let n ← realizeGlobalConstNoOverloadWithInfo h
      thms ← match (← getConstInfo n) with
        | .defnInfo _ => thms.addDeclToUnfold n
        | _ => thms.addConst n (inv := symm)
      names := names.push h
  unless names.isEmpty do Walk.rwTheory thms names

/-- `core_rw [r, …]`: `rw`/`sol_rw` on a scoped goal. -/
syntax "core_rw " "[" Lean.Parser.Tactic.rwRule,+ "]" : tactic

elab_rules : tactic
  | `(tactic| core_rw [$rs,*]) => Walk.rwRules (rs.getElems.map (·.raw))

/-! ## Today's lines, read on a scoped goal -/

namespace Scoped

scoped macro_rules
  | `(tactic| refine merge rfl ?_) =>
    `(tactic| first | core_merge | refine Solidity.NFml.Proves.merge rfl ?_)
  | `(tactic| refine Proves.merge rfl ?_) =>
    `(tactic| first | core_merge | refine Solidity.NFml.Proves.merge rfl ?_)
  | `(tactic| refine mergeStorage ?_) =>
    `(tactic| first | core_merge | refine Solidity.NFml.Proves.mergeStorage ?_)
  | `(tactic| refine Proves.mergeStorage ?_) =>
    `(tactic| first | core_merge | refine Solidity.NFml.Proves.mergeStorage ?_)
  | `(tactic| refine simplify ?_) =>
    `(tactic| first | core_simplify | refine Solidity.NFml.Proves.simplify ?_)
  | `(tactic| refine Proves.simplify ?_) =>
    `(tactic| first | core_simplify | refine Solidity.NFml.Proves.simplify ?_)
  | `(tactic| refine Proves.eqDSplit ?_ ?_ ?_) =>
    `(tactic| first | refine Solidity.Proves.eqDSplit ?_ ?_ ?_ | refine Solidity.NFml.Proves.eqDSplit ?_ ?_ ?_)
  | `(tactic| exact Proves.definedWritten) =>
    `(tactic| first | exact Solidity.Proves.definedWritten | exact Solidity.NFml.Proves.definedWritten)
  | `(tactic| exact Proves.definedLit) =>
    `(tactic| first | exact Solidity.Proves.definedLit | exact Solidity.NFml.Proves.definedLit)
  | `(tactic| exact Proves.eqRefl) =>
    `(tactic| first | exact Solidity.Proves.eqRefl | exact Solidity.NFml.Proves.eqRefl)
  | `(tactic| exact Proves.eqClose) =>
    `(tactic| first | exact Solidity.Proves.eqClose | exact Solidity.NFml.Proves.eqClose)
  | `(tactic| exact Proves.eqDClose) =>
    `(tactic| first | exact Solidity.Proves.eqDClose | exact Solidity.NFml.Proves.eqDClose)
  | `(tactic| sol_apply_upd) => `(tactic| core_apply_upd)
  | `(tactic| sol_rw [$rs,*]) => `(tactic| core_rw [$rs,*])
  | `(tactic| rw [$rs,*]) => `(tactic| core_rw [$rs,*])

end Scoped

end Solidity
