import Solidity.Calculus.Logic
import Solidity.Calculus.Quote

/-!
# A Theory lemma as a rewrite rule

`Proves.rewrite` rewrites a sequent with a term taclet, and
`TermTaclet.theory` makes one of any `Term.Theq t t'`; a law of
the Theory (`Theory/Storage.lean`, `Theory/Copy.lean`) is an `=` between
values of the algebra — `findSt (copyTo s p v) p = copyVal (findSt s p) v` —
not between terms.  This module turns one into the other, as mini-solkey's
`sol_rw` does: for a term `u` of the sequent it unfolds `u.denote σ` for an
arbitrary `σ` into `findSt`, `copyTo`, `delAt`, … (the `denote_*` lemmas of
`Calculus/TermRules.lean`), rewrites that with the lemmas, as
`simp only [lemma, …]` would, and reads the result back as a term `u'`
(`reifyTerm`).  The two `simp` runs are the proof of
`∀ σ, u.denote σ = u'.denote σ`, which `Term.Theq.of_eq` makes a rewrite
rule.  The kernel checks it: the search is all this module does.

Only the arms that read back are unfolded: a local, a memory read or a
condition stays `t.denote σ`, which reads back as `t`.  A lemma whose result
is not a term (`find_delAt_same` leaves `delValue (findSt s p)`) is not used
alone: `sol_rw [find_delAt_same, find_copyTo_same, copyVal, delValueDefault,
primDefault]` reads a written-then-deleted word as its default in one step.
A definition in the list (`copyVal`, `primDefault`) is unfolded.

A side condition is closed on the paths the terms fix: `p ≠ []` or
`diverges p q = true` by `decide`, where `p`, `q` are lists of literal
segments.  A path through an alias is not known, so a law needing one
does not fire there.

The tactic itself, `sol_rw [l₁, …]`, is in `Calculus/Rewrite.lean`: it
applies the rule this module finds with the rest of the `rw` machinery.
-/

namespace Solidity

open Lean Meta Semantics Theory Theory.StValue

/-- The denotation lemmas `theoryRewrite` unfolds with. -/
def theoryUnfoldLemmas : List Lean.Name :=
  [``Term.denote_lit, ``Term.denote_find, ``Term.denote_len, ``STerm.denote_storage,
    ``STerm.denote_save, ``STerm.denote_delAt, ``SValT.denote_val, ``SValT.denote_find,
    ``PTerm.denote_root, ``PTerm.denote_field, ``PTerm.denote_at]

/-! ## Reading a value back as a term -/

/-- `e`, a `denote` of a term of the sort `srt` at `σ` (`Tm.denote σ t`),
is that term. -/
def reifyFolded? (srt : Lean.Name) (σ e : Expr) : MetaM (Option Expr) := do
  unless e.isAppOfArity ``Tm.denote 4 do return none
  unless (← whnf (e.getArg! 1)).isConstOf srt do return none
  if ← isDefEq (e.getArg! 2) σ then return some e.appArg! else return none

/-- The elements of a list literal `[a, b, …]`. -/
partial def listLit? (e : Expr) : Option (List Expr) :=
  if e.isAppOfArity ``List.nil 1 then some []
  else if e.isAppOfArity ``List.cons 3 then (listLit? e.appArg!).map (e.appFn!.appArg! :: ·)
  else none

/-- The two sides of `p ++ q`. -/
def append? (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``HAppend.hAppend 6 then some (e.appFn!.appArg!, e.appArg!) else none

/-- `p`, where `e` is `p ++ [lengthSeg]`: the path of a `len`. -/
def lengthOf? (e : Expr) : MetaM (Option Expr) := do
  let some (p, q) := append? e | return none
  let some [a] := listLit? q | return none
  if ← isDefEq a (mkConst ``lengthSeg) then return some p
  return none

mutual

/-- A value of the Theory, written as a term: the inverse of `Tm.denote σ`,
for the values it gives. -/
partial def reifyTerm (C σ e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if let some t ← reifyFolded? ``Srt.val σ e then return t
  match_expr e with
  | StValue.prim v => return mkApp2 (mkConst ``Term.lit) C v
  | StValue.int n => return mkApp2 (mkConst ``Term.lit) C (mkApp (mkConst ``PrimVal.int) n)
  | StValue.bool b => return mkApp2 (mkConst ``Term.lit) C (mkApp (mkConst ``PrimVal.bool) b)
  | findSt s p =>
    let s ← reifySTerm C σ s
    if let some p' ← lengthOf? p then
      return mkApp3 (mkConst ``Term.len) C s (← reifyPTerm C σ p')
    return mkApp3 (mkConst ``Term.find) C s (← reifyPTerm C σ p)
  | _ => throwError "not a term: {e}"

/-- A storage node, written as a storage term. -/
partial def reifySTerm (C σ e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if let some s ← reifyFolded? ``Srt.st σ e then return s
  match_expr e with
  | State.abs σ' =>
    unless ← isDefEq σ σ' do throwError "not a storage term: {e}"
    return mkApp (mkConst ``STerm.storage) C
  | copyTo s p v =>
    return mkApp4 (mkConst ``STerm.save) C (← reifySTerm C σ s) (← reifyPTerm C σ p)
      (← reifySValT C σ v)
  | StValue.delAt s p =>
    return mkApp3 (mkConst ``STerm.delAt) C (← reifySTerm C σ s) (← reifyPTerm C σ p)
  | _ => throwError "not a storage term: {e}"

/-- A value stored by a `save`, written as its right-hand side. -/
partial def reifySValT (C σ e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if let some v ← reifyFolded? ``Srt.sv σ e then return v
  match_expr e with
  | findSt s p =>
    return mkApp3 (mkConst ``SValT.find) C (← reifySTerm C σ s) (← reifyPTerm C σ p)
  | _ => return mkApp2 (mkConst ``SValT.val) C (← reifyTerm C σ e)

/-- A list of segments, written as a path term: a root member, then members
and indices, whether appended one at a time (`denote`'s `p ++ [a]`) or
written out (`[a, b]`). -/
partial def reifyPTerm (C σ e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if let some p ← reifyFolded? ``Srt.path σ e then return p
  if let some (p, q) := append? e then
    let some segs := listLit? q | throwError "not a path term: {e}"
    return ← segs.foldlM (extend C σ) (← reifyPTerm C σ p)
  let some (a :: segs) := listLit? e | throwError "not a path term: {e}"
  let_expr Seg.field r := a | throwError "not a path term: {e}"
  segs.foldlM (extend C σ) (mkApp2 (mkConst ``PTerm.root) C r)

/-- The path `p` one segment further. -/
partial def extend (C σ : Expr) (p a : Expr) : MetaM Expr := do
  match_expr a with
  | Seg.field f => return mkApp3 (mkConst ``PTerm.field) C p f
  | Seg.at i =>
    let i ← match_expr i with
      | asInt t => reifyTerm C σ t
      | _ => pure (mkApp2 (mkConst ``Term.lit) C (mkApp (mkConst ``PrimVal.int) i))
    return mkApp3 (mkConst ``PTerm.at) C p i
  | _ => throwError "not a segment: {a}"

end

/-! ## Side conditions -/

/-- A proof of a closed decidable fact, by `decide`, if it is true. -/
def decideProof? (prop : Expr) : MetaM (Option Expr) := do
  if prop.hasMVar then return none
  try
    let d ← mkDecide prop
    if (← withAtLeastTransparency .default <| whnf d).isConstOf ``true then
      return some (← mkDecideProof prop)
    return none
  catch _ => return none

/-- The side conditions of a law, on the paths the terms fix: `p ≠ []`,
`diverges p q = true`, anything decidable once they are literal lists. -/
def dischargeTheory : Simp.Discharge := fun e => do
  decideProof? (← instantiateMVars e)

/-! ## The rewrite -/

/-- The term `u : Term C` rewritten by the laws `thms` in the Theory: the term
`u'` and a proof of `Term.Theq u u'`, if a law applies and the result is a
term. -/
def theoryRewrite (thms : SimpTheorems) (C u : Expr) : MetaM (Option (Expr × Expr)) :=
  withLocalDeclD `σ (mkConst ``Semantics.State) fun σ => do
    let denote (t : Expr) : Expr := mkApp4 (mkConst ``Tm.denote) C (mkConst ``Srt.val) σ t
    let lhs := denote u
    let mut unfold : SimpTheorems := {}
    for n in theoryUnfoldLemmas do unfold ← unfold.addConst n
    let (r₁, _) ← simp lhs (← Simp.mkContext (simpTheorems := #[unfold]))
    let (r₂, _) ← simp r₁.expr (← Simp.mkContext (simpTheorems := #[thms]))
      (discharge? := dischargeTheory)
    if r₂.expr == r₁.expr then return none
    let some u' ← (try some <$> reifyTerm C σ r₂.expr catch _ => pure none) | return none
    if u' == u then return none
    let ty ← mkEq lhs (denote u')
    let pf ← mkEqTrans (← r₁.getProof) (← r₂.getProof)
    unless ← isDefEq (← inferType pf) ty do return none
    let h ← mkLambdaFVars #[σ] (← mkExpectedTypeHint pf ty)
    return some (u', mkApp4 (mkConst ``Term.Theq.of_eq) C u u' h)

/-! ## The sequent, computed

A context that the steps before built (`Var.fresh`, `Upd.subst`, `withSt`)
stands in the goal as the call that computes it, which only the `dl{ … }`
printer evaluates.  `normProves` computes it, by the compiled code, and
quotes it back, as `normValid` (`Calculus/Symex.lean`) does for a `⊨` goal,
so that the terms of the sequent are there to be found.  The kernel re-checks
it (`replaceTargetDefEq`). -/

section Quote
variable {C : Contract} (c : Expr)

/-- A context entry as the expression that builds it. -/
def Hyp.quote : Hyp C → Expr
  | .pre a => mkAppN (mkConst ``Hyp.pre) #[c, Fml.quote c a]
  | .upd m U => mkAppN (mkConst ``Hyp.upd) #[c, toExpr m, Upd.quote c U]
  | .havoc => mkAppN (mkConst ``Hyp.havoc) #[c]

/-- A context as the list literal that builds it. -/
def Hyp.quoteList : List (Hyp C) → Expr
  | [] => mkAppN (mkConst ``List.nil [0]) #[mkAppN (mkConst ``Hyp) #[c]]
  | h :: Γ => mkAppN (mkConst ``List.cons [0])
      #[mkAppN (mkConst ``Hyp) #[c], Hyp.quote c h, Hyp.quoteList Γ]

end Quote

/-- The goal `Γ ⟹ φ` of a named contract with `Γ` and `φ` computed; any
other goal as it is. -/
def normProves (g : MVarId) : MetaM MVarId := do
  let ty ← instantiateMVars (← g.getType)
  let_expr Proves C R Γ φ := ty | return g
  let some n := C.constName? | return g
  if Γ.hasFVar || Γ.hasMVar || φ.hasFVar || φ.hasMVar then return g
  let Γ' ← unsafe evalExpr Expr (mkConst ``Expr)
    (mkApp3 (mkConst ``Hyp.quoteList) C (quoteConstName n) Γ)
  let φ' ← unsafe evalExpr Expr (mkConst ``Expr)
    (mkApp3 (mkConst ``Fml.quote) C (quoteConstName n) φ)
  g.replaceTargetDefEq (mkAppN ty.getAppFn #[C, R, Γ', φ'])

/-- The goal `[h₁, …, hₙ] ⟹ φ` as `[] ++ [h₁] ++ … ++ [hₙ] ⟹ φ`, the shape the
steps of a derivation build, so that a rule stated on `Γ ++ [.upd m U]`
(`Proves.merge`, `Proves.applyOnRigidBox`) finds its `Γ` by unification;
any other goal as it is. -/
def snocProves (g : MVarId) : MetaM MVarId := do
  let ty ← instantiateMVars (← g.getType)
  let_expr Proves C R Γ φ := ty | return g
  let some hs := listLit? Γ | return g
  let hyp := mkApp (mkConst ``Hyp) C
  let Γ' ← hs.foldlM (fun acc h => do mkAppM ``HAppend.hAppend #[acc, ← mkListLit hyp [h]])
    (← mkListLit hyp [])
  g.replaceTargetDefEq (mkAppN ty.getAppFn #[C, R, Γ', φ])

/-- The terms of `e` a Theory law may rewrite (`find` and `len` reads),
outermost first, each once. -/
partial def theoryCandidates (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let read := e.isAppOfArity ``Term.find 3 || e.isAppOfArity ``Term.len 3 ||
    (e.isAppOfArity ``Tm.app2 7 &&
      ((e.getArg! 4).isConstOf ``Op2.find || (e.getArg! 4).isConstOf ``Op2.len))
  let acc := if read
      && !e.hasLooseBVars && !e.hasMVar && !acc.contains e
    then acc.push e else acc
  e.getAppArgs.foldl (fun acc a => theoryCandidates a acc) acc

end Solidity
