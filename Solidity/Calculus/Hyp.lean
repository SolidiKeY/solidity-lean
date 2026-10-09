import Solidity.Calculus.NFmlUpdateRules

/-!
# Today's sequents: the context, the rule sets, fresh indices

What `Calculus/NFmlLogic.lean`'s judgement `Γ ⊢ φ` shares with the scoped one
(`Calculus/Proves.lean`) and with the closer's drivers on the erasure
(`Calculus/NFmlDerive.lean`, `Calculus/TheoryRewrite.lean`, `Calculus/Problem.lean`):
the context of a sequent (`Hyp`, put back in front of a formula by
`Hyp.wrap`), the rule sets a derivation may use (`RuleSet`), the fresh index
above every index in sight (`maxIdx`, `Fml.fresh`, `Hyp.fresh`) and the
printer of a context entry (`ppHyp?`).  Moved out of `Logic.lean`
(`docs/intrinsic.md`, W4 item 11), which keeps the rules.
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-! ## Fresh names -/

/-- The largest index of a list of variables. -/
def maxIdx : List Var → Nat
  | [] => 0
  | x :: xs => max x.idx (maxIdx xs)

/-- Every variable's index is at most the largest index in the list.

Example: after Step 2 on `alice.account.balance = 10; uint x = alice.account.balance;`
the formula mentions `sp1`, so `maxIdx` is at least `1`, and the read's
receiver is captured as `sp2`, not as `sp1` again. -/
theorem le_maxIdx {x : Var} : ∀ {xs : List Var}, x ∈ xs → x.idx ≤ maxIdx xs
  | _ :: _, .head _ => Nat.le_max_left _ _
  | _ :: _, .tail _ h => Nat.le_trans (le_maxIdx h) (Nat.le_max_right _ _)

/-- A list whose variables all occur in another has no larger `maxIdx`. -/
theorem maxIdx_le {xs ys : List Var} (h : ∀ x ∈ ys, x ∈ xs) : maxIdx ys ≤ maxIdx xs := by
  induction ys with
  | nil => exact Nat.zero_le _
  | cons y ys ih =>
    simp only [maxIdx]
    exact Nat.max_le.2 ⟨le_maxIdx (h y (.head _)), ih (fun x hx => h x (.tail _ hx))⟩

/-- The largest index of two lists is the larger of theirs: `[x, se1] ++ [sp2]`
has `2`.  With it the fresh index of a line whose postcondition `φ` names no
fresh variable is computed without knowing `φ` (`Chains.lean`). -/
theorem maxIdx_append (xs ys : List Var) : maxIdx (xs ++ ys) = max (maxIdx xs) (maxIdx ys) := by
  induction xs with
  | nil => exact (Nat.zero_max _).symm
  | cons x xs ih => simp only [List.cons_append, maxIdx, ih, Nat.max_assoc]


/-- Fresh names are numbered one above every index in the formula. -/
abbrev NFml.fresh (φ : NFml C) : Nat := maxIdx φ.vars + 1


/-- One entry of the context. -/
inductive Hyp (C : Contract) where
  /-- `a → …` -/
  | pre (a : NFml C)
  /-- `{U} …`, produced under the modality `m` -/
  | upd (m : Modality) (U : Surface.Upd C)
  /-- `{havoc} …`: any storage and ledger a callee may leave, as
  KeY's anonymising update with fresh skolem symbols. -/
  | havoc
  /-- `∀ p x. …`: the local `x` holds any value of the type `p`, as KeY's
  skolem constant for a quantified variable (a `try`'s return values). -/
  | all (x : Var) (p : PrimTy)
  /-- `{anon(xs)} …`: the locals `xs` hold anything, bound or not, as KeY's
  anonymising update of a loop's frame (`#loopAnon`). -/
  | anon (xs : List Var)

/-- Put the context back in front of a formula. -/
def Hyp.wrap : List (Hyp C) → NFml C → NFml C
  | [], φ => φ
  | .pre a :: Γ, φ => dl_schema{ a → ‹Hyp.wrap Γ φ› }
  | .upd m U :: Γ, φ => dl_schema{ {U} ‹Hyp.wrap Γ φ› }
  | .havoc :: Γ, φ => dl_schema{ { havoc } ‹Hyp.wrap Γ φ› }
  | .all x p :: Γ, φ => .all x p (Hyp.wrap Γ φ)
  | .anon xs :: Γ, φ => .anon xs (Hyp.wrap Γ φ)

/-- A Theory rewrite of the context (`NFml.rwEq`): in every precondition; an
update or a `havoc` stays as it is, since its right-hand sides run in the
interpreter. -/
def Hyp.rwEq (q : Term C × Term C) : List (Hyp C) → List (Hyp C)
  | [] => []
  | .pre a :: Γ => .pre (a.rwEq q) :: Hyp.rwEq q Γ
  | .upd m U :: Γ => .upd m U :: Hyp.rwEq q Γ
  | .havoc :: Γ => .havoc :: Hyp.rwEq q Γ
  | .all x p :: Γ => .all x p :: Hyp.rwEq q Γ
  | .anon xs :: Γ => .anon xs :: Hyp.rwEq q Γ

/-- An update rewrite of the context (`Upd.rw`): in the right-hand sides of
every box update.  A precondition, a diamond update or a `havoc` stays as it
is: a rewritten diamond update would also have to return where the old one
does, which `Term.EvalRefines` does not say. -/
def Hyp.rwUpd (q : Term C × Term C) : List (Hyp C) → List (Hyp C)
  | [] => []
  | .pre a :: Γ => .pre a :: Hyp.rwUpd q Γ
  | .upd .box U :: Γ => .upd .box (U.rw q) :: Hyp.rwUpd q Γ
  | .upd .diamond U :: Γ => .upd .diamond U :: Hyp.rwUpd q Γ
  | .havoc :: Γ => .havoc :: Hyp.rwUpd q Γ
  | .all x p :: Γ => .all x p :: Hyp.rwUpd q Γ
  | .anon xs :: Γ => .anon xs :: Hyp.rwUpd q Γ


/-- Fresh names are numbered one above every index in the whole sequent. -/
def Hyp.fresh (Γ : List (Hyp C)) (φ : NFml C) : Nat := (Hyp.wrap Γ φ).fresh

/-- Which rules a derivation may use: solkey's (`Taclet`), or all of them
(`LeanTaclet` too). -/
inductive RuleSet where
  | solkey
  | all
  deriving DecidableEq, Repr

/-! ## Printing a context entry -/

section Print
open Lean Meta PrettyPrinter Delaborator SubExpr
set_option hygiene false

/-- One entry of a sequent's context, as `dl{ … ⟹ … }` writes it; none for
an entry the notation does not read back. -/
def ppHyp? (e : Lean.Expr) : MetaM (Option (TSyntax `dl_hyp)) := do
  match_expr (← whnf (← instantiateMVars e)) with
  | Hyp.pre _ a => return some (← `(dl_hyp| $(← ppFml a):dl_fml))
  | Hyp.upd _ m U =>
    let u ← ppUpd U
    -- an escaped update would read back as a precondition
    if isEscape u then return none
    -- a rule's update, at a fixed modality: `{U} [ ]`, `{U} ⟨ ⟩`
    if (← instantiateMVars U).hasFVar then
      match_expr (← whnf m) with
      | Modality.box => return some (← `(dl_hyp| $u:dl_upd [ ]))
      | Modality.diamond => return some (← `(dl_hyp| $u:dl_upd ⟨ ⟩))
      | _ => pure ()
    return some (← `(dl_hyp| $u:dl_upd))
  | Hyp.havoc _ => return some (← `(dl_hyp| { havoc }))
  | Hyp.anon _ xs =>
    let some xs ← listElems? xs | return none
    let ids ← xs.mapM ppVar?
    if ids.any Option.isNone then return none
    let ids : Array Ident := ids.filterMap id
    return some (← `(dl_hyp| { anon($ids,*) }))
  | Hyp.all _ x p =>
    let some x ← ppVar? x | return none
    let some T ← (do pure ((← primName? p) <|> (← fvarName? p))) | return none
    return some (← `(dl_hyp| ∀ $(mkIdent (Name.mkSimple T)):ident $x:ident))
  | _ => return none

/-- A context: the rest `..Γ` when it is a variable, then its entries, read
off the spine `Γ ++ [h₁] ++ …` the rules write. -/
partial def hypSpine? (e : Lean.Expr) : MetaM (Option (Option Ident × Array Lean.Expr)) := do
  let e ← instantiateMVars e
  if let some n ← fvarName? e then return some (some (nameIdent n), #[])
  if e.isAppOfArity ``HAppend.hAppend 6 then
    let some (Γ, hs) ← hypSpine? (e.getArg! 4) | return none
    let some hs' ← listElems? (e.getArg! 5) | return none
    return some (Γ, hs ++ hs')
  let some hs ← listElems? e | return none
  return some (none, hs)

end Print

/-! ## Reading a sequent

The arrow and the keywords of `sequent[C]{ Γ ⟹ φ }` (moved out of
`Calculus/Sequents.lean`, which reads them;
`Calculus/Sequents.lean` reads them on a scoped goal), the sequent's
formula written (`sequentFml`), and a quoted formula's first layers as
context entries (`peelHyps`). -/

section Sequent
open Lean

/-- The arrow of a sequent: `⟹` for the whole calculus (`⊢`), `⟹ₖ` for
solkey's rules alone (`⊢ₖ`). -/
declare_syntax_cat seq_arrow
syntax " ⟹ " : seq_arrow
syntax " ⟹ₖ " : seq_arrow

/-- `sequent[C]{ Γ ⟹ φ }`: the sequent `Γ ⊢ φ` (with `⟹ₖ`, `Γ ⊢ₖ φ`), read
against the contract `C`. -/
syntax (name := sequentStx) "sequent[" term "]{ " sepBy(dl_hyp, ", ") seq_arrow dl_fml " }" :
  term
/-- `sequent[C, m]{ Γ ⟹ φ }`: `sequent[C]{ … }` at the modality `m`. -/
syntax "sequent[" term ", " term "]{ " sepBy(dl_hyp, ", ") seq_arrow dl_fml " }" : term
/-- `sequent!{ Γ ⟹ φ }`: `sequent[C]{ … }` for the file's `InContract` contract. -/
syntax "sequent!{ " sepBy(dl_hyp, ", ") seq_arrow dl_fml " }" : term
/-- `sequent![m]{ Γ ⟹ φ }`: `sequent[C, m]{ … }` for the file's `InContract` contract. -/
syntax "sequent![" term "]{ " sepBy(dl_hyp, ", ") seq_arrow dl_fml " }" : term

section Expand

/-- The sequent's formula `Hyp.wrap Γ φ`, written: `a → …` for a
precondition, `{U} …` for an update. -/
def sequentFml (hs : Array (TSyntax `dl_hyp)) (φ : TSyntax `dl_fml) : MacroM (TSyntax `dl_fml) :=
  hs.foldrM (init := φ) fun h acc => do
    match h with
    | `(dl_hyp| { havoc }) =>
      Macro.throwErrorAt h "`{ havoc }` is what a callback rule leaves, not an entry to write"
    | `(dl_hyp| $U:dl_upd) => `(dl_fml| $U:dl_upd ($acc))
    | `(dl_hyp| $a:dl_fml) => `(dl_fml| ($a) → ($acc))
    | _ => Macro.throwUnsupported

end Expand

section Elab
open Elab Term Meta

/-- A quoted formula as written with no modality in it (`Surface.Fml`) as
the closer's (`Fml`): the constructors of the same names. -/
partial def toFmlE (e : Expr) : Expr :=
  if e.isAppOfArity ``NFml.toSurface 2 then e.appArg! else
  match e.getAppFn with
  | .const (.str pre c) us =>
    if pre == ``Surface.Fml then mkAppN (.const (.str ``NFml c) us) (e.getAppArgs.map toFmlE) else e
  | _ => e

/-- The first `n` layers of a quoted formula as context entries: `Fml.imp a _`
is `Hyp.pre a`, `Fml.upd m U _` is `Hyp.upd m U`. -/
def peelHyps (C : Expr) : Nat → Expr → MetaM (List Expr × Expr)
  | 0, e => pure ([], e)
  | n + 1, e => do
    if e.isAppOfArity ``NFml.imp 3 || e.isAppOfArity ``Surface.Fml.imp 3 then
      let (hs, φ) ← peelHyps C n (e.getArg! 2)
      return (mkApp2 (mkConst ``Hyp.pre) C (toFmlE (e.getArg! 1)) :: hs, φ)
    if e.isAppOfArity ``NFml.upd 4 || e.isAppOfArity ``Surface.Fml.upd 4 then
      let (hs, φ) ← peelHyps C n (e.getArg! 3)
      return (mkApp3 (mkConst ``Hyp.upd) C (e.getArg! 1) (e.getArg! 2) :: hs, φ)
    throwError "sequent: not a context entry{indentExpr e}"


end Elab

end Sequent

end Solidity
