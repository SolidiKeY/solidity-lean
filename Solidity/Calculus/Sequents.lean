import Solidity.Calculus.Chains
import Solidity.Calculus.Close

/-!
# Reading sequents: `sequent!{ Γ ⟹ φ }`

A goal of a `⊢` derivation (`Calculus/Logic.lean`) prints as the sequent
`dl{ Γ ⟹ φ }`: the context, preconditions and updates in the order the rules
put them there, and the formula still to prove.  This module reads that
sequent back against a contract, so that a walk states its intermediate
goals as checked lines, `show sequent!{ Γ ⟹ φ }`, where it had comments.
KeY writes a problem the same way, `\problem { Γ ==> φ }`: a keyword around
the sequent, the arrow between antecedent and succedent.  The keyword is
needed here because `dl!{ Γ ⟹ φ }` is taken: it is a line of a chain, the
one formula `a₁ → … → φ` (`Notation.lean`), which the chains of
`Examples/Tactics/Payment.lean` are written in.

* `sequent!{ Γ ⟹ φ }` is `Γ ⊢ φ`, `sequent!{ Γ ⟹ₖ φ }` is `Γ ⊢ₖ φ`, for the
  file's `InContract`; `sequent[C]{ … }` names the contract.  An entry of
  `Γ` is a formula (`Hyp.pre`) or an update (`Hyp.upd`), as the printer
  shows them; `{ havoc }` is what a callback rule leaves, and is not read.
* **One scope.**  The sequent is read as its formula `Hyp.wrap Γ φ`, left to
  right, and split back into `Γ` and `φ` by the number of entries: a name no
  program declares is a parameter of the whole sequent, and an update binds
  its aliases (`{ sp1 := alice.account }`) for the entries after it.  So
  `h.sound` states `⊨ dl!{ Γ ⟹ φ }` for `h : sequent!{ Γ ⟹ φ }`.
* **An entry's modality** is the one of the goal it was produced under.
  The sequent is read as `dl![?m]{ … }` would read it (`elabDlAt`), at a
  metavariable `?m`: `φ`'s modality fixes it when `φ` has one at its head,
  and otherwise, after `emptyModality`, `show` fills it from the goal.  So
  `⟨[ ]⟩` in a sequent, and an update with no modality under it, are the
  goal's modality too.  `sequent![m]{ … }` gives it; a Lean formula
  `φ : Post C` stands where a formula does.
* **The context is built by appending** (`[] ++ [h₁] ++ … ++ [hₙ]`), the
  shape the rules leave (`Γ ++ [.pre c, .upd m U]` after `guard`), so a
  rule stated on `Γ ++ [.upd m U]` (`Proves.merge`, `Proves.simplify`,
  `Proves.applyOnRigidBox`) still finds its `Γ` after a `show`
  (`snocProves`, `Calculus/TheoryRewrite.lean`).

`show` checks the line by unfolding the goal: the rules' `Premise.fml`,
`List.append`, `Simple.lower` and the fresh index `Hyp.fresh` of each
capture (`se1` is `Var.fresh "se" (Hyp.fresh Γ φ)` in the goal).  On the
walks of the examples that takes no noticeable time; a long one can compute
its goal first (`normProves`, `Calculus/TheoryRewrite.lean`).

`Fml.Steps.valid_in` is the bridge the other way: a chain proved without
antecedents, then closed under them, as funded diamonds are.
-/

namespace Solidity

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

/-- The first `n` layers of a quoted formula as context entries: `Fml.imp a _`
is `Hyp.pre a`, `Fml.upd m U _` is `Hyp.upd m U`. -/
def peelHyps (C : Expr) : Nat → Expr → MetaM (List Expr × Expr)
  | 0, e => pure ([], e)
  | n + 1, e => do
    if e.isAppOfArity ``Fml.imp 3 then
      let (hs, φ) ← peelHyps C n (e.getArg! 2)
      return (mkApp2 (mkConst ``Hyp.pre) C (e.getArg! 1) :: hs, φ)
    if e.isAppOfArity ``Fml.upd 4 then
      let (hs, φ) ← peelHyps C n (e.getArg! 3)
      return (mkApp3 (mkConst ``Hyp.upd) C (e.getArg! 1) (e.getArg! 2) :: hs, φ)
    throwError "sequent: not a context entry{indentExpr e}"

/-- The modality at the head of a quoted formula, through its updates. -/
partial def headModality? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``Fml.modal 4 then some (e.getArg! 1)
  else if e.isAppOfArity ``Fml.upd 4 then headModality? (e.getArg! 3)
  else none

/-- `sequent[C, m]{ Γ ⟹ φ }`, `m` optional: `Proves R Γ φ`, the context built
by appending.  Without `m` the sequent is read at a metavariable, which `φ`'s
modality fixes when it has one. -/
def elabSequent (c : Lean.Term) (m? : Option Lean.Term) (arrow : TSyntax `seq_arrow)
    (hs : Array (TSyntax `dl_hyp)) (φ : TSyntax `dl_fml) : TermElabM Expr := do
  let R ← match arrow with
    | `(seq_arrow| ⟹ₖ) => pure (Lean.mkConst ``RuleSet.solkey)
    | _ => pure (Lean.mkConst ``RuleSet.all)
  let F ← liftMacroM (sequentFml hs φ)
  let (m, e) ← match m? with
    | some m => pure (none, ← elabDlAt c (some m) F)
    | none => do
      let m ← mkFreshExprMVar (Lean.mkConst ``Modality) (userName := `modality)
      registerMVarErrorCustomInfo m.mvarId! (← getRef) (.ofFormat <|
        "sequent: the modality of the updates in the context is not fixed by the formula " ++
          "after `⟹`: write `sequent![m]{ … }`, or use the sequent where a goal fixes it (`show`)")
      -- read at a local standing for `m`, which is then replaced by it
      let n ← MonadQuotation.addMacroScope `modality
      let e ← withLocalDeclD n (Lean.mkConst ``Modality) fun x => do
        pure ((← elabDlAt c (some (mkIdent n)) F).replaceFVar x m)
      pure (some m, e)
  let C := e.getAppArgs[0]!
  let (entries, φ') ← peelHyps C hs.size e
  if let some m := m then
    if let some m' := headModality? φ' then
      if m'.isConstOf ``Modality.diamond || m'.isConstOf ``Modality.box then
        discard <| isDefEq m m'
  let hyp := mkApp (Lean.mkConst ``Hyp) C
  let Γ ← entries.foldlM (fun acc h => do mkAppM ``HAppend.hAppend #[acc, ← mkListLit hyp [h]])
    (← mkListLit hyp [])
  return mkApp4 (Lean.mkConst ``Proves) C R Γ (← instantiateMVars φ')

elab_rules : term
  | `(sequent[ $c ]{ $[$hs:dl_hyp],* $a:seq_arrow $φ:dl_fml }) => elabSequent c none a hs φ
  | `(sequent[ $c, $m ]{ $[$hs:dl_hyp],* $a:seq_arrow $φ:dl_fml }) => elabSequent c (some m) a hs φ

macro_rules
  | `(sequent!{ $[$hs:dl_hyp],* $a:seq_arrow $φ:dl_fml }) =>
    `(sequent[InContract.contract]{ $[$hs],* $a $φ })
  | `(sequent![ $m ]{ $[$hs:dl_hyp],* $a:seq_arrow $φ:dl_fml }) =>
    `(sequent[InContract.contract, $m]{ $[$hs],* $a $φ })

end Elab

/-! ## A chain under a context -/

variable {C : Contract} in
/-- A chain `φ ~*> ψ` proves `φ` in any context `Γ` in which `ψ` holds:
a diamond is its chain, closed under the context's assumptions. -/
theorem Fml.Steps.valid_in {φ ψ : Fml C} (c : φ ~*> ψ) (Γ : List (Hyp C))
    (h : ⊨ Hyp.wrap Γ ψ) : ⊨ Hyp.wrap Γ φ :=
  fun σ => Hyp.wrap_mono c.sound Γ σ (h σ)

/-! ## Examples -/

section Examples
open Proves

local instance instInContractSequents : InContract := ⟨StandardExample⟩

/-- A sequent is its formula, split back. -/
example (h : sequent!{ 5 <= selfBalance ⟹ ⟨ to.transfer(5); ⟩ true }) :
    ⊨ dl!{ 5 <= selfBalance ⟹ ⟨ to.transfer(5); ⟩ true } := h.sound
example (h : sequent!{ { x := 1 } ⟹ [ ] x == 1 }) : ⊨ dl!{ { x := 1 } [ ] x == 1 } := h.sound
example : sequent!{ ⟹ [ revert(); ] true } = (⊢ dl!{ [ revert(); ] true }) := rfl
example : sequent!{ ⟹ₖ [ revert(); ] true } = (⊢ₖ dl!{ [ revert(); ] true }) := rfl

/-- An update binds its alias for the entries after it. -/
example : Prop := sequent![.box]{ { sp1 := alice.account }, sp1.balance == 1 ⟹ true }

-- Outside `show`, a context modality nothing fixes is an error.
/--
error: sequent: the modality of the updates in the context is not fixed by the formula after `⟹`: write `sequent![m]{ … }`, or use the sequent where a goal fixes it (`show`)
-/
#guard_msgs in example : Prop := sequent!{ { x := 1 } ⟹ true }

-- … and prints as the goal it is.
/-- info: dl{ 5 <= selfBalance ⟹ ⟨ to .transfer(5); ⟩ true } : Prop -/
#guard_msgs in #check sequent!{ 5 <= selfBalance ⟹ ⟨ to.transfer(5); ⟩ true }

/-- An entry's modality is `φ`'s, else left to the goal. -/
example : sequent!{ { x := 1 } ⟹ [ ] true } =
    Proves .all ([] ++ [.upd .box [.val (.user "x") (.lit (.int 1))]]) dl!{ [ ] true } := rfl
example : sequent![.box]{ { x := 1 } ⟹ true } =
    Proves .all ([] ++ [.upd .box [.val (.user "x") (.lit (.int 1))]]) dl!{ true } := rfl
example (m : Modality) (φ : Fml StandardExample) : sequent![m]{ { x := 1 } ⟹ ⟨[ ]⟩ φ } =
    Proves .all ([] ++ [.upd m [.val (.user "x") (.lit (.int 1))]]) (.modal m [] φ) := rfl

/-- A walk, every goal a checked line. -/
example : ⊢ dl!{ [ x = 1; ] x == 1 } := by
  apply update .localValueAssign
  fail_if_success show sequent!{ { x := 2 } ⟹ [ ] x == 1 }
  show sequent!{ { x := 1 } ⟹ [ ] x == 1 }
  apply empty
  show sequent!{ { x := 1 } ⟹ x == 1 }
  refine close ?_
  sol_close

/-- After a `show` the context is still appended to: `merge` finds its two updates. -/
example : ⊢ dl!{ [ x = 1; y = x; ] y == 1 } := by
  apply update .localValueAssign
  apply update .localValueAssign
  apply empty
  show sequent!{ { x := 1 }, { y := x } ⟹ y == 1 }
  apply merge rfl
  show sequent!{ { x := 1 ‖ y := 1 } ⟹ y == 1 }
  refine close ?_
  sol_close

/-- A capture's fresh index is computed by `show`. -/
example : ⊢ dl!{ [ to.transfer(x + 2); ] true } := by
  apply unfold .transfer_unfold_rightSndArgument
  show sequent!{ ⟹ [ uint se1 = x + 2; to.transfer(se1); ] true }
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  show sequent!{ { se1 := x + 2 } ⟹ [ to.transfer(se1); ] true }
  apply guard .transferNoCallback
  · show sequent!{ { se1 := x + 2 }, 0 <= se1,
      { net := store(net, at(to), net(to) - se1) ‖ net := store(net, at(this), net(this) + se1) }
        ⟹ [ ] true }
    apply empty
    refine close ?_
    sol_close
  · show sequent!{ { se1 := x + 2 }, ¬(0 <= se1) ⟹ [ revert(); ] true }
    apply done .revertBox
    refine close ?_
    sol_close

end Examples

end Solidity
