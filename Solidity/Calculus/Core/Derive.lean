import Solidity.Calculus.Core.Symex
import Solidity.Calculus.Core.Close
import Solidity.Calculus.Core.Completeness
import Solidity.Calculus.Core.ProofTree

/-!
# The scoped strategy as one kernel evaluation: `sol_prove`

`Derive.lean`'s `sol_prove` on a goal `Core.Valid φ`: the scoped strategy
runs to its end (`Core.symex`), what it leaves is erased (`Fml.erase`) and
handed to today's closer (`Derive.proves`, `Calculus/Closer.lean`), the
erasure being enough where `Fml.posB` takes the leaf (`Valid.of_erase`).
The kernel checks it as one evaluation, `Derive.proves φ = true`
(`Valid.of_proves`): the strategy, the check and the closer, with no term
quoted back.

Where the closer leaves goals, `sol_prove` computes today's residue of the
erasure (`Derive.residue`), checked with the strategy and the leaf's
`Fml.posB` as one more kernel evaluation (`Derive.residueOf`), and leaves one
goal per leaf, `leaf1`, `leaf2`,
… , each a sequent of today's calculus, closed by today's tactics
(`Valid.of_residue`).

There is no search, so `sol_prove` is its own replay; the fuel of the
strategy (`fuel`) and the closer's budget (`Derive.budget`) bound the
compiled run before the kernel sees it.
-/

namespace Solidity.Core

open Solidity (Modality)

variable {C : Contract}

namespace Derive

/-- The steps `sol_prove` gives the scoped strategy. -/
def fuel : Nat := 5000

/-- A leaf left by the strategy is closed: taken by `Fml.posB`, its erasure
proved by today's closer. -/
def closes (ψ : Fml C []) : Bool :=
  (ψ.posB []).isSome && Solidity.Derive.proves [] (ψ.erase [])

/-- **`sol_prove`'s check**: the strategy run to its end, and what it leaves
closed. -/
def proves (φ : Fml C []) : Bool := closes (symex fuel φ)

/-- Today's residue of the erasure of a leaf `Fml.posB` takes. -/
def residueAt (ψ : Fml C []) : Option (List (Solidity.Derive.Leaf C) × Nat) :=
  if (ψ.posB []).isSome then
    Solidity.Derive.residue Solidity.Derive.budget Solidity.Derive.synClose
      Solidity.Derive.budget [] (ψ.erase [])
  else none

/-- **`sol_prove`'s check when leaves are left**: the strategy run once, its
leaf checked and its erasure's residue computed, in one kernel evaluation. -/
def residueOf (φ : Fml C []) : Option (List (Solidity.Derive.Leaf C) × Nat) :=
  residueAt (symex fuel φ)

end Derive

/-- What `Derive.closes` accepts is valid. -/
theorem Valid.of_closes {ψ : Fml C []} (h : Derive.closes ψ = true) : Valid ψ := by
  simp only [Derive.closes, Bool.and_eq_true] at h
  exact Valid.of_erase h.1 (Solidity.Proves.valid (Solidity.Proves.of_proves h.2))

/-- **`sol_prove`'s proof when nothing is left.** -/
theorem Valid.of_proves (hS : Stmt.Sound C) {φ : Fml C []} (h : Derive.proves φ = true) :
    Valid φ :=
  symex_valid hS Derive.fuel (Valid.of_closes h)

/-- **`sol_prove`'s proof when leaves are left**: today's residue of the
erasure, each leaf proved. -/
theorem Valid.of_residue (hS : Stmt.Sound C) {φ : Fml C []}
    {ls : List (Solidity.Derive.Leaf C)} {b' : Nat} (h : Derive.residueOf φ = some (ls, b'))
    (hl : ∀ l ∈ ls, Solidity.Proves .all l.1 l.2) : Valid φ := by
  unfold Derive.residueOf Derive.residueAt at h
  split at h
  · exact symex_valid hS Derive.fuel
      (Valid.of_erase ‹_› (Solidity.Proves.valid (Solidity.Proves.of_synResidue h hl)))
  · cases h

/-! ## The tactic -/

namespace Derive

open Lean Elab Tactic Meta

/-- The residue of the erasure of what the strategy leaves of `φ`, quoted
(`Derive.residueQuote`), when the leaf is taken by `Fml.posB`. -/
def residueQuoteC (c : Lean.Expr) (φ : Fml C []) :
    Option (List (Lean.Expr × Lean.Expr) × Nat) :=
  let ψ := symex fuel φ
  if (ψ.posB []).isSome then Solidity.Derive.residueQuote c [] (ψ.erase []) else none

/-- `sol_prove` on the scoped goal `g`, `Core.Valid φ`: the goals it leaves,
one per leaf of today's residue. -/
def prove (g : MVarId) (C φ : Expr) : MetaM (List MVarId) := do
  let some n := C.constName? | throwError "sol_prove: the contract is not a named constant"
  if φ.hasFVar || φ.hasMVar then
    throwError "sol_prove: the formula mentions a local hypothesis or a metavariable"
  let sound := mkApp (mkConst Symex.soundName) C
  let φe ← Symex.evaluable φ
  let bool := mkConst ``Bool
  -- the kernel first: compiling the check of a formula with no code of its
  -- own costs about as much as the kernel's evaluation
  let type := mkApp3 (mkConst ``Eq [1]) bool (mkApp2 (mkConst ``proves) C φ) (mkConst ``Bool.true)
  if let some h ← (some <$> Solidity.Derive.kernelLemma type
      (mkApp2 (mkConst ``Eq.refl [1]) bool (mkConst ``Bool.true))) <|> pure none then
    g.assign (mkApp4 (mkConst ``Valid.of_proves) C sound φ h)
    return []
  let resTy := mkApp (mkConst ``Option [0]) (mkApp2 (mkConst ``Prod [0, 0])
    (mkApp (mkConst ``List [0])
      (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Expr) (mkConst ``Expr)))
    (mkConst ``Nat))
  let some (leaves, left) ← unsafe evalExpr (Option (List (Expr × Expr) × Nat)) resTy
      (mkAppN (mkConst ``residueQuoteC) #[C, quoteConstName n, φe])
    | throwError "sol_prove: the strategy leaves a formula the erasure does not close \
        (`Fml.posB`), or today's closer takes more than {Solidity.Derive.budget} steps"
  let hyp := mkApp (mkConst ``Solidity.Hyp) C
  let leafTy := mkApp2 (mkConst ``Prod [0, 0]) (mkApp (mkConst ``List [0]) hyp)
    (mkApp (mkConst ``Solidity.Fml) C)
  let mkLeaf (Γ' φ' : Expr) : Expr :=
    mkAppN (mkConst ``Prod.mk [0, 0]) #[mkApp (mkConst ``List [0]) hyp,
      mkApp (mkConst ``Solidity.Fml) C, Γ', φ']
  let ls ← mkListLit leafTy (leaves.map fun (Γ', φ') => mkLeaf Γ' φ')
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) (mkApp (mkConst ``List [0]) leafTy) (mkConst ``Nat)
  let someLs := mkApp2 (mkConst ``Option.some [0]) pairTy
    (mkAppN (mkConst ``Prod.mk [0, 0]) #[mkApp (mkConst ``List [0]) leafTy, mkConst ``Nat, ls,
      mkRawNatLit left])
  -- one lemma: the strategy, the check of its leaf and the residue, so the
  -- kernel runs the strategy once more, not twice
  let type := mkApp3 (mkConst ``Eq [1]) (mkApp (mkConst ``Option [0]) pairTy)
    (mkApp2 (mkConst ``residueOf) C φ) someLs
  let rfl' := mkApp2 (mkConst ``Eq.refl [1]) (mkApp (mkConst ``Option [0]) pairTy) someLs
  let h ← try Solidity.Derive.kernelLemma type rfl'
    catch e => throwError "sol_prove: the kernel rejects the residue:{indentD e.toMessageData}"
  let mut goals : Array MVarId := #[]
  let mut proofs : Array Expr := #[]
  for (Γ', φ') in leaves, i in [1:leaves.length + 1] do
    let gi ← mkFreshExprSyntheticOpaqueMVar
      (mkAppN (mkConst ``Solidity.Proves) #[C, mkConst ``RuleSet.all, Γ', φ'])
      (Name.mkSimple s!"leaf{i}")
    goals := goals.push gi.mvarId!
    proofs := proofs.push gi
  let mut hl := mkApp (mkConst ``Solidity.Derive.leaves_nil) C
  let mut rest := mkApp (mkConst ``List.nil [0]) leafTy
  for (Γ', φ') in leaves.reverse, p in proofs.reverse do
    hl := mkAppN (mkConst ``Solidity.Derive.leaves_cons) #[C, Γ', φ', rest, p, hl]
    rest := mkAppN (mkConst ``List.cons [0]) #[leafTy, mkLeaf Γ' φ', rest]
  g.assign (mkAppN (mkConst ``Valid.of_residue) #[C, sound, φ, ls, mkRawNatLit left, h, hl])
  return goals.toList

end Derive

open Lean Elab Tactic Meta in
/-- `sol_prove` on a scoped goal `Core.Valid φ`: the scoped strategy, its
leaves erased and closed by today's closer, as one kernel evaluation
(`Valid.of_proves`); one goal `leafᵢ` per leaf the closer leaves. -/
@[tactic Solidity.tacticSol_prove]
def evalSolProveCore : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let some (C, φ) ← Symex.validGoal? g | throwUnsupportedSyntax
  let rest := (← getUnsolvedGoals).erase g
  Symex.reporting g do
    let leaves ← Derive.prove g C φ
    setGoals (leaves ++ rest)

/-! ## `sol_close` on a scoped leaf -/

/-- A formula valid with `x` free is valid under `∀ p x`: the erasure of a
scoped leaf binds the parameters by `∀` (`cdl!`), today's leaf has them free. -/
theorem _root_.Solidity.Valid.all_of_free {φ : Solidity.Fml C} (x : Var) (p : PrimTy)
    (h : Solidity.Valid φ) : Solidity.Valid (.all x p φ) :=
  fun _ _ _ => h _

/-- Today's formula without its leading quantifiers: a scoped leaf's
erasure with its parameters free, as today's leaves have them. -/
def _root_.Solidity.Fml.stripAlls : Solidity.Fml C → Solidity.Fml C
  | .all _ _ φ => φ.stripAlls
  | φ => φ

/-- A formula is valid where it is with its leading quantifiers' locals free. -/
theorem _root_.Solidity.Valid.of_stripAlls : {φ : Solidity.Fml C} →
    Solidity.Valid φ.stripAlls → Solidity.Valid φ
  | .all x p φ, h => Solidity.Valid.all_of_free x p (Solidity.Valid.of_stripAlls (φ := φ) h)
  | .tt, h | .eq _ _, h | .not _, h | .and _ _, h | .imp _ _, h
  | .modal _ _ _, h | .upd _ _ _, h | .havoc _, h | .anon _ _, h | .defined _, h => h

namespace Derive

open Lean Elab Tactic Meta

/-- Today's goal `Valid (∀ p x. … φ)` as `Valid φ`, its leading quantifiers'
locals free, as today's leaves have them (`Valid.all_of_free`). -/
partial def stripAlls (g : MVarId) : MetaM MVarId := do
  let ty ← instantiateMVars (← g.getType)
  let_expr Solidity.Valid C φ := ty | return g
  let_expr Solidity.Fml.all _ x p φ' := φ | return g
  let g' ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Solidity.Valid) C φ') (← g.getTag)
  g.assign (mkAppN (mkConst ``Solidity.Valid.all_of_free) #[C, φ', x, p, g'])
  stripAlls g'.mvarId!

/-- A scoped leaf `Core.Valid ψ` with no modality left, as today's goal: the
leaf taken by `Fml.posB` (checked by the kernel), its erasure computed
(`Solidity.normValid`), the goal `Solidity.Valid` of it (`Valid.of_erase`),
the parameters' quantifiers stripped (`stripAlls`).  `tac` names the tactic
in the error. -/
def eraseLeaf (tac : String) (g : MVarId) (C ψ : Expr) : TacticM MVarId := do
  let bool := mkConst ``Bool
  let nilCtx := mkApp (mkConst ``List.nil [0]) (mkConst ``LTy)
  let nilVar := mkApp (mkConst ``List.nil [0]) (mkConst ``Var)
  let hpTy := mkApp3 (mkConst ``Eq [1]) bool
    (mkApp2 (mkConst ``Option.isSome [0]) (mkApp (mkConst ``List [0]) (mkConst ``Var))
      (mkAppN (mkConst ``Fml.posB) #[C, nilCtx, ψ, nilVar])) (mkConst ``Bool.true)
  let hp ← try Solidity.Derive.kernelLemma hpTy (mkApp2 (mkConst ``Eq.refl [1]) bool (mkConst ``Bool.true))
    catch _ => throwError "{tac}: the leaf is not one its erasure closes (`Fml.posB`): a \
      hidden binder under a negation, a precondition or a modality, or named twice, or what \
      is negated or assumed is not first-order (an update, a modality or a `havoc` there)"
  let erased := mkAppN (mkConst ``Fml.erase) #[C, nilCtx, nilVar, ψ]
  let g' ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Solidity.Valid) C erased) (← g.getTag)
  g.assign (mkAppN (mkConst ``Valid.of_erase) #[C, ψ, hp, g'])
  stripAlls (← Solidity.normValid g'.mvarId!)

/-- Run today's closer `stx` on a scoped leaf: the leaf erased
(`eraseLeaf`), then `stx` itself on today's goal, where today's tactic
takes it.  Throws `unsupportedSyntax` on a goal that is not scoped, so
today's tactic runs there. -/
def onErased (tac : String) (stx : Syntax) : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let some (C, ψ) ← Symex.validGoal? g | throwUnsupportedSyntax
  Symex.reporting g do
    replaceMainGoal [← eraseLeaf tac g C ψ]
    evalTactic stx

end Derive

open Lean Elab Tactic Meta in
/-- `sol_close_unwrap` on a scoped goal `Core.Valid ψ` with no modality left
(after `sol_symex`): the leaf erased (`Derive.eraseLeaf`), then today's.
It is the first step of today's `sol_close`, `sol_close_mt` and
`sol_spec_close`, so each of them runs on a scoped leaf as on today's, its
erasure. -/
@[tactic Solidity.tacticSol_close_unwrap]
def evalSolCloseUnwrapCore : Tactic := fun stx => Derive.onErased "sol_close" stx stx

/-! ## `sol_derive`: the strategy as a walk

On a scoped sequent `H ⊢ φ` (`Core.Proves`), one `refine` per step: a
precondition, a quantifier, an update or a hidden binder into the context,
an empty modality through its frames (the first, the second and this by
solkey's names, `impRight`, `allRight`, `emptyModality`,
`Calculus/Core/ProofTree.lean`), `closeTrue`, or the rule the
statement fires, named as solkey names it (`ruleOf?`,
`Calculus/Core/Completeness.lean`) and cited by its taclet
(`Taclet.step_eq .rule`, `LeanTaclet.toStep .rule`).  A goal with no
modality is a leaf: `sol_derive` leaves it, `sol_derive?` closes it as
today's suggestion does where it can (`Proves.close`, then today's
`sol_symex; sol_close` on the erasure, as the tree's leaves close).

Under `open scoped Solidity.Core.Surface` (`Walk.surfaceOn`) `sol_derive?`
writes today's short walk instead, which the scope's macros read
(`Calculus/Core/WalkSyntax.lean`): `apply Proves.valid`, solkey's aliases
(`apply impRight`, `apply allRight`, `apply emptyModality`), one `apply
update .r` (`unfold`, `splitBox`, `split`, `done`, `Proves.check`, `cases`,
`branches`, `invBox`, the `…Lean` forms) per rule, `refine close ?_` at a
leaf (`true` too, as today's), and nothing for the steps KeY does not show
(`core_silent`: a scope's end, a hidden binder, the parameters' `∀`).  The
walk runs those very lines, so the suggestion is what was checked; where a
short line fails, the explicit `refine` stands in. -/

namespace Walk

open Lean Elab Tactic Meta

/-- The `Proves` constructor of a premise's kind. -/
def provesCtor? (p : Expr) : Option Lean.Name :=
  match p.getAppFn.constName? with
  | some ``Premise.update => some ``Proves.update
  | some ``Premise.unfold => some ``Proves.unfold
  | some ``Premise.bind => some ``Proves.bind
  | some ``Premise.split => some ``Proves.split
  | some ``Premise.check => some ``Proves.check
  | some ``Premise.done => some ``Proves.done
  | some ``Premise.branches => some ``Proves.branches
  | some ``Premise.cases => some ``Proves.cases
  | some ``Premise.inv => some ``Proves.inv
  | some ``Premise.inline => some ``Proves.inline
  | _ => none

/-- The explicit arguments of the constructor `c` after the rule `d`. -/
def ctorArgs (c : Lean.Name) : MetaM (Array Lean.Name) := do
  let some info := (← getEnv).find? c | throwError "unknown constant {c}"
  forallTelescope info.type fun xs _ => do
    let mut out : Array Lean.Name := #[]
    let mut seen := false
    for x in xs do
      let ld ← x.fvarId!.getDecl
      unless ld.binderInfo.isExplicit do continue
      if !seen then seen := true; continue
      out := out.push ld.userName
    return out

/-- The rule `d` by the constructor `c`, two ways: `apply c d`, its goals
tagged by the constructor's arguments (`thn`, `els`), with `rfl` for a
non-emptiness check (`hne`); and `refine c d ?_ … ?_`, where a side
condition of the rule needs the goal to be elaborated.  A rule of labelled
goals (`cases`, `branches`) is the `apply` with its goals taken apart. -/
def ctorTacs (c : Lean.Name) (d : Lean.Term) : MetaM (Array (Array (TSyntax `tactic))) := do
  let names ← ctorArgs c
  let f ← ProofTree.short c
  let rflId := mkIdent `rfl
  let pre := names.toList.takeWhile (· == `hne) |>.length
  let rfls : Array Lean.Term := (List.replicate pre (⟨rflId⟩ : Lean.Term)).toArray
  let args ← names.mapM fun n => do
    if n == `hne then `(term| $rflId:ident) else `(term| ?_)
  let app ← `(tactic| apply $f $d $rfls*)
  -- a rule of labelled goals (`∀ f ∈ fs, …`): taken apart on its `apply`
  -- line, one goal per outcome, as today's walk writes it
  if c == ``Proves.cases || c == ``Proves.branches then
    let names := #[``List.forall_mem_cons, ``List.not_mem_nil, ``false_implies, ``implies_true,
      ``and_true]
    let lemmas ← names.mapM fun n => do
      `(Lean.Parser.Tactic.simpLemma| $(← ProofTree.short n):ident)
    return #[#[← `(tactic| $app <;> (try simp only [$lemmas,*]) <;> (try and_intros))],
      #[← `(tactic| refine $f $d $args*)]]
  return #[#[app], #[← `(tactic| refine $f $d $args*)]]

/-- Whether today's walk text reads here: `open scoped Solidity.Core.Surface`
is in effect (its `core_surface%` reads `true`, `Core.surfaceOn`, read
without importing the switch) and the walk's macros are loaded
(`Calculus/Core/WalkSyntax.lean`). -/
def surfaceOn : MetaM Bool := do
  unless (← getEnv).contains `Solidity.Core.evalCoreSilent do return false
  let stx := mkNode `Solidity.Core.coreSurfaceFlag #[mkAtom "core_surface%"]
  let some out ← (liftMacroM (expandMacro? stx) : TermElabM _).run' | return false
  return out.isIdent && out.getId.eraseMacroScopes == `true

/-- Today's walk line for the scoped rule `c` firing the taclet `.r`
(`lean`: a Lean taclet; `box`: under the box), as the scope's macros read
it (`Calculus/Core/WalkSyntax.lean`). -/
def shortTac (c : Lean.Name) (r : Lean.Name) (lean box : Bool) :
    MetaM (Option (TSyntax `tactic)) := do
  let rule := ProofTree.dotIdent r
  let kind? : Option Lean.Name :=
    if c == ``Proves.update then some `update
    else if c == ``Proves.unfold || c == ``Proves.bind || c == ``Proves.inline then
      some (if lean then `unfoldLean else `unfold)
    else if c == ``Proves.split then some (if box then `splitBox else `split)
    else if c == ``Proves.check then some (if lean then `checkLean else `Proves.check)
    else if c == ``Proves.done then some (if lean then `doneLean else `done)
    else if c == ``Proves.cases then some `cases
    else if c == ``Proves.branches then some `branches
    else if c == ``Proves.inv then some (if box then `invBox else `invLean)
    else none
  let some kind := kind? | return none
  let app ← `(tactic| apply $(mkIdent kind) $rule)
  -- a rule of labelled goals (`∀ f ∈ fs, …`): taken apart on its `apply`
  -- line, one goal per outcome, as today's walk writes it
  if c == ``Proves.cases || c == ``Proves.branches then
    let names := #[``List.forall_mem_cons, ``List.not_mem_nil, ``false_implies, ``implies_true,
      ``and_true]
    let lemmas ← names.mapM fun n => do
      `(Lean.Parser.Tactic.simpLemma| $(← ProofTree.short n):ident)
    return some (← `(tactic| $app <;> (try simp only [$lemmas,*]) <;> (try and_intros)))
  return some app

/-- The steps that may apply at the goal `g`, each as tactics, in the order
tried; none at a leaf.  `short`: today's walk line first (`shortTac`), the
explicit `refine` after it; `true` is then a leaf, closed as today's.  A
step's note, where it has one, is the solkey name of a rule its lines do not
write (`-- storageFieldReadFind` after a premise proved by `rfl`). -/
def movesAt (g : MVarId) (short : Bool := false) :
    MetaM (Array (Array (TSyntax `tactic) × Option String)) := g.withContext do
  let plain (ms : Array (Array (TSyntax `tactic))) := ms.map (·, (none : Option String))
  let ty ← instantiateMVars (← g.getType)
  let_expr Proves C _ Γ₀ Γ H φ0 := ty | return #[]
  let φ ← whnf φ0
  let one (c : Lean.Name) : MetaM (Array (Array (TSyntax `tactic))) := do
    return #[#[← `(tactic| refine $(← ProofTree.short c) ?_)]]
  let alias (n : Lean.Name) (c : Lean.Name) : MetaM (Array (Array (TSyntax `tactic))) := do
    if short then return #[#[← `(tactic| apply $(mkIdent n))]] ++ (← one c)
    one c
  match φ.getAppFn.constName? with
  | some ``Fml.imp => plain <$> alias `impRight ``Proves.impRight
  | some ``Fml.all => plain <$> alias `allRight ``Proves.allRight
  | some ``Fml.upd => plain <$> alias `updIntro ``Proves.updIntro
  | some ``Fml.bind => plain <$> one ``Proves.bindIntro
  | some ``Fml.tt =>
    if short then return #[]
    return plain
      #[#[← `(tactic| exact $(← ProofTree.short ``Proves.closeTrue) $(mkIdent `rfl):ident)]]
  | some ``Fml.modal =>
    let args := φ.getAppArgs
    let m := args[args.size - 4]!
    let P ← whnf args[args.size - 3]!
    if P.isAppOf ``Prog.nil then return plain (← alias `emptyModality ``Proves.emptyModality)
    unless P.isAppOf ``Prog.cons do return #[]
    let s := P.getArg! (P.getAppNumArgs - 2)
    let k := mkAppN (mkConst ``Hyps.fresh) #[C, Γ₀, Γ, H, φ]
    let some (r, p) ← ruleOf? k m s | return #[]
    let some c := provesCtor? (← whnf p) | return #[]
    let rName := Lean.Name.mkSimple r.getString!
    let rule := mkIdent rName
    let lean := r.getPrefix != ``Taclet
    let d ← if !lean then
        `(term| ($(← ProofTree.short ``Taclet.step_eq) .$rule:ident))
      else `(term| ($(← ProofTree.short ``LeanTaclet.toStep) .$rule:ident))
    -- a rule whose line `apply` cannot match (a read into a hole, whose
    -- `fill` does not reduce while unifying): the taclet elaborated after
    -- the goal (`by exact`), as `core_rule` does, so the line keeps its name
    let late ← ctorTacs c (← `(term| (by exact $d)))
    -- and where the taclet's side conditions are decided before its schema
    -- variables are read off the goal (a read into a hole after a hidden
    -- binder), the premise `Stmt.step` computes, by `rfl`; the line names
    -- no rule, so the rule's solkey name follows it as a comment
    let byStep ← ctorTacs c (← `(term| $(mkIdent `rfl):ident))
    let explicit := plain ((← ctorTacs c d) ++ late.extract (late.size - 1) late.size) ++
      (byStep.extract (byStep.size - 1) byStep.size).map (·, some rName.toString)
    if short then
      let box := (← whnf m).isConstOf ``Modality.box
      if let some t ← shortTac c rName lean box then return plain #[#[t]] ++ explicit
    return explicit
  | _ => return #[]

/-- A leaf closed as a walk ends, at the empty outer scope: its lines, or
none where the closer does not close it (the state rolled back). -/
def closeLeaf (g : MVarId) (short : Bool := false) : TacticM (Option (Array String)) := do
  let ty ← instantiateMVars (← g.getType)
  let_expr Proves _ _ Γ₀ _ _ _ := ty | return none
  unless (← whnfR Γ₀).isAppOf ``List.nil do return none
  let first ← if short then `(tactic| refine $(mkIdent `close) ?_)
    else `(tactic| refine $(← ProofTree.short ``Proves.close) [] $(mkIdent `rfl)
      $(← ProofTree.short ``List.nodup_nil) ?_)
  let tacs := #[first, ← `(tactic| sol_symex), ← `(tactic| sol_close)]
  let s ← saveState
  let ok ← tryCatchRuntimeEx
    (withCurrHeartbeats do return (← ProofTree.runOn g tacs).isEmpty) fun _ => pure false
  unless ok do s.restore; return none
  return some (← tacs.mapM fun t => (ProofTree.tacLines t : MetaM _)).flatten

/-- The walk from `g`: its script, lines indented relative to the first, a
`case` per goal of a step with several, `sorry` for a leaf; the leaves are
collected in `open`. -/
partial def walk (fuel : IO.Ref Nat) (leaves : IO.Ref (Array MVarId)) (g : MVarId)
    (close : Bool := false) (short : Bool := false) : TacticM (Array String) := do
  let n ← fuel.get
  if n == 0 then throwError "sol_derive: more than {Derive.fuel} steps"
  fuel.set (n - 1)
  -- today's text: the steps KeY does not show are taken unwritten, as each
  -- of the scope's lines takes them first (`core_silent`)
  let g ← if short then
      match ← ProofTree.runOn g #[⟨mkNode `Solidity.Core.coreSilent #[mkAtom "core_silent"]⟩] with
      | [g'] => pure g'
      | _ => pure g
    else pure g
  let mut step := none
  for (tacs, note) in ← movesAt g short do
    let s ← saveState
    -- each try with its own heartbeats, a timeout a failed try
    let r ← tryCatchRuntimeEx (some <$> withCurrHeartbeats (ProofTree.runOn g tacs))
      fun _ => do s.restore; pure none
    if let some gs := r then
      step := some (tacs, note, gs)
      break
  let some (tacs, note, gs) := step
    | if close then
        if let some lines ← closeLeaf g short then return lines
      leaves.modify (·.push g); return #["sorry"]
  let head := (← tacs.mapM fun t => (ProofTree.tacLines t : MetaM _)).flatten
  let head := match note with
    | some n => head.modify (head.size - 1) (· ++ s!" -- {n}")
    | none => head
  match gs with
  | [g'] => return head ++ (← walk fuel leaves g' close short)
  | gs =>
    -- a goal's name is its tag's first part past the step's goal's (`els`
    -- under `thn`, past a silent step's `els.h`); `and_intros`' goals
    -- (`refine_1`, …) have none to cite
    let parent := (← g.getTag).components
    let tags ← gs.mapM fun g' => do
      let cs := (← g'.getTag).components
      let cs := if parent.isPrefixOf cs then cs.drop parent.length else cs
      match cs.head? with
      | some (.str _ l) => return if l.startsWith "refine_" then none else some l
      | _ => return none
    -- cited by name when every goal of the step has one (`thn`, `els`); else
    -- bullets, in order, as today's walk takes a rule's goals apart (`cases`'
    -- formula goal is `fml`, its updates' goals have no name)
    let cite := tags.all Option.isSome
    let mut out := head
    for g' in gs, tag in tags do
      let body ← walk fuel leaves g' close short
      match cite, tag with
      | true, some l =>
        out := out.push s!"case {l} =>"
        out := out ++ body.map ("  " ++ ·)
      | _, _ => out := out ++ body.mapIdx fun i l => (if i == 0 then "· " else "  ") ++ l
    return out

/-- The walk from the goal `g` (`Core.Valid φ` starts with `Proves.valid`):
its lines, and the leaves it leaves. -/
def run (g : MVarId) (close : Bool := false) (short : Bool := false) :
    TacticM (Array String × List MVarId) := do
  let (pre, g) ← match ← Symex.validGoal? g with
    | some _ =>
      let t ← if short then `(tactic| apply $(mkIdent `Proves.valid))
        else `(tactic| refine $(← ProofTree.short ``Proves.valid)
          ($(mkIdent `R) := $(← ProofTree.short ``RuleSet.all)) ?_)
      let [g'] ← ProofTree.runOn g #[t] | throwError "sol_derive: `refine Proves.valid ?_` failed"
      pure ((← ProofTree.tacLines t), g')
    | none => pure (#[], g)
  let fuel ← IO.mkRef Derive.fuel
  let leaves ← IO.mkRef #[]
  let lines ← walk fuel leaves g close short
  return (pre ++ lines, (← leaves.get).toList)

/-- A scoped goal: `Core.Valid φ` or `H ⊢ φ` over `Core.Proves`. -/
def isCoreGoal (g : MVarId) : MetaM Bool := do
  let ty ← instantiateMVars (← g.getType)
  return ty.isAppOf ``Core.Valid || ty.isAppOf ``Core.Proves

end Walk

/-- `sol_derive` on a scoped goal, the expansion of `sol_derive` tried
before today's (below): today's is a macro that never fails, so an
elaborator of the same syntax would never run. -/
syntax (name := solDeriveScoped) "sol_derive_scoped" : tactic

/-- `sol_derive` is first `sol_derive_scoped`, which fails on a goal that is
not scoped; Lean then expands today's macro. -/
macro_rules | `(tactic| sol_derive) => `(tactic| sol_derive_scoped)

open Lean Elab Tactic Meta in
/-- `sol_derive` on a scoped goal: the strategy as a walk of `Core.Proves`
rules, leaving the leaves (`Walk.run`). -/
@[tactic solDeriveScoped]
def evalSolDeriveCore : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  unless ← Walk.isCoreGoal g do throwError "sol_derive_scoped: not a scoped goal"
  let rest := (← getUnsolvedGoals).erase g
  Symex.reporting g do
    let (_, leaves) ← Walk.run g
    setGoals (leaves ++ rest)

open Lean Elab Tactic Meta in
/-- `sol_derive?` on a scoped goal: the walk, offered as its script, one
`refine` per rule (today's short walk under the scope, `Walk.surfaceOn`); a leaf closed by its erasure where it can be
(`Walk.closeLeaf`), else left as a goal (`sorry` in the script). -/
@[tactic Solidity.ProofTree.tacticSol_derive?]
def evalSolDeriveQCore : Tactic := fun stx => withMainContext do
  let g ← getMainGoal
  unless ← Walk.isCoreGoal g do throwUnsupportedSyntax
  let rest := (← getUnsolvedGoals).erase g
  Symex.reporting g do
    let (lines, leaves) ← Walk.run g (close := true) (short := ← Walk.surfaceOn)
    setGoals (leaves ++ rest)
    ProofTree.suggest stx[0] lines

end Solidity.Core
