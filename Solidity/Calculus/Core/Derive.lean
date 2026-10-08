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

open Lean Elab Tactic Meta in
/-- `sol_close` on a scoped goal `Core.Valid ψ` with no modality left (after
`sol_symex`): the leaf taken by `Fml.posB` (checked by the kernel), its
erasure computed (`Solidity.normValid`) and closed by today's `sol_close`
(`Valid.of_erase`). -/
@[tactic Solidity.tacticSol_close]
def evalSolCloseCore : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let some (C, ψ) ← Symex.validGoal? g | throwUnsupportedSyntax
  Symex.reporting g do
    let bool := mkConst ``Bool
    let nilCtx := mkApp (mkConst ``List.nil [0]) (mkConst ``LTy)
    let nilVar := mkApp (mkConst ``List.nil [0]) (mkConst ``Var)
    let hpTy := mkApp3 (mkConst ``Eq [1]) bool
      (mkApp2 (mkConst ``Option.isSome [0]) (mkApp (mkConst ``List [0]) (mkConst ``Var))
        (mkAppN (mkConst ``Fml.posB) #[C, nilCtx, ψ, nilVar])) (mkConst ``Bool.true)
    let hp ← try Solidity.Derive.kernelLemma hpTy (mkApp2 (mkConst ``Eq.refl [1]) bool (mkConst ``Bool.true))
      catch _ => throwError "sol_close: the leaf is not one its erasure closes (`Fml.posB`): a \
        hidden binder under a negation, a precondition or a modality, or named twice, or a \
        diamond update that may set a `bool` local to what is not a `bool`"
    let erased := mkAppN (mkConst ``Fml.erase) #[C, nilCtx, nilVar, ψ]
    let g' ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Solidity.Valid) C erased) (← g.getTag)
    g.assign (mkAppN (mkConst ``Valid.of_erase) #[C, ψ, hp, g'])
    let g'' ← Solidity.normValid g'.mvarId!
    replaceMainGoal [g'']
    evalTactic (← `(tactic| sol_close))

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
`sol_symex; sol_close` on the erasure, as the tree's leaves close). -/

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

/-- The steps that may apply at the goal `g`, each as tactics, in the order
tried; none at a leaf. -/
def movesAt (g : MVarId) : MetaM (Array (Array (TSyntax `tactic))) := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let_expr Proves C _ Γ₀ Γ H φ0 := ty | return #[]
  let φ ← whnf φ0
  let one (c : Lean.Name) : MetaM (Array (Array (TSyntax `tactic))) := do
    return #[#[← `(tactic| refine $(← ProofTree.short c) ?_)]]
  match φ.getAppFn.constName? with
  | some ``Fml.imp => one ``Proves.impRight
  | some ``Fml.all => one ``Proves.allRight
  | some ``Fml.upd => one ``Proves.updIntro
  | some ``Fml.bind => one ``Proves.bindIntro
  | some ``Fml.tt =>
    return #[#[← `(tactic| exact $(← ProofTree.short ``Proves.closeTrue) $(mkIdent `rfl):ident)]]
  | some ``Fml.modal =>
    let args := φ.getAppArgs
    let m := args[args.size - 4]!
    let P ← whnf args[args.size - 3]!
    if P.isAppOf ``Prog.nil then return ← one ``Proves.emptyModality
    unless P.isAppOf ``Prog.cons do return #[]
    let s := P.getArg! (P.getAppNumArgs - 2)
    let k := mkAppN (mkConst ``Hyps.fresh) #[C, Γ₀, Γ, H, φ]
    let some (r, p) ← ruleOf? k m s | return #[]
    let some c := provesCtor? (← whnf p) | return #[]
    let rule := mkIdent (Lean.Name.mkSimple r.getString!)
    let d ← if r.getPrefix == ``Taclet then
        `(term| ($(← ProofTree.short ``Taclet.step_eq) .$rule:ident))
      else `(term| ($(← ProofTree.short ``LeanTaclet.toStep) .$rule:ident))
    ctorTacs c d
  | _ => return #[]

/-- A leaf closed as a walk ends, at the empty outer scope: its lines, or
none where the closer does not close it (the state rolled back). -/
def closeLeaf (g : MVarId) : TacticM (Option (Array String)) := do
  let ty ← instantiateMVars (← g.getType)
  let_expr Proves _ _ Γ₀ _ _ _ := ty | return none
  unless (← whnfR Γ₀).isAppOf ``List.nil do return none
  let tacs := #[← `(tactic| refine $(← ProofTree.short ``Proves.close) [] $(mkIdent `rfl)
      $(← ProofTree.short ``List.nodup_nil) ?_), ← `(tactic| sol_symex), ← `(tactic| sol_close)]
  let s ← saveState
  let ok ← tryCatchRuntimeEx
    (withCurrHeartbeats do return (← ProofTree.runOn g tacs).isEmpty) fun _ => pure false
  unless ok do s.restore; return none
  return some (← tacs.mapM fun t => (ProofTree.tacLines t : MetaM _)).flatten

/-- The walk from `g`: its script, lines indented relative to the first, a
`case` per goal of a step with several, `sorry` for a leaf; the leaves are
collected in `open`. -/
partial def walk (fuel : IO.Ref Nat) (leaves : IO.Ref (Array MVarId)) (g : MVarId)
    (close : Bool := false) : TacticM (Array String) := do
  let n ← fuel.get
  if n == 0 then throwError "sol_derive: more than {Derive.fuel} steps"
  fuel.set (n - 1)
  let mut step := none
  for tacs in ← movesAt g do
    let s ← saveState
    -- each try with its own heartbeats, a timeout a failed try
    let r ← tryCatchRuntimeEx (some <$> withCurrHeartbeats (ProofTree.runOn g tacs))
      fun _ => do s.restore; pure none
    if let some gs := r then
      step := some (tacs, gs)
      break
  let some (tacs, gs) := step
    | if close then
        if let some lines ← closeLeaf g then return lines
      leaves.modify (·.push g); return #["sorry"]
  let head := (← tacs.mapM fun t => (ProofTree.tacLines t : MetaM _)).flatten
  match gs with
  | [g'] => return head ++ (← walk fuel leaves g' close)
  | gs =>
    let mut out := head
    for g' in gs do
      let body ← walk fuel leaves g' close
      match ← g'.getTag with
      -- `and_intros`' goals (`refine_1`, …) have no name to cite: bullets
      | .str _ l =>
        if l.startsWith "refine_" then
          out := out ++ body.mapIdx fun i l => (if i == 0 then "· " else "  ") ++ l
          continue
        out := out.push s!"case {l} =>"
        out := out ++ body.map ("  " ++ ·)
      | _ => out := out ++ body.mapIdx fun i l => (if i == 0 then "· " else "  ") ++ l
    return out

/-- The walk from the goal `g` (`Core.Valid φ` starts with `Proves.valid`):
its lines, and the leaves it leaves. -/
def run (g : MVarId) (close : Bool := false) : TacticM (Array String × List MVarId) := do
  let (pre, g) ← match ← Symex.validGoal? g with
    | some _ =>
      let t ← `(tactic| refine $(← ProofTree.short ``Proves.valid)
        ($(mkIdent `R) := $(← ProofTree.short ``RuleSet.all)) ?_)
      let [g'] ← ProofTree.runOn g #[t] | throwError "sol_derive: `refine Proves.valid ?_` failed"
      pure ((← ProofTree.tacLines t), g')
    | none => pure (#[], g)
  let fuel ← IO.mkRef Derive.fuel
  let leaves ← IO.mkRef #[]
  let lines ← walk fuel leaves g close
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
`refine` per rule; a leaf closed by its erasure where it can be
(`Walk.closeLeaf`), else left as a goal (`sorry` in the script). -/
@[tactic Solidity.ProofTree.tacticSol_derive?]
def evalSolDeriveQCore : Tactic := fun stx => withMainContext do
  let g ← getMainGoal
  unless ← Walk.isCoreGoal g do throwUnsupportedSyntax
  let rest := (← getUnsolvedGoals).erase g
  Symex.reporting g do
    let (lines, leaves) ← Walk.run g (close := true)
    setGoals (leaves ++ rest)
    ProofTree.suggest stx[0] lines

end Solidity.Core
