import Solidity.Calculus.Notation
import Solidity.Calculus.ChainRewrites

/-!
# Chains: `φ ~> ψ`, `φ ~[r]~> ψ` and `φ ~*> ψ`

`apply` walks a derivation and `sol_step` runs one on a `⊨` goal; this
module makes a derivation something you *state*, both ends written out in
`dl!{ … }` (mini-solkey's `Ch13_Chains`):

```
dl!{ ⟨ alice.age = v; ⟩ alice.age == v }
  ~[storageFieldWriteSave]~> dl!{ { storage := save(storage, alice.age, v) } ⟨⟩ alice.age == v }
```

* `φ ~> ψ` — the strategy's step turns `φ` into `ψ` (`Fml.OneStep`, a `Prop`);
* `φ ~[r]~> ψ` — and the rule it fires is `r` (`Fml.StepBy`);
* `φ ~*> ψ` — zero or more steps (`Fml.Steps`, a `Type`: the derivation as
  a value, indexed by its two ends);
* `φ₀ ~*> φ₁ ~[r]~> φ₂ ~> φ₃` — a chain, every link holding (`Fml.Via`), and
  `calc`, whose steps are these links;
* past the program, `φ ~[sequentialToParallel]~> ψ`, `φ ~[findOnSave]~> ψ` —
  a rewrite of the line (`Fml.RwBy`, below), and `φ ~~> ψ` (`Fml.Leads`):
  wherever `ψ` holds, `φ` does, what a chain with a rewrite composes to.

**Rewrites.**  The last lines merge the updates the program left
into one parallel update, and a Theory law reads a term down to its value:
no step of the strategy.  The arrow then names an update rule (KeY's name)
or a law, and its label is a rewrite of `Calculus/ChainRewrites.lean`
(`LineRw`): the elaborator finds, from the line before, the position on the
update spine and the law's instance (as `rw` finds one) that give the line
after, and the kernel checks `r.apply φ = some ψ`.  A name that is no rule,
a rule that does not apply and a name that resolves twice are errors.  The
evidence is unique for `~*>` only: a rewrite and a step may commute.

**Naming a rule.**  mini-solkey names a step by a `RuleName`, an
enumeration its strategy computes with.  Here the strategy computes
`Stmt.step` (`Completeness.lean`), and a `Taclet` is a `Prop`: no function
can read a constructor's name off a derivation.  So the label is the
*derivation itself*, `StepRule.taclet k m s p d` with `d : Rule C k m s p`,
and `φ ~[r]~> ψ` says that `r`'s statement, modality, fresh index and premise
are exactly what `Stmt.step` fires on `φ` (`Fml.rule`).  The name between
the brackets is a `Taclet` or `LeanTaclet` constructor, which the elaborator (`rule%`)
checks by computing the strategy's derivation and comparing its head, or,
failing that, by elaborating the named constructor against the step's
instance; the kernel re-checks the resulting term.  A wrong name is an
elaboration error, not a false proposition: two constructors that derive
the same instance give the same label (proof irrelevance), and the printer
shows the name the elaborator found.  `emptyModality`, which is no
taclet here, is `StepRule.emptyModality`.

**The evidence is unique.**  A step is a function (`Fml.step`), so the
next line is determined (`Fml.OneStep.unique`), and so is the rule
(`Fml.StepBy.unique`).  That two derivations between the same ends are
equal needs them not to come back to where they started, which is
termination; `Fml.Steps.eq_of_measure` takes any measure the step
decreases, and `Fml.Steps.eq_of_length` needs none.

**What is not here** from mini-solkey's chapter: the `Subsingleton`
instance on `~*>` and `Fml.normalize` (a normal form as a value) need the
termination measure, which is ported separately; `#eval` of a chain, since
formulas print through the delaborators, not `ToString` — `#derivation`
prints a derivation instead, rule names included.

`sol_chain` proves a link by running the strategy as compiled code on a
closed formula (as `normValid` does), finding the line, and handing the
kernel a `rfl` to check.  A line left `_` becomes the next line (`~>`) or
the last (`~*>`).  When the line is not reached, the error shows the
derivation, to copy a line from.

**Unknowns in a line.**  A line may keep two unknowns
(`Notation.lean`): a modality `m`, `dl![m]{ ⟨[ p ]⟩ φ }`, and a
postcondition `φ : Post C`.  Every rule but a revert is the same under
either modality, so `sol_chain` runs such a line as the diamond and as the
box and keeps the lines the two share, up to a `revert();` or a branch's
cover (`Premise.cover`), which do depend on it; after a split nothing is
written under `m` (the cover, and every fresh index after it, are stuck on
it), and the chain goes on after `cases m`.  `φ` stands in a slot
(`Fml.slot`) while the strategy runs; `rfl` cannot compute a fresh index
over it, so a step is proved at the index the run found
(`Fml.OneStep.ofFresh`), the index by `simp` from `Post.noFresh`, the step
by the kernel.
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-! ## The rule that fires -/

/-- A rule as a chain names it: a derivation of a taclet at the fresh index
`k` under `m`, or the dropping of an empty modality. -/
inductive StepRule (C : Contract) : Type where
  | taclet (k : Nat) (m : Modality) (s : Stmt C) (p : Premise C) (d : Rule C k m s p)
  | emptyModality

/-- The rule the strategy fires on a formula, fresh names at index `k`:
`Fml.stepAt`'s choice, with its derivation. -/
def Fml.ruleAt (k : Nat) : Fml C → Option (StepRule C)
  | .upd _ _ φ | .imp _ φ | .havoc φ => φ.ruleAt k
  | .and φ ψ => if φ.active then φ.ruleAt k else ψ.ruleAt k
  | .modal _ [] _ => some .emptyModality
  | .modal m (s :: _) _ => some (.taclet k m s (s.step k m).premise (s.step k m).rule)
  | _ => none

/-- The rule `Fml.step` fires. -/
def Fml.rule (φ : Fml C) : Option (StepRule C) := φ.ruleAt φ.fresh

/-- A rule fires exactly where a step is taken.

Example: on `⟨ x = 1; ⟩ x == 1` both `localValueAssign` and the step to
`{ x := 1 } ⟨⟩ x == 1` exist; on `x == 1` neither does. -/
theorem Fml.ruleAt_isSome {k : Nat} :
    ∀ φ : Fml C, (φ.ruleAt k).isSome = (φ.stepAt k).isSome
  | .upd _ _ φ | .imp _ φ | .havoc φ => by simp [Fml.ruleAt, Fml.stepAt, Fml.ruleAt_isSome φ]
  | .and φ ψ => by
    simp only [Fml.ruleAt, Fml.stepAt]
    split <;> simp [Fml.ruleAt_isSome]
  | .modal _ [] _ | .modal _ (_ :: _) _ => rfl
  | .tt | .eq .. | .defined _ | .not _ | .all .. => rfl

/-! ## One step, several, a chain -/

/-- `φ ~> ψ`: the strategy's step turns `φ` into `ψ`. -/
def Fml.OneStep (φ ψ : Fml C) : Prop := φ.step = some ψ

/-- `φ ~[r]~> ψ`: the strategy's step turns `φ` into `ψ`, and the rule it
fires is `r`. -/
def Fml.StepBy (r : StepRule C) (φ ψ : Fml C) : Prop := (φ.rule, φ.step) = (some r, some ψ)

/-- `φ ~*> ψ`: a derivation from `φ` to `ψ`, its lines indexed by its ends. -/
inductive Fml.Steps : Fml C → Fml C → Type where
  | refl (φ : Fml C) : Fml.Steps φ φ
  | cons {φ ψ χ : Fml C} (s : Fml.OneStep φ ψ) (rest : Fml.Steps ψ χ) : Fml.Steps φ χ

/-- `φ ~[n]~> ψ` past the strategy: the rewrite `r` of
`Calculus/ChainRewrites.lean` turns `φ` into `ψ`, and `n` is the rule the
arrow names (`sequentialToParallel`, `findOnSave`, …).  The rewrite is the
one the elaborator found for `n` on `φ`: its position on the update spine,
and for a law its instance. -/
def Fml.RwBy (_n : String) (r : LineRw C) (φ ψ : Fml C) : Prop := r.apply φ = some ψ

/-- `φ ~~> ψ`: to prove `φ`, prove `ψ` — wherever `ψ` holds, `φ` does.  What
a chain with a rewrite in it composes to (a rewrite and a step may commute,
so it is no derivation `~*>`). -/
def Fml.Leads (φ ψ : Fml C) : Prop := ∀ σ, holds σ ψ → holds σ φ

@[inherit_doc] notation:50 φ:51 " ~~> " ψ:51 => Fml.Leads φ ψ

/-- The arrows of a chain. -/
inductive Link (C : Contract) : Type where
  /-- `~>` -/
  | one
  /-- `~*>` -/
  | many
  /-- `~[r]~>` -/
  | rule (r : StepRule C)
  /-- `~[n]~>` for a rewrite: an update rule or a Theory law -/
  | rw (n : String) (r : LineRw C)

/-- What an arrow says about the two lines it joins. -/
@[reducible] def Link.Rel : Link C → Fml C → Fml C → Type
  | .one => fun φ ψ => PLift (Fml.OneStep φ ψ)
  | .many => Fml.Steps
  | .rule r => fun φ ψ => PLift (Fml.StepBy r φ ψ)
  | .rw n r => fun φ ψ => PLift (Fml.RwBy n r φ ψ)

/-- `φ ~> φ₁ ~*> φ₂ …`: every link of a chain that starts at `φ`, as
evidence (a product, one factor per arrow). -/
@[reducible] def Fml.Via : Fml C → List (Link C × Fml C) → Type
  | _, [] => PUnit
  | φ, [(l, ψ)] => l.Rel φ ψ
  | φ, (l, ψ) :: w :: ws => l.Rel φ ψ × Fml.Via ψ (w :: ws)

/-- The last line of a chain. -/
def Fml.Via.last : Fml C → List (Link C × Fml C) → Fml C
  | φ, [] => φ
  | _, (_, ψ) :: ws => Fml.Via.last ψ ws

/-! ## The notation

`~[r]~>` needs the line before it to find its rule, so it is elaborated,
not expanded: `rule% φ r` is the strategy's derivation on `φ`, checked to
be `Taclet.r`.  In a `calc` step the line before is `_` until `calc` has
unified it, so the label waits (`tryPostpone`); prove such a step `by rfl`
or `by sol_chain`, which run after it. -/

namespace Chain
section Elab
open Lean Meta Elab Term

/-- The last component of a constructor's name, as `~[r]~>` shows it. -/
def lastName : Lean.Name → Lean.Name
  | .str _ s => .mkSimple s
  | n => n

/-- Whether a constant is a rule's constructor, solkey's or Lean's. -/
def isRuleCtor (c : Lean.Name) : Bool :=
  (`Solidity.Taclet).isPrefixOf c || (`Solidity.LeanTaclet).isPrefixOf c

/-- `Rule.key d` or `Rule.lean d`: the derivation `d` it wraps. -/
def unwrapRule? (d : Lean.Expr) : Option Lean.Expr :=
  if d.isAppOfArity ``Rule.key 6 || d.isAppOfArity ``Rule.lean 6 then some d.appArg! else none

/-- A derivation, with the auxiliary lemmas the elaborator abstracted it
into (a constructor applied to its side conditions' proofs) unfolded, down
to a constructor, under the `Rule` that wraps it. -/
partial def tacletHead (d : Lean.Expr) : MetaM Lean.Expr := do
  let d ← whnfCore d
  if let some inner := unwrapRule? d then
    return mkAppN d.getAppFn (d.getAppArgs.set! 5 (← tacletHead inner))
  let .const c us := d.getAppFn | return d
  if isRuleCtor c then return d
  match ← getConstInfo c with
  | info@(.thmInfo _) => tacletHead ((← instantiateValueLevelParams info us).beta d.getAppArgs)
  | _ => return d

/-- The constructor a rule's derivation is, if it is one. -/
def ruleCtor? (d : Lean.Expr) : Option Lean.Name := do
  let c ← ((unwrapRule? d).getD d).getAppFn.constName?
  if isRuleCtor c then some c else none

/-- The derivation a `Step` carries, reduced to a constructor. -/
partial def tacletOf (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← whnf e
  unless e.isAppOfArity ``Step.mk 6 do throwError "not a step:{indentExpr e}"
  let d ← whnfCore (e.getArg! 5)
  if d.isAppOf ``Step.rule then tacletOf d.appArg! else tacletHead d

/-- The derivation `Stmt.step` gives for `s` (fresh index `k`, modality
`m`), reduced to a constructor, and that constructor.  The derivation in a
`StepRule` that `Fml.ruleAt` built is an auxiliary lemma: this is where its
constructor is read instead. -/
def stepTaclet (C k m s : Lean.Expr) : MetaM (Lean.Expr × Option Lean.Name) := do
  let d ← tacletOf (mkAppN (mkConst ``Stmt.step) #[C, k, m, s])
  return (d, ruleCtor? d)

/-- The rule the strategy fires on the formula `φ`, as a `StepRule` term
whose derivation is a constructor, and that constructor's name. -/
def ruleOfLine (φ : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Name)) := do
  let r ← whnf (← mkAppM ``Fml.rule #[φ])
  unless r.isAppOfArity ``Option.some 2 do return none
  let r ← whnf r.appArg!
  if r.isAppOfArity ``StepRule.emptyModality 1 then return some (r, `emptyModality)
  unless r.isAppOfArity ``StepRule.taclet 6 do return none
  let #[C, k, m, s, p, _] := r.getAppArgs | return none
  let (d', c?) ← try stepTaclet C k m s catch
    | ex@(.error ..) => do
      -- a revert, under a modality that is a variable
      if (← whnfR m).isConst || !(← whnfR s).isAppOf ``Stmt.revert then throw ex
      throwError "the rule on{indentExpr φ}\ndepends on its modality {m} (`revertBox`, \
        `revertDiamond`): go on after `cases {m}`"
    | ex => throw ex
  let some c := c? | return some (r, `taclet)
  return some (mkAppN (mkConst ``StepRule.taclet) #[C, k, m, s, p, d'], lastName c)

/-- The name `~[r]~>` shows for a label: the head of its derivation, or, when
that is an auxiliary lemma (the one `Fml.ruleAt` makes), the head of the
derivation `Stmt.step` gives. -/
def ruleName? (r : Lean.Expr) : MetaM (Option Lean.Name) := do
  let r ← whnfR (← instantiateMVars r)
  if r.isAppOfArity ``StepRule.emptyModality 1 then return some `emptyModality
  unless r.isAppOfArity ``StepRule.taclet 6 do return none
  if let some c := ruleCtor? (← instantiateMVars r.appArg!) then return some (lastName c)
  let #[C, k, m, s, _, _] := r.getAppArgs | return none
  return (← stepTaclet C k m s).2.map lastName

/-- The label of `φ ~[r]~> ψ`: the rule the strategy fires on `φ`, which must be
`Taclet.r` or `LeanTaclet.r` (or `emptyModality`), or be derived by it. -/
def labelFor (a : Lean.Expr) (r : Ident) : TermElabM Lean.Expr := do
  let some (lbl, found) ← ruleOfLine a | throwError "~[{r}]~>: no rule applies to{indentExpr a}"
  let want := r.getId
  if found == want then return lbl
  -- another constructor may derive the same instance: try it
  let alt ← observing? do
    let_expr StepRule.taclet C k m s p _ := lbl | failure
    let d ← [(``Taclet, ``Rule.key), (``LeanTaclet, ``Rule.lean)].firstM fun (ty, wrap) => do
      unless (← getEnv).contains (ty ++ want) do failure
      let d ← elabTermEnsuringType (mkIdent (ty ++ want)) (mkAppN (mkConst ty) #[C, k, m, s, p])
      synthesizeSyntheticMVarsNoPostponing
      let d ← instantiateMVars d
      if d.hasExprMVar then failure
      return mkAppN (mkConst wrap) #[C, k, m, s, p, d]
    return mkAppN (mkConst ``StepRule.taclet) #[C, k, m, s, p, d]
  match alt with
  | some l => return l
  | none => throwError "~[{want}]~>: the rule for{indentExpr a}\nis {found}, not {want}"

/-- The line before a label, once it is known. -/
def lineBefore (a : Syntax) (r : Ident) : TermElabM Lean.Expr := do
  let a ← instantiateMVars (← elabTerm a none)
  if a.hasExprMVar then
    tryPostpone
    throwError "~[{r}]~>: the line before it is not known{indentExpr a}"
  return a

/-- `rule% φ r`: the label of `φ ~[r]~> ψ`. -/
elab "rule% " a:term:max r:ident : term => do labelFor (← lineBefore a r) r

/-- `ruleCheck% l φ r`: `l`, once `φ` is known and `l` is its label. -/
elab "ruleCheck% " l:term:max a:term:max r:ident : term => do
  let l ← elabTerm l none
  let a ← lineBefore a r
  let lbl ← labelFor a r
  unless ← isDefEq l lbl do
    throwError "~[{r}]~>: the rule for{indentExpr a}\nis not {r}"
  return l

/-- `φ ~[r]~> ψ` for a rule of the strategy, `φ : Fml C` and `ψ` elaborated.
In a `calc` step `φ` is not known yet: the label is left to the proof, and
checked after it. -/
def stepByRule (C a b : Lean.Expr) (r : Ident) : TermElabM Lean.Expr := do
  let rty := mkApp (mkConst ``StepRule) C
  let lbl ← if (← instantiateMVars a).hasExprMVar then
      let l ← mkFreshExprMVar rty
      discard <| elabTermEnsuringType
        (← `(ruleCheck% $(← exprToSyntax l) $(← exprToSyntax a) $r)) rty
      pure l
    else labelFor a r
  return mkAppN (mkConst ``Fml.StepBy) #[C, lbl, a, b]

end Elab
end Chain

/-- `stepBy% φ r ψ`: `φ ~[r]~> ψ`, with `φ` elaborated once: a rule of the
strategy (`Fml.StepBy`) or a rewrite (`Fml.RwBy`).  Elaborated at the end of
the module, after `sol_chain`'s search. -/
syntax "stepBy% " term:max ident term:max : term

/-- `link% φ r ψ`: the `Link` of `φ ~[r]~> ψ` in a chain. -/
syntax "link% " term:max ident term:max : term

declare_syntax_cat chain_arrow
syntax "~> " : chain_arrow
syntax "~*> " : chain_arrow
syntax "~[" ident "]~> " : chain_arrow
/-- `a ~> b`, `a ~*> b`, `a ~[r]~> b`, and chains of them: `a ~*> b ~[r]~> c ~*> d`. -/
syntax:50 (name := chainStx) term:51 (ppIndent(ppLine chain_arrow term:51))+ : term

open Lean in
/-- One link is the relation itself; a longer chain is `Fml.Via`. -/
@[macro chainStx] def expandChain : Macro := fun stx => do
  let a : Lean.Term := ⟨stx[0]⟩
  -- applications are built directly: in a quotation `$a $b` would read `$b` as an arrow
  let app (f : Lean.Name) (args : Array Lean.Term) : Lean.Term := Syntax.mkApp (mkCIdent f) args
  let mut prev := a
  let mut links := #[]
  for l in stx[1].getArgs do
    let b : Lean.Term := ⟨l[1]⟩
    let link ← match (⟨l[0]⟩ : TSyntax `chain_arrow) with
      | `(chain_arrow| ~>) => pure (← `(Link.one), app ``Fml.OneStep #[prev, b])
      | `(chain_arrow| ~*>) => pure (← `(Link.many), app ``Fml.Steps #[prev, b])
      | `(chain_arrow| ~[ $r:ident ]~>) =>
        pure (← `(link% ($prev) $r ($b)), ← `(stepBy% ($prev) $r ($b)))
      | _ => Macro.throwUnsupported
    links := links.push (link.1, link.2, b)
    prev := b
  match links with
  | #[(_, rel, _)] => pure rel
  | _ =>
    let ws ← links.mapM fun (l, _, b) => `((($l : Link _), $b:term))
    pure (app ``Fml.Via #[a, ← `([$ws,*])])

namespace Chain
section Print
open Lean Meta PrettyPrinter Delaborator SubExpr

/-- A line of a chain: `dl{ φ }`, or Lean's own printing. -/
def ppLine (e : Lean.Expr) : MetaM Lean.Term := do
  let φ ← ppFml e
  if isEscape φ then escapeTerm e else `(dl{ $φ:dl_fml })

/-- The arrow a `Link` stands for. -/
def arrowOf (l : Lean.Expr) : MetaM (TSyntax `chain_arrow) := do
  let l ← whnfR (← instantiateMVars l)
  if l.isAppOfArity ``Link.one 1 then `(chain_arrow| ~>)
  else if l.isAppOfArity ``Link.many 1 then `(chain_arrow| ~*>)
  else if l.isAppOfArity ``Link.rule 2 then
    let some n ← ruleName? l.appArg! | failure
    `(chain_arrow| ~[$(mkIdent n):ident]~>)
  else if l.isAppOfArity ``Link.rw 3 then
    let .lit (.strVal n) := l.getArg! 1 | failure
    `(chain_arrow| ~[$(mkIdent n.toName):ident]~>)
  else failure

def chainNode (a : Lean.Term) (arrows : Array (TSyntax `chain_arrow × Lean.Term)) : Lean.Term :=
  ⟨mkNode ``chainStx #[a, mkNullNode (arrows.map fun (l, b) => mkNode groupKind #[l, b])]⟩

/-- `Fml.OneStep φ ψ`: `φ ~> ψ`. -/
@[delab app.Solidity.Fml.OneStep]
def delabOneStep : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 3)
  return chainNode (← withNaryArg 1 delab) #[(← `(chain_arrow| ~>), ← withNaryArg 2 delab)]

/-- `Fml.Steps φ ψ`: `φ ~*> ψ`. -/
@[delab app.Solidity.Fml.Steps]
def delabSteps : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 3)
  return chainNode (← withNaryArg 1 delab) #[(← `(chain_arrow| ~*>), ← withNaryArg 2 delab)]

/-- `Fml.StepBy r φ ψ`: `φ ~[r]~> ψ`, `r` the name of its derivation. -/
@[delab app.Solidity.Fml.StepBy]
def delabStepBy : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 4)
  let some n ← ruleName? (e.getArg! 1) | failure
  return chainNode (← withNaryArg 2 delab)
    #[(← `(chain_arrow| ~[$(mkIdent n):ident]~>), ← withNaryArg 3 delab)]

/-- `Fml.RwBy n r φ ψ`: `φ ~[n]~> ψ`. -/
@[delab app.Solidity.Fml.RwBy]
def delabRwBy : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 5)
  let .lit (.strVal n) := e.getArg! 1 | failure
  return chainNode (← withNaryArg 3 delab)
    #[(← `(chain_arrow| ~[$(mkIdent n.toName):ident]~>), ← withNaryArg 4 delab)]

/-- `Fml.Via φ [(l₁, φ₁), …]`: `φ l₁ φ₁ …`. -/
@[delab app.Solidity.Fml.Via]
def delabVia : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 3)
  let some ws ← listElems? (e.getArg! 2) | failure
  guard !ws.isEmpty
  let arrows ← ws.mapM fun w => do
    let w ← whnfR w
    guard (w.isAppOfArity ``Prod.mk 4)
    pure (← arrowOf (w.getArg! 2), ← ppLine (w.getArg! 3))
  return chainNode (← withNaryArg 1 delab) arrows

end Print
end Chain

/-! ## A derivation is a list of lines -/

namespace Fml.Steps

/-- One step as a derivation. -/
def single {φ ψ : Fml C} (s : Fml.OneStep φ ψ) : φ ~*> ψ := .cons s (.refl ψ)

/-- Two derivations, one after the other. -/
def trans : {φ ψ χ : Fml C} → φ ~*> ψ → ψ ~*> χ → φ ~*> χ
  | _, _, _, .refl _, d => d
  | _, _, _, .cons s c, d => .cons s (c.trans d)

/-- The lines of the derivation after the first. -/
def lines : {φ ψ : Fml C} → φ ~*> ψ → List (Fml C)
  | _, _, .refl _ => []
  | _, _, .cons (ψ := ψ) _ c => ψ :: c.lines

/-- The number of steps. -/
def length {φ ψ : Fml C} (c : φ ~*> ψ) : Nat := c.lines.length

end Fml.Steps

/-- A named step is a step: `⟨ x = 1; ⟩ x == 1 ~[localValueAssign]~> { x := 1 } ⟨⟩ x == 1`
gives `⟨ x = 1; ⟩ x == 1 ~> { x := 1 } ⟨⟩ x == 1`. -/
theorem Fml.StepBy.oneStep {r : StepRule C} {φ ψ : Fml C} (h : Fml.StepBy r φ ψ) : φ ~> ψ :=
  (Prod.mk.inj h).2

/-- A named step names the rule `Fml.rule` finds: on `⟨ x = 1; ⟩ x == 1` that is
`localValueAssign`. -/
theorem Fml.StepBy.rule_eq {r : StepRule C} {φ ψ : Fml C} (h : Fml.StepBy r φ ψ) :
    φ.rule = some r :=
  (Prod.mk.inj h).1

/-- Every step has its rule: `φ ~> ψ` is `φ ~[r]~> ψ` for the `r` that fires.

Example: `⟨ x = 1; ⟩ x == 1 ~> { x := 1 } ⟨⟩ x == 1`, and the rule is
`localValueAssign`. -/
theorem Fml.OneStep.stepBy {φ ψ : Fml C} (h : φ ~> ψ) : ∃ r, Fml.StepBy r φ ψ := by
  have := Fml.ruleAt_isSome (k := φ.fresh) φ
  unfold Fml.OneStep Fml.step at h
  rw [h] at this
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 this
  exact ⟨r, by simp only [Fml.StepBy, Fml.rule, hr, Fml.step, h]⟩

/-- A step as a derivation of one line; the rule label is dropped:
`⟨ x = 1; ⟩ x == 1 ~[localValueAssign]~> …` as `⟨ x = 1; ⟩ x == 1 ~*> …`. -/
def Fml.StepBy.steps {r : StepRule C} {φ ψ : Fml C} (h : Fml.StepBy r φ ψ) : φ ~*> ψ :=
  .single h.oneStep

/-! `calc` chains `~>`, `~*>` and `~[r]~>`; the result is a derivation `~*>`.
With a rewrite among them it is `~~>` (the instances after `Fml.Leads.valid`). -/

instance : @Trans (Fml C) (Fml C) (Fml C) Fml.Steps Fml.Steps Fml.Steps := ⟨Fml.Steps.trans⟩
instance : @Trans (Fml C) (Fml C) (Fml C) Fml.OneStep Fml.Steps Fml.Steps := ⟨.cons⟩
instance : @Trans (Fml C) (Fml C) (Fml C) Fml.Steps Fml.OneStep Fml.Steps :=
  ⟨fun c s => c.trans (.single s)⟩
instance : @Trans (Fml C) (Fml C) (Fml C) Fml.OneStep Fml.OneStep Fml.Steps :=
  ⟨fun s t => .cons s (.single t)⟩
instance {r : StepRule C} : @Trans (Fml C) (Fml C) (Fml C) (Fml.StepBy r) Fml.Steps Fml.Steps :=
  ⟨fun h c => .cons h.oneStep c⟩
instance {r : StepRule C} : @Trans (Fml C) (Fml C) (Fml C) Fml.Steps (Fml.StepBy r) Fml.Steps :=
  ⟨fun c h => c.trans h.steps⟩
instance {r : StepRule C} : @Trans (Fml C) (Fml C) (Fml C) (Fml.StepBy r) Fml.OneStep Fml.Steps :=
  ⟨fun h s => .cons h.oneStep (.single s)⟩
instance {r : StepRule C} : @Trans (Fml C) (Fml C) (Fml C) Fml.OneStep (Fml.StepBy r) Fml.Steps :=
  ⟨fun s h => .cons s h.steps⟩
instance {r r' : StepRule C} :
    @Trans (Fml C) (Fml C) (Fml C) (Fml.StepBy r) (Fml.StepBy r') Fml.Steps :=
  ⟨fun h h' => .cons h.oneStep h'.steps⟩

/-! ## Running the strategy

`Steps.ofRun n h` is the derivation of `n` steps, given that they run from
`φ` to `ψ`: the evidence is computed, `h` only rules out a step that does
not fire.  `Steps.ofSymex` is the strategy of `Symex.lean` as a
derivation. -/

/-- Take `n` steps, each of which must fire. -/
def Fml.run : Nat → Fml C → Option (Fml C)
  | 0, φ => some φ
  | n + 1, φ => φ.step.bind (Fml.run n)

def Fml.Steps.ofRun : {φ ψ : Fml C} → (n : Nat) → φ.run n = some ψ → φ ~*> ψ
  | φ, _, 0, h => Option.some.inj h ▸ .refl φ
  | φ, _, n + 1, h =>
    match hs : φ.step with
    | some _ => .cons hs (Fml.Steps.ofRun n (by simpa [Fml.run, hs] using h))
    | none => absurd h (by simp [Fml.run, hs])

/-- The strategy, run for `n` steps, as a derivation. -/
def Fml.Steps.ofSymex : (n : Nat) → (φ : Fml C) → φ ~*> symex n φ
  | 0, φ => .refl φ
  | n + 1, φ =>
    match hs : φ.step with
    | some ψ => (congrArg (Fml.Steps φ) (by simp [symex, hs])).mpr (.cons hs (Fml.Steps.ofSymex n ψ))
    | none => (congrArg (Fml.Steps φ) (by simp [symex, hs])).mpr (.refl φ)

/-! ## Soundness: a chain is a proof -/

/-- One step is sound: where the line after it holds, the line before holds.

Example: `⟨ alice.age = v; ⟩ alice.age == v ~>
{ storage := save(storage, alice.age, v) } ⟨⟩ alice.age == v`, so in every
state where the second holds, so does the first. -/
theorem Fml.OneStep.sound {φ ψ : Fml C} (s : φ ~> ψ) (σ : State) : holds σ ψ → holds σ φ :=
  Fml.step_sound s σ

/-- A derivation is sound state by state: where its last line holds, its
first line holds.

Example: `alice.account.balance = 10;` derives, in seven steps,
`{ se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } …`;
in every state where that holds, so does the statement's formula. -/
theorem Fml.Steps.sound {φ ψ : Fml C} : φ ~*> ψ → ∀ σ, holds σ ψ → holds σ φ
  | .refl _, _, h => h
  | .cons s c, σ, h => s.sound σ (c.sound σ h)

/-- A rewrite is sound: where the line after it holds, the line before holds.

Example: `{ se1 := 10 } { sp1 := alice.account } ⟨ sp1.balance = se1; ⟩ φ
~[sequentialToParallel]~> { se1 := 10 ‖ sp1 := alice.account } ⟨ sp1.balance = se1; ⟩ φ`. -/
theorem Fml.RwBy.sound {n : String} {r : LineRw C} {φ ψ : Fml C} (h : Fml.RwBy n r φ ψ) :
    φ ~~> ψ :=
  r.sound h

/-- A chain is sound state by state: where its last line holds, its first
line holds, whatever its arrows. -/
theorem Fml.Via.sound : {φ : Fml C} → {ws : List (Link C × Fml C)} → Fml.Via φ ws →
    φ ~~> Fml.Via.last φ ws
  | _, [], _ => fun _ h => h
  | _, [(.one, _)], ⟨s⟩ => s.sound
  | _, [(.many, _)], c => Fml.Steps.sound c
  | _, [(.rule _, _)], ⟨h⟩ => h.oneStep.sound
  | _, [(.rw _ _, _)], ⟨h⟩ => h.sound
  | _, (.one, _) :: _ :: _, (⟨s⟩, v) => fun σ h => s.sound σ (Fml.Via.sound v σ h)
  | _, (.many, _) :: _ :: _, (c, v) => fun σ h => Fml.Steps.sound c σ (Fml.Via.sound v σ h)
  | _, (.rule _, _) :: _ :: _, (⟨s⟩, v) => fun σ h => s.oneStep.sound σ (Fml.Via.sound v σ h)
  | _, (.rw _ _, _) :: _ :: _, (⟨s⟩, v) => fun σ h => s.sound σ (Fml.Via.sound v σ h)

/-- **A derivation is a proof**: to prove `φ`, prove any line it reaches.

Example: `[ alice.age = v; ] alice.age == v ~*>
{ storage := save(storage, alice.age, v) } [ ] alice.age == v`, and the
last line is valid (a read after a write of the same path), so the first is. -/
theorem Fml.Steps.valid {φ ψ : Fml C} (c : φ ~*> ψ) (h : ⊨ ψ) : ⊨ φ :=
  fun σ => c.sound σ (h σ)

/-- One step is a proof: to prove `φ`, prove the line it steps to.

Example: `⊨ [ x = 1; ] x == 1` follows from `⊨ { x := 1 } [ ] x == 1`. -/
theorem Fml.OneStep.valid {φ ψ : Fml C} (s : φ ~> ψ) (h : ⊨ ψ) : ⊨ φ :=
  (Fml.Steps.single s).valid h

/-- A named step is a proof: to prove `φ`, prove the line `r` leaves.

Example: `⊨ [ x = 1; ] x == 1` follows from `⊨ { x := 1 } [ ] x == 1`, the
line `localValueAssign` leaves. -/
theorem Fml.StepBy.valid {r : StepRule C} {φ ψ : Fml C} (h : Fml.StepBy r φ ψ) (hψ : ⊨ ψ) :
    ⊨ φ :=
  h.oneStep.valid hψ

/-- A chain is a proof: to prove its first line, prove its last.

Example: the chain `⟨ alice.account.balance = 10; ⟩ … ~*> … ~[storageLocalDeclInitDrop]~> … ~*> …`
of `Examples/Chains.lean` proves its first line from its last. -/
theorem Fml.Via.valid {φ : Fml C} {ws : List (Link C × Fml C)} (v : Fml.Via φ ws)
    (h : ⊨ Fml.Via.last φ ws) : ⊨ φ :=
  fun σ => v.sound σ (h σ)

/-- A chain with rewrites is a proof: to prove its first line, prove its last.

Example: `headlineNamed .box φ` of `Examples/ChainRewrites.lean`, down to the
last line, proves `[ alice.account.balance = 10; ] φ` from
`{ se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10) } φ`. -/
theorem Fml.Leads.valid {φ ψ : Fml C} (h : φ ~~> ψ) (hψ : ⊨ ψ) : ⊨ φ :=
  fun σ => h σ (hψ σ)

universe u v

/-- A relation between lines whose evidence carries the second line's truth
back to the first: every arrow of a chain, and `~~>` itself. -/
class Fml.SoundRel (R : Fml C → Fml C → Sort u) : Prop where
  leads : ∀ {φ ψ : Fml C}, R φ ψ → φ ~~> ψ

instance : Fml.SoundRel (@Fml.OneStep C) := ⟨fun s => s.sound⟩
instance : Fml.SoundRel (@Fml.Steps C) := ⟨fun c => c.sound⟩
instance {r : StepRule C} : Fml.SoundRel (Fml.StepBy r) := ⟨fun h => h.oneStep.sound⟩
instance {n : String} {r : LineRw C} : Fml.SoundRel (Fml.RwBy n r) := ⟨fun h => h.sound⟩
instance : Fml.SoundRel (@Fml.Leads C) := ⟨id⟩

/-- A `calc` with a rewrite in it composes to `~~>`; one of steps alone still
composes to `~*>`, whose instances come first. -/
instance (priority := low) {R : Fml C → Fml C → Sort u} {S : Fml C → Fml C → Sort v}
    [Fml.SoundRel R] [Fml.SoundRel S] : @Trans (Fml C) (Fml C) (Fml C) R S Fml.Leads :=
  ⟨fun a b σ h => Fml.SoundRel.leads a σ (Fml.SoundRel.leads b σ h)⟩

/-! ## Determinism: the evidence is unique -/

/-- A formula steps to one formula only.

Example: `⟨ x = 1; ⟩ x == 1` steps only to `{ x := 1 } ⟨⟩ x == 1`. -/
theorem Fml.OneStep.unique {φ ψ χ : Fml C} (s : φ ~> ψ) (t : φ ~> χ) : ψ = χ :=
  Option.some.inj (s.symm.trans t)

/-- A step has one rule, and one line after it.

Example: on `⟨ alice.age = v; ⟩ alice.age == v` only `storageFieldWriteSave`
fires, and always to `{ storage := save(storage, alice.age, v) } ⟨⟩ alice.age == v`. -/
theorem Fml.StepBy.unique {r r' : StepRule C} {φ ψ χ : Fml C} (h : Fml.StepBy r φ ψ)
    (h' : Fml.StepBy r' φ χ) : r = r' ∧ ψ = χ :=
  ⟨Option.some.inj (h.rule_eq.symm.trans h'.rule_eq), h.oneStep.unique h'.oneStep⟩

/-- Two derivations of the same length between the same ends are equal: each
step is determined.

Example: any two seven-step derivations of `alice.account.balance = 10;`
are the `calc` chain `headline` of `Examples/Chains.lean`. -/
theorem Fml.Steps.eq_of_length {φ ψ : Fml C} :
    (c d : φ ~*> ψ) → c.length = d.length → c = d
  | .refl _, .refl _, _ => rfl
  | .refl _, .cons _ _, h | .cons _ _, .refl _, h => by
    simp [Fml.Steps.length, Fml.Steps.lines] at h
  | .cons (ψ := ψ₁) s c, .cons (ψ := ψ₂) s' c', h => by
    obtain rfl : ψ₁ = ψ₂ := s.unique s'
    have : c.length = c'.length := by
      simpa [Fml.Steps.length, Fml.Steps.lines] using h
    rw [Fml.Steps.eq_of_length c c' this]

/-- Along a derivation a measure the step decreases does not go up: every line
reached from `⟨ alice.account.balance = 10; ⟩ …` weighs at most what it does. -/
theorem Fml.Steps.measure_le (μ : Fml C → Nat) (hμ : ∀ {φ ψ : Fml C}, φ ~> ψ → μ ψ < μ φ) :
    {φ ψ : Fml C} → φ ~*> ψ → μ ψ ≤ μ φ
  | _, _, .refl _ => Nat.le_refl _
  | _, _, .cons s c => Nat.le_of_lt (Nat.lt_of_le_of_lt (c.measure_le μ hμ) (hμ s))

/-- A derivation between two formulas is unique, given a measure every step
decreases: it cannot come back to where it started.  (The termination
measure is such a `μ`; with it this is `Subsingleton (φ ~*> ψ)`.)

Example: every derivation from `⟨ alice.account.balance = 10; ⟩ …` to its
line with three updates is `headline`. -/
theorem Fml.Steps.eq_of_measure (μ : Fml C → Nat) (hμ : ∀ {φ ψ : Fml C}, φ ~> ψ → μ ψ < μ φ) :
    {φ ψ : Fml C} → (c d : φ ~*> ψ) → c = d
  | _, _, .refl _, .refl _ => rfl
  | _, _, .refl _, .cons s c | _, _, .cons s c, .refl _ =>
    absurd (hμ s) (Nat.not_lt.2 (c.measure_le μ hμ))
  | _, _, .cons (ψ := ψ₁) s c, .cons (ψ := ψ₂) s' c' => by
    obtain rfl : ψ₁ = ψ₂ := s.unique s'
    rw [Fml.Steps.eq_of_measure μ hμ c c']

/-! ## An abstract postcondition

The calculus derives `⟨[ p ]⟩ φ` for any postcondition `φ`.  Here `φ` is a
`Post C`, written by its name in a line (`dl![m]{ ⟨[ p ]⟩ φ }`, printed
back so).  `rfl` proves a step over it where the rule declares nothing
fresh; where it does, the fresh index is the largest in the whole line,
`φ`'s included, and `rfl` cannot compute it: `Fml.OneStep.ofFresh` takes it
as a hypothesis, which `sol_chain` proves from `Post.noFresh`. -/

/-- A postcondition `φ`: a formula that names no fresh variable
(`se1`, `sp1`, …), so that the rules' fresh names avoid it whatever it is,
and has no modality, so that the strategy never steps into it.

Example: `⟨dl!{ alice.account.balance == 10 }, by decide, by decide⟩`, which
`{ fml := dl!{ alice.account.balance == 10 } }` abbreviates. -/
structure Post (C : Contract) where
  fml : Fml C
  noFresh : maxIdx fml.vars = 0 := by decide
  inactive : fml.active = false := by decide

attribute [coe] Post.fml

instance : Coe (Post C) (Fml C) := ⟨Post.fml⟩

/-- A step, at the index its fresh names start from: `⟨ alice.account.balance = 10; ⟩ φ`
steps to its unfolding with `se1`, `sp1` once its fresh index is known to
be `1`, whatever `φ : Post C` is. -/
theorem Fml.OneStep.ofFresh {φ ψ : Fml C} {k : Nat} (hk : φ.fresh = k)
    (h : φ.stepAt k = some ψ) : φ ~> ψ := by
  unfold Fml.OneStep Fml.step
  rw [hk]
  exact h

/-- A step, and the rule `Fml.rule` finds, are a named step: `localValueAssign`
on `⟨ x = 1; ⟩ φ`. -/
theorem Fml.StepBy.ofOneStep {r : StepRule C} {φ ψ : Fml C} (hr : φ.rule = some r)
    (h : φ ~> ψ) : Fml.StepBy r φ ψ := by
  unfold Fml.StepBy
  rw [hr, show φ.step = some ψ from h]

/-! ## `sol_chain` and `#derivation`

On a goal `φ ~> ψ`, `φ ~[r]~> ψ`, `φ ~*> ψ` or a chain, `sol_chain` runs the
strategy on `φ` as compiled code (`φ` a formula of a named contract, its
modality and postconditions in slots), finds `ψ` among the lines, and closes
the goal with `rfl`, or `Steps.ofRun n rfl`: the kernel checks it by
computing the steps itself.  Over a postcondition each step is
`Fml.OneStep.ofFresh`. -/

/-- A line of a derivation as `sol_chain` computes it: the line, quoted; the
fresh index of the step that reached it; and whether that step was taken
without asking a slot (`Fml.slot`) whether it has a modality. -/
structure Chain.Line where
  fml : Lean.Expr
  fresh : Nat
  decided : Bool

/-- `Fml.active`, `none` where a slot decides it: a slot has no modality,
but the kernel does not know that of the postcondition put back in it. -/
def Fml.activeOpen : Fml C → Option Bool
  | .upd _ _ φ | .imp _ φ | .havoc φ => φ.activeOpen
  | .and φ ψ => match φ.activeOpen with
    | some false => ψ.activeOpen
    | r => r
  | .modal .. => some true
  | φ => if φ.isSlot then none else some false

/-- Whether the step on `φ` is taken without asking a slot whether it has a
modality: past the first goal of a branch, once it is done, it asks. -/
def Fml.stepOpenOk : Fml C → Bool
  | .upd _ _ φ | .imp _ φ | .havoc φ => φ.stepOpenOk
  | .and φ ψ => match φ.activeOpen with
    | some true => φ.stepOpenOk
    | some false => ψ.stepOpenOk
    | none => false
  | _ => true

/-- The lines of the derivation of `φ`, at most `n` of them, quoted. -/
def Fml.linesQuoted (c : Lean.Expr) : Nat → Fml C → List Chain.Line
  | 0, _ => []
  | n + 1, φ => match φ.step with
    | some ψ => ⟨ψ.quote c, φ.fresh, φ.stepOpenOk⟩ :: Fml.linesQuoted c n ψ
    | none => []

/-- Each rewrite of `rs` on `φ`: the line after, quoted, or `none`. -/
def Fml.rwQuoted (c : Lean.Expr) (φ : Fml C) (rs : List (LineRw C)) : List (Option Lean.Expr) :=
  rs.map fun r => (r.apply φ).map (Fml.quote c)

namespace Chain
section Tactic
open Lean Elab Tactic Meta

/-- The Lean terms of a line (`fillSlots`): its modality, a variable, and
its postconditions `↑φ` by slot, each with its `Post.noFresh`. -/
structure Splice where
  modality : Option Lean.Expr := none
  fmls : Array Lean.Expr := #[]
  noFresh : Array Lean.Expr := #[]

/-- The line with each open postcondition `↑φ` in its slot. -/
partial def punch (C : Lean.Expr) : Lean.Expr → StateT Splice MetaM Lean.Expr
  | e@(.app f x) => do
    unless e.isAppOfArity ``Post.fml 2 && e.hasFVar do
      return .app (← punch C f) (← punch C x)
    let sp ← get
    if let some i := sp.fmls.findIdx? (· == e) then return slotExpr C i
    set { sp with fmls := sp.fmls.push e,
                  noFresh := sp.noFresh.push (mkApp2 (mkConst ``Post.noFresh) (e.getArg! 0) x) }
    return slotExpr C sp.fmls.size
  | .mdata _ e => punch C e
  | e => return e

/-- The modality of a line with its postconditions in their slots, when it
is a variable; no other variable may be left. -/
def modalityOf? (φ : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let fvs := (collectFVars {} φ).fvarIds
  if fvs.isEmpty then return none
  for x in fvs do
    let ty ← instantiateMVars (← x.getType)
    if ty.isConstOf ``Modality && fvs.size == 1 then return some (.fvar x)
    if ty.isAppOfArity ``Fml 1 then
      throwError "sol_chain: {mkFVar x} may name a fresh variable or have a modality: \
        take it as a postcondition, `{mkFVar x} : Post {ty.appArg!}`"
    unless ty.isConstOf ``Modality do
      throwError "sol_chain: {mkFVar x} is free in the line: only a modality `m` and \
        postconditions `φ : Post C` may be{indentExpr φ}"
  throwError "sol_chain: the line is under two modalities: take `cases` on one{indentExpr φ}"

/-- The lines of the derivation of the closed formula `φ`, computed. -/
def closedLines (n : Lean.Name) (C φ : Lean.Expr) : MetaM (List Line) := do
  unsafe evalExpr (List Line) (mkApp (mkConst ``List [0]) (mkConst ``Line))
    (mkApp4 (mkConst ``Fml.linesQuoted) C (quoteConstName n) (toExpr 200) φ)

/-- A derivation as `sol_chain` computed it: the Lean terms of its first
line, its lines with them put back, and whether they stop because the next
rule depends on the modality. -/
structure Run where
  splice : Splice
  lines : List Line
  stuck : Bool

/-- The lines two runs share, put together (`fillSlots`), and whether the
runs part before they end. -/
def shared (f : Line → Line → Option Line) : List Line → List Line → List Line × Bool
  | d :: ds, b :: bs => match f d b with
    | some l => let (ls, stuck) := shared f ds bs; (l :: ls, stuck)
    | none => ([], true)
  | [], [] => ([], false)
  | _, _ => ([], true)

/-- The derivation of `φ`: its postconditions in slots, and, under a modality
`m`, run as the diamond and as the box, whose shared lines are the lines
under `m` — up to a revert or a branch's cover, the rules that look at it. -/
def runChain (C φ : Lean.Expr) : MetaM Run := do
  let some n := (← whnfR C).constName?
    | throwError "sol_chain: the contract is not a named constant: {C}"
  let φ ← instantiateMVars φ
  if φ.hasMVar then throwError "sol_chain: the formula is not known{indentExpr φ}"
  let (φ', sp) ← (punch C φ).run {}
  let fill (m? : Option Lean.Expr) (d b : Line) : Option Line :=
    match fillSlots m? sp.fmls d.fml b.fml with
    | .ok e => some { d with fml := e, decided := d.decided && b.decided }
    | .error _ => none
  match ← modalityOf? φ' with
  | none =>
    let ls ← closedLines n C φ'
    let ls := if sp.fmls.isEmpty then ls else ls.map fun l => (fill none l l).getD l
    return { splice := sp, lines := ls, stuck := false }
  | some m =>
    let ds ← closedLines n C (φ'.replaceFVar m (mkConst ``Modality.diamond))
    let bs ← closedLines n C (φ'.replaceFVar m (mkConst ``Modality.box))
    let (ls, stuck) := shared (fill m) ds bs
    return { splice := { sp with modality := m }, lines := ls, stuck }

/-- Why a line is not written under the modality `m`. -/
def modalityStop (m : Lean.Expr) : MessageData :=
  m!"depends on the modality {m}, through a `revert();` or a branch's cover: go on after `cases {m}`"

/-- Why the lines stop, when the modality stops them. -/
def stuckNote (run : Run) : MessageData :=
  match run.stuck, run.splice.modality with
  | true, some m => m!"\n  (the line after {modalityStop m})"
  | _, _ => m!""

/-- The derivation of `φ`, shown: every line with the rule that reached it. -/
def showLines (φ : Lean.Expr) (lines : List Lean.Expr) : MetaM MessageData := do
  let mut out := m!"    {φ}"
  let mut prev := φ
  for l in lines do
    let r := match ← ruleOfLine prev with
      | some (_, n) => toString n
      | none => "?"
    out := out ++ m!"\n  ~[{r}]~>\n    {l}"
    prev := l
  return out

/-- The index of `ψ` among `φ` (index `0`) and the lines after it. -/
def findLine (φ ψ : Lean.Expr) (lines : List Lean.Expr) : MetaM (Option Nat) := do
  let cands := φ :: lines
  for h : i in [0:cands.length] do
    let q := cands[i]
    if q == ψ then return some i
    if ← withReducible (isDefEq q ψ) then return some i
  return none

def notReached (φ ψ : Lean.Expr) (run : Run) (lines : List Lean.Expr) : MetaM α := do
  throwError "sol_chain: the derivation of{indentExpr φ}\ndoes not reach{indentExpr ψ}\n\
    Its lines:\n{← showLines φ lines}{stuckNote run}"

/-- `some ψ = some ψ`, the proof of `φ.step = some ψ` and `φ.run n = some ψ`. -/
def someRefl (C ψ : Lean.Expr) : Lean.Expr :=
  let ty := mkApp (mkConst ``Option [0]) (mkApp (mkConst ``Fml) C)
  mkApp2 (mkConst ``Eq.refl [1]) ty (mkApp2 (mkConst ``Option.some [0]) (mkApp (mkConst ``Fml) C) ψ)

/-- The next line, `ψ` if it is given. -/
def nextLine (C φ ψ : Lean.Expr) : MetaM (Run × Line) := do
  let run ← runChain C φ
  let some q := run.lines.head? |
    match run.stuck, run.splice.modality with
    | true, some m => throwError "sol_chain: the line after{indentExpr φ}\n{modalityStop m}"
    | _, _ => throwError "sol_chain: no rule applies to{indentExpr φ}"
  let ψ ← instantiateMVars ψ
  if ψ.isMVar then ψ.mvarId!.assign q.fml
  else unless q.fml == ψ || (← withReducible (isDefEq q.fml ψ)) do
    notReached φ ψ run [q.fml]
  return (run, q)

/-- `A.fresh = K`, from the postconditions' `Post.noFresh`: `simp` takes the
line's variables apart (`maxIdx_append`), `decide` computes the rest. -/
def proveFresh (C A : Lean.Expr) (K : Nat) (hs : Array Lean.Expr) : TermElabM Lean.Expr := do
  let g ← mkFreshExprMVar (← mkEq (mkApp2 (mkConst ``Fml.fresh) C A) (toExpr K))
  let names := #[``Fml.fresh, ``Fml.vars, ``maxIdx, ``maxIdx_append]
  let ts : Array Lean.Term := names.map fun n => mkCIdent n
  let ts := ts ++ (← hs.mapM Term.exprToSyntax)
  let args ← ts.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
  let fail (msg : MessageData) : MessageData :=
    m!"sol_chain: cannot compute the fresh index of{indentExpr A}\n{msg}"
  let left ← try Tactic.run g.mvarId! (evalTactic (← `(tactic| simp only [$args,*] <;> decide)))
    catch
      | .error _ msg => throwError (fail msg)
      | ex => throw ex
  unless left.isEmpty do throwError (fail m!"goals left: {left}")
  let p ← instantiateMVars g
  if p.hasSyntheticSorry || p.hasExprMVar then throwError (fail m!"not closed{indentExpr p}")
  return p

/-- Under a modality `m`, that `A` steps to the line `B` the diamond and the
box runs share (`Fml.stepAt`, at the index the runs used).  It fails for a
rule that looks at `m` and leaves premises that differ only in the modality:
`fillSlots` puts them together under `m`, and the kernel would refuse the
line at the end of the declaration. -/
def checkStep (C : Lean.Expr) (sp : Splice) (A : Lean.Expr) (B : Line) : MetaM Unit := do
  let some m := sp.modality | return
  let st := mkApp3 (mkConst ``Fml.stepAt) C (toExpr B.fresh) A
  let sB := mkApp2 (mkConst ``Option.some [0]) (mkApp (mkConst ``Fml) C) B.fml
  unless ← isDefEq st sB do
    throwError "sol_chain: the line after{indentExpr A}\n{modalityStop m}"

/-- `A ~> B`, for the line `B` computed after `A`: `rfl`, or, over a
postcondition, `Fml.OneStep.ofFresh` at the index the run used.

Not yet: a step that asks a postcondition whether it has a modality
(`Line.decided` false), past the first goal of a branch once it is done,
`(c → {U} φ) ∧ ψ`.  `Fml.stepAt`'s `.and` arm reads `(c → {U} ↑φ).active`,
which is `(↑φ).active` and stuck.  It would be a lemma `φ.active = false →
(φ.and ψ).stepAt k = (ψ.stepAt k).map φ.and` (`Fml.stepAt` unfolded), its
hypothesis by `simp only [Fml.active, Bool.or_false]` and the
postconditions' `Post.inactive`, and the kernel's `rfl` for `ψ.stepAt k`:
a proof built as `proveFresh`'s is. -/
def oneStepProof (C : Lean.Expr) (sp : Splice) (A : Lean.Expr) (B : Line) :
    TermElabM Lean.Expr := do
  checkStep C sp A B
  let refl := someRefl C B.fml
  if sp.fmls.isEmpty then return refl
  unless B.decided do
    throwError "sol_chain: the step on{indentExpr A}\nasks whether a postcondition has a \
      modality left (the first goal of a branch is done): not supported yet"
  let hk ← proveFresh C A B.fresh sp.noFresh
  return mkAppN (mkConst ``Fml.OneStep.ofFresh) #[C, A, B.fml, toExpr B.fresh, hk, refl]

/-- `A ~*> Z` along the computed lines `ls`, `Z` the last, a step at a time. -/
def stepsProof (C : Lean.Expr) (sp : Splice) (A : Lean.Expr) (ls : List Line) :
    TermElabM Lean.Expr := do
  let Z := (ls.getLast?.map (·.fml)).getD A
  let rec go (A : Lean.Expr) : List Line → TermElabM Lean.Expr
    | [] => pure (mkApp2 (mkConst ``Fml.Steps.refl) C A)
    | B :: ls => do
      let s ← oneStepProof C sp A B
      pure (mkAppN (mkConst ``Fml.Steps.cons) #[C, A, B.fml, Z, s, ← go B.fml ls])
  go A ls

/-! ### Rewrite links

`~[n]~>` names a rewrite when `n` is no rule of the strategy: an update rule
of `Calculus/ChainRewrites.lean`'s table, or a Theory law, a constant whose
statement is a `Term.Theq`.  The name stands for several rewrites, which the
line before tells apart: the position on the update spine, and for a law its
instance, found in the line as `rw` finds one.  They are tried in a fixed
order (`rwCandidates`), and the label is the first that gives the line after
— or, with the line after left `_`, the first that applies.  So the next
line is computed, as for a step, and the kernel checks `r.apply φ = some ψ`
by `rfl`. -/

/-- What `~[n]~>` names past the strategy. -/
inductive RwArrow where
  /-- An update rule of the table (`rwTable`). -/
  | table (n : Lean.Name)
  /-- A Theory law: a constant whose statement is a `Term.Theq`. -/
  | law (c : Lean.Name)

/-- The update rules an arrow names, KeY's names: `sequentialToParallel`
merges, `simplifyUpdate` drops, `applySkip` and the `applyOnRigid…` apply. -/
def rwTable : List Lean.Name :=
  [`sequentialToParallel, `simplifyUpdate, `applySkip, `applyOnRigid, `applyOnRigidBox,
    `applyStorageBox]

/-- Whether the constant `c` states a `Term.Theq`, under its arguments. -/
def isLaw (c : Lean.Name) : MetaM Bool := do
  let some info := (← getEnv).find? c | return false
  forallTelescope info.type fun _ ty => return (← whnfR ty).isAppOf ``Term.Theq

/-- What `~[r]~>` names: `none` for a rule of the strategy (a `Taclet` or
`LeanTaclet` constructor, `emptyModality`), else a rewrite; any other name is
an error, and so is a name that resolves to more than one constant. -/
def rwArrow? (r : Ident) : MetaM (Option RwArrow) := do
  let n := r.getId
  let env ← getEnv
  if n == `emptyModality || env.contains (``Taclet ++ n) || env.contains (``LeanTaclet ++ n) then
    return none
  if rwTable.contains n then return some (.table n)
  let cs := ((← resolveGlobalName n).filterMap fun (c, fs) =>
    if fs.isEmpty then some c else none).eraseDups
  match cs with
  | [c] => if ← isLaw c then return some (.law c)
  | [] => pure ()
  | cs => throwError "~[{r}]~>: ambiguous, {r} may be {", ".intercalate (cs.map toString)}"
  throwError "~[{r}]~>: {r} is no rule: not a `Taclet` or `LeanTaclet` constructor, not an \
    update rule ({", ".intercalate (rwTable.map toString)}), not a Theory law (`Term.Theq`)"

/-- The number of updates in front of a line. -/
partial def spineLen (e : Lean.Expr) : MetaM Nat := do
  let e ← whnf e
  if e.isAppOfArity ``Fml.upd 4 then return (← spineLen e.appArg!) + 1 else return 0

/-- The subterms of `e` with the head of `p`, outermost and leftmost first. -/
partial def subtermsLike (p e : Lean.Expr) : Array Lean.Expr :=
  let rec go (e : Lean.Expr) (acc : Array Lean.Expr) : Array Lean.Expr :=
    let acc := if !e.hasLooseBVars && e.toHeadIndex == p.toHeadIndex &&
        e.headNumArgs == p.headNumArgs then acc.push e else acc
    match e with
    | .app f x => go x (go f acc)
    | .mdata _ e => go e acc
    | _ => acc
  go e #[]

/-- The law `c` at the subterm `e`: `(t, t', h)` when `e` is its left side,
its arguments found there and its side conditions (`hp : p.hasSeg = true`,
…) closed by `rfl` or `decide`, as `sol_rw` closes them (`solRwSide`); else
why not, if a side condition is why. -/
def lawAt (c : Lean.Name) (e : Lean.Expr) :
    TermElabM (Except (Option MessageData) (Lean.Expr × Lean.Expr × Lean.Expr)) := do
  let pf ← mkConstWithFreshMVarLevels c
  let (args, _, ty) ← forallMetaTelescope (← inferType pf)
  let ty ← whnfR (← instantiateMVars ty)
  let_expr Term.Theq _ lhs rhs := ty | return .error none
  unless ← isDefEq lhs e do return .error none
  for a in args do
    let g := a.mvarId!
    if (← g.isAssigned) || !(← isProp (← g.getType)) then continue
    let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
    let g ← g.replaceTargetDefEq ty
    let closed ← try
        pure (← Term.withoutErrToSorry <|
          Tactic.run g (evalTactic (← `(tactic| first | rfl | decide)))).isEmpty
      catch _ => pure false
    unless closed do
      return .error (some m!"the side condition{indentExpr ty}\nof {lastName c} closes by neither \
        `rfl` nor `decide`")
  let pf ← instantiateMVars (mkAppN pf args)
  let t' ← instantiateMVars rhs
  if pf.hasExprMVar || t'.hasExprMVar then return .error none
  return .ok (← instantiateMVars lhs, t', pf)

/-- The instances `(t, t', h)` of the law `c` in the line `φ`, outermost and
leftmost first (`lawAt`), and the first side condition that did not close. -/
def lawInstances (c : Lean.Name) (φ : Lean.Expr) :
    TermElabM (Array (Lean.Expr × Lean.Expr × Lean.Expr) × Option MessageData) := do
  let lhs0 ← withoutModifyingState do
    let (_, _, ty) ← forallMetaTelescope (← inferType (← mkConstWithFreshMVarLevels c))
    let ty ← whnfR (← instantiateMVars ty)
    let_expr Term.Theq _ lhs _ := ty | throwError "not a law: {c}"
    instantiateMVars lhs
  let mut out := #[]
  let mut failed := none
  for e in subtermsLike lhs0 φ do
    let s ← saveState
    let r ← try lawAt c e catch _ => pure (.error none)
    s.restore
    match r with
    | .ok i => unless out.any (·.2.2 == i.2.2) do out := out.push i
    | .error m => if failed.isNone then failed := m
  return (out, failed)

/-- The rewrites `~[r]~>` stands for on the line `φ`, in the order they are
tried, and why a law found no instance.  `sequentialToParallel`: the whole
spine merged, then fewer updates, then one pair further in; the others at
each position of the spine, outermost first.  A law: at each instance, on
the equations, then in each box update's right-hand sides when its result
cannot halt. -/
def rwCandidates (C φ : Lean.Expr) : RwArrow → TermElabM (Array Lean.Expr × Option MessageData)
  | .table n => do
    let k ← spineLen φ
    let atPos (f : Lean.Name) (is : List Nat) : Array Lean.Expr :=
      (is.map fun i => mkApp2 (mkConst f) C (toExpr i)).toArray
    let upd (r : Lean.Name) : Array Lean.Expr := ((List.range k).map fun i =>
      mkApp3 (mkConst ``LineRw.updRule) C (mkConst r) (toExpr i)).toArray
    let rs :=
      if n == `sequentialToParallel then
        atPos ``LineRw.mergeSpine ((List.range (k - 1)).reverse.map (· + 1)) ++
          atPos ``LineRw.mergeAt ((List.range (k - 1)).drop 1)
      else if n == `simplifyUpdate then
        upd ``UpdRuleName.simplifyUpdate ++ atPos ``LineRw.dropShadowed (List.range k)
      else if n == `applySkip then upd ``UpdRuleName.applySkip
      else if n == `applyOnRigid then upd ``UpdRuleName.applyOnRigid
      else if n == `applyOnRigidBox then atPos ``LineRw.applyOnRigidBox (List.range k)
      else if n == `applyStorageBox then atPos ``LineRw.applyStorageBox (List.range k)
      else #[]
    return (rs, none)
  | .law c => do
    let (is, failed) ← lawInstances c φ
    let k ← spineLen φ
    let mut out := #[]
    for (t, t', pf) in is do
      out := out.push (mkAppN (mkConst ``LineRw.law) #[C, t, t', pf])
      if ← isDefEq (mkApp2 (mkConst ``Term.total) C t') (mkConst ``Bool.true) then
        let ht ← mkEqRefl (mkConst ``Bool.true)
        for i in List.range k do
          out := out.push (mkAppN (mkConst ``LineRw.lawUpd) #[C, t, t', pf, ht, toExpr i])
    return (out, failed)

/-- Each of the rewrites `rs` on the line `φ`, computed: the line after, with
the line's modality and postconditions put back, or `none`.  Under a
modality `m` a rewrite runs at the diamond and at the box, and gives a line
only where the two agree but for `m`. -/
def rwResults (C φ : Lean.Expr) (rs : Array Lean.Expr) :
    MetaM (List (Option Lean.Expr) × Option Lean.Expr) := do
  let some n := (← whnfR C).constName?
    | throwError "sol_chain: the contract is not a named constant: {C}"
  let (φ', sp) ← (punch C φ).run {}
  let ty := mkApp (mkConst ``List [0]) (mkApp (mkConst ``Option [0]) (mkConst ``Lean.Expr))
  let list ← mkListLit (mkApp (mkConst ``LineRw) C) rs.toList
  let eval (φ : Lean.Expr) : MetaM (List (Option Lean.Expr)) :=
    unsafe evalExpr (List (Option Lean.Expr)) ty
      (mkApp4 (mkConst ``Fml.rwQuoted) C (quoteConstName n) φ list)
  let fill (m? : Option Lean.Expr) (d b : Lean.Expr) : Option Lean.Expr :=
    (fillSlots m? sp.fmls d b).toOption
  match ← modalityOf? φ' with
  | none =>
    let qs ← eval φ'
    return (if sp.fmls.isEmpty then qs else qs.map (·.bind fun q => fill none q q), none)
  | some m =>
    let ds ← eval (φ'.replaceFVar m (mkConst ``Modality.diamond))
    let bs ← eval (φ'.replaceFVar m (mkConst ``Modality.box))
    let parts := (ds.zip bs).any fun (d, b) => d.isSome != b.isSome
    return ((ds.zip bs).map fun
      | (some d, some b) => fill m d b
      | _ => none, if parts then some m else none)

/-- The rewrite `~[n]~>` names on `φ`, among `rs`, and the line after it: the
first that gives `ψ`, or, with `ψ` left `_`, the first that applies.  On a
line with a modality `m` or a postcondition `φ : Post C`, the rewrite must
compute over them (`r.apply φ = some ψ` by the kernel, on the line itself):
`simplifyUpdate`, say, asks the postcondition which variables it reads. -/
def rwSelect (C φ ψ : Lean.Expr) (n : String) (rs : Array Lean.Expr)
    (failed : Option MessageData := none) : TermElabM (Lean.Expr × Lean.Expr) := do
  let φ ← instantiateMVars φ
  let ψ ← instantiateMVars ψ
  let (qs, parts) ← rwResults C φ rs
  let mut gives := #[]
  let mut stuck := false
  for (r, q?) in rs.toList.zip qs do
    let some q := q? | continue
    if φ.hasFVar then
      let lhs := mkApp2 (mkApp (mkConst ``LineRw.apply) C) r φ
      unless ← isDefEq lhs (mkApp2 (mkConst ``Option.some [0]) (mkApp (mkConst ``Fml) C) q) do
        stuck := true
        continue
    unless ψ.isMVar || q == ψ || (← withReducible (isDefEq q ψ)) do
      gives := gives.push q
      continue
    return (r, q)
  if !gives.isEmpty then
    let ls := gives.toList.map fun q => m!"{indentExpr q}"
    throwError "~[{n}]~>: on{indentExpr φ}\nit gives{MessageData.joinSep ls ""}\nnot{indentExpr ψ}"
  if stuck then
    throwError "~[{n}]~>: on{indentExpr φ}\nit looks at the line's modality or postcondition, \
      which are not known: state the line for a concrete one"
  let note := match failed, parts with
    | some m, _ => m!"\n({m})"
    | none, some m => m!"\n(it applies under one modality only: go on after `cases {m}`)"
    | none, none => m!""
  throwError "~[{n}]~>: {n} does not apply to{indentExpr φ}{note}"

/-- The label of `φ ~[r]~> ψ` for a rewrite, `φ` known, and the line after. -/
def rwLabel (C φ ψ : Lean.Expr) (r : Ident) (a : RwArrow) : TermElabM (Lean.Expr × Lean.Expr) := do
  let (rs, failed) ← rwCandidates C (← instantiateMVars φ) a
  rwSelect C φ ψ r.getId.toString rs failed

partial def solveChain (g : MVarId) : TermElabM Unit := do
  let ty ← instantiateMVars (← g.getType)
  if ty.isAppOfArity ``Fml.RwBy 5 then
    let #[C, n, r, φ, ψ] := ty.getAppArgs | unreachable!
    let .lit (.strVal n) := n | throwError "sol_chain: the arrow's name is not known{indentExpr ty}"
    let φ ← instantiateMVars φ
    if φ.hasExprMVar then throwError "sol_chain: ~[{n}]~>: the line before it is not known{indentExpr φ}"
    let r ← instantiateMVars r
    let (r', q) ← if r.isMVar then
        let some a ← rwArrow? (mkIdent n.toName) | throwError "sol_chain: {n} is a rule of the strategy"
        rwLabel C φ ψ (mkIdent n.toName) a
      else rwSelect C φ ψ n #[r]
    unless ← isDefEq r r' do throwError "sol_chain: ~[{n}]~>: the label is not {r'}"
    unless ← isDefEq ψ q do throwError "sol_chain: ~[{n}]~>: the line after is not{indentExpr q}"
    g.assign (someRefl C q)
  else if ty.isAppOfArity ``Fml.StepBy 4 then
    let #[C, r, φ, ψ] := ty.getAppArgs | unreachable!
    let (run, q) ← nextLine C φ ψ
    if run.splice.fmls.isEmpty then
      checkStep C run.splice φ q
      let pair ← mkAppM ``Prod.mk #[← mkAppM ``Option.some #[r], ← mkAppM ``Option.some #[q.fml]]
      g.assign (← mkEqRefl pair)
    else
      let hr ← mkEqRefl (← mkAppM ``Option.some #[r])
      g.assign (mkAppN (mkConst ``Fml.StepBy.ofOneStep)
        #[C, r, φ, q.fml, hr, ← oneStepProof C run.splice φ q])
  else if ty.isAppOfArity ``Fml.OneStep 3 then
    let #[C, φ, ψ] := ty.getAppArgs | unreachable!
    let (run, q) ← nextLine C φ ψ
    g.assign (← oneStepProof C run.splice φ q)
  else if ty.isAppOfArity ``Fml.Steps 3 then
    let #[C, φ, ψ] := ty.getAppArgs | unreachable!
    let φ ← instantiateMVars φ
    let run ← runChain C φ
    let lines := run.lines.map (·.fml)
    let ψ ← instantiateMVars ψ
    let i ← if ψ.isMVar then
        ψ.mvarId!.assign ((lines.getLast?).getD φ)
        pure lines.length
      else match ← findLine φ ψ lines with
        | some i => pure i
        | none => notReached φ ψ run lines
    if run.splice.fmls.isEmpty then
      discard <| (run.lines.take i).foldlM (init := φ) fun A B => do
        checkStep C run.splice A B
        pure B.fml
      let q := if i = 0 then φ else lines[i - 1]!
      g.assign (mkAppN (mkConst ``Fml.Steps.ofRun) #[C, φ, q, toExpr i, someRefl C q])
    else
      g.assign (← stepsProof C run.splice φ (run.lines.take i))
  else
    -- a chain: split it into its links
    match_expr ← whnf ty with
    | Prod A B =>
      let a ← mkFreshExprMVar A
      let b ← mkFreshExprMVar B
      solveChain a.mvarId!
      solveChain b.mvarId!
      g.assign (← mkAppM ``Prod.mk #[a, b])
    | PLift P =>
      let p ← mkFreshExprMVar P
      solveChain p.mvarId!
      g.assign (← mkAppM ``PLift.up #[p])
    | Fml.Steps _ _ _ => solveChain (← g.replaceTargetDefEq (← whnf ty))
    | _ => throwError "sol_chain: expected `φ ~> ψ`, `φ ~[r]~> ψ` (a rule or a rewrite), `φ ~*> ψ` \
        or a chain of them{indentExpr ty}"

/-- `sol_chain`: prove `φ ~> ψ`, `φ ~[r]~> ψ`, `φ ~*> ψ` or a chain of them by
running the strategy; the kernel checks the lines it found. -/
elab "sol_chain" : tactic => withMainContext do
  solveChain (← getMainGoal)
  replaceMainGoal []

/-- `#derivation φ`: the derivation the strategy takes from `φ`, one line per
step with the rule that reached it.  The section's variables are in scope
(`variable (m : Modality) (φ : Post C)`). -/
elab "#derivation " t:term : command => Command.runTermElabM fun _ => do
  let φ ← instantiateMVars (← Term.elabTerm t none)
  Term.synthesizeSyntheticMVarsNoPostponing
  let φ ← instantiateMVars φ
  let ty ← whnf (← inferType φ)
  unless ty.isAppOfArity ``Fml 1 do throwError "#derivation: not a formula{indentExpr φ}"
  let run ← runChain ty.appArg! φ
  logInfo ((← showLines φ (run.lines.map (·.fml))) ++ stuckNote run)

end Tactic

section Elab
open Lean Elab Term Meta

/-- `rwLabel% l φ r ψ`: `l`, once `φ` is known, the label of `φ ~[r]~> ψ`
for a rewrite, unless `sol_chain` found it first.  A line before that a
tactic still has to find (a `calc` step's `_` after `by sol_chain`) leaves the
label to the step's own `sol_chain`. -/
elab "rwLabel% " l:term:max a:term:max r:ident b:term:max : term => do
  let l ← elabTerm l none
  if (← instantiateMVars l).isMVar then
    let a' ← instantiateMVars (← elabTerm a none)
    if a'.hasExprMVar then
      tryPostpone
      return l
    let some arrow ← rwArrow? r | throwError "~[{r}]~>: not a rewrite"
    let ty ← whnfR (← inferType a')
    let_expr Fml C := ty | throwError "~[{r}]~>: not a formula{indentExpr a'}"
    let (lbl, _) ← rwLabel C a' (← elabTerm b none) r arrow
    unless ← isDefEq l lbl do throwError "~[{r}]~>: the rewrite on{indentExpr a'}\nis not {l}"
  return l

/-- The label of a rewrite arrow after the line `a`: computed when `a` is
known; otherwise left to the proof, `rwLabel%` filling it once `a` is known. -/
def rwLabelOf (C a b : Lean.Expr) (r : Ident) (arrow : RwArrow) : TermElabM Lean.Expr := do
  if !(← instantiateMVars a).hasExprMVar then return (← rwLabel C a b r arrow).1
  let lty := mkApp (mkConst ``LineRw) C
  let l ← mkFreshExprMVar lty
  discard <| elabTermEnsuringType (← `(rwLabel% $(← exprToSyntax l) $(← exprToSyntax a) $r
    $(← exprToSyntax b))) lty
  return l

/-- The contract of a line, `Fml C`. -/
def lineContract (a : Lean.Expr) (r : Ident) : TermElabM Lean.Expr := do
  let ty ← whnfR (← instantiateMVars (← inferType a))
  if let some C := ty.app1? ``Fml then return C
  let C ← mkFreshExprMVar (mkConst ``Contract)
  unless ← isDefEq ty (mkApp (mkConst ``Fml) C) do throwError "~[{r}]~>: not a formula{indentExpr a}"
  return C

elab_rules : term
  | `(stepBy% $a $r $b) => do
    let a ← elabTerm a none
    let C ← lineContract a r
    let b ← elabTermEnsuringType b (mkApp (mkConst ``Fml) C)
    match ← rwArrow? r with
    | none => stepByRule C a b r
    | some arrow =>
      let l ← rwLabelOf C a b r arrow
      return mkAppN (mkConst ``Fml.RwBy) #[C, toExpr r.getId.toString, l, a, b]
  | `(link% $a $r $b) => do
    match ← rwArrow? r with
    | none => elabTerm (← `(Link.rule (rule% $a $r))) none
    | some arrow =>
      let a ← elabTerm a none
      let C ← lineContract a r
      let b ← elabTermEnsuringType b (mkApp (mkConst ``Fml) C)
      let l ← rwLabelOf C a b r arrow
      return mkApp3 (mkConst ``Link.rw) C (toExpr r.getId.toString) l

end Elab
end Chain

end Solidity
