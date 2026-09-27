import Solidity.Calculus.Notation

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
  `calc`, whose steps are these links.

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
  | .upd _ _ φ | .imp _ φ => φ.ruleAt k
  | .and φ ψ => if φ.active then φ.ruleAt k else ψ.ruleAt k
  | .modal _ [] _ => some .emptyModality
  | .modal m (s :: _) _ => some (.taclet k m s (s.step k m).premise (s.step k m).rule)
  | _ => none

/-- The rule `Fml.step` fires. -/
def Fml.rule (φ : Fml C) : Option (StepRule C) := φ.ruleAt (maxIdx φ.vars + 1)

/-- A rule fires exactly where a step is taken.

Example: on `⟨ x = 1; ⟩ x == 1` both `localValueAssign` and the step to
`{ x := 1 } ⟨⟩ x == 1` exist; on `x == 1` neither does. -/
theorem Fml.ruleAt_isSome {k : Nat} :
    ∀ φ : Fml C, (φ.ruleAt k).isSome = (φ.stepAt k).isSome
  | .upd _ _ φ | .imp _ φ => by simp [Fml.ruleAt, Fml.stepAt, Fml.ruleAt_isSome φ]
  | .and φ ψ => by
    simp only [Fml.ruleAt, Fml.stepAt]
    split <;> simp [Fml.ruleAt_isSome]
  | .modal _ [] _ | .modal _ (_ :: _) _ => rfl
  | .tt | .eq .. | .not _ => rfl

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

/-- The arrows of a chain. -/
inductive Link (C : Contract) : Type where
  /-- `~>` -/
  | one
  /-- `~*>` -/
  | many
  /-- `~[r]~>` -/
  | rule (r : StepRule C)

/-- What an arrow says about the two lines it joins. -/
@[reducible] def Link.Rel : Link C → Fml C → Fml C → Type
  | .one => fun φ ψ => PLift (Fml.OneStep φ ψ)
  | .many => Fml.Steps
  | .rule r => fun φ ψ => PLift (Fml.StepBy r φ ψ)

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

/-- A derivation, with the auxiliary lemmas the elaborator abstracted it
into (a constructor applied to its side conditions' proofs) unfolded, down
to a constructor, under the `Rule` that wraps it. -/
partial def tacletHead (d : Lean.Expr) : MetaM Lean.Expr := do
  let d ← whnfCore d
  if d.isAppOfArity ``Rule.key 6 || d.isAppOfArity ``Rule.lean 6 then
    return mkAppN d.getAppFn (d.getAppArgs.set! 5 (← tacletHead d.appArg!))
  let .const c us := d.getAppFn | return d
  if isRuleCtor c then return d
  match ← getConstInfo c with
  | info@(.thmInfo _) => tacletHead ((← instantiateValueLevelParams info us).beta d.getAppArgs)
  | _ => return d

/-- The constructor a rule's derivation is, if it is one. -/
def ruleCtor? (d : Lean.Expr) : Option Lean.Name := do
  let d := if d.isAppOfArity ``Rule.key 6 || d.isAppOfArity ``Rule.lean 6 then d.appArg! else d
  let c ← d.getAppFn.constName?
  if isRuleCtor c then some c else none

/-- The derivation a `Step` carries, reduced to a constructor. -/
partial def tacletOf (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← whnf e
  unless e.isAppOfArity ``Step.mk 6 do throwError "not a step:{indentExpr e}"
  let d ← whnfCore (e.getArg! 5)
  if d.isAppOf ``Step.rule then tacletOf d.appArg! else tacletHead d

/-- The rule the strategy fires on the formula `φ`, as a `StepRule` term
whose derivation is a constructor, and that constructor's name. -/
def ruleOfLine (φ : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Name)) := do
  let r ← whnf (← mkAppM ``Fml.rule #[φ])
  unless r.isAppOfArity ``Option.some 2 do return none
  let r ← whnf r.appArg!
  if r.isAppOfArity ``StepRule.emptyModality 1 then return some (r, `emptyModality)
  unless r.isAppOfArity ``StepRule.taclet 6 do return none
  let #[C, k, m, s, p, _] := r.getAppArgs | return none
  -- the derivation in `Fml.ruleAt` is an auxiliary lemma: take it from `Stmt.step` again
  let d' ← tacletOf (mkAppN (mkConst ``Stmt.step) #[C, k, m, s])
  let some c := ruleCtor? d' | return some (r, `taclet)
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
  let some c := ruleCtor? (← tacletOf (mkAppN (mkConst ``Stmt.step) #[C, k, m, s]))
    | return none
  return some (lastName c)

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

/-- `stepBy% φ r ψ`: `φ ~[r]~> ψ`, with `φ` elaborated once.  In a `calc` step
`φ` is not known yet: the label is left to the proof, and checked after it. -/
elab "stepBy% " a:term:max r:ident b:term:max : term => do
  let a ← elabTerm a none
  let ty ← whnfR (← instantiateMVars (← inferType a))
  let_expr Fml C := ty | throwError "~[{r}]~>: not a formula{indentExpr a}"
  let b ← elabTermEnsuringType b ty
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
        pure (← `(Link.rule (rule% ($prev) $r)), ← `(stepBy% ($prev) $r ($b)))
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
  have := Fml.ruleAt_isSome (k := maxIdx φ.vars + 1) φ
  unfold Fml.OneStep Fml.step at h
  rw [h] at this
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 this
  exact ⟨r, by simp only [Fml.StepBy, Fml.rule, hr, Fml.step, h]⟩

/-- A step as a derivation of one line; the rule label is dropped:
`⟨ x = 1; ⟩ x == 1 ~[localValueAssign]~> …` as `⟨ x = 1; ⟩ x == 1 ~*> …`. -/
def Fml.StepBy.steps {r : StepRule C} {φ ψ : Fml C} (h : Fml.StepBy r φ ψ) : φ ~*> ψ :=
  .single h.oneStep

/-- A chain, composed: from its first line to its last. -/
def Fml.Via.steps : {φ : Fml C} → {ws : List (Link C × Fml C)} → Fml.Via φ ws →
    φ ~*> Fml.Via.last φ ws
  | _, [], _ => .refl _
  | _, [(.one, _)], ⟨s⟩ => .single s
  | _, [(.many, _)], c => c
  | _, [(.rule _, _)], ⟨h⟩ => h.steps
  | _, (.one, _) :: _ :: _, (⟨s⟩, v) => .cons s v.steps
  | _, (.many, _) :: _ :: _, (c, v) => c.trans v.steps
  | _, (.rule _, _) :: _ :: _, (⟨h⟩, v) => .cons h.oneStep v.steps

/-! `calc` chains `~>`, `~*>` and `~[r]~>`; the result is a derivation `~*>`. -/

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
  v.steps.valid h

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

/-! ## `sol_chain` and `#derivation`

On a goal `φ ~> ψ`, `φ ~[r]~> ψ`, `φ ~*> ψ` or a chain, `sol_chain` runs the
strategy on `φ` as compiled code (`φ` a closed formula of a named contract),
finds `ψ` among the lines, and closes the goal with `rfl`, or
`Steps.ofRun n rfl`: the kernel checks it by computing the steps itself. -/

/-- The lines of the derivation of `φ`, at most `n` of them, quoted. -/
def Fml.linesQuoted (c : Lean.Expr) : Nat → Fml C → List Lean.Expr
  | 0, _ => []
  | n + 1, φ => match φ.step with
    | some ψ => ψ.quote c :: Fml.linesQuoted c n ψ
    | none => []

namespace Chain
section Tactic
open Lean Elab Tactic Meta

/-- The lines of the derivation of the closed formula `φ`, computed. -/
def chainLines (C φ : Lean.Expr) : MetaM (List Lean.Expr) := do
  let some n := (← whnfR C).constName?
    | throwError "sol_chain: the contract is not a named constant: {C}"
  if φ.hasFVar || φ.hasMVar then
    throwError "sol_chain: the formula is not closed; give the number of steps instead: \
      `Fml.Steps.ofRun n rfl`{indentExpr φ}"
  let c := mkApp2 (mkConst ``Lean.mkConst) (toExpr n)
    (mkApp (mkConst ``List.nil [0]) (mkConst ``Lean.Level))
  let ty ← mkAppM ``List #[mkConst ``Lean.Expr]
  unsafe evalExpr (List Lean.Expr) ty
    (mkApp4 (mkConst ``Fml.linesQuoted) C c (toExpr 200) φ)

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

def notReached (φ ψ : Lean.Expr) (lines : List Lean.Expr) : MetaM α := do
  throwError "sol_chain: the derivation of{indentExpr φ}\ndoes not reach{indentExpr ψ}\n\
    Its lines:\n{← showLines φ lines}"

/-- `some ψ = some ψ`, the proof of `φ.step = some ψ` and `φ.run n = some ψ`. -/
def someRefl (C ψ : Lean.Expr) : Lean.Expr :=
  let ty := mkApp (mkConst ``Option [0]) (mkApp (mkConst ``Fml) C)
  mkApp2 (mkConst ``Eq.refl [1]) ty (mkApp2 (mkConst ``Option.some [0]) (mkApp (mkConst ``Fml) C) ψ)

/-- The next line, `ψ` if it is given. -/
def nextLine (C φ ψ : Lean.Expr) : MetaM Lean.Expr := do
  let lines ← chainLines C (← instantiateMVars φ)
  let some q := lines.head? | throwError "sol_chain: no rule applies to{indentExpr φ}"
  let ψ ← instantiateMVars ψ
  if ψ.isMVar then ψ.mvarId!.assign q
  else unless q == ψ || (← withReducible (isDefEq q ψ)) do notReached φ ψ (lines.take 1)
  return q

partial def solveChain (g : MVarId) : MetaM Unit := do
  let ty ← instantiateMVars (← g.getType)
  if ty.isAppOfArity ``Fml.StepBy 4 then
    let #[C, r, φ, ψ] := ty.getAppArgs | unreachable!
    let q ← nextLine C φ ψ
    let pair ← mkAppM ``Prod.mk #[← mkAppM ``Option.some #[r], ← mkAppM ``Option.some #[q]]
    g.assign (← mkEqRefl pair)
  else if ty.isAppOfArity ``Fml.OneStep 3 then
    let #[C, φ, ψ] := ty.getAppArgs | unreachable!
    let q ← nextLine C φ ψ
    g.assign (someRefl C q)
  else if ty.isAppOfArity ``Fml.Steps 3 then
    let #[C, φ, ψ] := ty.getAppArgs | unreachable!
    let φ ← instantiateMVars φ
    let lines ← chainLines C φ
    let ψ ← instantiateMVars ψ
    let i ← if ψ.isMVar then
        ψ.mvarId!.assign ((lines.getLast?).getD φ)
        pure lines.length
      else match ← findLine φ ψ lines with
        | some i => pure i
        | none => notReached φ ψ lines
    let q := if i = 0 then φ else lines[i - 1]!
    g.assign (mkAppN (mkConst ``Fml.Steps.ofRun) #[C, φ, q, toExpr i, someRefl C q])
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
    | _ => throwError "sol_chain: expected `φ ~> ψ`, `φ ~[r]~> ψ`, `φ ~*> ψ` or a chain of them\
        {indentExpr ty}"

/-- `sol_chain`: prove `φ ~> ψ`, `φ ~[r]~> ψ`, `φ ~*> ψ` or a chain of them by
running the strategy; the kernel checks the lines it found. -/
elab "sol_chain" : tactic => liftMetaTactic fun g => do solveChain g; pure []

/-- `#derivation φ`: the derivation the strategy takes from `φ`, one line per
step with the rule that reached it. -/
elab "#derivation " t:term : command => Command.liftTermElabM do
  let φ ← instantiateMVars (← Term.elabTerm t none)
  Term.synthesizeSyntheticMVarsNoPostponing
  let φ ← instantiateMVars φ
  let ty ← whnf (← inferType φ)
  unless ty.isAppOfArity ``Fml 1 do throwError "#derivation: not a formula{indentExpr φ}"
  logInfo (← showLines φ (← chainLines ty.appArg! φ))

end Tactic
end Chain

end Solidity
