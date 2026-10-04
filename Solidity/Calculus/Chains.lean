import Solidity.Calculus.Notation
import Solidity.Calculus.ChainRewrites
import Solidity.Calculus.ChainBranches
import Solidity.Calculus.Literals

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
  wherever `ψ` holds, `φ` does, what a chain with a rewrite composes to;
* `φ ~=> ψ` — a rewrite the arrow does not name (`Fml.RwAny`): the line
  after picks it, `sol_chain` trying the update rules and then the laws
  (`rwLaws`) until one gives it.  It is found, not determined: the same line
  may leave by several rewrites, as the printed order and KeY's part after
  the merge (`Examples/ChainRewrites.lean`).

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
either modality — a branch's cover too, `⟨[ revert(); ]⟩ false ∨ c ∨ c'`
(`Premise.coverFml`) — so `sol_chain` runs such a line as the diamond and
as the box and keeps the lines the two share, through branches,
up to the first `revert();` the strategy steps: `revertBox` leaves `true`
and `revertDiamond` `false`, as the calculus's traces part at
`⟨[ revert(); ]⟩ φ`.  That line ends the chain under `m`; after `cases m`
it goes on.  `φ` stands in a slot
(`Fml.slot`) while the strategy runs; `rfl` cannot compute a fresh index
over it, so a step is proved at the index the run found
(`Fml.OneStep.ofFresh`), the index by `simp` from `Post.noFresh`, the step
by the kernel — and, past the first goal of a branch once it is done, where
the step asks `φ` whether a modality is left, along the connectives to the
statement that fires, from `Post.inactive` (`Chain.stepAtProof`).  Such a
step is `by sol_chain`, not `rfl`.
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
  | .upd _ _ φ | .imp _ φ | .havoc φ | .all _ _ φ => φ.ruleAt k
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
  | .upd _ _ φ | .imp _ φ | .havoc φ | .all _ _ φ => by
    simp [Fml.ruleAt, Fml.stepAt, Fml.ruleAt_isSome φ]
  | .and φ ψ => by
    simp only [Fml.ruleAt, Fml.stepAt]
    split <;> simp [Fml.ruleAt_isSome]
  | .modal _ [] _ | .modal _ (_ :: _) _ => rfl
  | .tt | .eq .. | .defined _ | .not _ => rfl

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

/-- A postcondition names no fresh variable: `simplifyUpdate` over it drops
a capture of the rules (`LineRw.simplifyFresh`). -/
theorem Post.freshVars_eq_nil (φ : Post C) : φ.fml.freshVars = [] := by
  rw [Fml.freshVars_eq, List.filter_eq_nil_iff]
  intro x hx
  have : x.idx ≤ 0 := φ.noFresh ▸ le_maxIdx hx
  simp only [bne_iff_ne, ne_eq, Decidable.not_not]
  omega

instance : Coe (Post C) (Fml C) := ⟨Post.fml⟩

/-! ## Past a finished goal

Past the first goal of a branch, once it is done, `Fml.stepAt` and
`Fml.ruleAt` ask the goal whether a modality is left, and over a
postcondition only `Post.inactive` knows: the step is then taken apart, a
lemma per connective on the way to the statement that fires
(`Chain.stepAtProof`, `Chain.ruleFocus`). -/

theorem Fml.stepAt_upd_of {k : Nat} {m : Modality} {U : Upd C} {φ ψ : Fml C}
    (h : φ.stepAt k = some ψ) : (Fml.upd m U φ).stepAt k = some (.upd m U ψ) := by
  simp only [Fml.stepAt, h, Option.map_some]

theorem Fml.stepAt_imp_of {k : Nat} {a φ ψ : Fml C}
    (h : φ.stepAt k = some ψ) : (Fml.imp a φ).stepAt k = some (.imp a ψ) := by
  simp only [Fml.stepAt, h, Option.map_some]

theorem Fml.stepAt_havoc_of {k : Nat} {φ ψ : Fml C}
    (h : φ.stepAt k = some ψ) : (Fml.havoc φ).stepAt k = some (.havoc ψ) := by
  simp only [Fml.stepAt, h, Option.map_some]

theorem Fml.stepAt_all_of {k : Nat} {x : Var} {p : PrimTy} {φ ψ : Fml C}
    (h : φ.stepAt k = some ψ) : (Fml.all x p φ).stepAt k = some (.all x p ψ) := by
  simp only [Fml.stepAt, h, Option.map_some]

/-- The first goal steps while it is active. -/
theorem Fml.stepAt_and_left {k : Nat} {φ ψ φ' : Fml C} (ha : φ.active = true)
    (h : φ.stepAt k = some φ') : (Fml.and φ ψ).stepAt k = some (.and φ' ψ) := by
  simp only [Fml.stepAt, ha, h, if_true, Option.map_some]

/-- Once it is done, the second: `(c → {U} φ) ∧ (¬c → ⟨ revert(); ⟩ φ)`. -/
theorem Fml.stepAt_and_right {k : Nat} {φ ψ ψ' : Fml C} (ha : φ.active = false)
    (h : ψ.stepAt k = some ψ') : (Fml.and φ ψ).stepAt k = some (.and φ ψ') := by
  simp only [Fml.stepAt, ha, h, Bool.false_eq_true, if_false, Option.map_some]

theorem Fml.active_and_false {φ ψ : Fml C} (h : φ.active = false) (h' : ψ.active = false) :
    (Fml.and φ ψ).active = false := by
  simp only [Fml.active, h, h', Bool.or_self]

theorem Fml.active_and_true_left {φ ψ : Fml C} (h : φ.active = true) :
    (Fml.and φ ψ).active = true := by
  simp only [Fml.active, h, Bool.true_or]

theorem Fml.active_and_true_right {φ ψ : Fml C} (h : ψ.active = true) :
    (Fml.and φ ψ).active = true := by
  simp only [Fml.active, h, Bool.or_true]

theorem Fml.ruleAt_and_left {k : Nat} {φ ψ : Fml C} (ha : φ.active = true) :
    (Fml.and φ ψ).ruleAt k = φ.ruleAt k := by
  simp only [Fml.ruleAt, ha, if_true]

theorem Fml.ruleAt_and_right {k : Nat} {φ ψ : Fml C} (ha : φ.active = false) :
    (Fml.and φ ψ).ruleAt k = ψ.ruleAt k := by
  simp only [Fml.ruleAt, ha, Bool.false_eq_true, if_false]

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

/-- `φ ~=> ψ` past the strategy: some rewrite of `Calculus/ChainRewrites.lean`,
an update rule or a Theory law, turns `φ` into `ψ`.  The arrow names none:
the line after picks it (`sol_chain` searches for it). -/
def Fml.RwAny (φ ψ : Fml C) : Prop := ∃ r : LineRw C, r.apply φ = some ψ

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
  /-- `~=>`: a rewrite the line after picks -/
  | rwAny

/-- What an arrow says about the two lines it joins. -/
@[reducible] def Link.Rel : Link C → Fml C → Fml C → Type
  | .one => fun φ ψ => PLift (Fml.OneStep φ ψ)
  | .many => Fml.Steps
  | .rule r => fun φ ψ => PLift (Fml.StepBy r φ ψ)
  | .rw n r => fun φ ψ => PLift (Fml.RwBy n r φ ψ)
  | .rwAny => fun φ ψ => PLift (Fml.RwAny φ ψ)

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

/-- Whether a quoted line holds a postcondition `↑φ`. -/
def hasPost (e : Lean.Expr) : Bool := (e.find? (·.isAppOfArity ``Post.fml 2)).isSome

/-- Whether `Fml.active` and `Fml.stepAt` look through the head of `e` into
a formula below it: an update, a precondition, a havoc, a quantified local
or the goals of a branch.  On any other constructor they answer without looking at what is
below it (a `⟨ P ⟩ ↑φ` is active whatever `φ` is). -/
def isConnective (e : Lean.Expr) : Bool :=
  e.isAppOfArity ``Fml.upd 4 || e.isAppOfArity ``Fml.imp 3 || e.isAppOfArity ``Fml.havoc 2 ||
    e.isAppOfArity ``Fml.all 4 || e.isAppOfArity ``Fml.and 3

/-- `e.active = b`: the postconditions' `Post.inactive`, put together along
the connectives `Fml.active` looks through; the kernel's `rfl` where no
postcondition is left below one.  `none` when that is not how it goes. -/
partial def activeProof (C e : Lean.Expr) (b : Bool) : MetaM (Option Lean.Expr) := do
  let e := e.consumeMData
  let goal := mkApp2 (mkConst ``Fml.active) C e
  let ty ← mkEq goal (toExpr b)
  if e.isAppOfArity ``Post.fml 2 then
    return if b then none else some (mkApp2 (mkConst ``Post.inactive) (e.getArg! 0) (e.getArg! 1))
  if !isConnective e || !hasPost e then
    unless ← isDefEq goal (toExpr b) do return none
    return some (← mkExpectedTypeHint (← mkEqRefl (toExpr b)) ty)
  let a := e.getAppArgs
  if e.isAppOfArity ``Fml.upd 4 || e.isAppOfArity ``Fml.imp 3 || e.isAppOfArity ``Fml.havoc 2 ||
      e.isAppOfArity ``Fml.all 4 then
    let some h ← activeProof C a.back! b | return none
    return some (← mkExpectedTypeHint h ty)
  if !b then
    let some h ← activeProof C a[1]! false | return none
    let some h' ← activeProof C a[2]! false | return none
    return some (mkAppN (mkConst ``Fml.active_and_false) #[C, a[1]!, a[2]!, h, h'])
  if let some h ← activeProof C a[1]! true then
    return some (mkAppN (mkConst ``Fml.active_and_true_left) #[C, a[1]!, a[2]!, h])
  let some h ← activeProof C a[2]! true | return none
  return some (mkAppN (mkConst ``Fml.active_and_true_right) #[C, a[1]!, a[2]!, h])

/-- The goal of `φ` the strategy steps in, and `φ.ruleAt k = ψ.ruleAt k` for
it: through the connectives `Fml.ruleAt` looks through, past a goal that is
done (`Fml.ruleAt_and_right`, its `Post.inactive` from `activeProof`). -/
partial def ruleFocus (C k φ : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let φ := φ.consumeMData
  let here : MetaM (Lean.Expr × Lean.Expr) := do
    return (φ, ← mkEqRefl (mkApp3 (mkConst ``Fml.ruleAt) C k φ))
  unless hasPost φ do return ← here
  let a := φ.getAppArgs
  let into (ψ : Lean.Expr) (h? : Option Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
    let (χ, h) ← ruleFocus C k ψ
    let h ← match h? with
      | some h' => mkEqTrans h' h
      | none => mkExpectedTypeHint h (← mkEq (mkApp3 (mkConst ``Fml.ruleAt) C k φ)
          (mkApp3 (mkConst ``Fml.ruleAt) C k χ))
    return (χ, h)
  if φ.isAppOfArity ``Fml.upd 4 || φ.isAppOfArity ``Fml.imp 3 || φ.isAppOfArity ``Fml.havoc 2 ||
      φ.isAppOfArity ``Fml.all 4 then
    return ← into a.back! none
  if φ.isAppOfArity ``Fml.and 3 then
    if let some ha ← activeProof C a[1]! false then
      return ← into a[2]! (mkAppN (mkConst ``Fml.ruleAt_and_right) #[C, k, a[1]!, a[2]!, ha])
    if let some ha ← activeProof C a[1]! true then
      return ← into a[1]! (mkAppN (mkConst ``Fml.ruleAt_and_left) #[C, k, a[1]!, a[2]!, ha])
  here

/-- The rule the strategy fires on the formula `φ`, as a `StepRule` term
whose derivation is a constructor, and that constructor's name. -/
def ruleOfLine (φ : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Name)) := do
  let r ← whnf (← mkAppM ``Fml.rule #[φ])
  let r ← if r.isAppOfArity ``Option.some 2 || !hasPost φ then pure r else do
    -- past a goal that is done: the goal it steps in
    let C := (← whnfR (← inferType φ)).appArg!
    let k := mkApp2 (mkConst ``Fml.fresh) C φ
    whnf (mkApp3 (mkConst ``Fml.ruleAt) C k (← ruleFocus C k φ).1)
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
syntax "~=> " : chain_arrow
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
      | `(chain_arrow| ~=>) => pure (← `(Link.rwAny), app ``Fml.RwAny #[prev, b])
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

/-- A line of a chain: `dl{ φ }`, with its `where` clause, or Lean's own
printing. -/
def ppLine (e : Lean.Expr) : MetaM Lean.Term := do
  let φ ← ppFml e
  if isEscape φ then escapeTerm e else `(dl{ $(← withDecls e φ):dl_fml })

/-- The arrow a `Link` stands for. -/
def arrowOf (l : Lean.Expr) : MetaM (TSyntax `chain_arrow) := do
  let l ← whnfR (← instantiateMVars l)
  if l.isAppOfArity ``Link.one 1 then `(chain_arrow| ~>)
  else if l.isAppOfArity ``Link.many 1 then `(chain_arrow| ~*>)
  else if l.isAppOfArity ``Link.rule 2 then
    let some n ← ruleName? l.appArg! | failure
    `(chain_arrow| ~[$(mkIdent n):ident]~>)
  else if l.isAppOfArity ``Link.rwAny 1 then `(chain_arrow| ~=>)
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

/-- `Fml.RwAny φ ψ`: `φ ~=> ψ`. -/
@[delab app.Solidity.Fml.RwAny]
def delabRwAny : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 3)
  return chainNode (← withNaryArg 1 delab) #[(← `(chain_arrow| ~=>), ← withNaryArg 2 delab)]

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

/-- Some rewrite is sound: whichever one the line after picked. -/
theorem Fml.RwAny.sound {φ ψ : Fml C} (h : Fml.RwAny φ ψ) : φ ~~> ψ :=
  let ⟨r, hr⟩ := h
  r.sound hr

/-- A chain is sound state by state: where its last line holds, its first
line holds, whatever its arrows. -/
theorem Fml.Via.sound : {φ : Fml C} → {ws : List (Link C × Fml C)} → Fml.Via φ ws →
    φ ~~> Fml.Via.last φ ws
  | _, [], _ => fun _ h => h
  | _, [(.one, _)], ⟨s⟩ => s.sound
  | _, [(.many, _)], c => Fml.Steps.sound c
  | _, [(.rule _, _)], ⟨h⟩ => h.oneStep.sound
  | _, [(.rw _ _, _)], ⟨h⟩ => h.sound
  | _, [(.rwAny, _)], ⟨h⟩ => h.sound
  | _, (.one, _) :: _ :: _, (⟨s⟩, v) => fun σ h => s.sound σ (Fml.Via.sound v σ h)
  | _, (.many, _) :: _ :: _, (c, v) => fun σ h => Fml.Steps.sound c σ (Fml.Via.sound v σ h)
  | _, (.rule _, _) :: _ :: _, (⟨s⟩, v) => fun σ h => s.oneStep.sound σ (Fml.Via.sound v σ h)
  | _, (.rw _ _, _) :: _ :: _, (⟨s⟩, v) => fun σ h => s.sound σ (Fml.Via.sound v σ h)
  | _, (.rwAny, _) :: _ :: _, (⟨s⟩, v) => fun σ h => s.sound σ (Fml.Via.sound v σ h)

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

Example: the chain `⟨ alice.age = ageVal; ⟩ … ~[storageFieldWriteSave]~> … ~[emptyModality]~> …`
of `Examples/Chains/Storage.lean`'s `AgeWrite.chain` proves its first line from its last. -/
theorem Fml.Via.valid {φ : Fml C} {ws : List (Link C × Fml C)} (v : Fml.Via φ ws)
    (h : ⊨ Fml.Via.last φ ws) : ⊨ φ :=
  fun σ => v.sound σ (h σ)

/-- A chain with rewrites is a proof: to prove its first line, prove its last.

Example: `BalanceWrite.chain .box φ` of `Examples/Chains/Storage.lean`, down to the
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
instance : Fml.SoundRel (@Fml.RwAny C) := ⟨fun h => h.sound⟩
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

Example: any two two-step derivations of `alice.age = ageVal;`
are `AgeWrite.chain` of `Examples/Chains/Storage.lean`. -/
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

Example: every derivation from `⟨ alice.age = ageVal; ⟩ …` to its
line with its write is `AgeWrite.chain` of `Examples/Chains/Storage.lean`. -/
theorem Fml.Steps.eq_of_measure (μ : Fml C → Nat) (hμ : ∀ {φ ψ : Fml C}, φ ~> ψ → μ ψ < μ φ) :
    {φ ψ : Fml C} → (c d : φ ~*> ψ) → c = d
  | _, _, .refl _, .refl _ => rfl
  | _, _, .refl _, .cons s c | _, _, .cons s c, .refl _ =>
    absurd (hμ s) (Nat.not_lt.2 (c.measure_le μ hμ))
  | _, _, .cons (ψ := ψ₁) s c, .cons (ψ := ψ₂) s' c' => by
    obtain rfl : ψ₁ = ψ₂ := s.unique s'
    rw [Fml.Steps.eq_of_measure μ hμ c c']

/-! ## A step over a postcondition -/

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
  | .upd _ _ φ | .imp _ φ | .havoc φ | .all _ _ φ => φ.activeOpen
  | .and φ ψ => match φ.activeOpen with
    | some false => ψ.activeOpen
    | r => r
  | .modal .. => some true
  | φ => if φ.isSlot then none else some false

/-- Whether the step on `φ` is taken without asking a slot whether it has a
modality: past the first goal of a branch, once it is done, it asks. -/
def Fml.stepOpenOk : Fml C → Bool
  | .upd _ _ φ | .imp _ φ | .havoc φ | .all _ _ φ => φ.stepOpenOk
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
def Fml.rwQuoted (c : Lean.Expr) (φ : Fml C) (rs : List (Fml C → Option (Fml C))) :
    List (Option Lean.Expr) :=
  rs.map fun r => (r φ).map (Fml.quote c)

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
under `m` — up to a revert, the one rule that looks at it. -/
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
  m!"depends on the modality {m}, through a `revert();` (`revertBox`, `revertDiamond`): \
    go on after `cases {m}`"

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

/-- `A.stepAt k = some B`, where the step asks a postcondition whether it has
a modality left: taken apart along the path to the statement that fires
(`Fml.stepAt_and_right` past a goal that is done, its `Post.inactive` from
`activeProof`), the kernel's `rfl` from there. -/
partial def stepAtProof (C : Lean.Expr) (sp : Splice) (k : Nat) (A B : Lean.Expr) :
    MetaM Lean.Expr := do
  let A := A.consumeMData
  let B := B.consumeMData
  let kE := toExpr k
  let leaf : MetaM Lean.Expr := do
    let st := mkApp3 (mkConst ``Fml.stepAt) C kE A
    unless ← isDefEq st (mkApp2 (mkConst ``Option.some [0]) (mkApp (mkConst ``Fml) C) B) do
      match sp.modality with
      | some m => throwError "sol_chain: the line after{indentExpr A}\n{modalityStop m}"
      | none => throwError "sol_chain: the step after{indentExpr A}\nasks a postcondition \
          whether it has a modality left, along a path the step is not taken apart on"
    return someRefl C B
  unless hasPost A do return ← leaf
  let a := A.getAppArgs
  let b := B.getAppArgs
  if A.isAppOfArity ``Fml.upd 4 && B.isAppOfArity ``Fml.upd 4 then
    return mkAppN (mkConst ``Fml.stepAt_upd_of)
      #[C, kE, a[1]!, a[2]!, a[3]!, b[3]!, ← stepAtProof C sp k a[3]! b[3]!]
  if A.isAppOfArity ``Fml.imp 3 && B.isAppOfArity ``Fml.imp 3 then
    return mkAppN (mkConst ``Fml.stepAt_imp_of)
      #[C, kE, a[1]!, a[2]!, b[2]!, ← stepAtProof C sp k a[2]! b[2]!]
  if A.isAppOfArity ``Fml.havoc 2 && B.isAppOfArity ``Fml.havoc 2 then
    return mkAppN (mkConst ``Fml.stepAt_havoc_of) #[C, kE, a[1]!, b[1]!, ← stepAtProof C sp k a[1]! b[1]!]
  if A.isAppOfArity ``Fml.all 4 && B.isAppOfArity ``Fml.all 4 then
    return mkAppN (mkConst ``Fml.stepAt_all_of)
      #[C, kE, a[1]!, a[2]!, a[3]!, b[3]!, ← stepAtProof C sp k a[3]! b[3]!]
  if A.isAppOfArity ``Fml.and 3 && B.isAppOfArity ``Fml.and 3 then
    if let some ha ← activeProof C a[1]! false then
      return mkAppN (mkConst ``Fml.stepAt_and_right)
        #[C, kE, a[1]!, a[2]!, b[2]!, ha, ← stepAtProof C sp k a[2]! b[2]!]
    if let some ha ← activeProof C a[1]! true then
      return mkAppN (mkConst ``Fml.stepAt_and_left)
        #[C, kE, a[1]!, a[2]!, b[1]!, ha, ← stepAtProof C sp k a[1]! b[1]!]
  leaf

/-- `A ~> B`, for the line `B` computed after `A`: `rfl`, or, over a
postcondition, `Fml.OneStep.ofFresh` at the index the run used, the step by
the kernel's `rfl` — or by `stepAtProof`, where it asks a postcondition
whether it has a modality left (`Line.decided` false): past the first goal of
a branch once it is done, `(c → {U} φ) ∧ (¬c → ⟨ revert(); ⟩ φ)`, whose
`.and` arm reads `(↑φ).active`. -/
def oneStepProof (C : Lean.Expr) (sp : Splice) (A : Lean.Expr) (B : Line) :
    TermElabM Lean.Expr := do
  if sp.fmls.isEmpty then
    checkStep C sp A B
    return someRefl C B.fml
  let h ← if B.decided then do checkStep C sp A B; pure (someRefl C B.fml)
    else stepAtProof C sp B.fresh A B.fml
  let hk ← proveFresh C A B.fresh sp.noFresh
  return mkAppN (mkConst ``Fml.OneStep.ofFresh) #[C, A, B.fml, toExpr B.fresh, hk, h]

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
of `Calculus/ChainRewrites.lean`'s table, or a law: a term taclet
(`TermTaclet`, `Calculus/TermTaclets.lean`), a law of a memory read
(`EvalLaw`, `Calculus/ChainRewrites.lean`), or a constant whose statement is
one.  The name stands for several rewrites, which the
line before tells apart: the position on the update spine, and for a law its
instance, found in the line as `rw` finds one.  They are tried in a fixed
order (`rwCandidates`), and the label is the first that gives the line after
— or, with the line after left `_`, the first that applies.  So the next
line is computed, as for a step, and the kernel checks `r.apply φ = some ψ`
by `rfl` — or, where the rewrite asks a postcondition `φ : Post C` what it
reads (`LineRw.simplifyFresh`), `sol_chain` proves it from `Post.noFresh`
(`proveRw`), as it proves a step's fresh index (`proveFresh`). -/

/-- What `~[n]~>` names past the strategy. -/
inductive RwArrow where
  /-- An update rule of the table (`rwTable`). -/
  | table (n : Lean.Name)
  /-- A law: a term taclet, or a constant whose statement is one. -/
  | law (c : Lean.Name)
  /-- A law of a memory read (`EvalLaw`), or a constant whose statement is one. -/
  | evalLaw (c : Lean.Name)
  /-- A literal law (`LitLaw`), or a constant whose statement is one. -/
  | litLaw (c : Lean.Name)

/-- The update rules an arrow names, KeY's names: `sequentialToParallel`
merges, `simplifyUpdate` drops, `applySkip` and the `applyOnRigid…` apply,
`concrete` folds the literal connectives. -/
def rwTable : List Lean.Name :=
  [`sequentialToParallel, `simplifyUpdate, `applySkip, `applyOnRigid, `applyOnRigidBox,
    `applyStorageBox, `concrete]

/-- The kind of law the constant `c` states under its arguments:
`TermTaclet`, `EvalLaw`, `LitLaw`, or none. -/
def lawKind? (c : Lean.Name) : MetaM (Option Lean.Name) := do
  let some info := (← getEnv).find? c | return none
  forallTelescope info.type fun _ ty => do
    let ty ← whnfR ty
    if ty.isAppOf ``TermTaclet then return some ``TermTaclet
    if ty.isAppOf ``EvalLaw then return some ``EvalLaw
    if ty.isAppOf ``LitLaw then return some ``LitLaw
    return none

/-- Whether the constant `c` states a `TermTaclet`, an `EvalLaw` or a
`LitLaw`, under its arguments. -/
def isLaw (c : Lean.Name) : MetaM Bool := return (← lawKind? c).isSome

/-- The two sides of a law's statement, `TermTaclet C t t'`, `EvalLaw C u t t'`
or `LitLaw C t t'`. -/
def lawSides? (ty : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  if ty.isAppOfArity ``TermTaclet 3 || ty.isAppOfArity ``LitLaw 3 then
    let args := ty.getAppArgs
    some (args[1]!, args[2]!)
  else if ty.isAppOfArity ``EvalLaw 4 then
    let args := ty.getAppArgs
    some (args[2]!, args[3]!)
  else none

/-- The arrow for the law `c` of kind `k`. -/
def RwArrow.ofLaw (k c : Lean.Name) : RwArrow :=
  if k == ``EvalLaw then .evalLaw c else if k == ``LitLaw then .litLaw c else .law c

/-- What `~[r]~>` names: `none` for a rule of the strategy (a `Taclet` or
`LeanTaclet` constructor, `emptyModality`), else a rewrite; any other name is
an error, and so is a name that resolves to more than one constant. -/
def rwArrow? (r : Ident) : MetaM (Option RwArrow) := do
  let n := r.getId
  let env ← getEnv
  if n == `emptyModality || env.contains (``Taclet ++ n) || env.contains (``LeanTaclet ++ n) then
    return none
  if rwTable.contains n then return some (.table n)
  if env.contains (``TermTaclet ++ n) then return some (.law (``TermTaclet ++ n))
  if env.contains (``EvalLaw ++ n) then return some (.evalLaw (``EvalLaw ++ n))
  if env.contains (``LitLaw ++ n) then return some (.litLaw (``LitLaw ++ n))
  let cs := ((← resolveGlobalName n).filterMap fun (c, fs) =>
    if fs.isEmpty then some c else none).eraseDups
  match cs with
  | [c] => if let some k ← lawKind? c then return some (.ofLaw k c)
  | [] => pure ()
  | cs => throwError "~[{r}]~>: ambiguous, {r} may be {", ".intercalate (cs.map toString)}"
  throwError "~[{r}]~>: {r} is no rule: not a `Taclet` or `LeanTaclet` constructor, not an \
    update rule ({", ".intercalate (rwTable.map toString)}), not a term taclet (`TermTaclet`), \
    not a law of a memory read (`EvalLaw`), not a literal law (`LitLaw`)"

/-- The formula below `n` updates of the line `e`. -/
partial def bodyBelow (e : Lean.Expr) : Nat → MetaM Lean.Expr
  | 0 => pure e
  | n + 1 => do
    let e ← whnf e
    if e.isAppOfArity ``Fml.upd 4 then bodyBelow e.appArg! n else pure e

/-- What a part of a line folds to under `Fml.concrete`, as far as the
elaborator can tell: `true`, `false`, a formula it must not look at (a
postcondition variable, or a fold that returns one), or anything else. -/
inductive LitStatus where
  | tt | ff | opaque | other
  deriving DecidableEq

/-- The skeleton of a formula (`Skel`), read off the line: the connectives,
the literal leaves, the updates; a postcondition variable, a program, a
quantifier and a `havoc` are opaque, and so is a connective's part whose
fold may return an opaque formula (`LitStatus`), which the folds then do
not test.  The status mirrors `Fml.concrete`'s folds so the flags are exact. -/
partial def skelOf (e : Lean.Expr) : MetaM (Skel × LitStatus) := do
  let e ← instantiateMVars e
  let isLit (t : Lean.Expr) : MetaM Bool := do
    return (← whnfTm t).isAppOfArity ``Term.lit 2
  match e.getAppFnArgs with
  | (``Fml.tt, #[_]) => return (.lit, .tt)
  | (``Fml.eq, #[_, a, b]) =>
    if (← isLit a) && (← isLit b) then
      let va := (← whnfTm a).appArg!
      let vb := (← whnfTm b).appArg!
      return (.lit, if ← isDefEq va vb then .tt else .ff)
    return (.lit, .other)
  | (``Fml.defined, #[_, t]) => return (.lit, if ← isLit t then .tt else .other)
  | (``Fml.not, #[_, a]) =>
    let (sa, ta) ← skelOf a
    let st := match ta with
      | .ff => .tt
      | .tt => .ff
      | .opaque => .opaque
      | .other => .other
    return (.not (ta == .opaque) sa, st)
  | (``Fml.and, #[_, a, b]) =>
    let (sa, ta) ← skelOf a
    let (sb, tb) ← skelOf b
    let st := if ta == .tt then tb else if ta == .ff then .ff
      else if tb == .tt then ta else if tb == .ff then .ff else .other
    return (.and (ta == .opaque) (tb == .opaque) sa sb, st)
  | (``Fml.imp, #[_, a, b]) =>
    let (sa, ta) ← skelOf a
    let (sb, tb) ← skelOf b
    let st := if ta == .tt then tb else if ta == .ff then .tt
      else if tb == .tt then .tt else if tb == .ff then (if ta == .opaque then .opaque else .other)
      else .other
    return (.imp (ta == .opaque) (tb == .opaque) sa sb, st)
  | (``Fml.upd, #[_, _, _, ψ]) => return (.upd (← skelOf ψ).1, .opaque)
  | _ => return (.opaque, .opaque)

/-- The skeleton of the formula below `n` updates of the line `e`, quoted. -/
def skelBelow (e : Lean.Expr) (n : Nat) : MetaM Lean.Expr := do
  return toExpr (← skelOf (← bodyBelow e n)).1

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

/-- The positions on the spine of the storage term `S`: each storage subterm
reached through the storage argument of a save, a delete or a select, with
the context (`SCtx`) a hole there stands in. -/
partial def spinePositions (C S : Lean.Expr) (mk : Lean.Expr → Lean.Expr := id) :
    MetaM (Array (Lean.Expr × Lean.Expr)) := do
  let here := (S, mk (mkApp (mkConst ``SCtx.hole) C))
  if S.isAppOfArity ``STerm.save 4 then
    let #[_, S', p, v] := S.getAppArgs | return #[here]
    return #[here] ++ (← spinePositions C S' fun K => mk (mkAppN (mkConst ``SCtx.save) #[C, K, p, v]))
  else if S.isAppOfArity ``STerm.delAt 3 then
    let #[_, S', p] := S.getAppArgs | return #[here]
    return #[here] ++ (← spinePositions C S' fun K => mk (mkAppN (mkConst ``SCtx.delAt) #[C, K, p]))
  else if S.isAppOfArity ``STerm.select 3 then
    let #[_, S', r] := S.getAppArgs | return #[here]
    return #[here] ++ (← spinePositions C S' fun K => mk (mkAppN (mkConst ``SCtx.select) #[C, K, r]))
  else return #[here]

/-- `lhs` matched against `e`: by unification, or, for a law in a storage
context (`find(K[X], q)` with `K` to find), `X` against a position on the
spine of `e`'s storage and `K` the context there. -/
def matchLaw (lhs e : Lean.Expr) : MetaM Bool := do
  if lhs.isAppOfArity ``Term.find 3 then
    let #[C, st, q] := lhs.getAppArgs | return ← isDefEq lhs e
    if st.isAppOfArity ``SCtx.fill 3 then
      let #[_, K, X] := st.getAppArgs | return ← isDefEq lhs e
      if (← instantiateMVars K).isMVar then
        unless e.isAppOfArity ``Term.find 3 do return false
        let #[_, S, q'] := e.getAppArgs | return false
        for (T, Kpos) in ← spinePositions C S do
          let s ← saveState
          if (← isDefEq X T) && (← isDefEq K Kpos) && (← isDefEq q q') then return true
          s.restore
        return false
  isDefEq lhs e

/-- The law `c` at the subterm `e`: `(t, t', h)` when `e` is its left side,
its arguments found there and its side conditions (`hp : p.hasSeg = true`,
…) closed by `rfl` or `decide`, as `sol_rw` closes them (`solRwSide`), or by
a hypothesis of the chain (`findOnDelAtBelow`'s `hk`); else why not, if a
side condition is why. -/
def lawAt (c : Lean.Name) (e : Lean.Expr) :
    TermElabM (Except (Option MessageData) (Lean.Expr × Lean.Expr × Lean.Expr)) := do
  let pf ← mkConstWithFreshMVarLevels c
  let (args, _, ty) ← forallMetaTelescope (← inferType pf)
  let ty ← whnfR (← instantiateMVars ty)
  let some (lhs, rhs) := lawSides? ty | return .error none
  unless ← matchLaw lhs e do return .error none
  for a in args do
    let g := a.mvarId!
    if (← g.isAssigned) || !(← isProp (← g.getType)) then continue
    let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
    let g ← g.replaceTargetDefEq ty
    let closed ← try
        pure (← Term.withoutErrToSorry <|
          Tactic.run g (evalTactic (← `(tactic| first | rfl | decide | assumption)))).isEmpty
      catch _ => pure false
    unless closed do
      return .error (some m!"the side condition{indentExpr ty}\nof {lastName c} closes by neither \
        `rfl`, `decide` nor a hypothesis")
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
    let some (lhs, _) := lawSides? ty | throwError "not a law: {c}"
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
spine merged, then fewer updates, then a run of updates further in (the
longest first), then one pair further in; the others at
each position of the spine, outermost first; then, under a branch,
`sequentialToParallel` at the first spine the skeleton finds
(`LineRw.mergeIn`), `applyOnRigid` and `applyOnRigidBox` through the
connectives (`LineRw.applyOnRigidIn`, `LineRw.applyOnRigidBoxIn`), and
`concrete` below each number of updates (`LineRw.concrete`), each with the
skeleton of the formula it acts on (`skelBelow`).  A law: at each instance,
on the equations, then in each update's right-hand sides when its result
cannot halt — under any modality where the update holds the write the law
reads back (`LineRw.lawUpdAny`), else under the box.  A literal law: in
each update's right-hand sides (`LineRw.lit`), then in the skeleton below
each number of updates (`LineRw.litEq`). -/
def rwCandidatesWith (keep : Lean.Expr → Bool) (C φ : Lean.Expr) :
    RwArrow → TermElabM (Array Lean.Expr × Option MessageData)
  | .table n => do
    let k ← spineLen φ
    let atPos (f : Lean.Name) (is : List Nat) : Array Lean.Expr :=
      (is.map fun i => mkApp2 (mkConst f) C (toExpr i)).toArray
    let upd (r : Lean.Name) : Array Lean.Expr := ((List.range k).map fun i =>
      mkApp3 (mkConst ``LineRw.updRule) C (mkConst r) (toExpr i)).toArray
    -- a rewrite under a branch takes the skeleton of the formula it acts on,
    -- and is tried only where that skeleton gives it somewhere to act (`fit`)
    let skelAt (n : Nat) : MetaM Skel := do return (← skelOf (← bodyBelow φ n)).1
    let inSkel (f : Lean.Name) (is : List Nat) (body : Nat → Nat) (fit : Skel → Bool) :
        MetaM (Array Lean.Expr) :=
      is.toArray.filterMapM fun i => do
        let s ← skelAt (body i)
        return if fit s then some (mkApp3 (mkConst f) C (toExpr i) (toExpr s)) else none
    let rs ←
      if n == `sequentialToParallel then
        pure (atPos ``LineRw.mergeSpine ((List.range (k - 1)).reverse.map (· + 1)) ++
          ((List.range (k - 1)).drop 1).toArray.flatMap (fun i =>
            ((List.range (k - 1 - i)).reverse.map (· + 2)).toArray.map fun n =>
              mkApp3 (mkConst ``LineRw.mergeRun) C (toExpr i) (toExpr n)) ++
          atPos ``LineRw.mergeAt ((List.range (k - 1)).drop 1) ++
          (← do
            let s ← skelAt 0
            return if s.hasConn then #[1, 2, 3].map fun n =>
              mkApp3 (mkConst ``LineRw.mergeIn) C (toExpr n) (toExpr s) else #[]))
      else if n == `simplifyUpdate then
        pure (atPos ``LineRw.simplify (List.range k) ++ atPos ``LineRw.simplifyFresh (List.range k))
      else if n == `applySkip then pure (upd ``UpdRuleName.applySkip)
      else if n == `applyOnRigid then
        pure (upd ``UpdRuleName.applyOnRigid ++
          (← inSkel ``LineRw.applyOnRigidIn (List.range k) (· + 1) Skel.isConn))
      else if n == `applyOnRigidBox then
        pure (atPos ``LineRw.applyOnRigidBox (List.range k) ++
          (← inSkel ``LineRw.applyOnRigidBoxIn (List.range k) (· + 1) Skel.isConn))
      else if n == `applyStorageBox then pure (atPos ``LineRw.applyStorageBox (List.range k))
      else if n == `concrete then inSkel ``LineRw.concrete (List.range (k + 1)) id Skel.hasLit
      else pure #[]
    return (rs, none)
  | .law c => do
    let (is, failed) ← lawInstances c φ
    let k ← spineLen φ
    let mut out := #[]
    for (t, t', pf) in is do
      unless keep t do continue
      out := out.push (mkAppN (mkConst ``LineRw.law) #[C, t, t', pf])
      if ← isDefEq (mkApp3 (mkConst ``Tm.total) C (mkConst ``Srt.val) t') (mkConst ``Bool.true) then
        let ht ← mkEqRefl (mkConst ``Bool.true)
        for i in List.range k do
          out := out.push (mkAppN (mkConst ``LineRw.lawUpdAny) #[C, t, t', pf, ht, toExpr i])
        for i in List.range k do
          out := out.push (mkAppN (mkConst ``LineRw.lawUpd) #[C, t, t', pf, ht, toExpr i])
      let refCtor? :=
        if c == ``TermTaclet.findOnSaveFrame then some ``TermTaclet.RefLaw.findOnSaveFrame
        else if c == ``TermTaclet.findOnDelAtValue then some ``TermTaclet.RefLaw.findOnDelAtValue
        else if c == ``TermTaclet.findOnDelAtFrame then some ``TermTaclet.RefLaw.findOnDelAtFrame
        else if c == ``TermTaclet.lenOnSaveFrame then some ``TermTaclet.RefLaw.lenOnSaveFrame
        else if c == ``TermTaclet.lenOnDelAtFrame then some ``TermTaclet.RefLaw.lenOnDelAtFrame
        else none
      if let some refCtor := refCtor? then
        let hr := mkAppN (mkConst refCtor) pf.getAppArgs
        discard <| inferType hr
        for i in List.range k do
          out := out.push (mkAppN (mkConst ``LineRw.lawUpdRef) #[C, t, t', pf, hr, toExpr i])
      for i in List.range k do
        out := out.push (mkAppN (mkConst ``LineRw.lawUpdEq) #[C, t, t', pf, toExpr i])
    return (out, failed)
  | .evalLaw c => do
    let (is, failed) ← lawInstances c φ
    let k ← spineLen φ
    let mut out := #[]
    for (t, t', pf) in is do
      unless keep t do continue
      let u := (← whnfR (← inferType t)).getAppArgs[1]!
      for i in List.range k do
        out := out.push (mkAppN (mkConst ``LineRw.lawUpdEval) #[C, u, t, t', pf, toExpr i])
    return (out, failed)
  | .litLaw c => do
    let (is, failed) ← lawInstances c φ
    let k ← spineLen φ
    let mut out := #[]
    for (t, t', pf) in is do
      unless keep t do continue
      for i in List.range k do
        out := out.push (mkAppN (mkConst ``LineRw.lit) #[C, t, t', pf, toExpr i])
      for n in List.range (k + 1) do
        let s := (← skelOf (← bodyBelow φ n)).1
        if s.hasLit then
          out := out.push (mkAppN (mkConst ``LineRw.litEq) #[C, t, t', pf, toExpr n, toExpr s])
    return (out, failed)

/-- `rwCandidatesWith` at every instance of a law. -/
def rwCandidates (C φ : Lean.Expr) (a : RwArrow) :
    TermElabM (Array Lean.Expr × Option MessageData) :=
  rwCandidatesWith (fun _ => true) C φ a

/-- Each of the rewrites `rs` on the line `φ`, computed: the line after, with
the line's modality and postconditions put back, or `none`.  Under a
modality `m` a rewrite runs at the diamond and at the box, and gives a line
only where the two agree but for `m`. -/
def rwResults (C φ : Lean.Expr) (rs : Array Lean.Expr) :
    MetaM (List (Option Lean.Expr) × Option (Lean.Expr × Bool)) := do
  let some n := (← whnfR C).constName?
    | throwError "sol_chain: the contract is not a named constant: {C}"
  let (φ', sp) ← (punch C φ).run {}
  let ty := mkApp (mkConst ``List [0]) (mkApp (mkConst ``Option [0]) (mkConst ``Lean.Expr))
  -- the rewrites' functions alone: a law closed by a hypothesis of the chain
  -- carries that variable in its proof, which a compiled evaluation cannot
  -- take, and the projection drops the proof
  let fs ← rs.mapM fun r => whnf (mkApp2 (mkConst ``LineRw.apply) C r)
  let fml := mkApp (mkConst ``Fml) C
  let list ← mkListLit (← mkArrow fml (mkApp (mkConst ``Option [0]) fml)) fs.toList
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
    let boxOnly := (ds.zip bs).all fun (d, b) => d.isNone || b.isSome
    return ((ds.zip bs).map fun
      | (some d, some b) => fill m d b
      | _ => none, if parts then some (m, boxOnly) else none)

/-- `r.apply A = some B` over a postcondition or a modality, where the kernel
cannot compute what the rewrite asks of them: `simp` takes the rewrite and the
line's fresh variables apart, `Post.freshVars_eq_nil` says the postcondition
has none, and `rfl` computes the rest (`LineRw.simplifyFresh`); a merge of two
updates that may halt compares the line's modalities (`Upd.merge`), which
`cases m` decides, one `rfl` per modality.  `none` if that does not close it. -/
def proveRw (C r A B : Lean.Expr) : TermElabM (Option Lean.Expr) := do
  let ty ← mkEq (mkApp2 (mkApp (mkConst ``LineRw.apply) C) r A)
    (mkApp2 (mkConst ``Option.some [0]) (mkApp (mkConst ``Fml) C) B)
  let simps ← `(tactic| simp only [LineRw.simplifyFresh, Fml.simplifyFreshAt, Fml.atSpine,
    Option.map_some, Fml.simplifyFreshTop, Fml.freshVars, Post.freshVars_eq_nil, List.append_nil,
    List.nil_append])
  -- the line's modality variable, if any: a merge of two updates that may
  -- halt compares modalities, which `cases m` decides
  let m? ← (collectFVars {} A).fvarIds.findM? fun f => do
    return (← whnfR (← f.getType)).isConstOf ``Modality
  let mut tacs := #[← `(tactic| ($simps:tactic; rfl))]
  if let some m := m? then
    let mId := mkIdent (← m.getUserName)
    tacs := tacs.push (← `(tactic| (cases $mId:ident <;> first | rfl | ($simps:tactic; rfl))))
  for tac in tacs do
    let s ← saveState
    let g ← mkFreshExprMVar ty
    let ok ← try
        pure (← Term.withoutErrToSorry <| Tactic.run g.mvarId!
          (Tactic.withoutRecover (evalTactic tac))).isEmpty
      catch _ => pure false
    if ok then
      let p ← instantiateMVars g
      unless p.hasSyntheticSorry || p.hasExprMVar do return some p
    s.restore
  return none

/-- The rewrite `~[n]~>` names on `φ`, among `rs`, the line after it, and its
proof when `rfl` is not one: the first that gives `ψ`, or, with `ψ` left
`_`, the first that applies.  On a line with a modality `m` or a
postcondition `φ : Post C`, the rewrite must compute over them
(`r.apply φ = some ψ` by the kernel, on the line itself), or be proved from
`Post.noFresh` (`proveRw`): `simplifyUpdate`, say, asks the postcondition
which variables it reads, and it is asked only which fresh ones. -/
def rwSelect (C φ ψ : Lean.Expr) (n : String) (rs : Array Lean.Expr)
    (failed : Option MessageData := none) :
    TermElabM (Lean.Expr × Lean.Expr × Option Lean.Expr) := do
  let φ ← instantiateMVars φ
  let ψ ← instantiateMVars ψ
  let (qs, parts) ← rwResults C φ rs
  let mut gives := #[]
  let mut stuck := false
  for (r, q?) in rs.toList.zip qs do
    let some q := q? | continue
    let st ← saveState
    unless ψ.isMVar || q == ψ || (← withReducible (isDefEq q ψ)) do
      st.restore
      gives := gives.push q
      continue
    let mut pf := none
    if φ.hasFVar then
      let lhs := mkApp2 (mkApp (mkConst ``LineRw.apply) C) r φ
      unless ← isDefEq lhs (mkApp2 (mkConst ``Option.some [0]) (mkApp (mkConst ``Fml) C) q) do
        let some p ← proveRw C r φ q | stuck := true; st.restore; continue
        pf := some p
    return (r, q, pf)
  if stuck then
    throwError "~[{n}]~>: on{indentExpr φ}\nit looks at the line's modality or postcondition, \
      which are not known: state the line for a concrete one"
  if !gives.isEmpty then
    let ls := gives.toList.map fun q => m!"{indentExpr q}"
    throwError "~[{n}]~>: on{indentExpr φ}\nit gives{MessageData.joinSep ls ""}\nnot{indentExpr ψ}"
  let note := match failed, parts with
    | some m, _ => m!"\n({m})"
    | none, some (m, true) => m!"\n(it applies under the box only, where an update that halts \
        makes the line true: go on after `cases {m}`)"
    | none, some (m, false) => m!"\n(it applies under one modality only: go on after `cases {m}`)"
    | none, none => m!""
  throwError "~[{n}]~>: {n} does not apply to{indentExpr φ}{note}"

/-- The label of `φ ~[r]~> ψ` for a rewrite, `φ` known, the line after, and
its proof when `rfl` is not one. -/
def rwLabel (C φ ψ : Lean.Expr) (r : Ident) (a : RwArrow) :
    TermElabM (Lean.Expr × Lean.Expr × Option Lean.Expr) := do
  let (rs, failed) ← rwCandidates C (← instantiateMVars φ) a
  rwSelect C φ ψ r.getId.toString rs failed

/-- The term taclets `~=>` tries, after the update rules of `rwTable`: the
named rules of `TermTaclet`, and `findOnDelAtSave`. -/
def rwLaws : List Lean.Name :=
  [``TermTaclet.findOnSave, ``TermTaclet.findOnSaveFrame, ``TermTaclet.findMemberCons,
    ``TermTaclet.selectOnSaveMember, ``TermTaclet.selectOnSaveFrame, ``TermTaclet.selectOnDelAtMember,
    ``TermTaclet.selectOnDelAtFrame, ``TermTaclet.selectOnSaveMemberIn, ``TermTaclet.selectOnSaveFrameIn,
    ``TermTaclet.selectOnDelAtMemberIn, ``TermTaclet.selectOnDelAtFrameIn,
    ``TermTaclet.findOnDelAt, ``TermTaclet.findOnDelAtSave, ``TermTaclet.findOnDelAtValue,
    ``TermTaclet.delValueLit, ``TermTaclet.findOnDelAtBelow, ``TermTaclet.findOnDelAtFrame,
    ``TermTaclet.findOnPushFrame, ``TermTaclet.findOnPopFrame, ``TermTaclet.lenOnSaveFrame,
    ``TermTaclet.lenOnDelAtFrame]

/-- The laws of memory reads `~=>` tries, after the term taclets. -/
def rwEvalLaws : List Lean.Name :=
  [``EvalLaw.readOnWrite, ``EvalLaw.findCopyMem, ``EvalLaw.readCopySt, ``EvalLaw.readAddEqual,
    ``EvalLaw.readAddDifferent, ``EvalLaw.readAddDifferentIdentity, ``EvalLaw.readWriteDifferent,
    ``EvalLaw.readWriteDifferentIdentity, ``EvalLaw.readOnWriteIdentity]

/-- The literal laws `~=>` tries, after the laws of memory reads. -/
def rwLitLaws : List Lean.Name :=
  [``LitLaw.add_literals, ``LitLaw.sub_literals, ``LitLaw.leq_literals, ``LitLaw.less_literals]

/-- What `~=>` tries, in order: the update rules, then the laws in scope. -/
def rwAnyArrows : MetaM (List (String × RwArrow)) := do
  let env ← getEnv
  let laws ← rwLaws.filterM fun c => if env.contains c then isLaw c else pure false
  let evalLaws := rwEvalLaws.filter env.contains
  let litLaws := rwLitLaws.filter env.contains
  return rwTable.map (fun n => (n.toString, .table n)) ++
    laws.map (fun c => ((lastName c).toString, .law c)) ++
    evalLaws.map (fun c => ((lastName c).toString, .evalLaw c)) ++
    litLaws.map fun c => ((lastName c).toString, .litLaw c)

/-- The rewrite of `φ ~=> ψ`: the first of `rwAnyArrows` that gives `ψ`, the
line after, and its proof when `rfl` is not one; else an error with what
each rewrite that applies gives. -/
def rwAnyFind (C φ ψ : Lean.Expr) : TermElabM (Lean.Expr × Lean.Expr × Option Lean.Expr) := do
  let mut gives : Array MessageData := #[]
  for (n, a) in ← rwAnyArrows do
    let (rs, failed) ← rwCandidates C φ a
    if rs.isEmpty then continue
    let st ← saveState
    try
      return ← rwSelect C φ ψ n rs failed
    catch _ =>
      st.restore
      let (qs, _) ← rwResults C φ rs
      if let some q := qs.findSome? id then gives := gives.push m!"{n} gives{indentExpr q}"
  let note := if gives.isEmpty then m!"\nno rewrite applies to it" else
    m!"\n{MessageData.joinSep gives.toList "\n"}"
  throwError "~=>: no rewrite gives{indentExpr ψ}\nfrom{indentExpr φ}{note}"

partial def solveChain (g : MVarId) : TermElabM Unit := do
  let ty ← instantiateMVars (← g.getType)
  if ty.isAppOfArity ``Fml.RwAny 3 then
    let #[C, φ, ψ] := ty.getAppArgs | unreachable!
    let φ ← instantiateMVars φ
    let ψ ← instantiateMVars ψ
    if φ.hasExprMVar then throwError "sol_chain: ~=>: the line before it is not known{indentExpr φ}"
    if ψ.isMVar then throwError "sol_chain: ~=>: write the line after, it is what picks the rewrite"
    let (r, q, pf) ← rwAnyFind C φ ψ
    unless ← isDefEq ψ q do throwError "sol_chain: ~=>: the line after is not{indentExpr q}"
    let lrw := mkApp (mkConst ``LineRw) C
    let motive ← withLocalDeclD `r lrw fun x => do
      mkLambdaFVars #[x] (← mkEq (mkApp2 (mkApp (mkConst ``LineRw.apply) C) x φ)
        (mkApp2 (mkConst ``Option.some [0]) (mkApp (mkConst ``Fml) C) ψ))
    g.assign (mkApp4 (mkConst ``Exists.intro [1]) lrw motive r (pf.getD (someRefl C q)))
  else if ty.isAppOfArity ``Fml.RwBy 5 then
    let #[C, n, r, φ, ψ] := ty.getAppArgs | unreachable!
    let .lit (.strVal n) := n | throwError "sol_chain: the arrow's name is not known{indentExpr ty}"
    let φ ← instantiateMVars φ
    if φ.hasExprMVar then throwError "sol_chain: ~[{n}]~>: the line before it is not known{indentExpr φ}"
    let r ← instantiateMVars r
    let (r', q, pf) ← if r.isMVar then
        let some a ← rwArrow? (mkIdent n.toName) | throwError "sol_chain: {n} is a rule of the strategy"
        rwLabel C φ ψ (mkIdent n.toName) a
      else rwSelect C φ ψ n #[r]
    unless ← isDefEq r r' do throwError "sol_chain: ~[{n}]~>: the label is not {r'}"
    unless ← isDefEq ψ q do throwError "sol_chain: ~[{n}]~>: the line after is not{indentExpr q}"
    g.assign (pf.getD (someRefl C q))
  else if ty.isAppOfArity ``Fml.StepBy 4 then
    let #[C, r, φ, ψ] := ty.getAppArgs | unreachable!
    let (run, q) ← nextLine C φ ψ
    if run.splice.fmls.isEmpty then
      checkStep C run.splice φ q
      let pair ← mkAppM ``Prod.mk #[← mkAppM ``Option.some #[r], ← mkAppM ``Option.some #[q.fml]]
      g.assign (← mkEqRefl pair)
    else
      let hr ← if q.decided then mkEqRefl (← mkAppM ``Option.some #[r]) else do
        -- `φ.rule` is `φ.ruleAt φ.fresh`: the goal it steps in, then `rfl`
        let k := mkApp2 (mkConst ``Fml.fresh) C φ
        let (_, h) ← ruleFocus C k φ
        mkEqTrans h (← mkEqRefl (← mkAppM ``Option.some #[r]))
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
    | _ => throwError "sol_chain: expected `φ ~> ψ`, `φ ~[r]~> ψ` (a rule or a rewrite), `φ ~=> ψ`, \
        `φ ~*> ψ` or a chain of them{indentExpr ty}"

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
    let (lbl, _, _) ← rwLabel C a' (← elabTerm b none) r arrow
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
