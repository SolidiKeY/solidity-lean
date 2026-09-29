import Solidity.Calculus.Notation
import Solidity.Theory.Bridge.Denote

/-!
# Update simplification

Symbolic execution leaves a stack of updates in front of the postcondition,
one per terminal rule:

    { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } φ

KeY does not keep the stack: its update rules (`updateRules.key`) merge two
updates into one parallel update and drop the elements nothing reads, so
the goal carries one update:

    { storage := save(storage, alice.account.balance, 10) } φ

This module is those rules, each proved an equivalence over `holds`
(mini-solkey's `Ch14_Updates`):

| KeY taclet | here |
|---|---|
| `sequentialToParallel1/2/3`: `{u}{u2}φ ⇝ {u ‖ {u}u2}φ` | `UpdRule.sequentialToParallel` |
| `applyOnElementary`, `applyOnParallel`: `{u}(x := t)`, `{u}(u2 ‖ u3)` | `UpdElem.subst`, `Upd.subst` (functions) |
| `simplifyUpdate1/2/3` (`\dropEffectlessElementaries`) | `UpdRule.simplifyUpdate`, `Upd.dropEffectless` |
| `applySkip1/2/3`: `{skip}φ ⇝ φ` | `UpdRule.applySkip` |
| `applyOnRigidFormula`, `applyOnPV`, `applyOnDifferentPV` | `UpdRule.applyOnRigid`, `Fml.subst` |
| `elimSelfUpdate` (commented out in solkey) | `UpdElem.elimSelf_box`, `UpdElem.elimSelf_diamond`: one direction each |
| `parallelWithSkip1/2`: `skip ‖ u ⇝ u` | nothing: `‖` is `++`, `skip` is `[]` |

**What halting changes.**  A term here is a call of the interpreter
(`Update.lean`), so it can halt, and `{U} φ` with a halting `U` is judged as
the statement it came from: true under the box, false under the diamond.
KeY's terms do not halt, and three of its rules lean on that; here each
carries the side condition that makes it an equivalence again:

* dropping an element (`simplifyUpdate`) removes its halting too, so only
  an element that cannot halt is dropped (`UpdElem.total`: a literal, or a
  path of state variables and members) — `se1 := 10` and
  `sp1 := alice.account`, what Step 2 captures, are;
* substituting `U` into a formula (`applyOnRigid`) forgets whether `U`
  halts, so `U` must not halt — for the equivalence; under the box one
  direction holds for any update of locals, and for one that also writes
  the storage where the formula reads none (`Proves.applyOnRigidBox`);
* `x := x` halts when `x` is not bound to a value, so `elimSelfUpdate` is
  no equivalence: dropping it is sound under the box, keeping it under the
  diamond.

**What merges.**  `{U}V` substitutes `U` into `V` (`Upd.subst`); it is the
update `U ‖ {U}V` of `sequentialToParallel` when `U` writes only locals,
aliases and memory locals (`Upd.envOnly`): a storage term denotes a whole
state, and a `U` that writes the storage would have to be substituted for
it.  So the local captures of a stack merge, and two storage writes stay
two updates.  A variable read at another sort than `U` binds it
(`x := 1`, then `p.age` for an alias `p`) becomes a term that halts
(`Term.stuck`), as the read would.  `applyOnRigid` excludes that case
(`Fml.sortedFor`): an equation reads its terms in the Theory, where a halt
still denotes something, and a storage or path variable of the wrong sort
denotes something other than its substitution.

The rules are optional: nothing else uses them.  They are used through
`Fml.simpUpds` (merge every stack, drop what is dead), the tactics
`sol_merge` and `sol_upd r` on `⊨` goals, and `Proves.merge` and
`Proves.simplify` on `⊢` goals with no modality left.
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-! ## Terms that halt, and terms that cannot -/

/-- A value term that always halts: a conditional on a number. -/
def Term.stuck : Term C := .ite (.lit (.int 0)) (.lit (.int 0)) (.lit (.int 0))

/-- A path that always halts: its index does. -/
def PTerm.stuck : PTerm C := .at (.root "") Term.stuck

/-- An identity that always halts: its source does. -/
def ITerm.stuck : ITerm C := .copy .memory (.val Term.stuck)

/-- A storage that always halts: its path does. -/
def STerm.stuck : STerm C := .delAt .storage PTerm.stuck

/-- `x`, read as a value after `{ x := alice }` (`x` an alias), halts; so does its
substitution. -/
@[simp] theorem Term.stuck_eval (σ : State) : (Term.stuck : Term C).eval σ = .error .stuck := rfl
/-- `p.age`, `p` bound to a number by `{ p := 1 }`, halts; so does its substitution. -/
@[simp] theorem PTerm.stuck_eval (σ : State) : (PTerm.stuck : PTerm C).eval σ = .error .stuck := rfl
/-- `m.age`, `m` bound to a path, halts; so does its substitution. -/
@[simp] theorem ITerm.stuck_eval (σ : State) : (ITerm.stuck : ITerm C).eval σ = .error .stuck := rfl
/-- `old`, bound to a number by `{ old := 1 }`, halts as a storage; so does its substitution. -/
@[simp] theorem STerm.stuck_eval (σ : State) : (STerm.stuck : STerm C).eval σ = .error .stuck := rfl

/-- A value term that cannot halt: a literal. -/
def Term.total : Term C → Bool
  | .lit _ => true
  | _ => false

/-- A path that cannot halt: a state variable, and members of it. -/
def PTerm.total : PTerm C → Bool
  | .root _ => true
  | .field p _ => p.total
  | _ => false

/-- A literal does not halt: `10` in `{ se1 := 10 }` reads `10` in every state. -/
theorem Term.total_eval (σ : State) : {t : Term C} → t.total = true → ∃ v, t.eval σ = .ok v
  | .lit v, _ => ⟨v, rfl⟩

/-- A path of state variables and members does not halt: `alice.account` in
`{ sp1 := alice.account }` resolves in every state (it is not read, only named). -/
theorem PTerm.total_eval (σ : State) : {p : PTerm C} → p.total = true → ∃ r, p.eval σ = .ok r
  | .root r, _ => ⟨(r, []), rfl⟩
  | .field p f, h => by
    obtain ⟨⟨r, segs⟩, hp⟩ := PTerm.total_eval σ (p := p) h
    exact ⟨(r, segs ++ [.field f]), by simp only [eval, bind, Except.bind, hp, pure, Except.pure]⟩

/-! ## What an element writes -/

/-- The variable an element writes, if it writes one. -/
def UpdElem.var? : UpdElem C → Option Var
  | .val x _ | .path x _ | .mref x _ => some x
  | _ => none

/-- The update writes locals, aliases and memory locals only. -/
def Upd.envOnly (U : Upd C) : Bool := U.all (·.var?.isSome)

/-- The element cannot halt: `x := 10`, `p := alice.account`. -/
def UpdElem.total : UpdElem C → Bool
  | .val _ t => t.total
  | .path _ p => p.total
  | _ => false

/-- No element of the update can halt. -/
def Upd.total (U : Upd C) : Bool := U.all (·.total)

/-- The binding an element writes, its right-hand side read in `σ₀`. -/
def UpdElem.binding (σ₀ : State) : UpdElem C → Res Binding
  | .val _ t => do pure (.val (← t.eval σ₀))
  | .path _ p => do
    let (r, segs) ← p.eval σ₀
    pure (.spath r segs)
  | .mref _ i => do pure (.mref (← i.eval σ₀))
  | _ => .error .stuck

/-- An element that writes `x` binds `x` to its binding: `x := a + 1` binds
`x` to the value of `a + 1` in the pre-state, or halts where that does. -/
theorem UpdElem.write_var {σ₀ τ : State} {x : Var} :
    {e : UpdElem C} → e.var? = some x → e.write σ₀ τ = (e.binding σ₀ >>= fun b => pure (τ.setEnv x b))
  | .val _ t, h | .path _ t, h | .mref _ t, h => by
    cases h
    simp only [UpdElem.write, UpdElem.binding, bind, Except.bind, pure, Except.pure]
    cases t.eval σ₀ <;> rfl

/-- An element that cannot halt has a binding: `sp1 := alice.account` binds
`sp1` to the path `alice.account` in every state. -/
theorem UpdElem.total_binding (σ₀ : State) :
    {e : UpdElem C} → e.total = true → ∃ b, e.binding σ₀ = .ok b
  | .val _ t, h => by
    obtain ⟨v, hv⟩ := Term.total_eval σ₀ (t := t) h
    exact ⟨.val v, by simp only [binding, bind, Except.bind, hv, pure, Except.pure]⟩
  | .path _ p, h => by
    obtain ⟨⟨r, segs⟩, hp⟩ := PTerm.total_eval σ₀ (p := p) h
    exact ⟨.spath r segs, by simp only [binding, bind, Except.bind, hp, pure, Except.pure]⟩

/-- An element that cannot halt writes a variable: `se1 := 10` writes `se1`. -/
theorem UpdElem.total_var : {e : UpdElem C} → e.total = true → ∃ x, e.var? = some x
  | .val x _, _ | .path x _, _ => ⟨x, rfl⟩

/-- The last element of `U` that writes `x`: the one whose binding `x` has
after `U`. -/
def Upd.lastWrite (x : Var) : Upd C → Option (UpdElem C)
  | [] => none
  | e :: U =>
    match Upd.lastWrite x U with
    | some e' => some e'
    | none => if e.var? = some x then some e else none

/-- The last write of `x` writes `x`: in `{ x := 0 ‖ y := 2 ‖ x := 1 }` it is `x := 1`. -/
theorem Upd.lastWrite_var {x : Var} : {U : Upd C} → {e : UpdElem C} → U.lastWrite x = some e →
    e.var? = some x
  | e' :: U, e, h => by
    simp only [Upd.lastWrite] at h
    split at h
    · exact Upd.lastWrite_var (U := U) (by assumption) |> fun h' => by cases h; exact h'
    · split at h
      · cases h; assumption
      · cases h

/-! ## An update applied to an update: `{U}V`

A variable is replaced by what `U` binds it to: `valOf`, `pathOf`,
`refOf`, one per sort.  The storage and the memory are left: `U` writes
neither (`Upd.envOnly`). -/

/-- `{U}x` for a value `x`. -/
def Upd.valOf (U : Upd C) (x : Var) : Term C :=
  match U.lastWrite x with
  | some (.val _ t) => t
  | some _ => Term.stuck
  | none => .pv x

/-- `{U}p` for an alias `p`. -/
def Upd.pathOf (U : Upd C) (x : Var) : PTerm C :=
  match U.lastWrite x with
  | some (.path _ p) => p
  | some _ => PTerm.stuck
  | none => .pv x

/-- `{U}m` for a memory local `m`. -/
def Upd.refOf (U : Upd C) (x : Var) : ITerm C :=
  match U.lastWrite x with
  | some (.mref _ i) => i
  | some _ => ITerm.stuck
  | none => .pv x

/-- `{U}old` for a storage variable `old`: `U` binds no storage
(`Upd.envOnly`), so `old` is itself where `U` does not write the name, and
halts where `U` binds it to a value, a path or an identity. -/
def Upd.storOf (U : Upd C) (x : Var) : STerm C :=
  match U.lastWrite x with
  | some _ => STerm.stuck
  | none => .pv x

mutual

/-- `{U}t`: KeY's `applyOnPV`/`applyOnDifferentPV`, through every operator. -/
def Term.subst (U : Upd C) : Term C → Term C
  | .lit v => .lit v
  | .pv x => U.valOf x
  | .binop op p a b => .binop op p (a.subst U) (b.subst U)
  | .unop op p a => .unop op p (a.subst U)
  | .find s p => .find (s.subst U) (p.subst U)
  | .len s p => .len (s.subst U) (p.subst U)
  | .read m a => .read (m.subst U) (a.subst U)
  | .ite c a b => .ite (c.subst U) (a.subst U) (b.subst U)
  | .mlen m i => .mlen (m.subst U) (i.subst U)
  | .env k => .env k
  | .net a => .net (a.subst U)
  | .netOf x a =>
    -- `U` binds no ledger (`Upd.envOnly`): a ledger variable it writes halts
    match U.lastWrite x with
    | some _ => Term.stuck
    | none => .netOf x (a.subst U)

def PTerm.subst (U : Upd C) : PTerm C → PTerm C
  | .root r => .root r
  | .pv x => U.pathOf x
  | .field p f => .field (p.subst U) f
  | .at p i => .at (p.subst U) (i.subst U)
  | .next p => .next (p.subst U)

def STerm.subst (U : Upd C) : STerm C → STerm C
  | .storage => .storage
  | .pv x => U.storOf x
  | .save s p v => .save (s.subst U) (p.subst U) (v.subst U)
  | .delAt s p => .delAt (s.subst U) (p.subst U)
  | .push s p v => .push (s.subst U) (p.subst U) (v.subst U)
  | .pushSlot s p E => .pushSlot (s.subst U) (p.subst U) E
  | .pop s p => .pop (s.subst U) (p.subst U)
  | .shrink s p => .shrink (s.subst U) (p.subst U)
  | .extend s p E => .extend (s.subst U) (p.subst U) E

def SValT.subst (U : Upd C) : SValT C → SValT C
  | .val t => .val (t.subst U)
  | .find s p => .find (s.subst U) (p.subst U)
  | .copyMem m i => .copyMem (m.subst U) (i.subst U)
  | .newArr R n => .newArr R (n.subst U)

def ITerm.subst (U : Upd C) : ITerm C → ITerm C
  | .pv x => U.refOf x
  | .read m a => .read (m.subst U) (a.subst U)
  | .alloc m R => .alloc (m.subst U) R
  | .copy m v => .copy (m.subst U) (v.subst U)

def MAddr.subst (U : Upd C) : MAddr C → MAddr C
  | .field i f => .field (i.subst U) f
  | .at i k => .at (i.subst U) (k.subst U)

def MTerm.subst (U : Upd C) : MTerm C → MTerm C
  | .memory => .memory
  | .write m a v => .write (m.subst U) (a.subst U) (v.subst U)
  | .addM m R => .addM (m.subst U) R
  | .copySt m v => .copySt (m.subst U) (v.subst U)

def MValT.subst (U : Upd C) : MValT C → MValT C
  | .val t => .val (t.subst U)
  | .ref i => .ref (i.subst U)

end

/-- `{U}(x := t)` is `x := {U}t`: KeY's `applyOnElementary`. -/
def UpdElem.subst (U : Upd C) : UpdElem C → UpdElem C
  | .val x t => .val x (t.subst U)
  | .path x p => .path x (p.subst U)
  | .mref x i => .mref x (i.subst U)
  | .storage s => .storage (s.subst U)
  | .store x s => .store x (s.subst U)
  | .memory m => .memory (m.subst U)
  | .transfer r a => .transfer (r.subst U) (a.subst U)
  | .saveNet x => .saveNet x
  | .book a => .book (a.subst U)

/-- `V.subst U` is `{U}V`: `{U}(e₁ ‖ … ‖ eₙ)` is `{U}e₁ ‖ … ‖ {U}eₙ`, KeY's
`applyOnParallel`. -/
def Upd.subst (V U : Upd C) : Upd C := V.map (·.subst U)

/-! ### Substitution is evaluation after the update

`SubstAgree U ns σ τ`: `τ` is what `U` leaves of `σ`, seen from the leaves
of a term — every variable read in `τ` is what `U` binds it to read in `σ`,
and the two states agree off the variables `ns` that `U` writes.  Then a
substituted term read in `σ` is the term read in `τ`. -/

structure SubstAgree (U : Upd C) (ns : List Var) (σ τ : State) : Prop where
  agree : EnvAgreeExcept ns σ τ
  val : ∀ x, (U.valOf x).eval σ = (Term.pv x : Term C).eval τ
  path : ∀ x, (U.pathOf x).eval σ = (PTerm.pv x : PTerm C).eval τ
  ref : ∀ x, (U.refOf x).eval σ = (ITerm.pv x : ITerm C).eval τ
  stor : ∀ x, ResultsAgree ns ((U.storOf x).eval σ) ((STerm.pv x : STerm C).eval τ)
  /-- A variable `U` does not write, a ledger variable `oldNet`, is bound alike. -/
  unwritten : ∀ x, U.lastWrite x = none → σ.getEnv x = τ.getEnv x
  /-- A variable `U` writes holds no ledger after it. -/
  written : ∀ x e, U.lastWrite x = some e → ∃ b, τ.getEnv x = .ok b ∧ ∀ l, b ≠ .ledger l
  /-- Every element of `U` that writes a variable returns in `σ`: `U` did not halt. -/
  bound : ∀ x e, U.lastWrite x = some e → ∃ b, e.binding σ = .ok b

section Subst

variable {U : Upd C} {ns : List Var} {σ τ : State}

mutual

/-- Example: after `x = 1;`, `{ x := 1 }(x + 1)` is `1 + 1`, which reads
`2` before the update as `x + 1` reads it after. -/
theorem Term.subst_eval (h : SubstAgree U ns σ τ) : (t : Term C) → (t.subst U).eval σ = t.eval τ
  | .lit _ => rfl
  | .pv x => h.val x
  | .binop _ _ a b => by
    simp only [Term.subst, Term.eval, a.subst_eval h, b.subst_eval h]
  | .unop _ _ a => by simp only [Term.subst, Term.eval, a.subst_eval h]
  | .find s p => by
    simp only [Term.subst, Term.eval, p.subst_eval h]
    exact ResultsAgree.bindEq (s.subst_eval h) fun _ _ h' => by
      simp only [findStorage_congr h']
  | .len s p => by
    simp only [Term.subst, Term.eval, p.subst_eval h]
    exact ResultsAgree.bindEq (s.subst_eval h) fun _ _ h' => by
      simp only [arrayLen_congr h']
  | .read m a => by
    simp only [Term.subst, Term.eval, a.subst_eval h]
    exact ResultsAgree.bindEq (m.subst_eval h) fun _ _ h' => by
      simp only [readAddr_congr h']
  | .ite c a b => by
    simp only [Term.subst, Term.eval, c.subst_eval h, a.subst_eval h, b.subst_eval h]
  | .mlen m i => by
    simp only [Term.subst, Term.eval, i.subst_eval h]
    exact ResultsAgree.bindEq (m.subst_eval h) fun _ _ h' => by
      simp only [memArrayLen, getObj_congr h']
  | .env k => by simp only [Term.subst, Term.eval, State.envVal_congr h.agree]
  | .net a => by simp only [Term.subst, Term.eval, a.subst_eval h, State.getNet, h.agree.net]
  | .netOf x a => by
    simp only [Term.subst]
    split
    · rename_i e hx
      obtain ⟨b, hb, hnl⟩ := h.written x e hx
      simp only [Term.stuck_eval, Term.eval, hb, bind, Except.bind]
      cases b with
      | ledger l => exact absurd rfl (hnl l)
      | _ => rfl
    · rename_i hx
      simp only [Term.eval, h.unwritten x hx, a.subst_eval h]

/-- Example: after `Person storage p = alice;`, `{ p := alice }(p.age)` is
`alice.age`. -/
theorem PTerm.subst_eval (h : SubstAgree U ns σ τ) : (p : PTerm C) → (p.subst U).eval σ = p.eval τ
  | .root _ => rfl
  | .pv x => h.path x
  | .field p _ => by simp only [PTerm.subst, PTerm.eval, p.subst_eval h]
  | .at p i => by
    simp only [PTerm.subst, PTerm.eval, p.subst_eval h, i.subst_eval h, checkIndex_congr h.agree]
  | .next p => by simp only [PTerm.subst, PTerm.eval, p.subst_eval h, findStorage_congr h.agree]

/-- Example: after `uint se1 = 10;`, `{ se1 := 10 }save(storage, alice.age, se1)` is
`save(storage, alice.age, 10)`: the same storage, the rest of the state
agreeing off `se1`. -/
theorem STerm.subst_eval (h : SubstAgree U ns σ τ) :
    (s : STerm C) → ResultsAgree ns ((s.subst U).eval σ) (s.eval τ)
  | .storage => h.agree
  | .pv x => h.stor x
  | .save s p v => by
    simp only [STerm.subst, STerm.eval, v.subst_eval h, p.subst_eval h]
    refine bindPureResults_agree _ fun _ => ?_
    refine ResultsAgree.bind (s.subst_eval h) fun _ _ h' => ?_
    agree_run h'
  | .delAt s p => by
    simp only [STerm.subst, STerm.eval, p.subst_eval h]
    refine ResultsAgree.bind (s.subst_eval h) fun _ _ h' => ?_
    simp only [findStorage_congr h']
    agree_run h'
  | .push s p v => by
    simp only [STerm.subst, STerm.eval, p.subst_eval h]
    refine ResultsAgree.bind (s.subst_eval h) fun _ _ h' => ?_
    refine bindPureResults_agree _ fun _ => pushAt_agree h' _ _ _ fun _ => ?_
    simp only [v.subst_eval h]
  | .pushSlot s p _ => by
    simp only [STerm.subst, STerm.eval, p.subst_eval h]
    refine ResultsAgree.bind (s.subst_eval h) fun _ _ h' => ?_
    exact bindPureResults_agree _ fun _ => pushAt_agree h' _ _ _ fun _ => rfl
  | .pop s p => by
    simp only [STerm.subst, STerm.eval, p.subst_eval h]
    refine ResultsAgree.bind (s.subst_eval h) fun _ _ h' => ?_
    agree_run h'
  | .shrink s p => by
    simp only [STerm.subst, STerm.eval, p.subst_eval h]
    refine ResultsAgree.bind (s.subst_eval h) fun _ _ h' => ?_
    agree_run h'
  | .extend s p _ => by
    simp only [STerm.subst, STerm.eval, p.subst_eval h]
    refine ResultsAgree.bind (s.subst_eval h) fun _ _ h' => ?_
    refine bindPureResults_agree _ fun _ => ?_
    exact ResAgree.bindState (pushPlaceAt_agree h' _ _ _) fun _ _ _ h'' => h''

/-- Example: `{ se1 := 10 }se1`, a stored value, is `10`. -/
theorem SValT.subst_eval (h : SubstAgree U ns σ τ) : (v : SValT C) → (v.subst U).eval σ = v.eval τ
  | .val t => by simp only [SValT.subst, SValT.eval, t.subst_eval h]
  | .find s p => by
    simp only [SValT.subst, SValT.eval, p.subst_eval h]
    exact ResultsAgree.bindEq (s.subst_eval h) fun _ _ h' => by
      simp only [findStorage_congr h']
  | .copyMem m i => by
    simp only [SValT.subst, SValT.eval, i.subst_eval h]
    exact ResultsAgree.bindEq (m.subst_eval h) fun _ _ h' => by
      simp only [copyMem_congr h']
  | .newArr _ n => by simp only [SValT.subst, SValT.eval, n.subst_eval h]

/-- Example: after `Person memory m = n;` (`n` a memory local), `{ m := n }m` is `n`. -/
theorem ITerm.subst_eval (h : SubstAgree U ns σ τ) : (i : ITerm C) → (i.subst U).eval σ = i.eval τ
  | .pv x => h.ref x
  | .read m a => by
    simp only [ITerm.subst, ITerm.eval, a.subst_eval h]
    exact ResultsAgree.bindEq (m.subst_eval h) fun _ _ h' => by
      simp only [readAddr_congr h']
  | .alloc m R => by
    simp only [ITerm.subst, ITerm.eval]
    refine ResultsAgree.bindEq (m.subst_eval h) fun _ _ h' => ?_
    rcases (allocDefault_agree h' R).cases with ⟨e, h₁, h₂⟩ | ⟨_, _, a, h₁, h₂, _⟩ <;>
      simp only [h₁, h₂] <;> rfl
  | .copy m v => by
    simp only [ITerm.subst, ITerm.eval, v.subst_eval h]
    refine congrArg (_ >>= ·) (funext fun sv => ?_)
    refine ResultsAgree.bindEq (m.subst_eval h) fun _ _ h' => ?_
    rcases (copyStToM_agree h' sv).cases with ⟨e, h₁, h₂⟩ | ⟨_, _, a, h₁, h₂, _⟩ <;>
      simp only [h₁, h₂] <;> rfl

/-- Example: `{ ie1 := 2 }(m[ie1])` is the address `m[2]`. -/
theorem MAddr.subst_eval (h : SubstAgree U ns σ τ) : (a : MAddr C) → (a.subst U).eval σ = a.eval τ
  | .field i _ => by simp only [MAddr.subst, MAddr.eval, i.subst_eval h]
  | .at i k => by simp only [MAddr.subst, MAddr.eval, i.subst_eval h, k.subst_eval h]

/-- Example: `{ ie1 := 2 }write(memory, m[ie1], 5)` is `write(memory, m[2], 5)`. -/
theorem MTerm.subst_eval (h : SubstAgree U ns σ τ) :
    (m : MTerm C) → ResultsAgree ns ((m.subst U).eval σ) (m.eval τ)
  | .memory => h.agree
  | .write m a v => by
    simp only [MTerm.subst, MTerm.eval, v.subst_eval h, a.subst_eval h]
    refine bindPureResults_agree _ fun _ => ?_
    refine ResultsAgree.bind (m.subst_eval h) fun _ _ h' => ?_
    exact bindPureResults_agree _ fun _ => writeAddr_agree h' _ _
  | .addM m R => by
    simp only [MTerm.subst, MTerm.eval]
    refine ResultsAgree.bind (m.subst_eval h) fun _ _ h' => ?_
    exact ResAgree.bindState (allocDefault_agree h' R) fun _ _ _ h'' => h''
  | .copySt m v => by
    simp only [MTerm.subst, MTerm.eval, v.subst_eval h]
    refine bindPureResults_agree _ fun sv => ?_
    refine ResultsAgree.bind (m.subst_eval h) fun _ _ h' => ?_
    exact ResAgree.bindState (copyStToM_agree h' sv) fun _ _ _ h'' => h''

/-- Example: `{ se1 := 5 }se1`, a value written to memory, is `5`. -/
theorem MValT.subst_eval (h : SubstAgree U ns σ τ) : (v : MValT C) → (v.subst U).eval σ = v.eval τ
  | .val t => by simp only [MValT.subst, MValT.eval, t.subst_eval h]
  | .ref i => by simp only [MValT.subst, MValT.eval, i.subst_eval h]

end

/-- Writing `{U}e` reads its right-hand side before `U`; that is writing `e`
with its right-hand side read after `U`.

Example: after `x = 1; y = x;`, `{ x := 1 }(y := x)` is `y := 1`, and writing
it sets `y` to `1`, as `y := x` does once `x` is `1`. -/
theorem UpdElem.subst_write (h : SubstAgree U ns σ τ) (τ' : State) :
    (e : UpdElem C) → (e.subst U).write σ τ' = e.write τ τ'
  | .val _ t => by simp only [UpdElem.subst, UpdElem.write, t.subst_eval h]
  | .path _ p => by simp only [UpdElem.subst, UpdElem.write, p.subst_eval h]
  | .mref _ i => by simp only [UpdElem.subst, UpdElem.write, i.subst_eval h]
  | .storage s => by
    simp only [UpdElem.subst, UpdElem.write]
    match (s.subst U).eval σ, s.eval τ, s.subst_eval h with
    | .error _, .error _, he => subst he; rfl
    | .ok a, .ok b, hs => simp only [bind, Except.bind, hs.storage]
  | .store _ s => by
    simp only [UpdElem.subst, UpdElem.write]
    match (s.subst U).eval σ, s.eval τ, s.subst_eval h with
    | .error _, .error _, he => subst he; rfl
    | .ok a, .ok b, hs => simp only [bind, Except.bind, hs.storage]
  | .memory m => by
    simp only [UpdElem.subst, UpdElem.write]
    match (m.subst U).eval σ, m.eval τ, m.subst_eval h with
    | .error _, .error _, he => subst he; rfl
    | .ok a, .ok b, hs => simp only [bind, Except.bind, hs.heap, hs.nextId]
  | .transfer r a => by simp only [UpdElem.subst, UpdElem.write, r.subst_eval h, a.subst_eval h]
  | .saveNet _ => by simp only [UpdElem.subst, UpdElem.write, h.agree.net]
  | .book a => by
    simp only [UpdElem.subst, UpdElem.write, a.subst_eval h, State.book, State.getNet, h.agree.net,
      h.agree.tx, h.agree.selfBalance]

/-- Running `{U}V` before `U` is running `V` after it, element by element.

Example: `{ x := 1 }(y := x ‖ z := x + 1)` is `y := 1 ‖ z := 1 + 1`, which
writes what `y := x ‖ z := x + 1` writes once `x` is `1`. -/
theorem Upd.foldl_subst (h : SubstAgree U ns σ τ) :
    (V : Upd C) → ∀ τ', (V.subst U).foldlM (fun ρ e => e.write σ ρ) τ' =
      V.foldlM (fun ρ e => e.write τ ρ) τ'
  | [], _ => rfl
  | e :: V, τ' => by
    simp only [Upd.subst, List.map_cons, List.foldlM_cons] at *
    rw [UpdElem.subst_write h]
    congr 1
    funext ρ
    exact Upd.foldl_subst h V ρ

end Subst

/-! ### What an update of locals leaves -/

/-- The variables an update writes. -/
def Upd.targets (U : Upd C) : List Var := U.filterMap (·.var?)

/-- Running an update of locals changes the environment at the variables it
writes, and there to the binding of the last element that writes each.

Example: `{ x := 0 ‖ y := 2 ‖ x := 1 }` (after `x = 0; y = 2; x = 1;`) leaves
`x` bound to `1`, `y` to `2`, and everything else as it was. -/
theorem Upd.foldl_env (σ₀ : State) : (U : Upd C) → U.envOnly = true →
    ∀ {τ₀ τ : State}, U.foldlM (fun ρ e => e.write σ₀ ρ) τ₀ = .ok τ →
      EnvAgreeExcept U.targets τ₀ τ ∧
      (∀ x, U.lastWrite x = none → lookupBy x τ.env = lookupBy x τ₀.env) ∧
      (∀ x e, U.lastWrite x = some e → ∃ b, e.binding σ₀ = .ok b ∧ lookupBy x τ.env = some b)
  | [], _, τ₀, τ, h => by
    cases h
    exact ⟨EnvAgreeExcept.refl _ _, fun _ _ => rfl, fun _ _ h => by cases h⟩
  | e :: U, hU, τ₀, τ, h => by
    simp only [Upd.envOnly, List.all_cons, Bool.and_eq_true] at hU
    obtain ⟨he, hU⟩ := hU
    obtain ⟨x₀, hx₀⟩ := Option.isSome_iff_exists.1 he
    simp only [List.foldlM_cons] at h
    obtain ⟨τ₁, h₁, h⟩ := bind_ok_inv h
    rw [UpdElem.write_var hx₀] at h₁
    obtain ⟨b₀, hb₀, h₁⟩ := bind_ok_inv h₁
    cases h₁
    obtain ⟨hag, hnone, hsome⟩ := Upd.foldl_env σ₀ U hU h
    have htargets : Upd.targets (e :: U) = x₀ :: Upd.targets U := by
      simp only [targets, hx₀, Option.some.injEq, List.filterMap_cons_some]
    refine ⟨?_, fun x hx => ?_, fun x e' hx => ?_⟩
    · rw [htargets]
      refine ⟨hag.storage, hag.heap, hag.nextId, hag.net, fun n hn => ?_, hag.selfBalance, hag.tx⟩
      have hne : n ≠ x₀ := fun he => hn (he ▸ List.mem_cons_self)
      rw [← hag.env n (fun h' => hn (List.mem_cons_of_mem _ h'))]
      simp only [State.setEnv, SemanticsProperties.lookupBy_setBy_ne hne]
    · simp only [Upd.lastWrite] at hx
      split at hx
      · cases hx
      · rename_i hU'
        split at hx
        · cases hx
        · rename_i hne
          rw [hnone x hU']
          have : x ≠ x₀ := fun h' => hne (h' ▸ hx₀)
          simp only [State.setEnv, SemanticsProperties.lookupBy_setBy_ne this]
    · simp only [Upd.lastWrite] at hx
      split at hx
      · rename_i hU'
        cases hx
        exact hsome x _ hU'
      · rename_i hU'
        split at hx
        · rename_i hxe
          cases hx
          rw [hx₀] at hxe
          cases hxe
          exact ⟨b₀, hb₀, by rw [hnone _ hU']; simp only [State.setEnv,
              SemanticsProperties.lookupBy_setBy_self]⟩
        · cases hx

/-- After an update of locals, a variable reads as what the update binds it
to, read before the update.

Example: after `{ se1 := 10 ‖ sp1 := alice.account }`, `se1` reads `10` and
`sp1` the path `alice.account`, as `10` and `alice.account` read before it. -/
theorem Upd.substAgree {U : Upd C} (hU : U.envOnly = true) {σ τ : State}
    (h : U.apply σ = .ok τ) : SubstAgree U U.targets σ τ := by
  obtain ⟨hag, hnone, hsome⟩ := Upd.foldl_env σ U hU h
  have getEnv_eq : ∀ x, U.lastWrite x = none → τ.getEnv x = σ.getEnv x := fun x hx => by
    simp only [State.getEnv, hnone x hx]
  have written : ∀ x e, U.lastWrite x = some e →
      ∃ b, τ.getEnv x = .ok b ∧ ∀ l, b ≠ .ledger l := fun x e hx => by
    obtain ⟨b, hb, hl⟩ := hsome x e hx
    refine ⟨b, by simp only [State.getEnv, hl], fun l hbl => ?_⟩
    subst hbl
    have hvar := Upd.lastWrite_var hx
    cases e with
    | val _ t | path _ t | mref _ t =>
      simp only [UpdElem.binding, bind, Except.bind] at hb
      split at hb <;> simp only [pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hb
    | storage | memory | transfer | store | saveNet | book => simp only [UpdElem.var?,
        reduceCtorEq] at hvar
  refine ⟨hag, fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_,
    fun x hx => (getEnv_eq x hx).symm, written, fun x e hx => ?_⟩
  rotate_left 4
  · obtain ⟨b, hb, _⟩ := hsome x e hx
    exact ⟨b, hb⟩
  rotate_left 3
  · unfold Upd.storOf
    split
    · rename_i e hx
      obtain ⟨b, hb, hl⟩ := hsome x _ hx
      have hvar := Upd.lastWrite_var hx
      have hτ : τ.getEnv x = .ok b := by simp only [State.getEnv, hl]
      have hb' : ∀ st, b ≠ .store st := by
        intro st hst
        subst hst
        cases e with
        | val _ t =>
          simp only [UpdElem.binding, bind, Except.bind] at hb
          split at hb <;> simp only [pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hb
        | path _ p =>
          simp only [UpdElem.binding, bind, Except.bind] at hb
          split at hb <;> simp only [pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hb
        | mref _ i =>
          simp only [UpdElem.binding, bind, Except.bind] at hb
          split at hb <;> simp only [pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hb
        | storage | memory | transfer | store | saveNet | book => simp only [UpdElem.var?,
            reduceCtorEq] at hvar
      simp only [STerm.stuck_eval, STerm.eval, hτ, bind, Except.bind]
      cases b with
      | store st => exact absurd rfl (hb' st)
      | _ => rfl
    · rename_i hx
      simp only [STerm.eval, getEnv_eq x hx, bind, Except.bind]
      cases σ.getEnv x with
      | error => rfl
      | ok b =>
        cases b with
        | store st => exact ⟨rfl, hag.heap, hag.nextId, hag.net, hag.env, hag.selfBalance, hag.tx⟩
        | _ => rfl
  · unfold Upd.valOf
    split
    · rename_i y t hx
      obtain ⟨b, hb, hl⟩ := hsome x _ hx
      simp only [UpdElem.binding, bind, Except.bind] at hb
      cases ht : t.eval σ with
      | error e => simp only [ht, reduceCtorEq] at hb
      | ok v =>
        simp only [ht, pure, Except.pure, Except.ok.injEq] at hb
        subst hb
        simp only [Term.eval, bind, Except.bind, State.getEnv, hl, pure, Except.pure]
    · rename_i e hnv hx
      obtain ⟨b, hb, hl⟩ := hsome x _ hx
      have hvar := Upd.lastWrite_var hx
      cases e with
      | val => exact absurd rfl (hnv _ _)
      | path _ p =>
        simp only [UpdElem.binding, bind, Except.bind] at hb
        cases hp : p.eval σ with
        | error => simp only [hp, reduceCtorEq] at hb
        | ok r =>
          simp only [hp, pure, Except.pure, Except.ok.injEq] at hb
          subst hb
          simp only [Term.stuck_eval, Term.eval, bind, Except.bind, State.getEnv, hl]
      | mref _ i =>
        simp only [UpdElem.binding, bind, Except.bind] at hb
        cases hi : i.eval σ with
        | error => simp only [hi, reduceCtorEq] at hb
        | ok r =>
          simp only [hi, pure, Except.pure, Except.ok.injEq] at hb
          subst hb
          simp only [Term.stuck_eval, Term.eval, bind, Except.bind, State.getEnv, hl]
      | storage | memory | transfer | store | saveNet | book => simp only [UpdElem.var?,
          reduceCtorEq] at hvar
    · rename_i hx
      simp only [Term.eval, getEnv_eq x hx]
  · unfold Upd.pathOf
    split
    · rename_i y p hx
      obtain ⟨b, hb, hl⟩ := hsome x _ hx
      simp only [UpdElem.binding, bind, Except.bind] at hb
      cases hp : p.eval σ with
      | error e => simp only [hp, reduceCtorEq] at hb
      | ok r =>
        simp only [hp, pure, Except.pure, Except.ok.injEq] at hb
        subst hb
        simp only [PTerm.eval, aliasPath, bind, Except.bind, State.getEnv, hl, pure, Except.pure]
    · rename_i e hnp hx
      obtain ⟨b, hb, hl⟩ := hsome x _ hx
      have hvar := Upd.lastWrite_var hx
      cases e with
      | path => exact absurd rfl (hnp _ _)
      | val _ t =>
        simp only [UpdElem.binding, bind, Except.bind] at hb
        cases ht : t.eval σ with
        | error => simp only [ht, reduceCtorEq] at hb
        | ok r =>
          simp only [ht, pure, Except.pure, Except.ok.injEq] at hb
          subst hb
          simp only [PTerm.stuck_eval, PTerm.eval, aliasPath, bind, Except.bind, State.getEnv, hl]
      | mref _ i =>
        simp only [UpdElem.binding, bind, Except.bind] at hb
        cases hi : i.eval σ with
        | error => simp only [hi, reduceCtorEq] at hb
        | ok r =>
          simp only [hi, pure, Except.pure, Except.ok.injEq] at hb
          subst hb
          simp only [PTerm.stuck_eval, PTerm.eval, aliasPath, bind, Except.bind, State.getEnv, hl]
      | storage | memory | transfer | store | saveNet | book => simp only [UpdElem.var?,
          reduceCtorEq] at hvar
    · rename_i hx
      simp only [PTerm.eval, aliasPath, getEnv_eq x hx]
  · unfold Upd.refOf
    split
    · rename_i y i hx
      obtain ⟨b, hb, hl⟩ := hsome x _ hx
      simp only [UpdElem.binding, bind, Except.bind] at hb
      cases hi : i.eval σ with
      | error e => simp only [hi, reduceCtorEq] at hb
      | ok r =>
        simp only [hi, pure, Except.pure, Except.ok.injEq] at hb
        subst hb
        simp only [ITerm.eval, bind, Except.bind, State.getEnv, hl, pure, Except.pure]
    · rename_i e hnr hx
      obtain ⟨b, hb, hl⟩ := hsome x _ hx
      have hvar := Upd.lastWrite_var hx
      cases e with
      | mref => exact absurd rfl (hnr _ _)
      | val _ t =>
        simp only [UpdElem.binding, bind, Except.bind] at hb
        cases ht : t.eval σ with
        | error => simp only [ht, reduceCtorEq] at hb
        | ok r =>
          simp only [ht, pure, Except.pure, Except.ok.injEq] at hb
          subst hb
          simp only [ITerm.stuck_eval, ITerm.eval, bind, Except.bind, State.getEnv, hl]
      | path _ p =>
        simp only [UpdElem.binding, bind, Except.bind] at hb
        cases hp : p.eval σ with
        | error => simp only [hp, reduceCtorEq] at hb
        | ok r =>
          simp only [hp, pure, Except.pure, Except.ok.injEq] at hb
          subst hb
          simp only [ITerm.stuck_eval, ITerm.eval, bind, Except.bind, State.getEnv, hl]
      | storage | memory | transfer | store | saveNet | book => simp only [UpdElem.var?,
          reduceCtorEq] at hvar
    · rename_i hx
      simp only [ITerm.eval, getEnv_eq x hx]

/-- **Running `U` then `V` is running `U ‖ {U}V`**, for `U` an update of locals.

Example: for `x = 1; y = x;`, running `{ x := 1 }` then `{ y := x }` is
running `{ x := 1 ‖ y := 1 }`. -/
theorem Upd.apply_seq {U : Upd C} (hU : U.envOnly = true) (V : Upd C) (σ : State) :
    (U ++ V.subst U).apply σ = (U.apply σ >>= V.apply) := by
  unfold Upd.apply
  rw [List.foldlM_append]
  cases h : U.foldlM (fun ρ e => e.write σ ρ) σ with
  | error => rfl
  | ok τ => exact Upd.foldl_subst (Upd.substAgree hU h) V τ

/-! ## Effectless elements

An element has no effect on `{U} φ` when a later element of `U` writes the
same variable (it is *shadowed*), or when `φ` does not mention the variable
(it is *unused*).  Dropping it also drops its halting, so only an element
that cannot halt goes.  A `storage :=`, `memory :=` or `transfer` element
never goes. -/

/-- The element can go from `{e ‖ rest} φ`, `F` the variables of `φ`. -/
def UpdElem.effectless (F : List Var) (rest : Upd C) (e : UpdElem C) : Bool :=
  e.total && match e.var? with
    | some x => !(F.contains x) || rest.any (·.var? == some x)
    | none => false

/-- `\dropEffectlessElementaries`: drop the elements that are shadowed or
unused and cannot halt, reading `F` as the variables of the formula under
the update. -/
def Upd.dropEffectless (F : List Var) : Upd C → Upd C
  | [] => []
  | e :: U => if e.effectless F U then Upd.dropEffectless F U else e :: Upd.dropEffectless F U

/-- Agreeing off fewer names is agreeing off more: two states that differ
only at `se1` differ only at `se1` and `sp1`. -/
theorem Semantics.EnvAgreeExcept.mono {A B : List Var} {σ τ : State} (h : EnvAgreeExcept A σ τ)
    (hAB : ∀ x ∈ A, x ∈ B) : EnvAgreeExcept B σ τ :=
  ⟨h.storage, h.heap, h.nextId, h.net, fun n hn => h.env n (fun h' => hn (hAB n h')), h.selfBalance, h.tx⟩

/-- Binding `x` on both sides makes two states agree at `x`: after `x = 1;` in
two states that differed at `x` and `y`, they differ at `y` only. -/
theorem Semantics.EnvAgreeExcept.setEnv_filter {A : List Var} {σ τ : State} (h : EnvAgreeExcept A σ τ)
    (x : Var) (b : Binding) :
    EnvAgreeExcept (A.filter (· != x)) (σ.setEnv x b) (τ.setEnv x b) :=
  ⟨h.storage, h.heap, h.nextId, h.net, fun n hn => by
    by_cases he : n = x
    · subst he; simp only [State.setEnv, SemanticsProperties.lookupBy_setBy_self]
    · have : n ∉ A := fun h' => hn (List.mem_filter.2 ⟨h', by simpa using he⟩)
      simp only [State.setEnv, SemanticsProperties.lookupBy_setBy_ne he, h.env n this],
    h.selfBalance, h.tx⟩

/-- One element written into two agreeing states, its right-hand side read
in the same pre-state, leaves them agreeing: `y := 2` written into two
states that differ at `x` gives two that differ at `x`. -/
theorem UpdElem.write_agree {A : List Var} {σ₀ τ₁ τ₂ : State} (h : EnvAgreeExcept A τ₁ τ₂) :
    (e : UpdElem C) → ResultsAgree A (e.write σ₀ τ₁) (e.write σ₀ τ₂)
  | .val .. | .path .. | .mref .. | .transfer .. => by simp only [UpdElem.write]; agree_run h
  | .store x s => by
    simp only [UpdElem.write]
    cases s.eval σ₀ with
    | error => rfl
    | ok a => exact h.setEnv_both x _
  | .storage s => by
    simp only [UpdElem.write]
    cases s.eval σ₀ with
    | error => rfl
    | ok a => exact ⟨rfl, h.heap, h.nextId, h.net, h.env, h.selfBalance, h.tx⟩
  | .memory m => by
    simp only [UpdElem.write]
    cases m.eval σ₀ with
    | error => rfl
    | ok a => exact ⟨h.storage, rfl, rfl, h.net, h.env, h.selfBalance, h.tx⟩
  | .saveNet x => by simp only [UpdElem.write]; exact h.setEnv_both x _
  | .book _ => by
    simp only [UpdElem.write]
    agree_run h
    exact ⟨h.storage, h.heap, h.nextId, rfl, h.env, rfl, h.tx⟩

/-- The invariant of dropping: the two runs agree off `A`, and every variable
of `A` is either one the formula does not read (`G`) or one the rest of the
update writes again — whose last write is kept, and sets it alike on both
sides.

Example: in `{ x := 0 ‖ y := 2 ‖ x := 1 } x = 1` (after `x = 0; y = 2; x = 1;`)
`x := 0` goes, the runs differ at `x` until `x := 1`, and `y := 2` goes,
the runs then differing at `y`, which `x = 1` does not read. -/
theorem Upd.dropEffectless_foldl (F G : List Var) (σ₀ : State) :
    (U : Upd C) → (∀ e ∈ U, ∀ x, e.var? = some x → x ∉ F → x ∈ G) →
    ∀ {A : List Var} {τ₁ τ₂ : State}, EnvAgreeExcept A τ₁ τ₂ →
      (∀ x ∈ A, x ∈ G ∨ (x ∈ F ∧ U.any (·.var? == some x) = true)) →
      ResultsAgree G ((U.dropEffectless F).foldlM (fun ρ e => e.write σ₀ ρ) τ₁)
        (U.foldlM (fun ρ e => e.write σ₀ ρ) τ₂)
  | [], _, A, τ₁, τ₂, h, hA =>
    h.mono fun x hx => (hA x hx).elim id fun ⟨_, h'⟩ => by simp only [List.any_nil,
        Bool.false_eq_true] at h'
  | e :: U, hG, A, τ₁, τ₂, h, hA => by
    have hGU : ∀ e ∈ U, ∀ x, e.var? = some x → x ∉ F → x ∈ G :=
      fun e' he' => hG e' (List.mem_cons_of_mem _ he')
    simp only [Upd.dropEffectless]
    split
    · -- dropped: the full run writes `x₀`, the other does not
      rename_i hd
      simp only [UpdElem.effectless, Bool.and_eq_true] at hd
      obtain ⟨ht, hx⟩ := hd
      obtain ⟨x₀, hx₀⟩ := UpdElem.total_var ht
      obtain ⟨b, hb⟩ := UpdElem.total_binding σ₀ ht
      rw [hx₀] at hx
      simp only [List.foldlM_cons, UpdElem.write_var hx₀, hb]
      refine Upd.dropEffectless_foldl F G σ₀ U hGU (A := x₀ :: A)
        ((h.mono fun y hy => List.mem_cons_of_mem _ hy).setEnv_right List.mem_cons_self b) ?_
      have hx₀' : x₀ ∈ G ∨ (x₀ ∈ F ∧ U.any (·.var? == some x₀) = true) := by
        by_cases hF : x₀ ∈ F
        · simp only [Bool.or_eq_true, Bool.not_eq_true'] at hx
          rcases hx with hx | hx
          · rw [List.contains_iff_mem.2 hF] at hx; cases hx
          · exact .inr ⟨hF, hx⟩
        · exact .inl (hG e List.mem_cons_self x₀ hx₀ hF)
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hx₀'
      rcases hA y hy with hy | ⟨hF, hany⟩
      · exact .inl hy
      simp only [List.any_cons, Bool.or_eq_true] at hany
      rcases hany with he | hany
      · have : y = x₀ := by
          rw [hx₀] at he; exact (by simpa using he : x₀ = y).symm
        subst this; exact hx₀'
      · exact .inr ⟨hF, hany⟩
    · -- kept: both runs write it
      simp only [List.foldlM_cons]
      cases hv : e.var? with
      | some x₀ =>
        rw [UpdElem.write_var hv, UpdElem.write_var hv]
        cases e.binding σ₀ with
        | error => rfl
        | ok b =>
          refine Upd.dropEffectless_foldl F G σ₀ U hGU (h.setEnv_filter x₀ b) fun y hy => ?_
          obtain ⟨hy, hne⟩ := List.mem_filter.1 hy
          have hne : y ≠ x₀ := by simpa using hne
          rcases hA y hy with hy | ⟨hF, hany⟩
          · exact .inl hy
          simp only [List.any_cons, Bool.or_eq_true, hv, beq_iff_eq, Option.some.injEq] at hany
          rcases hany with he | hany
          · exact absurd he.symm hne
          · exact .inr ⟨hF, hany⟩
      | none =>
        match e.write σ₀ τ₁, e.write σ₀ τ₂, UpdElem.write_agree (σ₀ := σ₀) h e with
        | .error _, .error _, he => subst he; rfl
        | .ok a, .ok c, hac =>
          refine Upd.dropEffectless_foldl F G σ₀ U hGU hac fun y hy => ?_
          rcases hA y hy with hy | ⟨hF, hany⟩
          · exact .inl hy
          simp only [List.any_cons, Bool.or_eq_true, hv] at hany
          rcases hany with he | hany
          · simp only [Option.none_beq_some, Bool.false_eq_true] at he
          · exact .inr ⟨hF, hany⟩

/-- Dropping the effectless elements changes only variables the formula does
not read.

Example: dropping `se1 := 10` and `sp1 := alice.account` from the update of
`alice.account.balance = 10;` changes only `se1` and `sp1`. -/
theorem Upd.dropEffectless_apply (F : List Var) (U : Upd C) (σ : State) :
    ResultsAgree ((Upd.targets U).filter (· ∉ F)) ((U.dropEffectless F).apply σ) (U.apply σ) :=
  Upd.dropEffectless_foldl F _ σ U
    (fun e he x hx hF => List.mem_filter.2 ⟨List.mem_filterMap.2 ⟨e, he, hx⟩, by simpa using hF⟩)
    (EnvAgreeExcept.refl [] σ) (by simp)

/-- Dropping the effectless elements does not change whether the formula under
the update holds.

Example: for `alice.account.balance = 10;`,
`{ storage := save(storage, alice.account.balance, 10) } find(storage, alice.account.balance) = 10`
holds exactly when the same formula under the three-element merged update does. -/
theorem Upd.dropEffectless_holds (m : Modality) (U : Upd C) (φ : Fml C) (σ : State) :
    holds σ (.upd m (U.dropEffectless φ.vars) φ) ↔ holds σ (.upd m U φ) :=
  m.after_frame (Upd.dropEffectless_apply φ.vars U σ) fun _ _ h =>
    holds_frame φ (fun x hx hG => by
      have := (List.mem_filter.1 hG).2
      simp only [decide_eq_true_eq] at this
      exact this hx) h

/-! ## `x := x` -/

/-- An element that writes a variable its own old value, `x := x`. -/
def UpdElem.isSelf : UpdElem C → Bool
  | .val x (.pv y) | .path x (.pv y) | .mref x (.pv y) => x == y
  | _ => false

/-- Binding `x` to what it is bound to changes nothing: after `x = 1;`,
binding `x` to `1` again gives the same lookups. -/
theorem State.setEnv_same {σ : State} {x : Var} {b : Binding} (hl : lookupBy x σ.env = some b) :
    EnvAgreeExcept [] (σ.setEnv x b) σ := by
  refine ⟨rfl, rfl, rfl, rfl, fun n _ => ?_, rfl, rfl⟩
  by_cases he : n = x
  · subst he; simp only [State.setEnv, SemanticsProperties.lookupBy_setBy_self, hl]
  · simp only [State.setEnv, SemanticsProperties.lookupBy_setBy_ne he]

/-- Writing `x := x` changes nothing, when it does not halt.

Example: `x = x;` leaves `{ x := x }`; where `x` holds a value, writing it
gives back the state it started from. -/
theorem UpdElem.write_self {σ τ : State} :
    {e : UpdElem C} → e.isSelf = true → e.write σ σ = .ok τ → EnvAgreeExcept [] τ σ
  | .val x (.pv y), h, hw | .path x (.pv y), h, hw | .mref x (.pv y), h, hw => by
    simp only [UpdElem.isSelf, beq_iff_eq] at h
    subst h
    cases hl : lookupBy x σ.env with
    | none =>
      simp only [write, bind, Except.bind, Term.eval, PTerm.eval, aliasPath, ITerm.eval,
        State.getEnv, hl, reduceCtorEq] at hw
    | some b =>
      cases b <;>
        simp only [write, bind, Except.bind, Term.eval, PTerm.eval, aliasPath, ITerm.eval,
          State.getEnv, hl, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hw <;>
        subst hw <;> exact State.setEnv_same hl

/-- `{x := x ‖ U} φ` is `{U} φ` when `x := x` does not halt. -/
theorem UpdElem.elimSelf_holds {e : UpdElem C} (he : e.isSelf = true) {σ τ : State}
    (hw : e.write σ σ = .ok τ) (m : Modality) (U : Upd C) (φ : Fml C) :
    holds σ (.upd m (e :: U) φ) ↔ holds σ (.upd m U φ) := by
  simp only [holds, Upd.apply, List.foldlM_cons, hw]

  exact m.after_frame (Upd.foldl_frame (EnvAgreeExcept.refl [] σ) U (fun _ _ h => nomatch h)
    (UpdElem.write_self he hw)) fun _ _ h => holds_frame φ (fun _ _ h => by simp at h) h

/-- **`elimSelfUpdate`, under the box**: to prove `{x := x ‖ U} φ`, prove
`{U} φ`.  Where `x` holds no value `x := x` halts, and the box is true.

Example: `[ x = x; y = 3; ] y == 3` leaves `{ x := x ‖ y := 3 } y = 3`, which
`{ y := 3 } y = 3` proves. -/
theorem UpdElem.elimSelf_box {e : UpdElem C} (he : e.isSelf = true) {σ : State} {U : Upd C}
    {φ : Fml C} (h : holds σ (.upd .box U φ)) : holds σ (.upd .box (e :: U) φ) := by
  cases hw : e.write σ σ with
  | error => simp only [holds, Modality.after, Upd.apply, List.foldlM_cons, bind, Except.bind, hw,
      Modality.onHalt]
  | ok τ => exact (UpdElem.elimSelf_holds he hw .box U φ).2 h

/-- **`elimSelfUpdate`, under the diamond**, the other way: `{x := x ‖ U} φ`
gives `{U} φ`; the converse fails where `x` holds no value.

Example: `⟨ x = x; y = 3; ⟩ y == 3` leaves `{ x := x ‖ y := 3 } y = 3`, from
which `{ y := 3 } y = 3` follows. -/
theorem UpdElem.elimSelf_diamond {e : UpdElem C} (he : e.isSelf = true) {σ : State}
    {U : Upd C} {φ : Fml C} (h : holds σ (.upd .diamond (e :: U) φ)) :
    holds σ (.upd .diamond U φ) := by
  cases hw : e.write σ σ with
  | error => simp only [holds, Modality.after, Upd.apply, List.foldlM_cons, bind, Except.bind, hw,
      Modality.onHalt] at h
  | ok τ => exact (UpdElem.elimSelf_holds he hw .diamond U φ).1 h

/-! ### Substitution is denotation after the update

`holds` reads an equation through `denote`, which is total: a halting term
denotes something (`Res.toSt`), and so does `Term.stuck`, `PTerm.stuck` and
`STerm.stuck` — not always what the variable they replace denotes after the
update.  A value variable is fine (`Term.stuck` and an unbound value both
denote `st mtSt`); a path or storage variable written at another sort is not:
`find(x, a)` after `{ x := 1 }` denotes `st mtSt`, its substitution
`find(STerm.stuck, a)` reads `a` in the storage.  KeY's terms are sorted and
cannot say it; here `Term.sortedFor U` excludes it. -/

/-- `U` writes `x`, if at all, as an alias. -/
def Upd.pathSorted (U : Upd C) (x : Var) : Bool :=
  match U.lastWrite x with
  | some (.path ..) | none => true
  | some _ => false

mutual

/-- Every alias the term reads `U` writes, if at all, as an alias, and every
storage variable it reads `U` does not write. -/
def Term.sortedFor (U : Upd C) : Term C → Bool
  | .lit _ | .pv _ | .env _ | .read .. | .mlen .. => true
  | .binop _ _ a b => a.sortedFor U && b.sortedFor U
  | .unop _ _ a | .net a | .netOf _ a => a.sortedFor U
  | .find s p | .len s p => s.sortedFor U && p.sortedFor U
  | .ite c a b => c.sortedFor U && a.sortedFor U && b.sortedFor U

def PTerm.sortedFor (U : Upd C) : PTerm C → Bool
  | .root _ => true
  | .pv x => U.pathSorted x
  | .field p _ | .next p => p.sortedFor U
  | .at p i => p.sortedFor U && i.sortedFor U

def STerm.sortedFor (U : Upd C) : STerm C → Bool
  | .storage => true
  | .pv x => (U.lastWrite x).isNone
  | .save s p v | .push s p v => s.sortedFor U && p.sortedFor U && v.sortedFor U
  | .delAt s p | .pop s p | .shrink s p | .pushSlot s p _ | .extend s p _ =>
    s.sortedFor U && p.sortedFor U

def SValT.sortedFor (U : Upd C) : SValT C → Bool
  | .val t | .newArr _ t => t.sortedFor U
  | .find s p => s.sortedFor U && p.sortedFor U
  | .copyMem .. => true

end

/-- A value variable that does not read denotes nothing. -/
theorem Term.pv_denote_of_error {σ : State} {x : Var} {e : Halt}
    (h : (Term.pv x : Term C).eval σ = .error e) : (Term.pv x : Term C).denote σ = .st .mtSt := by
  simp only [Term.eval, bind, Except.bind] at h
  simp only [Term.denote]
  split at h
  · rename_i he
    simp only [he]
  · rename_i b hb
    rw [hb]
    cases b <;> simp_all only [pure, Except.pure, reduceCtorEq]

/-- An alias that does not resolve denotes the empty path. -/
theorem PTerm.pv_denote_of_error {σ : State} {x : Var} {e : Halt}
    (h : (PTerm.pv x : PTerm C).eval σ = .error e) : (PTerm.pv x : PTerm C).denote σ = [] := by
  have h' : aliasPath σ x = .error e := h
  simp only [PTerm.denote, h']

section SubstDenote

variable {U : Upd C} {ns : List Var} {σ τ : State}

open Theory Theory.StValue

theorem SubstAgree.abs_eq (h : SubstAgree U ns σ τ) : σ.abs = τ.abs := by
  simp only [State.abs, h.agree.storage]

/-- `{U}x` denotes before the update what `x` denotes after it. -/
theorem SubstAgree.val_denote (h : SubstAgree U ns σ τ) (x : Var) :
    Equiv ((U.valOf x).denote σ) ((Term.pv x : Term C).denote τ) := by
  have h1 : (U.valOf x).eval σ = (Term.pv x : Term C).eval τ := h.val x
  cases hv : (U.valOf x).eval σ with
  | ok v =>
    rw [hv] at h1
    rw [Term.denote_eval hv, Term.denote_eval h1.symm]
    exact Equiv.refl _
  | error e =>
    rw [hv] at h1
    rw [Term.pv_denote_of_error h1.symm]
    unfold Upd.valOf at hv ⊢
    split
    · rename_i y t hx
      rw [hx] at hv
      obtain ⟨b, hb⟩ := h.bound x _ hx
      simp only [UpdElem.binding, hv, bind, Except.bind, reduceCtorEq] at hb
    · exact Equiv.refl _
    · rename_i hx
      rw [hx] at hv
      rw [Term.pv_denote_of_error hv]
      exact Equiv.refl _

/-- `{U}p` denotes before the update the path `p` denotes after it. -/
theorem SubstAgree.path_denote (h : SubstAgree U ns σ τ) {x : Var} (hs : U.pathSorted x = true) :
    (U.pathOf x).denote σ = (PTerm.pv x : PTerm C).denote τ := by
  have h1 : (U.pathOf x).eval σ = (PTerm.pv x : PTerm C).eval τ := h.path x
  cases hp : (U.pathOf x).eval σ with
  | ok rs =>
    obtain ⟨r, segs⟩ := rs
    rw [hp] at h1
    rw [PTerm.denote_eval hp, PTerm.denote_eval h1.symm]
  | error e =>
    rw [hp] at h1
    rw [PTerm.pv_denote_of_error h1.symm]
    unfold Upd.pathSorted at hs
    unfold Upd.pathOf at hp ⊢
    split
    · rename_i y q hx
      rw [hx] at hp
      obtain ⟨b, hb⟩ := h.bound x _ hx
      simp only [UpdElem.binding, hp, bind, Except.bind, reduceCtorEq] at hb
    · rename_i e' hne hx
      rw [hx] at hs
      split at hs
      · rename_i heq
        cases heq
        exact absurd rfl (hne _ _)
      · simp_all only [reduceCtorEq]
      · cases hs
    · rename_i hx
      rw [hx] at hp
      exact PTerm.pv_denote_of_error hp

mutual

/-- A substituted term denotes before the update, up to `Equiv`, what the
term denotes after it.

Example: after `y = 3;`, `{ y := 3 }(y + 1)` is `3 + 1`, which denotes `4`
before the update as `y + 1` does after it. -/
theorem Term.subst_denote (h : SubstAgree U ns σ τ) :
    (t : Term C) → t.sortedFor U = true → Equiv ((t.subst U).denote σ) (t.denote τ)
  | .lit _, _ => Equiv.refl _
  | .pv x, _ => h.val_denote x
  | .binop op p a b, hs => by
    simp only [Term.sortedFor, Bool.and_eq_true] at hs
    simp only [Term.subst, Term.denote, (Term.subst_denote h a hs.1).toRes,
      (Term.subst_denote h b hs.2).toRes]
    exact Equiv.refl _
  | .unop op p a, hs => by
    simp only [Term.subst, Term.denote, (Term.subst_denote h a hs).toRes]
    exact Equiv.refl _
  | .find s p, hs => by
    simp only [Term.sortedFor, Bool.and_eq_true] at hs
    simp only [Term.subst, Term.denote, PTerm.subst_denote h p hs.2]
    exact Equiv.findSt (STerm.subst_denote h s hs.1) _
  | .len s p, hs => by
    simp only [Term.sortedFor, Bool.and_eq_true] at hs
    simp only [Term.subst, Term.denote, PTerm.subst_denote h p hs.2]
    exact Equiv.findSt (STerm.subst_denote h s hs.1) _
  | .read m a, _ => by
    show Equiv (Res.toSt (((Term.read m a).subst U).eval σ)) (Res.toSt ((Term.read m a).eval τ))
    rw [Term.subst_eval h]
    exact Equiv.refl _
  | .mlen m i, _ => by
    show Equiv (Res.toSt (((Term.mlen m i).subst U).eval σ)) (Res.toSt ((Term.mlen m i).eval τ))
    rw [Term.subst_eval h]
    exact Equiv.refl _
  | .ite c a b, hs => by
    simp only [Term.sortedFor, Bool.and_eq_true] at hs
    have ea : Equiv ((a.subst U).denote σ) (a.denote τ) := Term.subst_denote h a hs.1.2
    have eb : Equiv ((b.subst U).denote σ) (b.denote τ) := Term.subst_denote h b hs.2
    simp only [Term.subst, Term.denote]
    rcases (Term.subst_denote h c hs.1.1).eq_or_st with hc | ⟨s, t, hc, hc'⟩
    · rw [hc]
      split
      · exact ea
      · exact eb
      · exact Equiv.refl _
    · rw [hc, hc']
      exact Equiv.refl _
  | .env k, _ => by
    simp only [Term.subst, Term.denote, State.envVal_congr h.agree]
    exact Equiv.refl _
  | .net a, hs => by
    simp only [Term.subst, Term.denote, State.getNet, h.agree.net]
    rcases (Term.subst_denote h a hs).eq_or_st with ha | ⟨s, t, ha, ha'⟩
    · rw [ha]
      exact Equiv.refl _
    · rw [ha, ha']
      exact Equiv.refl _
  | .netOf x a, hs => by
    simp only [Term.subst]
    split
    · rename_i e hx
      obtain ⟨b, hb, hnl⟩ := h.written x e hx
      show Equiv (Term.stuck.denote σ) _
      simp only [Term.denote, hb]
      cases b with
      | ledger l => exact absurd rfl (hnl l)
      | _ => exact Equiv.refl _
    · rename_i hx
      simp only [Term.denote, h.unwritten x hx]
      rcases (Term.subst_denote h a hs).eq_or_st with ha | ⟨s, t, ha, ha'⟩
      · rw [ha]
        exact Equiv.refl _
      · rw [ha, ha']
        rcases τ.getEnv x with _ | b
        · exact Equiv.refl _
        · cases b <;> exact Equiv.refl _

/-- A substituted path denotes before the update the path it denotes after it. -/
theorem PTerm.subst_denote (h : SubstAgree U ns σ τ) :
    (p : PTerm C) → p.sortedFor U = true → (p.subst U).denote σ = p.denote τ
  | .root _, _ => rfl
  | .pv _, hs => h.path_denote hs
  | .field p _, hs => by simp only [PTerm.subst, PTerm.denote, PTerm.subst_denote h p hs]
  | .at p i, hs => by
    simp only [PTerm.sortedFor, Bool.and_eq_true] at hs
    simp only [PTerm.subst, PTerm.denote, PTerm.subst_denote h p hs.1,
      (Term.subst_denote h i hs.2).asInt]
  | .next p, hs => by
    simp only [PTerm.subst, PTerm.denote, PTerm.subst_denote h p hs, h.abs_eq]

/-- A substituted storage denotes before the update, up to `Equiv`, the
storage it denotes after it. -/
theorem STerm.subst_denote (h : SubstAgree U ns σ τ) :
    (s : STerm C) → s.sortedFor U = true → Struct.Equiv ((s.subst U).denote σ) (s.denote τ)
  | .storage, _ => by
    simp only [STerm.subst, STerm.denote, h.abs_eq]
    exact Equiv.refl _
  | .pv x, hs => by
    simp only [STerm.sortedFor, Option.isNone_iff_eq_none] at hs
    simp only [STerm.subst, Upd.storOf, hs, STerm.denote, h.unwritten x hs]
    exact Equiv.refl _
  | .save s p v, hs => by
    simp only [STerm.sortedFor, Bool.and_eq_true] at hs
    simp only [STerm.subst, STerm.denote, PTerm.subst_denote h p hs.1.2]
    exact Struct.Equiv.copyTo (STerm.subst_denote h s hs.1.1) (SValT.subst_denote h v hs.2) _
  | .delAt s p, hs => by
    simp only [STerm.sortedFor, Bool.and_eq_true] at hs
    simp only [STerm.subst, STerm.denote, PTerm.subst_denote h p hs.2]
    exact Struct.Equiv.delAt (STerm.subst_denote h s hs.1) _
  | .push s p v, hs => by
    simp only [STerm.sortedFor, Bool.and_eq_true] at hs
    simp only [STerm.subst, STerm.denote, PTerm.subst_denote h p hs.1.2]
    exact Struct.Equiv.pushT (STerm.subst_denote h s hs.1.1)
      (Equiv.stripVal (SValT.subst_denote h v hs.2)) _
  | .pushSlot s p _, hs => by
    simp only [STerm.sortedFor, Bool.and_eq_true] at hs
    simp only [STerm.subst, STerm.denote, PTerm.subst_denote h p hs.2]
    exact Struct.Equiv.pushSlotT _ _ (STerm.subst_denote h s hs.1) _
  | .extend s p _, hs => by
    simp only [STerm.sortedFor, Bool.and_eq_true] at hs
    simp only [STerm.subst, STerm.denote, PTerm.subst_denote h p hs.2]
    exact Struct.Equiv.pushSlotT _ _ (STerm.subst_denote h s hs.1) _
  | .pop s p, hs => by
    simp only [STerm.sortedFor, Bool.and_eq_true] at hs
    simp only [STerm.subst, STerm.denote, PTerm.subst_denote h p hs.2]
    exact Struct.Equiv.popT (STerm.subst_denote h s hs.1) _
  | .shrink s p, hs => by
    simp only [STerm.sortedFor, Bool.and_eq_true] at hs
    simp only [STerm.subst, STerm.denote, PTerm.subst_denote h p hs.2]
    exact Struct.Equiv.shrinkT (STerm.subst_denote h s hs.1) _

/-- A substituted stored value denotes before the update, up to `Equiv`, what
it denotes after it. -/
theorem SValT.subst_denote (h : SubstAgree U ns σ τ) :
    (v : SValT C) → v.sortedFor U = true → Equiv ((v.subst U).denote σ) (v.denote τ)
  | .val t, hs => Term.subst_denote h t hs
  | .find s p, hs => by
    simp only [SValT.sortedFor, Bool.and_eq_true] at hs
    simp only [SValT.subst, SValT.denote, PTerm.subst_denote h p hs.2]
    exact Equiv.findSt (STerm.subst_denote h s hs.1) _
  | .copyMem m i, _ => by
    show Equiv (match ((SValT.copyMem m i).subst U).eval σ with
      | .ok w => w.abs
      | .error _ => .st .mtSt) _
    rw [SValT.subst_eval h]
    exact Equiv.refl _
  | .newArr R n, hs => by
    simp only [SValT.subst, SValT.denote, (Term.subst_denote h n hs).asInt]
    exact Equiv.refl _

end

end SubstDenote

/-! ## An update on a first-order formula -/

/-- No update and no modality in it: `applyOnRigidFormula` applies. -/
def Fml.rigid : Fml C → Bool
  | .tt | .eq .. | .defined _ => true
  | .not φ => φ.rigid
  | .and φ ψ | .imp φ ψ => φ.rigid && ψ.rigid
  | _ => false

/-- `{U} φ` for a first-order `φ`: `U` substituted into its terms. -/
def Fml.subst (U : Upd C) : Fml C → Fml C
  | .tt => .tt
  | .eq a b => .eq (a.subst U) (b.subst U)
  | .defined t => .defined (t.subst U)
  | .not φ => .not (φ.subst U)
  | .and φ ψ => .and (φ.subst U) (ψ.subst U)
  | .imp φ ψ => .imp (φ.subst U) (ψ.subst U)
  | φ => φ

/-- Every equation of `φ` reads its variables at the sorts `U` writes them
(`Term.sortedFor`). -/
def Fml.sortedFor (U : Upd C) : Fml C → Bool
  | .eq a b => a.sortedFor U && b.sortedFor U
  | .not φ => φ.sortedFor U
  | .and φ ψ | .imp φ ψ => φ.sortedFor U && ψ.sortedFor U
  | _ => true

/-- A substituted first-order formula holds before the update as the formula
does after it.

Example: after `y = 3;`, `(y = 3).subst { y := 3 }` is `3 = 3`, true before
the update as `y = 3` is after it. -/
theorem Fml.subst_holds {U : Upd C} {ns : List Var} {σ τ : State} (h : SubstAgree U ns σ τ) :
    (φ : Fml C) → φ.rigid = true → φ.sortedFor U = true → (holds σ (φ.subst U) ↔ holds τ φ)
  | .tt, _, _ => Iff.rfl
  | .eq a b, _, hs => by
    simp only [Fml.sortedFor, Bool.and_eq_true] at hs
    have ea : Theory.StValue.Equiv ((a.subst U).denote σ) (a.denote τ) :=
      Term.subst_denote h a hs.1
    have eb : Theory.StValue.Equiv ((b.subst U).denote σ) (b.denote τ) :=
      Term.subst_denote h b hs.2
    simp only [Fml.subst, holds]
    exact ⟨fun e => (ea.symm.trans e).trans eb, fun e => (ea.trans e).trans eb.symm⟩
  | .defined t, _, _ => by simp only [Fml.subst, holds, t.subst_eval h]
  | .not φ, hr, hs => by simp only [Fml.subst, holds, Fml.subst_holds h φ hr hs]
  | .and φ ψ, hr, hs => by
    simp only [Fml.rigid, Bool.and_eq_true] at hr
    simp only [Fml.sortedFor, Bool.and_eq_true] at hs
    simp only [Fml.subst, holds, Fml.subst_holds h φ hr.1 hs.1, Fml.subst_holds h ψ hr.2 hs.2]
  | .imp φ ψ, hr, hs => by
    simp only [Fml.rigid, Bool.and_eq_true] at hr
    simp only [Fml.sortedFor, Bool.and_eq_true] at hs
    simp only [Fml.subst, holds, Fml.subst_holds h φ hr.1 hs.1, Fml.subst_holds h ψ hr.2 hs.2]

/-- An update that cannot halt writes only locals: `{ se1 := 10 ‖ sp1 := alice.account }`. -/
theorem Upd.total_envOnly : {U : Upd C} → U.total = true → U.envOnly = true
  | [], _ => rfl
  | e :: U, h => by
    simp only [Upd.total, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨x, hx⟩ := UpdElem.total_var h.1
    simp only [Upd.envOnly, List.all_cons, hx, Option.isSome_some, Bool.true_and]
    exact Upd.total_envOnly (U := U) h.2

/-- An update none of whose elements can halt does not halt:
`{ se1 := 10 ‖ sp1 := alice.account }` runs in every state. -/
theorem Upd.foldl_total (σ₀ : State) : (U : Upd C) → U.total = true →
    ∀ τ₀, ∃ τ, U.foldlM (fun ρ e => e.write σ₀ ρ) τ₀ = .ok τ
  | [], _, τ₀ => ⟨τ₀, rfl⟩
  | e :: U, h, τ₀ => by
    simp only [Upd.total, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨x, hx⟩ := UpdElem.total_var h.1
    obtain ⟨b, hb⟩ := UpdElem.total_binding σ₀ h.1
    simp only [List.foldlM_cons, UpdElem.write_var hx, hb]
    exact Upd.foldl_total σ₀ U h.2 _

/-! ## The rules -/

/-- The update rules, each a rewrite `φ ⇝ ψ` of a formula.  Hover a
constructor for the KeY taclet it is. -/
inductive UpdRule : Fml C → Fml C → Prop
  /-- `sequentialToParallel2 { \find({u}{u2}phi) \replacewith({u || {u}u2}phi) }`,
  for `u` an update of locals. -/
  | sequentialToParallel {m : Modality} {U V : Upd C} {φ : Fml C} (hU : U.envOnly = true) :
      UpdRule (.upd m U (.upd m V φ)) (.upd m (U ++ V.subst U) φ)
  /-- `simplifyUpdate2 { \find({u}phi)
  \varcond(\dropEffectlessElementaries(u, phi, result)) \replacewith(result) }` -/
  | simplifyUpdate {m : Modality} {U : Upd C} {φ : Fml C} :
      UpdRule (.upd m U φ) (.upd m (U.dropEffectless φ.vars) φ)
  /-- `applySkip2 { \find({skip}phi) \replacewith(phi) }` -/
  | applySkip {m : Modality} {φ : Fml C} : UpdRule (.upd m [] φ) φ
  /-- `applyOnRigidFormula { \find({u}phi)
  \varcond(\applyUpdateOnRigid(u, phi, result)) \replacewith(result) }`, and
  `applyOnPV`/`applyOnDifferentPV` on the terms under it; for `u` that
  cannot halt, and `φ` reading no variable at another sort than `u` writes it
  (`Fml.sortedFor`, which KeY's sorts give for free). -/
  | applyOnRigid {m : Modality} {U : Upd C} {φ : Fml C} (hU : U.total = true)
      (hφ : φ.rigid = true) (hs : φ.sortedFor U = true) : UpdRule (.upd m U φ) (φ.subst U)

/-- **Soundness of the update rules**: each rewrites a formula to an
equivalent one.

Example: `x = 1; y = x;` leaves `{ x := 1 } { y := x } y = 1`;
`sequentialToParallel` rewrites it to `{ x := 1 ‖ y := 1 } y = 1`, and the two
hold in the same states. -/
theorem UpdRule.sound {φ ψ : Fml C} : UpdRule φ ψ → ∀ σ, (holds σ ψ ↔ holds σ φ)
  | .sequentialToParallel hU, σ => by
    simp only [holds]
    rw [Upd.apply_seq hU, ← Modality.after_bind]
  | .simplifyUpdate, σ => Upd.dropEffectless_holds _ _ _ σ
  | .applySkip, _ => Iff.rfl
  | @UpdRule.applyOnRigid _ m U φ hU hφ hs, σ => by
    obtain ⟨τ, hτ⟩ := Upd.foldl_total σ U hU σ
    simp only [holds, Upd.apply, hτ]
    exact Fml.subst_holds (Upd.substAgree (Upd.total_envOnly hU) hτ) φ hφ hs

/-! ## One rule at a time: `sol_upd r`

`Fml.updAt r φ` applies rule `r` at the first update in `φ` where it fits,
looking through every connective and into the postcondition of a
modality.  The rules are equivalences, so every position is sound. -/

inductive UpdRuleName where
  | sequentialToParallel
  | simplifyUpdate
  | applySkip
  | applyOnRigid
  deriving DecidableEq, Repr

/-- Rule `r` on `{U} φ` under `m`, if it fits and changes something. -/
def UpdRuleName.top : UpdRuleName → Modality → Upd C → Fml C → Option (Fml C)
  | .sequentialToParallel, m, U, .upd m' V φ =>
    if m' = m ∧ U.envOnly = true then some (.upd m (U ++ V.subst U) φ) else none
  | .simplifyUpdate, m, U, φ =>
    if (U.dropEffectless φ.vars).length < U.length then some (.upd m (U.dropEffectless φ.vars) φ)
    else none
  | .applySkip, _, [], φ => some φ
  | .applyOnRigid, _, U, φ =>
    if U.total = true ∧ φ.rigid = true ∧ φ.sortedFor U = true then some (φ.subst U) else none
  | _, _, _, _ => none

/-- When rule `r` fits at the top of `{U} φ`, what it returns is an `UpdRule`
rewrite of `{U} φ`.

Example: `sequentialToParallel` fits `{ x := 1 } { y := x } y = 1` (after
`x = 1; y = x;`) and returns `{ x := 1 ‖ y := 1 } y = 1`. -/
theorem UpdRuleName.top_rule {r : UpdRuleName} {m : Modality} {U : Upd C} {φ ψ : Fml C}
    (h : r.top m U φ = some ψ) : UpdRule (.upd m U φ) ψ := by
  unfold UpdRuleName.top at h
  split at h
  · split at h
    · rename_i hc; obtain ⟨rfl, hU⟩ := hc; cases h; exact .sequentialToParallel hU
    · cases h
  · split at h
    · cases h; exact .simplifyUpdate
    · cases h
  · cases h; exact .applySkip
  · split at h
    · rename_i hc; cases h; exact .applyOnRigid hc.1 hc.2.1 hc.2.2
    · cases h
  · cases h

/-- Rule `r` at the first update where it fits: outermost first, then left to right. -/
def Fml.updAt (r : UpdRuleName) : Fml C → Option (Fml C)
  | .upd m U φ => (r.top m U φ).orElse fun _ => (φ.updAt r).map (.upd m U)
  | .not φ => (φ.updAt r).map .not
  | .and φ ψ => match φ.updAt r with
    | some φ' => some (.and φ' ψ)
    | none => (ψ.updAt r).map (.and φ)
  | .imp φ ψ => match φ.updAt r with
    | some φ' => some (.imp φ' ψ)
    | none => (ψ.updAt r).map (.imp φ)
  | .modal m P φ => (φ.updAt r).map (.modal m P)
  | .havoc φ => (φ.updAt r).map .havoc
  | .all x p φ => (φ.updAt r).map (.all x p)
  | .tt | .eq .. | .defined _ => none

/-- Two postconditions that hold in the same states hold after the same run:
`{ x := 1 } (y = 1 → y = 1)` and `{ x := 1 } true` alike. -/
theorem Modality.after_congr (m : Modality) {p q : State → Prop} (h : ∀ τ, p τ ↔ q τ) :
    (r : Res State) → (m.after p r ↔ m.after q r)
  | .ok τ => h τ
  | .error _ => Iff.rfl

/-- Applying an update rule wherever it fits first gives an equivalent formula.

Example: for `alice.account.balance = 10;`, `sequentialToParallel` on
`{ se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } φ`
merges the first two updates, and the result holds exactly when the
original does. -/
theorem Fml.updAt_sound {r : UpdRuleName} :
    (φ : Fml C) → ∀ {ψ}, φ.updAt r = some ψ → ∀ σ, (holds σ ψ ↔ holds σ φ)
  | .upd m U φ, ψ, h, σ => by
    simp only [Fml.updAt] at h
    cases ht : r.top m U φ with
    | some χ =>
      simp only [ht, Option.orElse, Option.some.injEq] at h; subst h
      exact (UpdRuleName.top_rule ht).sound σ
    | none =>
      simp only [ht, Option.orElse, Option.map_eq_some_iff] at h
      obtain ⟨φ', h', rfl⟩ := h
      exact m.after_congr (fun τ => Fml.updAt_sound φ h' τ) _
  | .not φ, ψ, h, σ => by
    simp only [Fml.updAt, Option.map_eq_some_iff] at h
    obtain ⟨φ', h', rfl⟩ := h
    simp only [holds, Fml.updAt_sound φ h' σ]
  | .and φ₁ φ₂, ψ, h, σ => by
    simp only [Fml.updAt] at h
    split at h
    · cases h; simp only [holds, Fml.updAt_sound φ₁ (by assumption) σ]
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨φ', h', rfl⟩ := h
      simp only [holds, Fml.updAt_sound φ₂ h' σ]
  | .imp φ₁ φ₂, ψ, h, σ => by
    simp only [Fml.updAt] at h
    split at h
    · cases h; simp only [holds, Fml.updAt_sound φ₁ (by assumption) σ]
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨φ', h', rfl⟩ := h
      simp only [holds, Fml.updAt_sound φ₂ h' σ]
  | .modal m P φ, ψ, h, σ => by
    simp only [Fml.updAt, Option.map_eq_some_iff] at h
    obtain ⟨φ', h', rfl⟩ := h
    exact m.after_congr (fun τ => Fml.updAt_sound φ h' τ) _
  | .havoc φ, ψ, h, σ => by
    simp only [Fml.updAt, Option.map_eq_some_iff] at h
    obtain ⟨φ', h', rfl⟩ := h
    exact forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
      Fml.updAt_sound φ h' _
  | .all _ _ φ, ψ, h, σ => by
    simp only [Fml.updAt, Option.map_eq_some_iff] at h
    obtain ⟨φ', h', rfl⟩ := h
    exact forall_congr' fun _ => imp_congr_right fun _ => Fml.updAt_sound φ h' _
  | .tt, _, h, _ | .eq .., _, h, _ | .defined _, _, h, _ => by
    simp only [updAt, reduceCtorEq] at h

/-! ## All of them: `Fml.simpUpds`

Bottom-up, every stack `{U}{V}…` of one modality whose outer update writes
only locals becomes one parallel update (`sequentialToParallel`), its
effectless elements go (`simplifyUpdate`), and an update left empty goes
too (`applySkip`). -/

/-- `{U} φ` without its effectless elements, and without the braces if none is left. -/
def Fml.clean (m : Modality) (U : Upd C) (φ : Fml C) : Fml C :=
  if (U.dropEffectless φ.vars).isEmpty then φ else .upd m (U.dropEffectless φ.vars) φ

/-- `{U} φ`, merged with an update at the head of `φ`, then cleaned. -/
def Fml.mkUpd (m : Modality) (U : Upd C) : Fml C → Fml C
  | .upd m' V φ =>
    if m' = m ∧ U.envOnly = true then Fml.clean m (U ++ V.subst U) φ
    else Fml.clean m U (.upd m' V φ)
  | φ => Fml.clean m U φ

/-- Merge every stack of updates and drop what is dead. -/
def Fml.simpUpds : Fml C → Fml C
  | .upd m U φ => Fml.mkUpd m U φ.simpUpds
  | .not φ => .not φ.simpUpds
  | .and φ ψ => .and φ.simpUpds ψ.simpUpds
  | .imp φ ψ => .imp φ.simpUpds ψ.simpUpds
  | .modal m P φ => .modal m P φ.simpUpds
  | .havoc φ => .havoc φ.simpUpds
  | .all x p φ => .all x p φ.simpUpds
  | φ => φ

/-- `Fml.clean m U φ` holds exactly when `{U} φ` does.

Example: after `x = 1;`, `Fml.clean m [x := 1] true` is `true` (its only
element is unused, and the braces go). -/
theorem Fml.clean_holds (m : Modality) (U : Upd C) (φ : Fml C) (σ : State) :
    holds σ (Fml.clean m U φ) ↔ holds σ (.upd m U φ) := by
  rw [← Upd.dropEffectless_holds]
  unfold Fml.clean
  split
  · rename_i h; simp only [List.isEmpty_iff] at h; rw [h]; exact Iff.rfl
  · exact Iff.rfl

/-- `Fml.mkUpd m U φ` holds exactly when `{U} φ` does.

Example: after `x = 1; y = x;`, `mkUpd m [x := 1] ({ y := x } y = 1)` merges to
`{ x := 1 ‖ y := 1 }` and cleans that to `{ y := 1 } y = 1`. -/
theorem Fml.mkUpd_holds (m : Modality) (U : Upd C) (φ : Fml C) (σ : State) :
    holds σ (Fml.mkUpd m U φ) ↔ holds σ (.upd m U φ) := by
  cases φ with
  | upd m' V φ =>
    simp only [Fml.mkUpd]
    split
    · rename_i hc
      obtain ⟨rfl, hU⟩ := hc
      rw [Fml.clean_holds]
      exact (UpdRule.sequentialToParallel (V := V) (φ := φ) hU).sound σ
    · exact Fml.clean_holds _ _ _ σ
  | _ => exact Fml.clean_holds _ _ _ σ

/-- `Fml.simpUpds` gives an equivalent formula: in every state it holds exactly
when the original does.

Example: `x = 1; y = x;` leaves `{ x := 1 } { y := x } y = 1`, which
`simpUpds` turns into `{ y := 1 } y = 1`: merged, then `x := 1` dropped as
unused. -/
theorem Fml.simpUpds_holds : (φ : Fml C) → ∀ σ, (holds σ φ.simpUpds ↔ holds σ φ)
  | .upd m U φ, σ => by
    simp only [Fml.simpUpds, Fml.mkUpd_holds, holds]
    exact m.after_congr (fun τ => Fml.simpUpds_holds φ τ) _
  | .not φ, σ => by simp only [Fml.simpUpds, holds, Fml.simpUpds_holds φ σ]
  | .and φ ψ, σ => by
    simp only [Fml.simpUpds, holds, Fml.simpUpds_holds φ σ, Fml.simpUpds_holds ψ σ]
  | .imp φ ψ, σ => by
    simp only [Fml.simpUpds, holds, Fml.simpUpds_holds φ σ, Fml.simpUpds_holds ψ σ]
  | .modal m P φ, σ => by
    simp only [Fml.simpUpds, holds]
    exact m.after_congr (fun τ => Fml.simpUpds_holds φ τ) _
  | .havoc φ, σ => by
    simp only [Fml.simpUpds, holds]
    exact forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
      Fml.simpUpds_holds φ _
  | .all _ _ φ, σ => by
    simp only [Fml.simpUpds, holds]
    exact forall_congr' fun _ => imp_congr_right fun _ => Fml.simpUpds_holds φ _
  | .tt, _ | .eq .., _ | .defined _, _ => Iff.rfl

/-! ## In a derivation: `Proves.merge`, `Proves.simplify`

Under `⊢` the updates sit in the context, the latest last.  These two
lemmas rewrite the last two, or the last one, as `sequentialToParallel` and
`simplifyUpdate` do, once no modality is left in the sequent.  They are not
constructors of `Proves`: each is proved from `Proves.sound` and closes with
`Proves.close`, which is why they wait for the modalities to be gone. -/

/-- Under `⊢`, the last two updates of the context merge into one parallel
update, the first substituted into the second, when the first writes only
locals.

Example: for `x = 1; y = x;` the context `{ x := 1 }, { y := x }` becomes
`{ x := 1 ‖ y := 1 }`. -/
theorem Proves.merge {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {U V : Upd C} {φ : Fml C}
    (hU : U.envOnly = true) (h : Proves R (Γ ++ [.upd m (U ++ V.subst U)]) φ)
    (hφ : (Hyp.wrap (Γ ++ [.upd m U] ++ [.upd m V]) φ).modalFree = true := by first | rfl | decide) :
    Proves R (Γ ++ [.upd m U] ++ [.upd m V]) φ :=
  .close (fun σ => by
    have := h.sound σ
    simp only [List.append_assoc, List.cons_append, List.nil_append, Hyp.wrap_append,
      Hyp.wrap] at this ⊢
    exact Hyp.wrap_mono (fun τ hτ => ((UpdRule.sequentialToParallel (V := V) (φ := φ) hU).sound τ).1 hτ)
      Γ σ this) hφ

/-- Under `⊢`, the effectless elements of the last update can be dropped.

Example: for `alice.account.balance = 10;`, the context
`{ se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10) }`
becomes `{ storage := save(storage, alice.account.balance, 10) }`. -/
theorem Proves.simplify {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {U : Upd C} {φ : Fml C}
    (h : Proves R (Γ ++ [.upd m (U.dropEffectless φ.vars)]) φ)
    (hφ : (Hyp.wrap (Γ ++ [.upd m U]) φ).modalFree = true := by first | rfl | decide) :
    Proves R (Γ ++ [.upd m U]) φ :=
  .close (fun σ => by
    have := h.sound σ
    simp only [Hyp.wrap_append, Hyp.wrap] at this ⊢
    exact Hyp.wrap_mono (fun τ hτ => (Upd.dropEffectless_holds m U φ τ).1 hτ) Γ σ this) hφ

/-! ## Under the box: `applyOnRigid` without totality

`UpdRule.applyOnRigid` is an equivalence, so it asks that `U` cannot halt
(`Upd.total`): the substituted formula has forgotten the halt.  Under the box
a halting update proves what follows it (`Modality.onHalt .box`), so one
direction needs no totality: where `U` runs, the run itself is the agreement
the substitution needs (`Upd.substAgree`, whose `bound` is the run), and
where `U` halts there is nothing to prove.  That direction — the substituted
formula gives `{U} φ` — is the one a derivation uses, so under the box KeY's
`applyOnRigidFormula` is a derived rule for every update of locals:
`{ x := find(storage, alice.age) }` may halt (no `alice`), and is still
applied.

What the substitution forgets, that `U` ran, a derivation keeps apart:
`defined(x)` behind a box update that binds `x` to a value
(`Proves.definedWritten`), proved before the update is dropped. -/

/-- Under the box, a first-order formula substituted with an update of
locals gives the formula behind the update: where `U` runs, the run gives
`SubstAgree` (`Upd.substAgree`); where it halts, the box holds.

Example: `find(storage, alice.age) ≐ 42` gives
`[{ x := find(storage, alice.age) }] x ≐ 42`, also where `alice.age` does not
read and the update halts. -/
theorem Fml.subst_box {U : Upd C} (hU : U.envOnly = true) {φ : Fml C} (hφ : φ.rigid = true)
    (hs : φ.sortedFor U = true) (σ : State) (h : holds σ (φ.subst U)) :
    holds σ (.upd .box U φ) := by
  simp only [holds]
  cases hτ : U.apply σ with
  | error _ => trivial
  | ok τ => exact (Fml.subst_holds (Upd.substAgree hU hτ) φ hφ hs).1 h

/-! ### Under the box, past a storage write

A parallel update reads every right-hand side in the pre-state
(`UpdElem.write`), so in the merged `{ storage := S ‖ x := t }` of
`Proves.mergeStorage` the storage write does not reach `t`: the locals it
binds are the ones its locals alone bind (`Upd.locals`, with the same
`lastWrite`, so the same substitution), and the state it leaves differs from
theirs in the storage only (`Upd.foldl_locals`).  A formula that reads no
storage (`Fml.stFree`) cannot see that difference (`Fml.holds_withStorage`),
so substituting the locals is still the box direction of
`applyOnRigidFormula`.

`stFree` is syntactic and conservative, so that `rfl` decides it: no
storage, path or memory subterm at all.  That also leaves out a
`find(old, p)` of a storage variable, which reads only the environment, and
a path, whose index check reads the storage. -/

/-- The element writes the storage: `storage := s`. -/
def UpdElem.isStorage : UpdElem C → Bool
  | .storage _ => true
  | _ => false

/-- Every element writes a local, an alias, a memory local or the storage:
`{ storage := S ‖ x := find(storage, alice.age) }`. -/
def Upd.localsOrStorage (U : Upd C) : Bool := U.all fun e => e.var?.isSome || e.isStorage

/-- The elements that write a variable: `{ x := t }` of
`{ storage := S ‖ x := t }`. -/
def Upd.locals (U : Upd C) : Upd C := U.filter (·.var?.isSome)

/-- A value term with no storage, path or memory subterm: `x + 1`, not
`find(storage, alice.age)`. -/
def Term.stFree : Term C → Bool
  | .lit _ | .pv _ | .env _ => true
  | .binop _ _ a b => a.stFree && b.stFree
  | .unop _ _ a | .net a | .netOf _ a => a.stFree
  | .ite c a b => c.stFree && a.stFree && b.stFree
  | .find .. | .len .. | .read .. | .mlen .. => false

/-- A first-order formula whose terms are `Term.stFree`: `x ≐ 42`. -/
def Fml.stFree : Fml C → Bool
  | .tt => true
  | .eq a b => a.stFree && b.stFree
  | .defined t => t.stFree
  | .not φ => φ.stFree
  | .and φ ψ | .imp φ ψ => φ.stFree && ψ.stFree
  | _ => false

/-- A storage-free formula is first-order. -/
theorem Fml.stFree_rigid : {φ : Fml C} → φ.stFree = true → φ.rigid = true
  | .tt, _ | .eq .., _ | .defined _, _ => rfl
  | .not φ, h => Fml.stFree_rigid (φ := φ) h
  | .and φ ψ, h | .imp φ ψ, h => by
    simp only [Fml.stFree, Bool.and_eq_true] at h
    simp only [Fml.rigid, Fml.stFree_rigid h.1, Fml.stFree_rigid h.2, Bool.and_self]

/-- The locals of an update are an update of locals. -/
theorem Upd.locals_envOnly : (U : Upd C) → Upd.envOnly (Upd.locals U) = true
  | [] => rfl
  | e :: U => by
    have ih : Upd.envOnly (Upd.locals U) = true := Upd.locals_envOnly U
    cases he : e.var?.isSome
    · simpa only [Upd.locals, List.filter_cons, he] using ih
    · simp only [Upd.locals, List.filter_cons, he, if_true, Upd.envOnly, List.all_cons,
        Bool.true_and] at ih ⊢
      exact ih

/-- The locals of an update write each variable last where the update does:
an element that writes no variable is no write of one. -/
theorem Upd.lastWrite_locals (x : Var) :
    (U : Upd C) → Upd.lastWrite x (Upd.locals U) = Upd.lastWrite x U
  | [] => rfl
  | e :: U => by
    have ih : Upd.lastWrite x (Upd.locals U) = Upd.lastWrite x U := Upd.lastWrite_locals x U
    cases he : e.var? with
    | none =>
      have hf : Upd.locals (e :: U) = Upd.locals U := by
        simp only [Upd.locals, List.filter_cons, he, Option.isSome_none]
        rfl
      rw [hf, ih]
      simp only [Upd.lastWrite, he, reduceCtorEq, if_false]
      split <;> simp_all only
    | some y =>
      have hf : Upd.locals (e :: U) = e :: Upd.locals U := by
        simp only [Upd.locals, List.filter_cons, he, Option.isSome_some, if_true]
      rw [hf]
      simp only [Upd.lastWrite, ih]

/-- `SubstAgree` sees an update through its `lastWrite` only. -/
theorem SubstAgree.of_lastWrite {U V : Upd C} {ns : List Var} {σ τ : State}
    (hw : ∀ x, Upd.lastWrite x U = V.lastWrite x) (h : SubstAgree V ns σ τ) :
    SubstAgree U ns σ τ where
  agree := h.agree
  val x := by
    rw [show U.valOf x = V.valOf x by simp only [Upd.valOf, hw x]]
    exact h.val x
  path x := by
    rw [show U.pathOf x = V.pathOf x by simp only [Upd.pathOf, hw x]]
    exact h.path x
  ref x := by
    rw [show U.refOf x = V.refOf x by simp only [Upd.refOf, hw x]]
    exact h.ref x
  stor x := by
    rw [show U.storOf x = V.storOf x by simp only [Upd.storOf, hw x]]
    exact h.stor x
  unwritten x hx := h.unwritten x (by rw [← hw x]; exact hx)
  written x e hx := h.written x e (by rw [← hw x]; exact hx)
  bound x e hx := h.bound x e (by rw [← hw x]; exact hx)

/-- Run from a state, an update of locals and storage writes the locals its
`Upd.locals` write from that state with any storage, and leaves the state
they leave with some storage: the storage writes read the pre-state `σ₀`,
and no other element reads the storage it is writing into. -/
theorem Upd.foldl_locals (σ₀ : State) : (U : Upd C) → U.localsOrStorage = true →
    ∀ {ρ : State} {st : List (Name × SVal)} {τ : State},
      U.foldlM (fun ρ e => e.write σ₀ ρ) { ρ with storage := st } = .ok τ →
      ∃ τ', (Upd.locals U).foldlM (fun ρ e => e.write σ₀ ρ) ρ = .ok τ' ∧
        ∃ st', τ = { τ' with storage := st' }
  | [], _, ρ, st, τ, h => by
    cases h
    exact ⟨ρ, rfl, st, rfl⟩
  | e :: U, hU, ρ, st, τ, h => by
    simp only [Upd.localsOrStorage, List.all_cons, Bool.and_eq_true, Bool.or_eq_true] at hU
    obtain ⟨he, hU⟩ := hU
    simp only [List.foldlM_cons] at h
    obtain ⟨ρ₁, h₁, h⟩ := bind_ok_inv h
    cases hv : e.var? with
    | some x =>
      rw [UpdElem.write_var hv] at h₁
      obtain ⟨b, hb, h₁⟩ := bind_ok_inv h₁
      cases h₁
      obtain ⟨τ', hτ', st', rfl⟩ := Upd.foldl_locals σ₀ U hU (ρ := ρ.setEnv x b) (st := st) h
      have hf : Upd.locals (e :: U) = e :: Upd.locals U := by
        simp only [Upd.locals, List.filter_cons, hv, Option.isSome_some, if_true]
      refine ⟨τ', ?_, st', rfl⟩
      rw [hf, List.foldlM_cons, UpdElem.write_var hv, hb]
      exact hτ'
    | none =>
      have hs : e.isStorage = true := by
        simpa only [hv, Option.isSome_none, Bool.false_eq_true, false_or] using he
      have hf : Upd.locals (e :: U) = Upd.locals U := by
        simp only [Upd.locals, List.filter_cons, hv, Option.isSome_none]
        rfl
      rw [hf]
      cases e with
      | storage s =>
        simp only [UpdElem.write] at h₁
        obtain ⟨v, -, h₁⟩ := bind_ok_inv h₁
        cases h₁
        exact Upd.foldl_locals σ₀ U hU (ρ := ρ) (st := v.storage) h
      | _ => simp only [UpdElem.isStorage, Bool.false_eq_true] at hs

/-- A storage-free term reads alike in two states that differ in the storage. -/
theorem Term.eval_withStorage (σ : State) (st : List (Name × SVal)) :
    (t : Term C) → t.stFree = true → t.eval { σ with storage := st } = t.eval σ
  | .lit _, _ | .pv _, _ | .env _, _ => rfl
  | .binop _ _ a b, h => by
    simp only [Term.stFree, Bool.and_eq_true] at h
    simp only [Term.eval, Term.eval_withStorage σ st a h.1, Term.eval_withStorage σ st b h.2]
  | .unop _ _ a, h => by simp only [Term.eval, Term.eval_withStorage σ st a h]
  | .net a, h => by
    simp only [Term.eval, Term.eval_withStorage σ st a h]
    rfl
  | .netOf _ a, h => by
    simp only [Term.eval, Term.eval_withStorage σ st a h]
    rfl
  | .ite c a b, h => by
    simp only [Term.stFree, Bool.and_eq_true] at h
    simp only [Term.eval, Term.eval_withStorage σ st c h.1.1, Term.eval_withStorage σ st a h.1.2,
      Term.eval_withStorage σ st b h.2]

/-- A storage-free term denotes alike in two states that differ in the storage. -/
theorem Term.denote_withStorage (σ : State) (st : List (Name × SVal)) :
    (t : Term C) → t.stFree = true → t.denote { σ with storage := st } = t.denote σ
  | .lit _, _ | .pv _, _ | .env _, _ => rfl
  | .binop _ _ a b, h => by
    simp only [Term.stFree, Bool.and_eq_true] at h
    simp only [Term.denote, Term.denote_withStorage σ st a h.1,
      Term.denote_withStorage σ st b h.2]
  | .unop _ _ a, h => by simp only [Term.denote, Term.denote_withStorage σ st a h]
  | .net a, h => by
    simp only [Term.denote, Term.denote_withStorage σ st a h]
    rfl
  | .netOf _ a, h => by
    simp only [Term.denote, Term.denote_withStorage σ st a h]
    rfl
  | .ite c a b, h => by
    simp only [Term.stFree, Bool.and_eq_true] at h
    simp only [Term.denote, Term.denote_withStorage σ st c h.1.1,
      Term.denote_withStorage σ st a h.1.2, Term.denote_withStorage σ st b h.2]

/-- A storage-free formula holds alike in two states that differ in the storage. -/
theorem Fml.holds_withStorage (σ : State) (st : List (Name × SVal)) :
    (φ : Fml C) → φ.stFree = true → (holds { σ with storage := st } φ ↔ holds σ φ)
  | .tt, _ => Iff.rfl
  | .eq a b, h => by
    simp only [Fml.stFree, Bool.and_eq_true] at h
    simp only [holds, Term.denote_withStorage σ st a h.1, Term.denote_withStorage σ st b h.2]
  | .defined t, h => by simp only [holds, Term.eval_withStorage σ st t h]
  | .not φ, h => by simp only [holds, Fml.holds_withStorage σ st φ h]
  | .and φ ψ, h | .imp φ ψ, h => by
    simp only [Fml.stFree, Bool.and_eq_true] at h
    simp only [holds, Fml.holds_withStorage σ st φ h.1, Fml.holds_withStorage σ st ψ h.2]

/-- Under the box, a storage-free formula substituted with an update of
locals and storage writes gives the formula behind the update: where `U`
runs, its locals ran to the same state up to the storage.

Example: `x ≐ 42` substituted is `find(S, alice.age) ≐ 42`, which gives
`[{ storage := S ‖ x := find(S, alice.age) }] x ≐ 42`. -/
theorem Fml.subst_box_st {U : Upd C} (hU : U.localsOrStorage = true) {φ : Fml C}
    (hφ : φ.stFree = true) (hs : φ.sortedFor U = true) (σ : State) (h : holds σ (φ.subst U)) :
    holds σ (.upd .box U φ) := by
  simp only [holds]
  cases hτ : U.apply σ with
  | error _ => trivial
  | ok τ =>
    obtain ⟨τ', hτ', st', rfl⟩ := Upd.foldl_locals σ U hU (ρ := σ) (st := σ.storage) hτ
    have hA : SubstAgree U U.locals.targets σ τ' :=
      (Upd.substAgree (Upd.locals_envOnly U) hτ').of_lastWrite
        fun x => (Upd.lastWrite_locals x U).symm
    exact (Fml.holds_withStorage τ' st' φ hφ).2
      ((Fml.subst_holds hA φ (Fml.stFree_rigid hφ) hs).1 h)

/-- **`applyOnRigidFormula` under the box**: the last update of the context
is applied to a first-order goal and dropped — with no totality premise,
since a halting box update proves what follows.  The update writes locals
(`Fml.subst_box`), or locals and the storage where the goal reads no storage
(`Fml.subst_box_st`): the merged update of `Proves.mergeStorage` is applied
in one step.

Example: `{ storage := S }, { x := find(storage, alice.age) } ⟹ x ≐ 42`
becomes `{ storage := S } ⟹ find(storage, alice.age) ≐ 42`, and
`{ storage := S ‖ x := find(storage, alice.age) } ⟹ x ≐ 42` becomes
`⟹ find(storage, alice.age) ≐ 42`. -/
theorem Proves.applyOnRigidBox {R : RuleSet} {Γ : List (Hyp C)} {U : Upd C} {φ : Fml C}
    (h : Proves R Γ (φ.subst U))
    (hU : (U.envOnly || U.localsOrStorage && φ.stFree) = true := by first | rfl | decide)
    (hr : φ.rigid = true := by first | rfl | decide)
    (hs : φ.sortedFor U = true := by first | rfl | decide)
    (hφ : (Hyp.wrap (Γ ++ [.upd .box U]) φ).modalFree = true := by first | rfl | decide) :
    Proves R (Γ ++ [.upd .box U]) φ :=
  .close (fun σ => by
    have hσ : holds σ (Hyp.wrap Γ (φ.subst U)) := h.sound σ
    rw [Hyp.wrap_append]
    refine Hyp.wrap_mono (fun τ hτ => ?_) Γ σ hσ
    rcases Bool.or_eq_true_iff.1 hU with hU | hU
    · exact Fml.subst_box hU hr hs τ hτ
    · simp only [Bool.and_eq_true] at hU
      exact Fml.subst_box_st hU.1 hU.2 hs τ hτ) hφ

/-! ### `defined` of a written local -/

/-- The local an element binds in the environment: `var?`'s, and also a
storage variable (`old := s`) and a ledger variable (`oldNet := net`), which
`var?` leaves out because `Upd.subst` has nothing to put for them. -/
def UpdElem.envVar? : UpdElem C → Option Var
  | .val x _ | .path x _ | .mref x _ | .store x _ | .saveNet x => some x
  | _ => none

/-- An element that binds another local leaves `x` as it was: a storage,
memory or funds write does not touch the environment. -/
theorem UpdElem.write_getEnv_other {σ₀ ρ ρ' : State} {x : Var} :
    (e : UpdElem C) → e.envVar? ≠ some x → e.write σ₀ ρ = .ok ρ' → ρ'.getEnv x = ρ.getEnv x
  | .val y t, hne, h | .mref y t, hne, h => by
    obtain ⟨v, -, h⟩ := bind_ok_inv h
    cases h
    exact SemanticsProperties.State.getEnv_setEnv_ne (by rintro rfl; exact hne rfl) _ _
  | .path y p, hne, h => by
    obtain ⟨⟨r, segs⟩, -, h⟩ := bind_ok_inv h
    cases h
    exact SemanticsProperties.State.getEnv_setEnv_ne (by rintro rfl; exact hne rfl) _ _
  | .store y s, hne, h => by
    obtain ⟨v, -, h⟩ := bind_ok_inv h
    cases h
    exact SemanticsProperties.State.getEnv_setEnv_ne (by rintro rfl; exact hne rfl) _ _
  | .saveNet y, hne, h => by
    cases h
    exact SemanticsProperties.State.getEnv_setEnv_ne (by rintro rfl; exact hne rfl) _ _
  | .storage s, _, h => by
    obtain ⟨v, -, h⟩ := bind_ok_inv h
    cases h
    rfl
  | .memory m, _, h => by
    obtain ⟨v, -, h⟩ := bind_ok_inv h
    cases h
    rfl
  | .transfer r a, _, h => by
    obtain ⟨v, -, h⟩ := bind_ok_inv h
    obtain ⟨addr, -, h⟩ := bind_ok_inv h
    obtain ⟨w, -, h⟩ := bind_ok_inv h
    obtain ⟨amt, -, h⟩ := bind_ok_inv h
    simp only [transferAt] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        rfl
  | .book a, _, h => by
    obtain ⟨v, -, h⟩ := bind_ok_inv h
    obtain ⟨amt, -, h⟩ := bind_ok_inv h
    cases h
    rfl

/-- The last element of `U` that binds `x` in the environment (`envVar?`)
binds it to a value: `x := t`.

Example: true of `x` in `{ storage := S ‖ x := find(S, alice.age) }`, false
in `{ x := 1 ‖ x := alice.account }`, where the last write makes `x` an
alias. -/
def Upd.bindsVal (x : Var) : Upd C → Bool
  | [] => false
  | e :: U =>
    if U.any (fun e' => decide (e'.envVar? = some x)) then Upd.bindsVal x U
    else match e with
      | .val y _ => decide (y = x)
      | _ => false

/-- A run of an update leaves a local no element binds as it was, and a local
whose last binder is `x := t` bound to a value. -/
theorem Upd.foldl_getEnv (σ₀ : State) {x : Var} : (U : Upd C) → ∀ {τ₀ τ : State},
    U.foldlM (fun ρ e => e.write σ₀ ρ) τ₀ = .ok τ →
      (U.any (fun e => decide (e.envVar? = some x)) = false → τ.getEnv x = τ₀.getEnv x) ∧
      (U.bindsVal x = true → ∃ v, τ.getEnv x = .ok (.val v))
  | [], τ₀, τ, h => by
    cases h
    exact ⟨fun _ => rfl, fun hb => by cases hb⟩
  | e :: U, τ₀, τ, h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨τ₁, h₁, h⟩ := bind_ok_inv h
    obtain ⟨ih₁, ih₂⟩ := Upd.foldl_getEnv σ₀ U h
    refine ⟨fun hn => ?_, fun hb => ?_⟩
    · simp only [List.any_cons, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hn
      rw [ih₁ hn.2, UpdElem.write_getEnv_other e hn.1 h₁]
    · simp only [Upd.bindsVal] at hb
      split at hb
      · exact ih₂ hb
      · rename_i hn
        split at hb
        · rename_i y t
          have hyx : y = x := of_decide_eq_true hb
          subst hyx
          obtain ⟨v, -, h₁⟩ := bind_ok_inv h₁
          cases h₁
          exact ⟨v, by
            rw [ih₁ (Bool.eq_false_iff.2 hn), SemanticsProperties.State.getEnv_setEnv_self]⟩
        · cases hb

/-- Behind a box update whose last binder of `x` is `x := t`, `x` reads:
where the update runs it bound `x` to the value of `t`, and where it halts
the box holds. -/
theorem Upd.defined_box {U : Upd C} {x : Var} (hw : U.bindsVal x = true) (σ : State) :
    holds σ (.upd .box U (.defined (.pv x))) := by
  simp only [holds]
  cases hτ : U.apply σ with
  | error _ => trivial
  | ok τ =>
    obtain ⟨v, hv⟩ := (Upd.foldl_getEnv σ U hτ).2 hw
    exact ⟨v, by simp only [Term.eval, hv, bind, Except.bind, pure, Except.pure]⟩

/-- **`defined(x)` after `x := t`**: behind a box update whose last binder of
`x` is `x := t`, in a context with no diamond, `x` is defined.  This keeps
what `Proves.applyOnRigidBox` forgets, that the update ran.

Example: `{ storage := S }, { x := find(storage, alice.age) } ⟹ defined(x)`. -/
theorem Proves.definedWritten {R : RuleSet} {Γ : List (Hyp C)} {U : Upd C} {x : Var}
    (hw : U.bindsVal x = true := by first | rfl | decide)
    (hb : Hyp.boxOnly Γ = true := by first | rfl | decide)
    (hφ : (Hyp.wrap (Γ ++ [.upd .box U]) (.defined (.pv x))).modalFree = true := by
      first | rfl | decide) :
    Proves R (Γ ++ [.upd .box U]) (.defined (.pv x)) :=
  .close (fun σ => by
    rw [Hyp.wrap_append]
    exact Hyp.wrap_of_reaches Γ hb σ (fun τ _ => Upd.defined_box hw τ)) hφ

/-- **`{U}(φ ∧ ψ)` from `{U}φ` and `{U}ψ`**, under either modality: where
`U` runs both hold after it, where it halts both judge the halt alike.

Example: `⟹ [{ x := t }](defined(x) ∧ x ≐ 42)` from
`⟹ [{ x := t }] defined(x)` and `⟹ [{ x := t }] x ≐ 42`. -/
theorem Proves.andSplitUpd {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {U : Upd C}
    {φ ψ : Fml C} (h₁ : Proves R Γ (.upd m U φ)) (h₂ : Proves R Γ (.upd m U ψ))
    (hφ : (Hyp.wrap Γ (.upd m U (.and φ ψ))).modalFree = true := by first | rfl | decide) :
    Proves R Γ (.upd m U (.and φ ψ)) :=
  .close (fun σ => Hyp.wrap_mono₃ (fun τ a b _ => by
      simp only [holds] at a b ⊢
      cases hU : U.apply τ with
      | error _ => rw [hU] at a; exact a
      | ok ρ => rw [hU] at a b; exact ⟨a, b⟩) Γ σ (h₁.sound σ) (h₂.sound σ) (h₁.sound σ)) hφ

/-! ## Tactics -/

/-- To prove a formula, prove it with rule `r` applied where it fits first (or
unchanged, if it fits nowhere); `sol_upd r` applies this.

Example: `sol_upd .applyOnRigid` turns `⊨ dl{ { y := 3 } y = 3 }` into
`⊨ dl{ 3 = 3 }`. -/
theorem Fml.updAt_valid (r : UpdRuleName) {φ : Fml C} (h : Valid ((φ.updAt r).getD φ)) :
    Valid φ := by
  intro σ
  cases hs : φ.updAt r with
  | none => simpa [hs] using h σ
  | some ψ => exact (Fml.updAt_sound φ hs σ).1 (by simpa [hs] using h σ)

/-- To prove a formula, prove its `simpUpds`; `sol_merge` applies this.

Example: after `sol_symex` on `[ alice.account.balance = 10; ] …`, `sol_merge` leaves
`⊨ { storage := save(storage, alice.account.balance, 10) } find(storage, alice.account.balance) = 10`. -/
theorem Fml.simpUpds_valid {φ : Fml C} (h : Valid φ.simpUpds) : Valid φ :=
  fun σ => (Fml.simpUpds_holds φ σ).1 (h σ)

open Lean Elab Tactic Meta in
/-- `sol_upd r`: apply the update rule `r` at the first update where it fits. -/
elab "sol_upd " r:term : tactic => do
  applyValid "sol_upd" (← `(Fml.updAt_valid $r)) (some m!"rule {r} does not apply here")

open Lean Elab Tactic Meta in
/-- `sol_merge`: merge every stack of updates into one and drop what is dead
(`Fml.simpUpds`). -/
elab "sol_merge" : tactic => do
  applyValid "sol_merge" (← `(Fml.simpUpds_valid))

end Solidity
