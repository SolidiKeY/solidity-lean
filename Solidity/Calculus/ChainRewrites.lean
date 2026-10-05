import Solidity.Calculus.UpdateRules
import Solidity.Calculus.TermTaclets
import Solidity.Calculus.StateParts

/-!
# The rewrites of a chain's line

Past the last statement a worked example keeps going, and so
does KeY: the stack of updates the program left merges into one parallel
update, the right-hand sides substituted, dead
captures go, the update is applied, and Theory laws read the terms down to
values:

    { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } φ
      ⇝ { se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10) } φ

None of these is a step of the strategy (`Fml.step`).  Each is here a
function on the whole line, computing the line after, with the one fact a
chain needs of it: wherever the line after holds, the line before does
(`LineRw`).  The semantics is `Calculus/UpdateRules.lean`'s and
`Calculus/TermRules.lean`'s; this module says *where* a rule acts.  A
function returns `none` where its rule does not fit or would change
nothing, so a link never repeats its line.

| `LineRw` | computes | line before ⇝ line after | sound by | the rule on `⊢` |
|---|---|---|---|---|
| `mergeAt i` | `Fml.mergeAt` | `{U}{V} ⇝ {U ‖ {U}V}`, `U` at `i` | `Upd.merge_holds` (iff) | `merge`, `mergeStorage` |
| `mergeSpine n` | `Fml.mergeSpine` | the first `n + 1` updates into one | `n` merges (iff) | — |
| `mergeRun i n` | `Fml.mergeRun` | the `n + 1` updates from `i` into one | `n` merges (iff) | — |
| `updRule r i` | `Fml.updRuleAt` | `applySkip`, `applyOnRigid` | `UpdRule.sound` (iff) | `simplify` |
| `simplify i` | `Fml.simplifyAt` | the elements `ψ` does not read, or a later one overwrites, go | `Upd.dropEffectless_holds_of` (iff) | `simplify` |
| `simplifyFresh i` | `Fml.simplifyFreshAt` | the same, `ψ` asked its fresh variables only | `Upd.dropEffectless_holds_of` (iff) | — |
| `applyOnRigidBox i` | `Fml.applyOnRigidBoxAt` | `[{U}] φ ⇝ φ[U]`, `φ` first-order; any modality if `U` cannot halt | `Fml.subst_box(_st)` | `applyOnRigidBox` |
| `applyStorageBox i` | `Fml.applyStorageBoxAt` | `[{storage := s}] φ ⇝ φ[s/storage]` | `Fml.withSt_box` | `applyStorageBox` |
| `law r` | `Fml.rwLaw` | `t ⇝ t'` in every equation | `Fml.rwEq_holds` (iff) | `rewrite` |
| `lawUpd r ht i` | `Fml.rwUpdAt` | `t ⇝ t'` in `[{Uᵢ}]`'s right-hand sides | `Upd.rw_box` | `updRw` |
| `lawUpdAny r ht i` | `Fml.rwUpdCoveredAt` | `t ⇝ t'` in `{Uᵢ}`'s right-hand sides, memory terms included, `Uᵢ` holding the write `t` reads back | `Upd.rwEv_holds` (iff) | `updRw` |
| `lawUpdRef r hr i` | `Fml.rwUpdRefAt` | a frame or delete-value law in `{Uᵢ}`'s right-hand sides, `Uᵢ` holding its storage operation | `Upd.rw_holds`, `TermTaclet.RefLaw.evalRefines` (iff) | `updRw` |
| `lawUpdEq r i` | `Fml.rwUpdEqAt` | `t ⇝ t'` in `{Uᵢ}`'s right-hand sides, `t` and `t'` one read member-wise | `Upd.rw_holds`, `Term.base_eval` (iff) | `updRw` |
| `lawUpdEval r i` | `Fml.rwUpdEvalAt` | a memory law `t ⇝ t'` (`EvalLaw`) in `{Uᵢ}`'s right-hand sides, `Uᵢ` holding the write `t` reads back | `Upd.rw_holds`, `EvalLaw.sound` (iff) | `updRw` |

KeY's names: the merges are `sequentialToParallel`, the two `simplify…` are
`simplifyUpdate` (with `applySkip` when they empty the update), the two
`apply…Box` are `applyOnRigidFormula`, and a law is the term taclet it
names (`TermTaclet`); `lawUpdAny` is `updRw` under any modality, where the
update itself holds the write the law reads back (`Upd.covers`).

**Where.**  A line is an update prefix, its *spine* `{U₀}{U₁}…{Uₙ} ψ`, over
a body `ψ`: a program still to run, or the postcondition.  A chain rewrites
the spine at a position, so the functions take one, `i` counted from the
outside (`Fml.atSpine` walks there); the innermost pair of three updates is
`mergeAt 1`.  The `⊢` rules act on the last update of the context; a chain's
line has no context, and names the position instead.  An update under a
connective (a branch's `c → {U} …`) is not reached: no worked trace merges
there.  A law acts where `Fml.rwEq` does — every equation, never `defined(…)`,
an update's right-hand side or a program — and `lawUpd` in one box update's
right-hand sides, where `t'` cannot halt (`Term.EvalRefines.of_theq`).

**What is looked at.**  A function looks at nothing below what it rewrites,
so a line over an opaque postcondition `φ` computes as far as its concrete
part goes, and a link on it is `rfl`.  The merges look at two updates, never
the body; `applySkip` and `lawUpd` at one update.  The rules whose premise
is about the body read it: `simplify` (the variables it reads),
`applyOnRigid` and the `apply…Box` (a first-order body), `law` (its
equations).  `simplifyFresh` reads only the body's fresh variables, which a
postcondition `φ : Post C` has none of: over `φ` it computes by `simp` from
`Post.noFresh`, not by `rfl` (`Chain.proveRw`, `Calculus/Chains.lean`).

**The modality of an update.**  An update carries the modality it was
produced under, and merging `{U}_m {V}_m'` needs `m = m'`: a halting update
is true under the box and false under the diamond.  An update that cannot
halt (`Upd.total`: literals and paths of state variables, what the rules
capture) reads alike under both (`Upd.holds_total`), so a merge with one
takes the other's modality without comparing them.  That is what lets the
merges compute over a modality variable `m`; a merge of two updates
that may both halt compares `m' = m`, which a variable does not decide.  The
same holds of `applyOnRigidBox`: under the box, or where `U` cannot halt.
`applyStorageBox` and `lawUpd` are the box's only, since a storage write and
a right-hand side a law rewrites can halt; they match `.box`.

**Merging, innermost first.**  `{U}{V}` merges when `U` writes only locals
(`Upd.envOnly`, substituted into `V`), or is one storage write
(`withStM`, `Calculus/StateParts.lean`: memory reads included, an index
check carried over as `p[i]@S`), or is locals and a memory write,
`{carol := freshId(copySt(memory, v)) ‖ memory := copySt(memory, v)}`, the
write substituted for `memory` in `V` and the locals after it
(`Upd.mergeMem`), or is locals and a storage write, substituted into `V` in
one pass (`Upd.mergeStL`, `Tm.substSt`), the write dropped where `V` writes
the storage over it.  Inside out every merge of a stack the program leaves
is one of the four.  `Fml.mergeSpine` merges that way.  It takes
the count from the chain: whether the body is one more update is a question
about the body.
-/

namespace Solidity

open Semantics SemanticsProperties

variable {C : Contract}

/-! ## What a chain needs of a rewrite -/

/-- A rewrite of a chain's line: the line after, computed (`apply`), and why
the line before follows from it (`sound`).  A link `φ ⇝ ψ` by `r` is
`r.apply φ = some ψ`, proved by `rfl` on a line whose rewritten part is
concrete. -/
structure LineRw (C : Contract) where
  /-- The line after, or `none` where the rule does not fit. -/
  apply : Fml C → Option (Fml C)
  /-- Wherever the line after holds, the line before does. -/
  sound : ∀ {φ ψ : Fml C}, apply φ = some ψ → ∀ σ, holds σ ψ → holds σ φ

/-- A line rewritten to a valid one is valid. -/
theorem LineRw.valid (r : LineRw C) {φ ψ : Fml C} (h : r.apply φ = some ψ) (hψ : Valid ψ) :
    Valid φ :=
  fun σ => r.sound h σ (hψ σ)

/-- A postcondition that follows from another after the same run:
`{ x := 1 } (y ≐ 1)` gives `{ x := 1 } true`. -/
theorem Modality.after_mono (m : Modality) {p q : State → Prop} (h : ∀ τ, p τ → q τ) :
    (r : Res State) → m.after p r → m.after q r
  | .ok τ, hp => h τ hp
  | .error _, hp => hp

/-! ## A position on the spine -/

/-- `f` on the update at position `i` of the spine, `0` the outermost:
`f m U φ` rewrites `{U}_m φ`.  The updates above it stay; nothing below
`{U} φ` is looked at but what `f` looks at. -/
def Fml.atSpine (f : Modality → Upd C → Fml C → Option (Fml C)) : Nat → Fml C → Option (Fml C)
  | 0, .upd m U φ => f m U φ
  | i + 1, .upd m U φ => (φ.atSpine f i).map (.upd m U)
  | _, _ => none

/-- A rewrite of one update, one direction, is one of the line. -/
theorem Fml.atSpine_sound {f : Modality → Upd C → Fml C → Option (Fml C)}
    (hf : ∀ {m U φ ψ}, f m U φ = some ψ → ∀ σ, holds σ ψ → holds σ (.upd m U φ)) :
    (i : Nat) → (φ : Fml C) → ∀ {ψ : Fml C}, φ.atSpine f i = some ψ → ∀ σ, holds σ ψ → holds σ φ
  | 0, φ, _, h, σ, hψ => by
    cases φ with
    | upd m U φ => exact hf h σ hψ
    | _ => nomatch h
  | i + 1, φ, _, h, σ, hψ => by
    cases φ with
    | upd m U φ =>
      simp only [Fml.atSpine, Option.map_eq_some_iff] at h
      obtain ⟨φ', h', rfl⟩ := h
      exact m.after_mono (fun τ => Fml.atSpine_sound hf i φ h' τ) _ hψ
    | _ => nomatch h

/-- A rewrite of one update that is an equivalence is one of the line. -/
theorem Fml.atSpine_holds {f : Modality → Upd C → Fml C → Option (Fml C)}
    (hf : ∀ {m U φ ψ}, f m U φ = some ψ → ∀ σ, (holds σ ψ ↔ holds σ (.upd m U φ))) :
    (i : Nat) → (φ : Fml C) → ∀ {ψ : Fml C}, φ.atSpine f i = some ψ → ∀ σ, (holds σ ψ ↔ holds σ φ)
  | 0, φ, _, h, σ => by
    cases φ with
    | upd m U φ => exact hf h σ
    | _ => nomatch h
  | i + 1, φ, _, h, σ => by
    cases φ with
    | upd m U φ =>
      simp only [Fml.atSpine, Option.map_eq_some_iff] at h
      obtain ⟨φ', h', rfl⟩ := h
      exact m.after_congr (fun τ => Fml.atSpine_holds hf i φ h' τ) _
    | _ => nomatch h

/-! ## A storage write shadowed by one over it

`{storage := s}{storage := t}` merges to `{storage := t[s/storage]}`, one
element: the first write is read by the second, so wherever the second
returns the first did, and running the second from the state the first left
is running it from the state before — no element of an update reads the
storage it runs in (`Upd.foldl_setStorage`).  The printed merged line has one
`storage :=` for that reason, and so does the chain's. -/

/-- `s` is read before anything else of `t` (`t.onSpine s`): `t` is `s`, or
a storage operation whose storage argument is on the spine of `s`.  So `t`
halts wherever `s` does (`Tm.onSpine_error`).  `spineAny f` asks `f` of each
term on the spine. -/
def Tm.spineAny (f : STerm C → Bool) : Tm C u → Bool
  | .app1 (.select r) a => f (.app1 (.select r) a) || a.spineAny f
  | .app2 .delAt a p => f (.app2 .delAt a p) || a.spineAny f
  | .app2 (.pushSlot E) a p => f (.app2 (.pushSlot E) a p) || a.spineAny f
  | .app2 .pop a p => f (.app2 .pop a p) || a.spineAny f
  | .app2 .shrink a p => f (.app2 .shrink a p) || a.spineAny f
  | .app2 (.extend E) a p => f (.app2 (.extend E) a p) || a.spineAny f
  | .app3 .save a p v => f (.app3 .save a p v) || a.spineAny f
  | .app3 .push a p v => f (.app3 .push a p v) || a.spineAny f
  | t => match u, t with
    | .st, t => f t
    | _, _ => false

@[inherit_doc Tm.spineAny]
def Tm.onSpine (t s : STerm C) : Bool := t.spineAny (· == s)

theorem Tm.app1_eval (σ : State) (o : Op1 a s) (x : Tm C a) :
    (Tm.app1 o x).eval σ = o.eval σ (x.eval σ) := rfl
theorem Tm.app2_eval (σ : State) (o : Op2 a b s) (x : Tm C a) (y : Tm C b) :
    (Tm.app2 o x y).eval σ = o.eval σ (x.eval σ) (y.eval σ) := rfl
theorem Tm.app3_eval (σ : State) (o : Op3 a b c s) (x : Tm C a) (y : Tm C b) (z : Tm C c) :
    (Tm.app3 o x y z).eval σ = o.eval σ (x.eval σ) (y.eval σ) (z.eval σ) := rfl

/-- A term on the spine of `s` halts wherever `s` does. -/
theorem Tm.onSpine_error {s : STerm C} {σ : State} {e : Halt} (hs : s.eval σ = .error e) :
    (t : STerm C) → t.onSpine s = true → ∃ e', t.eval σ = .error e'
  | .app1 (.select r) a, h => by
    simp only [Tm.onSpine, Tm.spineAny, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact ⟨e, hs⟩
    · obtain ⟨e', ha⟩ := Tm.onSpine_error hs a h
      exact ⟨e', by rw [Tm.app1_eval, ha]; rfl⟩
  | .app2 .delAt a p, h | .app2 (.pushSlot _) a p, h | .app2 .pop a p, h | .app2 .shrink a p, h
  | .app2 (.extend _) a p, h => by
    simp only [Tm.onSpine, Tm.spineAny, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact ⟨e, hs⟩
    · obtain ⟨e', ha⟩ := Tm.onSpine_error hs a h
      exact ⟨e', by rw [Tm.app2_eval, ha]; rfl⟩
  | .app3 .save a p v, h => by
    simp only [Tm.onSpine, Tm.spineAny, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact ⟨e, hs⟩
    · obtain ⟨e', ha⟩ := Tm.onSpine_error hs a h
      rw [Tm.app3_eval, ha]
      cases v.eval σ <;> exact ⟨_, rfl⟩
  | .app3 .push a p v, h => by
    simp only [Tm.onSpine, Tm.spineAny, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact ⟨e, hs⟩
    · obtain ⟨e', ha⟩ := Tm.onSpine_error hs a h
      exact ⟨e', by rw [Tm.app3_eval, ha]; rfl⟩
  | .pvS _, h | .app0 .storage, h => by
    simp only [Tm.onSpine, Tm.spineAny, beq_iff_eq] at h
    exact ⟨e, h ▸ hs⟩

/-- `t` is read before anything else of `s` on the memory spine: `s` is `t`,
or a memory operation over a term on the spine of `t`. -/
def Tm.memSpineAny (f : MTerm C → Bool) : Tm C u → Bool
  | .app1 (.addM R) a => f (.app1 (.addM R) a) || a.memSpineAny f
  | .app2 .copySt a v => f (.app2 .copySt a v) || a.memSpineAny f
  | .app3 .write a p v => f (.app3 .write a p v) || a.memSpineAny f
  | t => match u, t with
    | .mem, t => f t
    | _, _ => false

@[inherit_doc Tm.memSpineAny]
def Tm.onMemSpine (t s : MTerm C) : Bool := t.memSpineAny (· == s)

/-- A term on the memory spine of `s` halts wherever `s` does. -/
theorem Tm.onMemSpine_error {s : MTerm C} {σ : State} {e : Halt} (hs : s.eval σ = .error e) :
    (t : MTerm C) → t.onMemSpine s = true → ∃ e', t.eval σ = .error e'
  | .app1 (.addM _) a, h => by
    simp only [Tm.onMemSpine, Tm.memSpineAny, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact ⟨e, hs⟩
    · obtain ⟨e', ha⟩ := Tm.onMemSpine_error hs a h
      exact ⟨e', by rw [Tm.app1_eval, ha]; rfl⟩
  | .app2 .copySt a v, h => by
    simp only [Tm.onMemSpine, Tm.memSpineAny, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact ⟨e, hs⟩
    · obtain ⟨e', ha⟩ := Tm.onMemSpine_error hs a h
      rw [Tm.app2_eval, ha]
      cases v.eval σ <;> exact ⟨_, rfl⟩
  | .app3 .write a p v, h => by
    simp only [Tm.onMemSpine, Tm.memSpineAny, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact ⟨e, hs⟩
    · obtain ⟨e', ha⟩ := Tm.onMemSpine_error hs a h
      rw [Tm.app3_eval, ha]
      cases v.eval σ <;> exact ⟨_, rfl⟩
  | .app0 .memory, h => by
    simp only [Tm.onMemSpine, Tm.memSpineAny, beq_iff_eq] at h
    exact ⟨e, h ▸ hs⟩

/-- The element writes the storage with a term on the spine of `s`. -/
def UpdElem.onSpine (s : STerm C) : UpdElem C → Bool
  | .storage t => t.onSpine s
  | _ => false

theorem UpdElem.onSpine_eq {s : STerm C} : (e : UpdElem C) → e.onSpine s = true →
    ∃ t, e = .storage t ∧ t.onSpine s = true
  | .storage t, h => ⟨t, rfl, h⟩

/-- An element run from a state with another storage: the storage write
writes the same, every other element leaves that storage where it is.  No
element reads the storage it runs in — a right-hand side is read in the
pre-state `σ₀`. -/
theorem UpdElem.write_setStorage (σ₀ : State) (st : List (Name × SVal)) (ρ : State) :
    (e : UpdElem C) → e.write σ₀ { ρ with storage := st } =
      if e.isStorage then e.write σ₀ ρ else (e.write σ₀ ρ).map fun τ => { τ with storage := st }
  | .val _ t => by
    simp only [UpdElem.write, UpdElem.isStorage, Bool.false_eq_true, ↓reduceIte]
    cases t.eval σ₀ <;> rfl
  | .path _ p => by
    simp only [UpdElem.write, UpdElem.isStorage, Bool.false_eq_true, ↓reduceIte]
    cases p.eval σ₀ with
    | error _ => rfl
    | ok rs => cases rs; rfl
  | .mref _ i => by
    simp only [UpdElem.write, UpdElem.isStorage, Bool.false_eq_true, ↓reduceIte]
    cases i.eval σ₀ <;> rfl
  | .storage s => by
    simp only [UpdElem.write, UpdElem.isStorage, ↓reduceIte]
  | .store _ s => by
    simp only [UpdElem.write, UpdElem.isStorage, Bool.false_eq_true, ↓reduceIte]
    cases s.eval σ₀ <;> rfl
  | .memory μ => by
    simp only [UpdElem.write, UpdElem.isStorage, Bool.false_eq_true, ↓reduceIte]
    cases μ.eval σ₀ <;> rfl
  | .selfBalance _ a => by
    simp only [UpdElem.write, UpdElem.isStorage, Bool.false_eq_true, ↓reduceIte]
    cases a.eval σ₀ with
    | error _ => rfl
    | ok v => cases v <;> rfl
  | .net r _ a => by
    simp only [UpdElem.write, UpdElem.isStorage, Bool.false_eq_true, ↓reduceIte]
    cases r.eval σ₀ with
    | error _ => rfl
    | ok v =>
      cases v with
      | bool _ => rfl
      | int _ =>
        cases a.eval σ₀ with
        | error _ => rfl
        | ok w => cases w <;> rfl
  | .pay r a => by
    simp only [UpdElem.write, UpdElem.isStorage, Bool.false_eq_true, ↓reduceIte]
    cases r.eval σ₀ with
    | error _ => rfl
    | ok v =>
      cases v with
      | bool _ => rfl
      | int _ =>
        cases a.eval σ₀ with
        | error _ => rfl
        | ok w =>
          cases w with
          | bool _ => rfl
          | int _ =>
            simp only [bind, Except.bind, Value.asInt, pure, Except.pure]
            split <;> rfl
  | .saveNet _ => rfl

/-- An update run from a state with another storage: the same run, if some
element writes the storage; else the run with that storage put back. -/
theorem Upd.foldl_setStorage (σ₀ : State) (st : List (Name × SVal)) :
    (W : Upd C) → ∀ ρ, W.foldlM (fun τ e => e.write σ₀ τ) { ρ with storage := st } =
      if W.any (·.isStorage) then W.foldlM (fun τ (e : UpdElem C) => e.write σ₀ τ) ρ
      else (W.foldlM (fun τ (e : UpdElem C) => e.write σ₀ τ) ρ).map fun τ => { τ with storage := st }
  | [], ρ => rfl
  | e :: W, ρ => by
    simp only [List.foldlM_cons, List.any_cons, UpdElem.write_setStorage σ₀ st ρ e]
    cases he : e.isStorage
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_or]
      cases e.write σ₀ ρ with
      | error _ => cases W.any (·.isStorage) <;> rfl
      | ok ρ' =>
        show W.foldlM (fun τ e => e.write σ₀ τ) { ρ' with storage := st } = _
        rw [Upd.foldl_setStorage σ₀ st W ρ']
        cases W.any (·.isStorage) <;> rfl
    · simp only [↓reduceIte, Bool.true_or]

/-- A run of an update with a storage element does not see the storage it
starts from. -/
theorem Upd.foldl_storage_irrel (σ₀ : State) {W : Upd C} (hW : W.any (·.isStorage) = true)
    (st : List (Name × SVal)) (ρ : State) :
    W.foldlM (fun τ e => e.write σ₀ τ) { ρ with storage := st } =
      W.foldlM (fun τ e => e.write σ₀ τ) ρ := by
  rw [Upd.foldl_setStorage, if_pos hW]

/-- A run of an update halts where a storage write of it halts. -/
theorem Upd.foldl_error_of_storage (σ₀ : State) {t : STerm C} {e : Halt} (ht : t.eval σ₀ = .error e) :
    (W : Upd C) → UpdElem.storage t ∈ W → ∀ ρ,
      ∃ e', W.foldlM (fun τ d => d.write σ₀ τ) ρ = .error e'
  | [], h, _ => nomatch h
  | d :: W, h, ρ => by
    simp only [List.foldlM_cons]
    rcases List.mem_cons.1 h with rfl | h
    · refine ⟨e, ?_⟩
      rw [UpdElem.storage_write, ht]
      rfl
    · cases d.write σ₀ ρ with
      | error e' => exact ⟨e', rfl⟩
      | ok ρ' => exact Upd.foldl_error_of_storage σ₀ ht W h ρ'

/-- **The shadowed storage write goes**: `{L ‖ storage := s ‖ W}` is
`{L ‖ W}` where `W` writes the storage with a term on the spine of `s`. -/
theorem Upd.dropStorage_holds {s : STerm C} {W : Upd C} (hW : W.any (·.onSpine s) = true)
    (m : Modality) (L : Upd C) (ψ : Fml C) (σ : State) :
    holds σ (.upd m (L ++ W) ψ) ↔ holds σ (.upd m (L ++ .storage s :: W) ψ) := by
  obtain ⟨d, hd, hd'⟩ := List.any_eq_true.1 hW
  obtain ⟨t, rfl, ht⟩ := UpdElem.onSpine_eq d hd'
  simp only [holds, Upd.apply, List.foldlM_append, List.foldlM_cons, UpdElem.storage_write]
  cases L.foldlM (fun τ e => e.write σ τ) σ with
  | error _ => exact Iff.rfl
  | ok ρ =>
    simp only [bind, Except.bind]
    cases hs : s.eval σ with
    | error e =>
      obtain ⟨e', ht'⟩ := Tm.onSpine_error hs t ht
      obtain ⟨e'', h⟩ := Upd.foldl_error_of_storage σ ht' W hd ρ
      dsimp only
      rw [h]
      exact Iff.rfl
    | ok τ =>
      have hst : W.any (·.isStorage) = true := List.any_eq_true.2 ⟨_, hd, rfl⟩
      dsimp only
      rw [Upd.foldl_storage_irrel σ hst τ.storage ρ]

/-- `{storage := s}{V}` as one update: `V` over the write (`withStM`, memory
reads included), and the write itself unless `V` writes the storage over it
(`Upd.dropStorage_holds`). -/
def Upd.mergeSt (s : STerm C) (V : Upd C) : Upd C :=
  if (V.withStM s).any (·.onSpine s) then V.withStM s else .storage s :: V.withStM s

theorem Upd.mergeSt_holds (s : STerm C) (V : Upd C) (m : Modality) (ψ : Fml C) (σ : State) :
    holds σ (.upd m (Upd.mergeSt s V) ψ) ↔ holds σ (.upd m (.storage s :: V.withStM s) ψ) := by
  unfold Upd.mergeSt
  split
  · exact Upd.dropStorage_holds ‹_› m [] ψ σ
  · exact Iff.rfl

/-- The element writes the memory with a term on the memory spine of `M`. -/
def UpdElem.onMemSpine (M : MTerm C) : UpdElem C → Bool
  | .memory N => N.onMemSpine M
  | _ => false

theorem UpdElem.onMemSpine_eq {M : MTerm C} : (e : UpdElem C) → e.onMemSpine M = true →
    ∃ N, e = .memory N ∧ N.onMemSpine M = true
  | .memory N, h => ⟨N, rfl, h⟩

/-- The element writes the memory: `memory := M`. -/
def UpdElem.isMemory : UpdElem C → Bool
  | .memory _ => true
  | _ => false

/-- An element run from a state with another memory: the memory write
writes the same, every other element leaves that memory where it is
(`UpdElem.write_setStorage`'s mirror). -/
theorem UpdElem.write_setMem (σ₀ : State) (hp : List (Nat × MObj)) (n : Nat) (ρ : State) :
    (e : UpdElem C) → e.write σ₀ { ρ with heap := hp, nextId := n } =
      if e.isMemory then e.write σ₀ ρ
      else (e.write σ₀ ρ).map fun τ => { τ with heap := hp, nextId := n }
  | .val _ t => by
    simp only [UpdElem.write, UpdElem.isMemory, Bool.false_eq_true, ↓reduceIte]
    cases t.eval σ₀ <;> rfl
  | .path _ p => by
    simp only [UpdElem.write, UpdElem.isMemory, Bool.false_eq_true, ↓reduceIte]
    cases p.eval σ₀ with
    | error _ => rfl
    | ok rs => cases rs; rfl
  | .mref _ i => by
    simp only [UpdElem.write, UpdElem.isMemory, Bool.false_eq_true, ↓reduceIte]
    cases i.eval σ₀ <;> rfl
  | .storage s => by
    simp only [UpdElem.write, UpdElem.isMemory, Bool.false_eq_true, ↓reduceIte]
    cases s.eval σ₀ <;> rfl
  | .store _ s => by
    simp only [UpdElem.write, UpdElem.isMemory, Bool.false_eq_true, ↓reduceIte]
    cases s.eval σ₀ <;> rfl
  | .memory μ => by
    simp only [UpdElem.write, UpdElem.isMemory, ↓reduceIte]
  | .selfBalance _ a => by
    simp only [UpdElem.write, UpdElem.isMemory, Bool.false_eq_true, ↓reduceIte]
    cases a.eval σ₀ with
    | error _ => rfl
    | ok v => cases v <;> rfl
  | .net r _ a => by
    simp only [UpdElem.write, UpdElem.isMemory, Bool.false_eq_true, ↓reduceIte]
    cases r.eval σ₀ with
    | error _ => rfl
    | ok v =>
      cases v with
      | bool _ => rfl
      | int _ =>
        cases a.eval σ₀ with
        | error _ => rfl
        | ok w => cases w <;> rfl
  | .pay r a => by
    simp only [UpdElem.write, UpdElem.isMemory, Bool.false_eq_true, ↓reduceIte]
    cases r.eval σ₀ with
    | error _ => rfl
    | ok v =>
      cases v with
      | bool _ => rfl
      | int _ =>
        cases a.eval σ₀ with
        | error _ => rfl
        | ok w =>
          cases w with
          | bool _ => rfl
          | int _ =>
            simp only [bind, Except.bind, Value.asInt, pure, Except.pure]
            split <;> rfl
  | .saveNet _ => rfl

/-- An update run from a state with another memory: the same run, if some
element writes the memory; else the run with that memory put back. -/
theorem Upd.foldl_setMem (σ₀ : State) (hp : List (Nat × MObj)) (n : Nat) :
    (W : Upd C) → ∀ ρ, W.foldlM (fun τ e => e.write σ₀ τ) { ρ with heap := hp, nextId := n } =
      if W.any (·.isMemory) then W.foldlM (fun τ (e : UpdElem C) => e.write σ₀ τ) ρ
      else (W.foldlM (fun τ (e : UpdElem C) => e.write σ₀ τ) ρ).map
        fun τ => { τ with heap := hp, nextId := n }
  | [], ρ => rfl
  | e :: W, ρ => by
    simp only [List.foldlM_cons, List.any_cons, UpdElem.write_setMem σ₀ hp n ρ e]
    cases he : e.isMemory
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_or]
      cases e.write σ₀ ρ with
      | error _ => cases W.any (·.isMemory) <;> rfl
      | ok ρ' =>
        show W.foldlM (fun τ e => e.write σ₀ τ) { ρ' with heap := hp, nextId := n } = _
        rw [Upd.foldl_setMem σ₀ hp n W ρ']
        cases W.any (·.isMemory) <;> rfl
    · simp only [↓reduceIte, Bool.true_or]

/-- A run of an update with a memory element does not see the memory it
starts from. -/
theorem Upd.foldl_mem_irrel (σ₀ : State) {W : Upd C} (hW : W.any (·.isMemory) = true)
    (hp : List (Nat × MObj)) (n : Nat) (ρ : State) :
    W.foldlM (fun τ e => e.write σ₀ τ) { ρ with heap := hp, nextId := n } =
      W.foldlM (fun τ e => e.write σ₀ τ) ρ := by
  rw [Upd.foldl_setMem, if_pos hW]

/-- A run of an update halts where a memory write of it halts. -/
theorem Upd.foldl_error_of_memory (σ₀ : State) {t : MTerm C} {e : Halt} (ht : t.eval σ₀ = .error e) :
    (W : Upd C) → UpdElem.memory t ∈ W → ∀ ρ,
      ∃ e', W.foldlM (fun τ d => d.write σ₀ τ) ρ = .error e'
  | [], h, _ => nomatch h
  | d :: W, h, ρ => by
    simp only [List.foldlM_cons]
    rcases List.mem_cons.1 h with rfl | h
    · refine ⟨e, ?_⟩
      rw [UpdElem.memory_write, ht]
      rfl
    · cases d.write σ₀ ρ with
      | error e' => exact ⟨e', rfl⟩
      | ok ρ' => exact Upd.foldl_error_of_memory σ₀ ht W h ρ'

/-- **The shadowed memory write goes**: `{L ‖ memory := M ‖ W}` is `{L ‖ W}`
where `W` writes the memory with a term on the memory spine of `M`
(`Upd.dropStorage_holds`'s mirror, with the elements before the write). -/
theorem Upd.dropMemory_holds {M : MTerm C} {W : Upd C} (hW : W.any (·.onMemSpine M) = true)
    (m : Modality) (L : Upd C) (ψ : Fml C) (σ : State) :
    holds σ (.upd m (L ++ W) ψ) ↔ holds σ (.upd m (L ++ .memory M :: W) ψ) := by
  obtain ⟨d, hd, hd'⟩ := List.any_eq_true.1 hW
  obtain ⟨N, rfl, hN⟩ := UpdElem.onMemSpine_eq d hd'
  simp only [holds, Upd.apply, List.foldlM_append, List.foldlM_cons, UpdElem.memory_write]
  cases L.foldlM (fun τ e => e.write σ τ) σ with
  | error _ => exact Iff.rfl
  | ok ρ =>
    simp only [bind, Except.bind]
    cases hs : M.eval σ with
    | error e =>
      obtain ⟨e', hN'⟩ := Tm.onMemSpine_error hs N hN
      obtain ⟨e'', h⟩ := Upd.foldl_error_of_memory σ hN' W hd ρ
      rw [h]
      exact Iff.rfl
    | ok μ =>
      have hmem : W.any (·.isMemory) = true := List.any_eq_true.2 ⟨_, hd, rfl⟩
      dsimp only
      rw [Upd.foldl_mem_irrel σ hmem μ.heap μ.nextId ρ]

/-! ## `sequentialToParallel` -/

/-- An update that cannot halt reads alike under either modality:
`{ se1 := 10 } φ` under the box is `{ se1 := 10 } φ` under the diamond. -/
theorem Upd.holds_total {U : Upd C} (hU : U.total = true) (m m' : Modality) (φ : Fml C)
    (σ : State) : holds σ (.upd m U φ) ↔ holds σ (.upd m' U φ) := by
  obtain ⟨τ, hτ⟩ := Upd.foldl_total σ U hU σ
  simp only [holds, Upd.apply, hτ, Modality.after]

/-- `{L ‖ memory := M}{V}` as one update, `L` locals: `M` substituted for
`memory` in `V` (`withMem`), then the locals (`subst`), after the write.
`{L ‖ memory := M}` is `{L}{memory := M}` where `M` reads none of `L`'s
variables (`M.subst L = M`), and the two merges are `Upd.mergeMemory_holds`
and `sequentialToParallel`.  The write itself goes where `V` writes the
memory over it (`Upd.dropMemory_holds`), so a merged line has one
`memory :=`. -/
def Upd.mergeMem (L : Upd C) (M : MTerm C) (V : Upd C) : Upd C :=
  if (Upd.subst (V.withMem M) L).any (·.onMemSpine M) then L ++ Upd.subst (V.withMem M) L
  else L ++ (.memory M :: Upd.subst (V.withMem M) L)

theorem Upd.mergeMem_holds {L : Upd C} (hL : L.envOnly = true) {M : MTerm C} (hM : M.subst L = M)
    (V : Upd C) (m : Modality) (ψ : Fml C) (σ : State) :
    holds σ (.upd m (Upd.mergeMem L M V) ψ) ↔ holds σ (.upd m (L ++ [.memory M]) (.upd m V ψ)) := by
  have h1 : Upd.subst (UpdElem.memory M :: V.withMem M) L = .memory M :: Upd.subst (V.withMem M) L := by
    simp only [Upd.subst, List.map_cons, UpdElem.subst, hM]
  have h2 : Upd.subst [UpdElem.memory M] L = [.memory M] := by
    simp only [Upd.subst, List.map_cons, List.map_nil, UpdElem.subst, hM]
  calc holds σ (.upd m (Upd.mergeMem L M V) ψ)
      ↔ holds σ (.upd m (L ++ (.memory M :: Upd.subst (V.withMem M) L)) ψ) := by
        unfold Upd.mergeMem
        split
        · exact Upd.dropMemory_holds ‹_› m L ψ σ
        · exact Iff.rfl
    _ ↔ holds σ (.upd m L (.upd m (.memory M :: V.withMem M) ψ)) := by
        rw [← h1]
        exact (UpdRule.sequentialToParallel hL).sound σ
    _ ↔ holds σ (.upd m L (.upd m [.memory M] (.upd m V ψ))) := by
        simp only [holds]
        exact m.after_congr (fun τ => Upd.mergeMemory_holds m M V ψ τ) _
    _ ↔ holds σ (.upd m (L ++ [.memory M]) (.upd m V ψ)) := by
        conv => rhs; rw [← h2]
        exact ((UpdRule.sequentialToParallel hL).sound σ).symm

/-- The update's one element that writes no local, with the locals before
and after it. -/
def Upd.splitWrite : Upd C → Option (Upd C × UpdElem C × Upd C)
  | [] => none
  | e :: U =>
    if e.var?.isSome then (Upd.splitWrite U).map fun r => (e :: r.1, r.2.1, r.2.2)
    else if Upd.envOnly U then some ([], e, U) else none

theorem Upd.splitWrite_eq {L₁ L₂ : Upd C} {e : UpdElem C} :
    (U : Upd C) → U.splitWrite = some (L₁, e, L₂) →
      U = L₁ ++ e :: L₂ ∧ L₁.envOnly = true ∧ L₂.envOnly = true
  | [], h => nomatch h
  | d :: U, h => by
    simp only [Upd.splitWrite] at h
    split at h
    · rename_i hd
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨L₁', e', L₂'⟩, h', rfl, rfl, rfl⟩ := h
      obtain ⟨rfl, h₁, h₂⟩ := Upd.splitWrite_eq U h'
      exact ⟨rfl, by simpa [Upd.envOnly, hd] using h₁, h₂⟩
    · split at h
      · rename_i hU
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨rfl, rfl, hU⟩
      · nomatch h

/-- A storage write moved past locals of a parallel update: the locals read
the pre-state and write no storage, so the run leaves the same state, or
halts either way. -/
theorem Upd.storage_perm_holds (m : Modality) (L₁ : Upd C) (S : STerm C) {L₂ : Upd C}
    (hL : L₂.any (·.isStorage) = false) (W : Upd C) (ψ : Fml C) (σ : State) :
    holds σ (.upd m (L₁ ++ .storage S :: (L₂ ++ W)) ψ) ↔
      holds σ (.upd m (L₁ ++ (L₂ ++ .storage S :: W)) ψ) := by
  simp only [holds, Upd.apply, List.foldlM_append, List.foldlM_cons, UpdElem.storage_write]
  cases L₁.foldlM (fun τ e => e.write σ τ) σ with
  | error _ => exact Iff.rfl
  | ok ρ =>
    simp only [bind, Except.bind]
    cases S.eval σ with
    | error _ =>
      dsimp only
      cases L₂.foldlM (fun τ e => e.write σ τ) ρ with
      | error _ => simp only [Modality.after]
      | ok _ => simp only [Modality.after]
    | ok τ' =>
      dsimp only
      rw [Upd.foldl_setStorage σ τ'.storage L₂ ρ, if_neg (by simp [hL])]
      cases L₂.foldlM (fun τ e => e.write σ τ) ρ with
      | error _ => simp only [Except.map, Modality.after]
      | ok ρ₂ => simp only [Except.map]

/-- An update of locals writes no storage. -/
theorem Upd.envOnly_isStorage {L : Upd C} (h : L.envOnly = true) : L.any (·.isStorage) = false := by
  simp only [Upd.envOnly, List.all_eq_true] at h
  simp only [List.any_eq_false]
  intro e he
  have := h e he
  cases e <;> simp_all [UpdElem.var?, UpdElem.isStorage]

/-- `{L₁ ‖ storage := S ‖ L₂}{V}` as one update, `L₁`, `L₂` locals: the
locals and `S` substituted into `V` (`Upd.substSt`), after the three; the
write stays where it was unless `V` writes the storage over it
(`Upd.dropStorage_holds`). -/
def Upd.mergeStL (L₁ : Upd C) (S : STerm C) (L₂ : Upd C) (V : Upd C) : Upd C :=
  let V' := Upd.substSt (L₁ ++ L₂) S V
  if V'.any (·.onSpine S) then L₁ ++ (L₂ ++ V') else L₁ ++ .storage S :: (L₂ ++ V')

/-- The merge with the write kept, `L` locals: every element of
`{L ‖ storage := S ‖ {L ‖ storage := S}V}` reads the pre-state, and `V`'s
substituted right-hand sides read there what `V`'s read after the two
(`Tm.substSt_eval`). -/
theorem Upd.mergeStL_core {L : Upd C} (hL : L.envOnly = true) (S : STerm C) (V : Upd C)
    (m : Modality) (ψ : Fml C) (σ : State) :
    holds σ (.upd m (L ++ .storage S :: Upd.substSt L S V) ψ) ↔
      holds σ (.upd m (L ++ [.storage S]) (.upd m V ψ)) := by
  simp only [holds, Upd.apply, List.foldlM_append, List.foldlM_cons, List.foldlM_nil,
    UpdElem.storage_write]
  cases hL' : L.foldlM (fun τ e => e.write σ τ) σ with
  | error _ => exact Iff.rfl
  | ok σ₁ =>
    simp only [bind, Except.bind]
    cases hs : S.eval σ with
    | error _ => exact Iff.rfl
    | ok τ =>
      have h := Upd.substAgree hL hL'
      have hr : σ.Rest { σ₁ with storage := τ.storage } :=
        ⟨h.agree.net, h.agree.selfBalance, h.agree.tx⟩
      dsimp only
      simp only [pure, Except.pure, Modality.after]
      rw [Upd.substSt, Upd.mapTm_foldl (P := fun {_} _ => true) hr
        (fun t _ => Tm.substSt_eval h hs t) V (List.all_eq_true.2 fun e _ => by cases e <;> rfl)]

/-- `Upd.mergeStL_core` with the write between the locals, where
`Upd.splitWrite` finds it. -/
theorem Upd.mergeStL_keep_holds {L₁ L₂ : Upd C} (h₁ : L₁.envOnly = true) (h₂ : L₂.envOnly = true)
    (S : STerm C) (V : Upd C) (m : Modality) (ψ : Fml C) (σ : State) :
    holds σ (.upd m (L₁ ++ .storage S :: (L₂ ++ Upd.substSt (L₁ ++ L₂) S V)) ψ) ↔
      holds σ (.upd m (L₁ ++ .storage S :: L₂) (.upd m V ψ)) := by
  have hL : (L₁ ++ L₂).envOnly = true := by simp only [Upd.envOnly, List.all_append] at *; simp [h₁, h₂]
  have hL₂ := Upd.envOnly_isStorage h₂
  rw [Upd.storage_perm_holds m L₁ S hL₂ _ ψ σ]
  have hperm := Upd.storage_perm_holds m L₁ S hL₂ [] (.upd m V ψ) σ
  simp only [List.append_nil] at hperm
  rw [hperm, ← List.append_assoc, ← List.append_assoc]
  exact Upd.mergeStL_core hL S V m ψ σ

theorem Upd.mergeStL_holds {L₁ L₂ : Upd C} (h₁ : L₁.envOnly = true) (h₂ : L₂.envOnly = true)
    {S : STerm C} {V : Upd C} (m : Modality) (ψ : Fml C) (σ : State) :
    holds σ (.upd m (Upd.mergeStL L₁ S L₂ V) ψ) ↔
      holds σ (.upd m (L₁ ++ .storage S :: L₂) (.upd m V ψ)) := by
  rw [← Upd.mergeStL_keep_holds h₁ h₂ S V m ψ σ]
  dsimp only [Upd.mergeStL]
  split
  · rename_i hW
    rw [Upd.storage_perm_holds m L₁ S (Upd.envOnly_isStorage h₂) _ ψ σ, ← List.append_assoc,
      ← List.append_assoc]
    exact Upd.dropStorage_holds hW m (L₁ ++ L₂) ψ σ
  · exact Iff.rfl

/-- The update's last element, and the rest. -/
def Upd.splitLast : Upd C → Option (Upd C × UpdElem C)
  | [] => none
  | [e] => some ([], e)
  | e :: d :: U => (Upd.splitLast (d :: U)).map fun r => (e :: r.1, r.2)

theorem Upd.splitLast_eq {L : Upd C} {e : UpdElem C} :
    (U : Upd C) → U.splitLast = some (L, e) → U = L ++ [e]
  | [], h => nomatch h
  | [_], h => by
    simp only [Upd.splitLast, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | e' :: d :: U, h => by
    simp only [Upd.splitLast, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨L', e''⟩, h', rfl, rfl⟩ := h
    rw [List.cons_append, ← Upd.splitLast_eq (d :: U) h']

/-- `{U}_m {V}_m'` as one parallel update and its modality, if a rule merges
them: `U` of locals substituted into `V`; `U` one storage write substituted
for `V`'s `storage` — and dropped where `V` writes the storage over it
(`Upd.mergeSt`), so `{storage := s}{storage := t}` is one element; or `U`
locals and a memory write, substituted into `V` (`Upd.mergeMem`); or `U`
locals and a storage write (`Upd.mergeStL`).  The two
modalities are compared only when neither update can stand for the other's:
`{ se1 := 10 }` cannot halt, so it merges under any `m'`. -/
def Upd.merge (m : Modality) (U : Upd C) (m' : Modality) (V : Upd C) :
    Option (Modality × Upd C) :=
  if (U.envOnly && (U.total || decide (m' = m))) = true then some (m', U ++ V.subst U)
  else match U with
    | [.storage s] =>
      if (V.total || decide (m' = m)) = true then some (m, Upd.mergeSt s V) else none
    | _ => match U.splitLast with
      | some (L, .memory M) =>
        if (L.envOnly && (M.subst L == M) && (V.total || decide (m' = m))) = true then
          some (m, Upd.mergeMem L M V)
        else none
      | _ => match U.splitWrite with
        | some (L₁, .storage S, L₂) =>
          if (V.total || decide (m' = m)) = true then some (m, Upd.mergeStL L₁ S L₂ V) else none
        | _ => none

/-- **`sequentialToParallel`**: the merged update holds exactly where the
two did.

Example: `{ sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }`
merges to `{ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, se1) }`,
and `{ storage := save(storage, alice.age, 1) } { storage := save(storage, alice.age, 2) }`
to `{ storage := save(save(storage, alice.age, 1), alice.age, 2) }`. -/
theorem Upd.merge_holds {m m' m'' : Modality} {U V W : Upd C}
    (h : Upd.merge m U m' V = some (m'', W)) (φ : Fml C) (σ : State) :
    holds σ (.upd m'' W φ) ↔ holds σ (.upd m U (.upd m' V φ)) := by
  unfold Upd.merge at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
    rw [(UpdRule.sequentialToParallel (m := m') (V := V) (φ := φ) hc.1).sound σ]
    rcases hc.2 with ht | rfl
    · exact Upd.holds_total ht m' m _ σ
    · exact Iff.rfl
  · split at h
    · split at h
      · rename_i s _ hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
        rw [Upd.mergeSt_holds, Upd.mergeStorageM_holds m s V φ σ]
        simp only [holds]
        refine m.after_congr (fun τ => ?_) _
        rcases hc with ht | rfl
        · exact Upd.holds_total ht m m' φ τ
        · exact Iff.rfl
      · nomatch h
    · split at h
      · split at h
        · rename_i L M hsplit hc
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
          rw [Upd.splitLast_eq U hsplit, Upd.mergeMem_holds hc.1.1 hc.1.2 V m φ σ]
          simp only [holds]
          refine m.after_congr (fun τ => ?_) _
          rcases hc.2 with ht | rfl
          · exact Upd.holds_total ht m m' φ τ
          · exact Iff.rfl
        · nomatch h
      · split at h
        · split at h
          · rename_i L₁ S L₂ hsplit hc
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
            obtain ⟨heq, h₁, h₂⟩ := Upd.splitWrite_eq U hsplit
            rw [heq, Upd.mergeStL_holds h₁ h₂ m φ σ]
            simp only [holds]
            refine m.after_congr (fun τ => ?_) _
            rcases hc with ht | rfl
            · exact Upd.holds_total ht m m' φ τ
            · exact Iff.rfl
          · nomatch h
        · nomatch h

/-- `{U}_m φ` merged with the update at the head of `φ`. -/
def Fml.mergeInto (m : Modality) (U : Upd C) : Fml C → Option (Fml C)
  | .upd m' V φ => (Upd.merge m U m' V).map fun r => .upd r.1 r.2 φ
  | _ => none

theorem Fml.mergeInto_holds {m : Modality} {U : Upd C} {φ ψ : Fml C}
    (h : Fml.mergeInto m U φ = some ψ) (σ : State) : holds σ ψ ↔ holds σ (.upd m U φ) := by
  cases φ with
  | upd m' V χ =>
    simp only [Fml.mergeInto, Option.map_eq_some_iff] at h
    obtain ⟨⟨m'', W⟩, hw, rfl⟩ := h
    exact Upd.merge_holds hw χ σ
  | _ => nomatch h

/-- `sequentialToParallel` on the updates at positions `i` and `i + 1`. -/
def Fml.mergeAt (i : Nat) : Fml C → Option (Fml C) := Fml.atSpine Fml.mergeInto i

theorem Fml.mergeAt_holds {i : Nat} {φ ψ : Fml C} (h : φ.mergeAt i = some ψ) (σ : State) :
    holds σ ψ ↔ holds σ φ :=
  Fml.atSpine_holds (fun h σ => Fml.mergeInto_holds h σ) i φ h σ

/-- The first `n + 1` updates of the spine merged into one, the innermost
pair first: `sequentialToParallel` `n` times, as a chain's last line
shows it.  `none` unless every pair merges, and for `n = 0`, which would
merge nothing. -/
def Fml.mergeSpine : Nat → Fml C → Option (Fml C)
  | 1, .upd m U φ => Fml.mergeInto m U φ
  | n + 2, .upd m U φ => (φ.mergeSpine (n + 1)).bind (Fml.mergeInto m U)
  | _, _ => none

theorem Fml.mergeSpine_holds :
    (n : Nat) → (φ : Fml C) → ∀ {ψ : Fml C}, φ.mergeSpine n = some ψ → ∀ σ, (holds σ ψ ↔ holds σ φ)
  | 0, _, _, h, _ => nomatch h
  | 1, φ, _, h, σ => by
    cases φ with
    | upd m U φ => exact Fml.mergeInto_holds h σ
    | _ => nomatch h
  | n + 2, φ, _, h, σ => by
    cases φ with
    | upd m U φ =>
      simp only [Fml.mergeSpine, Option.bind_eq_some_iff] at h
      obtain ⟨χ, hχ, h⟩ := h
      rw [Fml.mergeInto_holds h σ]
      simp only [holds]
      exact m.after_congr (fun τ => Fml.mergeSpine_holds (n + 1) φ hχ τ) _
    | _ => nomatch h

/-- The `n + 1` updates from position `i` merged into one, the innermost pair
first: `sequentialToParallel` `n` times on a run of the spine, where the
updates above `i` do not merge (a memory write, a parallel update of locals
and the storage).  `none` unless every pair merges, and for `n = 0`. -/
def Fml.mergeRun (i : Nat) : Nat → Fml C → Option (Fml C)
  | 1, φ => φ.mergeAt i
  | n + 2, φ => (φ.mergeAt (i + n + 1)).bind (Fml.mergeRun i (n + 1))
  | _, _ => none

theorem Fml.mergeRun_holds (i : Nat) :
    (n : Nat) → (φ : Fml C) → ∀ {ψ : Fml C}, φ.mergeRun i n = some ψ → ∀ σ, (holds σ ψ ↔ holds σ φ)
  | 0, _, _, h, _ => nomatch h
  | 1, φ, _, h, σ => Fml.mergeAt_holds h σ
  | n + 2, φ, _, h, σ => by
    simp only [Fml.mergeRun, Option.bind_eq_some_iff] at h
    obtain ⟨χ, hχ, h⟩ := h
    rw [Fml.mergeRun_holds i (n + 1) χ h σ, Fml.mergeAt_holds hχ σ]

/-- An update rule (`UpdRuleName.top`) on the update at position `i`:
`applySkip`, `applyOnRigid`, each an equivalence.  `sequentialToParallel`
and `simplifyUpdate` give `none`: those rules are `Fml.mergeAt` (and
`Fml.mergeSpine`), which also merges a storage write and compares no
modality where an update cannot halt, and `Fml.simplifyAt` (and
`Fml.simplifyFreshAt`), which also drops the update it empties, so a link
labelled with one has one spelling. -/
def Fml.updRuleAt : UpdRuleName → Nat → Fml C → Option (Fml C)
  | .sequentialToParallel, _, _ | .simplifyUpdate, _, _ => none
  | .applySkip, i, φ => Fml.atSpine UpdRuleName.applySkip.top i φ
  | .applyOnRigid, i, φ => Fml.atSpine UpdRuleName.applyOnRigid.top i φ

theorem Fml.updRuleAt_holds {r : UpdRuleName} {i : Nat} {φ ψ : Fml C} (h : φ.updRuleAt r i = some ψ)
    (σ : State) : holds σ ψ ↔ holds σ φ := by
  have top : ∀ (r : UpdRuleName), φ.atSpine r.top i = some ψ → (holds σ ψ ↔ holds σ φ) :=
    fun _ h => Fml.atSpine_holds (fun h σ => (UpdRuleName.top_rule h).sound σ) i φ h σ
  cases r with
  | sequentialToParallel | simplifyUpdate => nomatch h
  | applySkip => exact top _ h
  | applyOnRigid => exact top _ h

/-! ## `simplifyUpdate`

`simplifyUpdate` drops an element that cannot halt when the formula under
the update does not read its variable, or a later element writes it again;
an update it empties goes too (`applySkip`), since `dl!{}` has no spelling
for KeY's `skip`.  What the formula reads is asked of the update's own
variables only (`Upd.dropEffectless_holds_of`): any list `F` that holds
every one the formula reads will do, and the fewer it holds the more goes.

* `Fml.simplifyAt` reads the formula's variables, as KeY's
  `\dropEffectlessElementaries` does: `{ x := 10 ‖ y := 1 } y ≐ 1 ⇝ { y := 1 } y ≐ 1`.
* `Fml.simplifyFreshAt` reads only its *fresh* variables (`Fml.freshVars`),
  and counts every user variable the update writes as read.  A postcondition
  `φ : Post C` names no fresh variable, so over `φ` a capture of the rules
  (`se1`, `pv`) goes, and the rewrite computes from `Post.noFresh` rather than
  by `rfl` (`Chain.proveRw`): `{ pv := 10 ‖ acc := alice.account ‖
  storage := S } φ ⇝ { storage := S } φ`.  An overwritten element goes too,
  whatever it writes: `{ acc := alice.account ‖ acc := bob.account } φ`
  keeps the second. -/

/-- The fresh variables a formula mentions (`Var.idx` not `0`), taken apart
connective by connective, so that a postcondition's are asked of it alone
(`Post.freshVars_eq_nil`). -/
def Fml.freshVars : Fml C → List Var
  | .tt => []
  | .eq a b => (a.vars ++ b.vars).filter (·.idx != 0)
  | .defined t => t.vars.filter (·.idx != 0)
  | .not φ | .havoc φ => φ.freshVars
  | .and φ ψ | .imp φ ψ => φ.freshVars ++ ψ.freshVars
  | .upd _ U φ => U.vars.filter (·.idx != 0) ++ φ.freshVars
  | .modal _ P φ => (Prog.vars P).filter (·.idx != 0) ++ φ.freshVars
  | .all x _ φ => [x].filter (·.idx != 0) ++ φ.freshVars

theorem Fml.freshVars_eq : (φ : Fml C) → φ.freshVars = φ.vars.filter (·.idx != 0)
  | .tt | .eq .. | .defined _ => rfl
  | .not φ | .havoc φ => Fml.freshVars_eq φ
  | .and φ ψ | .imp φ ψ => by
    simp only [Fml.freshVars, Fml.vars, List.filter_append, Fml.freshVars_eq φ, Fml.freshVars_eq ψ]
  | .upd _ _ φ | .modal _ _ φ => by
    simp only [Fml.freshVars, Fml.vars, List.filter_append, Fml.freshVars_eq φ]
  | .all x _ φ => by
    simp only [Fml.freshVars, Fml.vars, Fml.freshVars_eq φ, ← List.filter_append, List.singleton_append]

/-- Dropping the effectless elements, reading `F` for what the formula
reads, changes no binding the formula sees, if `F` holds every variable of
the update the formula reads. -/
theorem Upd.dropEffectless_holds_of {F : List Var} {U : Upd C} {φ : Fml C}
    (hF : ∀ x ∈ φ.vars, x ∈ U.targets → x ∈ F) (m : Modality) (σ : State) :
    holds σ (.upd m (U.dropEffectless F) φ) ↔ holds σ (.upd m U φ) :=
  m.after_frame (Upd.dropEffectless_apply F U σ) fun _ _ h =>
    holds_frame φ (fun x hx hG => by
      obtain ⟨hU, hn⟩ := List.mem_filter.1 hG
      simp only [decide_eq_true_eq] at hn
      exact hn (hF x hx hU)) h

/-- `{U}_m φ` with its effectless elements dropped, `F` read for what `φ`
reads, and the update with them if none is left; `none` if none goes. -/
def Fml.simplifyWith (F : List Var) (m : Modality) (U : Upd C) (φ : Fml C) : Option (Fml C) :=
  if (U.dropEffectless F).length < U.length then
    some (match U.dropEffectless F with
      | [] => φ
      | V => .upd m V φ)
  else none

theorem Fml.simplifyWith_holds {F : List Var} {m : Modality} {U : Upd C} {φ ψ : Fml C}
    (hF : ∀ x ∈ φ.vars, x ∈ U.targets → x ∈ F) (h : Fml.simplifyWith F m U φ = some ψ)
    (σ : State) : holds σ ψ ↔ holds σ (.upd m U φ) := by
  unfold Fml.simplifyWith at h
  split at h
  · cases h
    rw [← Upd.dropEffectless_holds_of hF m σ]
    split
    · rename_i hV
      rw [hV]
      exact Iff.rfl
    · exact Iff.rfl
  · nomatch h

/-- `simplifyUpdate` on `{U}_m φ`, reading `φ`'s variables. -/
def Fml.simplifyTop (m : Modality) (U : Upd C) (φ : Fml C) : Option (Fml C) :=
  Fml.simplifyWith φ.vars m U φ

/-- `simplifyUpdate` on `{U}_m φ`, reading `φ`'s fresh variables, and every
user variable `U` writes. -/
def Fml.simplifyFreshTop (m : Modality) (U : Upd C) (φ : Fml C) : Option (Fml C) :=
  Fml.simplifyWith (φ.freshVars ++ U.targets.filter (·.idx == 0)) m U φ

theorem Fml.simplifyFreshTop_holds {m : Modality} {U : Upd C} {φ ψ : Fml C}
    (h : Fml.simplifyFreshTop m U φ = some ψ) (σ : State) : holds σ ψ ↔ holds σ (.upd m U φ) :=
  Fml.simplifyWith_holds (fun x hx hU => by
    rw [List.mem_append, Fml.freshVars_eq, List.mem_filter, List.mem_filter]
    by_cases h0 : x.idx = 0
    · exact .inr ⟨hU, by simp only [h0, BEq.rfl]⟩
    · exact .inl ⟨hx, by simp only [h0, bne_iff_ne, ne_eq, not_false_eq_true]⟩) h σ

/-- `simplifyUpdate` on the update at position `i`, reading the formula's variables. -/
def Fml.simplifyAt (i : Nat) : Fml C → Option (Fml C) := Fml.atSpine Fml.simplifyTop i

/-- `simplifyUpdate` on the update at position `i`, reading the formula's
fresh variables: it computes over a postcondition `φ : Post C`. -/
def Fml.simplifyFreshAt (i : Nat) : Fml C → Option (Fml C) := Fml.atSpine Fml.simplifyFreshTop i

/-! ## An update applied to the body, under the box

`[{U}] φ ⇝ φ[U]` holds where `U` halts because the box does, so these rules
are the box's.  Under the diamond an update that cannot halt reads as under
the box (`Upd.holds_total`), so `applyOnRigidBox` applies there too, and at
a modality variable `m`: it asks `U.total || m = .box`, which a total `U`
decides without `m`, as the merges do.  A storage write is never total (its
path may be missing), and neither is an update whose right-hand side a law
rewrites (`find(save(…), p)` halts where `p` does not resolve), so
`applyStorageBox` and `lawUpd` stay the box's. -/

/-- A line under the box gives it under `m` where `m` is the box or `U`
cannot halt. -/
theorem Fml.upd_of_box {m : Modality} {U : Upd C} {φ : Fml C} (hm : U.total = true ∨ m = .box)
    {σ : State} (h : holds σ (.upd .box U φ)) : holds σ (.upd m U φ) := by
  rcases hm with hU | rfl
  · exact (Upd.holds_total hU .box m φ σ).1 h
  · exact h

/-- `applyOnRigidFormula` under the box (`Proves.applyOnRigidBox`): `[{U}] φ ⇝ φ[U]`
for a first-order `φ`, `U` of locals, or of locals and storage writes under a
`φ` that reads no storage; under any modality where `U` cannot halt. -/
def Fml.applyOnRigidBoxTop (m : Modality) (U : Upd C) (φ : Fml C) : Option (Fml C) :=
  if ((U.total || decide (m = .box)) && (U.envOnly || U.localsOrStorage && φ.stFree) &&
      φ.rigid && φ.sortedFor U) = true then
    some (φ.subst U)
  else none

theorem Fml.applyOnRigidBoxTop_sound {m : Modality} {U : Upd C} {φ ψ : Fml C}
    (h : Fml.applyOnRigidBoxTop m U φ = some ψ) (σ : State) (hψ : holds σ ψ) :
    holds σ (.upd m U φ) := by
  unfold Fml.applyOnRigidBoxTop at h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hm, hU⟩, hr⟩, hs⟩ := hc
    refine Fml.upd_of_box hm ?_
    rcases hU with hU | hU
    · exact Fml.subst_box hU hr hs σ hψ
    · exact Fml.subst_box_st hU.1 hU.2 hs σ hψ
  · nomatch h

/-- `applyOnRigidFormula` on the update at position `i`. -/
def Fml.applyOnRigidBoxAt (i : Nat) : Fml C → Option (Fml C) := Fml.atSpine Fml.applyOnRigidBoxTop i

/-- `applyOnRigidFormula` for a storage write under the box
(`Proves.applyStorageBox`): `[{storage := s}] φ ⇝ φ[s/storage]`.  The box
only: the write halts where its path does not resolve. -/
def Fml.applyStorageBoxTop : Modality → Upd C → Fml C → Option (Fml C)
  | .box, [.storage s], φ => if (φ.rigid && φ.stExplicit) = true then some (φ.withSt s) else none
  | _, _, _ => none

theorem Fml.applyStorageBoxTop_sound {m : Modality} {U : Upd C} {φ ψ : Fml C}
    (h : Fml.applyStorageBoxTop m U φ = some ψ) (σ : State) (hψ : holds σ ψ) :
    holds σ (.upd m U φ) := by
  unfold Fml.applyStorageBoxTop at h
  split at h
  · split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      exact Fml.withSt_box hc.1 hc.2 σ hψ
    · nomatch h
  · nomatch h

/-- `applyOnRigidFormula` on the box storage write at position `i`. -/
def Fml.applyStorageBoxAt (i : Nat) : Fml C → Option (Fml C) := Fml.atSpine Fml.applyStorageBoxTop i

/-! ## Term taclets

A term taclet `r : TermTaclet t t'` (`Calculus/TermTaclets.lean`) rewrites `t` to `t'` where `Fml.rwEq` does: in
every equation, at any depth, never in `defined(…)`, an update's
right-hand side or a program (`Calculus/TermRules.lean` says why).  In the
right-hand sides of a box update it rewrites too when `t'` cannot halt
(`Term.EvalRefines.of_theq`), one update at a time:
`{ … ‖ v := find(save(S, p, 10), p) } ⇝ { … ‖ v := 10 }`. -/

/-- Some equation of the formula changes under the rewrite. -/
def Fml.eqRewrites (q : Term C × Term C) : Fml C → Bool
  | .eq a b => a.rw q != a || b.rw q != b
  | .not φ | .upd _ _ φ | .modal _ _ φ | .havoc φ | .all _ _ φ => φ.eqRewrites q
  | .and φ ψ | .imp φ ψ => φ.eqRewrites q || ψ.eqRewrites q
  | .tt | .defined _ => false

/-- The law `q.1 ≐ q.2` on every equation of the line, if it rewrites one. -/
def Fml.rwLaw (q : Term C × Term C) (φ : Fml C) : Option (Fml C) :=
  if φ.eqRewrites q = true then some (φ.rwEq q) else none

theorem Fml.rwLaw_holds {q : Term C × Term C} (h : Term.Theq q.1 q.2) {φ ψ : Fml C}
    (hl : φ.rwLaw q = some ψ) (σ : State) : holds σ ψ ↔ holds σ φ := by
  unfold Fml.rwLaw at hl
  split at hl
  · cases hl; exact Fml.rwEq_holds h φ σ
  · nomatch hl

-- Here rather than on `UpdElem` (`Update.lean`) to spare a low edit; it moves
-- to that type's `deriving` clause at the next batched edit of `Update.lean`.
deriving instance DecidableEq for UpdElem

/-- The law on the right-hand sides of `[{U}] φ` (`Proves.updRw`), if it
rewrites one.  The box only: the rewritten update may run where `U` halts
(`find(save(S, p, 10), p) ⇝ 10`), which the diamond would count against. -/
def Fml.rwUpdTop (q : Term C × Term C) : Modality → Upd C → Fml C → Option (Fml C)
  | .box, U, φ => if (U.rw q != U) = true then some (.upd .box (U.rw q) φ) else none
  | .diamond, _, _ => none

theorem Fml.rwUpdTop_sound {q : Term C × Term C} (hq : Term.EvalRefines q.1 q.2) {m : Modality}
    {U : Upd C} {φ ψ : Fml C} (h : Fml.rwUpdTop q m U φ = some ψ) (σ : State)
    (hψ : holds σ ψ) : holds σ (.upd m U φ) := by
  cases m with
  | diamond => nomatch h
  | box =>
    simp only [Fml.rwUpdTop] at h
    split at h
    · cases h; exact Upd.rw_box hq (fun _ h => h) σ hψ
    · nomatch h

/-- The law on the right-hand sides of the box update at position `i`. -/
def Fml.rwUpdAt (q : Term C × Term C) (i : Nat) : Fml C → Option (Fml C) :=
  Fml.atSpine (Fml.rwUpdTop q) i

/-! ### A law in an update's right-hand side, under any modality

`{ storage := save(storage, p, 10) ‖ x := find(save(storage, p, 10), p) }`
halts exactly where `save(storage, p, 10)` does, and so does
`{ storage := save(storage, p, 10) ‖ x := 10 }`: the read returns wherever the
write it reads back does (`State.findStorage_saveStorage_same`), and the
write is an element of the update.  Two updates that halt in the same states
and return the same state are one update to either modality
(`Upd.rw_holds`), so the law rewrites `x` under `m` as well as under the box.
`Upd.covers` is the syntactic side of it: the law's left side reads back a
storage write that is an element of the update. -/

/-- Where a run of an update returns, every element wrote: its right-hand
side returned. -/
theorem Upd.foldl_ok_elem (σ₀ : State) : (U : Upd C) → ∀ {ρ₀ τ : State},
    U.foldlM (fun ρ e => e.write σ₀ ρ) ρ₀ = .ok τ → ∀ {e : UpdElem C}, e ∈ U →
      ∃ ρ ρ', e.write σ₀ ρ = .ok ρ'
  | [], _, _, _, _, he => nomatch he
  | d :: U, ρ₀, τ, h, e, he => by
    simp only [List.foldlM_cons] at h
    obtain ⟨ρ₁, h₁, h⟩ := bind_ok_inv h
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨ρ₀, ρ₁, h₁⟩
    · exact Upd.foldl_ok_elem σ₀ U h he

theorem Upd.apply_ok_elem {U : Upd C} {σ τ : State} (h : U.apply σ = .ok τ) {e : UpdElem C}
    (he : e ∈ U) : ∃ ρ ρ', e.write σ ρ = .ok ρ' :=
  Upd.foldl_ok_elem σ U h he

/-- A storage write that is an element of an update that returns, returns. -/
theorem Upd.storage_eval_of_apply {U : Upd C} {σ τ : State} (h : U.apply σ = .ok τ) {s : STerm C}
    (he : UpdElem.storage s ∈ U) : ∃ τ', s.eval σ = .ok τ' := by
  obtain ⟨ρ, ρ', hw⟩ := Upd.apply_ok_elem h he
  rw [UpdElem.storage_write] at hw
  obtain ⟨τ', hs, -⟩ := bind_ok_inv hw
  exact ⟨τ', hs⟩

/-- `find(s, p)` read in `σ`: `s`, then `p`, then the slot. -/
theorem Term.find_eval (σ : State) (s : STerm C) (p : PTerm C) :
    (Term.find s p).eval σ = (do
      let τ ← s.eval σ
      let (r, segs) ← p.eval σ
      (← τ.findStorage r segs).asValue) := rfl

/-- `delAt(s, p)` read in `σ`: the slot read, then written to its default. -/
theorem STerm.delAt_eval (σ : State) (s : STerm C) (p : PTerm C) :
    (STerm.delAt s p).eval σ = (do
      let τ ← s.eval σ
      let (r, segs) ← p.eval σ
      let cur ← τ.findStorage r segs
      τ.saveStorage r segs cur.defaultOf) := rfl

/-- `save(s, p, v)` returned: the storage it returned reads `v` at `p`. -/
theorem STerm.save_lit_eval {s : STerm C} {p : PTerm C} {v : Value} {σ τ : State}
    (h : (STerm.save s p (.val (.lit v))).eval σ = .ok τ) :
    ∃ r segs, p.eval σ = .ok (r, segs) ∧ τ.findStorage r segs = .ok v.toSVal := by
  simp only [tm_eval] at h
  obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hsv
  subst hsv
  obtain ⟨τs, -, h⟩ := bind_ok_inv h
  obtain ⟨⟨r, segs⟩, hp, h⟩ := bind_ok_inv h
  rw [State.writeStorage_toSVal] at h
  exact ⟨r, segs, hp, State.findStorage_saveStorage_same h⟩

/-- `f` of some path on the way down to `t`'s root through members only. -/
def Tm.fieldsBelowAny (f : PTerm C → Bool) : Tm C u → Bool
  | .app1 (.field _) q => f q || q.fieldsBelowAny f
  | _ => false

/-- `q` is `p` with one or more member selectors after it: a read below `p`
that no index check can halt. -/
def PTerm.fieldsBelow (q p : PTerm C) : Bool := q.fieldsBelowAny (· == p)

/-- A member path is a field segment or more. -/
def Seg.isField : Seg → Bool
  | .field _ => true
  | .at _ => false

/-- The closed member path `q` is (`segs?`, members only): a path that
resolves in every state, to its segments. -/
def PTerm.fields? (q : PTerm C) : Option (List Seg) :=
  match q.segs? with
  | some l => if l.all Seg.isField then some l else none
  | none => none

/-- `q.fieldsBelow p` in a run: `q` resolves wherever `p` does, to `p`'s
segments and some members. -/
theorem PTerm.fieldsBelow_eval {p : PTerm C} {σ : State} {r : Name} {segs : List Seg}
    (hp : p.eval σ = .ok (r, segs)) :
    (q : PTerm C) → q.fieldsBelow p = true →
      ∃ tail, tail ≠ [] ∧ tail.all Seg.isField = true ∧ q.eval σ = .ok (r, segs ++ tail)
  | .app1 (.field f) q, h => by
    simp only [PTerm.fieldsBelow, Tm.fieldsBelowAny, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · refine ⟨[.field f], List.cons_ne_nil _ _, rfl, ?_⟩
      rw [Tm.app1_eval, hp]
      rfl
    · obtain ⟨tail, hne, hf, hq⟩ := PTerm.fieldsBelow_eval hp q h
      refine ⟨tail ++ [.field f], by simp, ?_, ?_⟩
      · simp only [List.all_append, hf, List.all_cons, List.all_nil, Seg.isField, Bool.and_self]
      · rw [Tm.app1_eval, hq]
        show Except.ok (r, (segs ++ tail) ++ [Seg.field f]) = _
        rw [List.append_assoc]
  | .pvP _, h | .app0 (.root _), h | .app1 .next _, h | .app2 .at _ _, h | .app2 .nextIn _ _, h
  | .app3 .atIn _ _ _, h => nomatch h

/-- `q` is `p`, or goes on below it through members: a read at or below `p`
that no index check can halt. -/
def PTerm.atOrBelow (q p : PTerm C) : Bool := q == p || q.fieldsBelow p

theorem PTerm.atOrBelow_eval {p : PTerm C} {σ : State} {r : Name} {segs : List Seg}
    (hp : p.eval σ = .ok (r, segs)) (q : PTerm C) (h : q.atOrBelow p = true) :
    ∃ tail, tail.all Seg.isField = true ∧ q.eval σ = .ok (r, segs ++ tail) := by
  unfold PTerm.atOrBelow at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h
  · exact ⟨[], rfl, by rw [List.append_nil]; exact hp⟩
  · obtain ⟨tail, -, hf, hq⟩ := PTerm.fieldsBelow_eval hp q h
    exact ⟨tail, hf, hq⟩

/-- A closed member path resolves in every state, to its segments: the root
first. -/
theorem PTerm.fields?_eval (σ : State) : (q : PTerm C) → {l : List Seg} → q.fields? = some l →
    ∃ r segs, l = .field r :: segs ∧ q.eval σ = .ok (r, segs)
  | .app0 (.root r), l, h => by
    simp only [PTerm.fields?, Tm.segs?, List.all_cons, List.all_nil, Seg.isField, Bool.and_self,
      ↓reduceIte, Option.some.injEq] at h
    exact ⟨r, [], h.symm, rfl⟩
  | .app1 (.field f) q, l, h => by
    simp only [PTerm.fields?, Tm.segs?] at h
    split at h
    · rename_i l' hl'
      simp only [Option.map_eq_some_iff] at hl'
      obtain ⟨l'', hl'', rfl⟩ := hl'
      split at h
      · rename_i hall
        simp only [Option.some.injEq] at h
        subst h
        simp only [List.all_append, List.all_cons, List.all_nil, Seg.isField, Bool.and_true] at hall
        obtain ⟨r, segs, rfl, hq⟩ := PTerm.fields?_eval σ q (l := l'') (by
          simp only [PTerm.fields?, hl'', hall, ↓reduceIte])
        refine ⟨r, segs ++ [.field f], rfl, ?_⟩
        rw [Tm.app1_eval, hq]
        rfl
      · nomatch h
    · nomatch h
  | .pvP _, _, h | .app1 .next _, _, h | .app2 .nextIn _ _, _, h => nomatch h
  | .app2 .at q i, _, h | .app3 .atIn _ q i, _, h => by
    simp only [PTerm.fields?, Tm.segs?] at h
    split at h
    · rename_i l' hl'
      split at hl'
      · rename_i k hk
        simp only [Option.map_eq_some_iff] at hl'
        obtain ⟨l'', -, rfl⟩ := hl'
        simp only [List.all_append, List.all_cons, List.all_nil, Seg.isField, Bool.false_and,
          Bool.and_false, Bool.false_eq_true, ↓reduceIte] at h
        nomatch h
      · nomatch hl'
    · nomatch h

/-- The Theory's `diverges` gives the interpreter's `Diverge`. -/
theorem Diverge_of_diverges : (a b : List Seg) → Theory.StValue.diverges a b = true → Close.Diverge a b
  | [], _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | x :: p, y :: q, h => by
    simp only [Theory.StValue.diverges] at h
    split at h
    · exact Or.inr (Diverge_of_diverges p q h)
    · exact Or.inl ‹_›

/-- Two closed member paths that leave each other resolve to a root apart or
to segments that do (`findStorage_saveStorage_apart`'s premise). -/
theorem PTerm.diverges_eval {p q : PTerm C} {σ : State} {r r' : Name} {segs segs' : List Seg}
    (hd : p.diverges q = true) (hp : (PTerm.fields? p).isSome = true)
    (hq : (PTerm.fields? q).isSome = true)
    (ep : p.eval σ = .ok (r, segs)) (eq : q.eval σ = .ok (r', segs')) :
    r' ≠ r ∨ Close.Diverge segs segs' := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hp
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hq
  obtain ⟨r₁, s₁, rfl, ep'⟩ := PTerm.fields?_eval σ p ha
  obtain ⟨r₂, s₂, rfl, eq'⟩ := PTerm.fields?_eval σ q hb
  have hs : p.segs? = some (.field r₁ :: s₁) := by
    unfold PTerm.fields? at ha; split at ha
    · rename_i hl; split at ha
      · cases ha; exact hl
      · nomatch ha
    · nomatch ha
  have hs' : q.segs? = some (.field r₂ :: s₂) := by
    unfold PTerm.fields? at hb; split at hb
    · rename_i hl; split at hb
      · cases hb; exact hl
      · nomatch hb
    · nomatch hb
  rw [ep'] at ep
  rw [eq'] at eq
  simp only [Except.ok.injEq, Prod.mk.injEq] at ep eq
  obtain ⟨rfl, rfl⟩ := ep
  obtain ⟨rfl, rfl⟩ := eq
  have hd' := PTerm.diverges_denote hd σ
  rw [PTerm.denote_of_segs? σ p hs, PTerm.denote_of_segs? σ q hs'] at hd'
  rcases Diverge_of_diverges _ _ hd' with h | h
  · exact Or.inl fun e => h (by rw [e])
  · exact Or.inr h

/-- A reset struct keeps its members, each reset: a word read below the node
reads a word after the reset. -/
theorem SVal.find_defaultOf_prim : (tail : List Seg) → tail.all Seg.isField = true → (v : SVal) →
    ∀ {x : PrimVal}, v.find tail = .ok (.prim x) → ∃ y, v.defaultOf.find tail = .ok (.prim y)
  | [], _, v, x, h => by
    rw [SVal.find_nil] at h
    cases h
    cases x <;> exact ⟨_, rfl⟩
  | .field n :: rest, hf, v, x, h => by
    simp only [List.all_cons, Seg.isField, Bool.true_and] at hf
    cases v with
    | prim _ => nomatch h
    | map _ _ => nomatch h
    | struct fields =>
      simp only [SVal.find] at h
      split at h
      · rename_i u hu
        obtain ⟨y, hy⟩ := SVal.find_defaultOf_prim rest hf u h
        refine ⟨y, ?_⟩
        simp only [SVal.defaultOf, SVal.find, lookupBy_defaultOfFields, hu, Option.map_some]
        exact hy
      · nomatch h
    | array elems sh fx =>
      by_cases hn : n = "length"
      · subst hn
        cases fx with
        | true => nomatch h
        | false =>
          cases rest with
          | nil =>
            exact ⟨.int 0, rfl⟩
          | cons _ _ => nomatch h
      · exact absurd h (by cases rest <;> simp [SVal.find])
  | .at _ :: _, hf, _, _, _ => by
    simp only [List.all_cons, Seg.isField, Bool.false_and, Bool.false_eq_true] at hf

/-- A write that returned saved, with the value it wrote laid over the old one
where it is not a word. -/
theorem State.writeStorage_ok {σ τ : State} {r : Name} {segs : List Seg} {v : SVal}
    (h : σ.writeStorage r segs v = .ok τ) : ∃ x, σ.saveStorage r segs x = .ok τ := by
  cases v with
  | prim _ => exact ⟨_, h⟩
  | struct _ =>
    simp only [State.writeStorage] at h
    obtain ⟨cur, -, h⟩ := bind_ok_inv h
    exact ⟨_, h⟩
  | array _ _ _ =>
    simp only [State.writeStorage] at h
    obtain ⟨cur, -, h⟩ := bind_ok_inv h
    exact ⟨_, h⟩
  | map _ _ =>
    simp only [State.writeStorage] at h
    obtain ⟨cur, -, h⟩ := bind_ok_inv h
    exact ⟨_, h⟩

theorem STerm.save_eval (σ : State) (s : STerm C) (p : PTerm C) (v : SValT C) :
    (STerm.save s p v).eval σ = (do
      let sv ← v.eval σ
      let τ ← s.eval σ
      let (r, segs) ← p.eval σ
      τ.writeStorage r segs sv) := rfl

/-- The word `s` reads at a closed member path `q`, read off its writes at
closed member paths (`Tm.findLitBy` on those): a run of `s` reads it there
(`STerm.findLitF?_eval`), so a read through a delete of `s` below `q` returns. -/
def Tm.findLitFBy (eq div : PTerm C → Bool) : Tm C u → Option Value
  | .app3 .save s p v =>
    if (PTerm.fields? p).isSome then
      if eq p then SValT.lit? v else if div p then s.findLitFBy eq div else none
    else none
  | _ => none

@[inherit_doc Tm.findLitFBy]
def STerm.findLitF? (s : STerm C) (q : PTerm C) : Option Value :=
  if (PTerm.fields? q).isSome then s.findLitFBy (· == q) (·.diverges q) else none

/-- The word read off the writes is the word a run reads. -/
theorem Tm.findLitFBy_eval {q : PTerm C} (hq : (PTerm.fields? q).isSome = true) {σ : State} {r : Name}
    {sq : List Seg} (eq : q.eval σ = .ok (r, sq)) :
    (s : STerm C) → {w : Value} → s.findLitFBy (· == q) (·.diverges q) = some w →
      ∀ {τ : State}, s.eval σ = .ok τ → τ.findStorage r sq = .ok w.toSVal
  | .app3 .save s p v, w, h, τ, hs => by
    simp only [Tm.findLitFBy] at h
    split at h
    · rename_i hpf
      split at h
      · rename_i hpq
        simp only [beq_iff_eq] at hpq
        subst hpq
        obtain rfl := SValT.lit?_eq v h
        obtain ⟨r', segs', ep, hf⟩ := STerm.save_lit_eval hs
        rw [ep] at eq
        simp only [Except.ok.injEq, Prod.mk.injEq] at eq
        obtain ⟨rfl, rfl⟩ := eq
        exact hf
      · split at h
        · rename_i hd
          rw [STerm.save_eval] at hs
          obtain ⟨sv, -, hs⟩ := bind_ok_inv hs
          obtain ⟨τs, hτs, hs⟩ := bind_ok_inv hs
          obtain ⟨⟨r'', segs''⟩, ep, hs⟩ := bind_ok_inv hs
          change τs.writeStorage r'' segs'' sv = .ok τ at hs
          obtain ⟨x, hs⟩ := State.writeStorage_ok hs
          rw [Close.findStorage_saveStorage_apart hs (PTerm.diverges_eval hd hpf hq ep eq)]
          exact Tm.findLitFBy_eval hq eq s h hτs
        · nomatch h
    · nomatch h
  | .pvS _, _, h, _, _ | .app0 .storage, _, h, _, _ | .app1 (.select _) _, _, h, _, _
  | .app2 .delAt _ _, _, h, _, _ | .app2 (.pushSlot _) _ _, _, h, _, _ | .app2 .pop _ _, _, h, _, _
  | .app2 .shrink _ _, _, h, _, _ | .app2 (.extend _) _ _, _, h, _, _
  | .app3 .push _ _ _, _, h, _, _ => nomatch h

theorem STerm.findLitF?_eval {s : STerm C} {q : PTerm C} {w : Value} (h : s.findLitF? q = some w)
    {σ τ : State} (hs : s.eval σ = .ok τ) {r : Name} {sq : List Seg} (eq : q.eval σ = .ok (r, sq)) :
    τ.findStorage r sq = .ok w.toSVal := by
  unfold STerm.findLitF? at h
  split at h
  · exact Tm.findLitFBy_eval ‹_› eq s h hs
  · nomatch h

/-- A word at or below a deleted node, in a run: the delete returned, so the
node was read and reset; the storage before it reads the word at the member path
(`STerm.findLitF?_eval`), so the reset node, which keeps its members
(`SVal.find_defaultOf_prim`), reads a word there. -/
theorem Upd.delAtBelow_eval {s : STerm C} {p q : PTerm C} {w : Value} (hb : q.atOrBelow p = true)
    (hw : STerm.findLitF? s q = some w) {σ τ'' : State} (hd : (STerm.delAt s p).eval σ = .ok τ'') :
    ∃ y, (Term.find (.delAt s p) q).eval σ = .ok y := by
  have hd' := hd
  rw [STerm.delAt_eval] at hd'
  obtain ⟨τ', hs, hd'⟩ := bind_ok_inv hd'
  obtain ⟨rs, hp, hd'⟩ := bind_ok_inv hd'
  obtain ⟨r, segs⟩ := rs
  obtain ⟨cur, hcur, hsave⟩ := bind_ok_inv hd'
  obtain ⟨tail, hfields, hq⟩ := PTerm.atOrBelow_eval hp q hb
  have hread : τ'.findStorage r (segs ++ tail) = Except.ok (Value.toSVal w) :=
    STerm.findLitF?_eval hw hs hq
  rw [State.findStorage_append, hcur] at hread
  simp only [bind, Except.bind] at hread
  obtain ⟨x, hx⟩ : ∃ x : PrimVal, Value.toSVal w = SVal.prim x := by cases w <;> exact ⟨_, rfl⟩
  rw [hx] at hread
  obtain ⟨y, hy⟩ := SVal.find_defaultOf_prim tail hfields cur hread
  have hfind : τ''.findStorage r (segs ++ tail) = Except.ok (SVal.prim y) := by
    rw [State.findStorage_append, State.findStorage_saveStorage_same hsave]
    exact hy
  cases y with
  | int n =>
    refine ⟨.int n, ?_⟩
    rw [Term.find_eval, hd, hq]
    simp only [bind, Except.bind, hfind]
    rfl
  | bool b =>
    refine ⟨.bool b, ?_⟩
    rw [Term.find_eval, hd, hq]
    simp only [bind, Except.bind, hfind]
    rfl

/-! ## Reading member-wise

solkey reads a path from its head (`findMemberCons`, `selectOnSaveMember`,
`selectOnDelAtMember`): `find(save(storage, alice.age, 42), alice.age)`
becomes `find(select(save(storage, alice.age, 42), alice), age)`, then
`find(save(select(storage, alice), age, 42), age)`, then `42`.  In the
interpreter `select(s, r)` is the state `s` leaves with the struct at its
root `r` for its storage (`State.selectRoot`), so a storage term read
member-wise runs as the term it reads, in that frame (`STerm.base?`,
`STerm.base_eval`), and a read of it returns exactly where the read of the
base does (`Term.base_eval`).  Two member-wise forms of one read have one
base, so a law between them rewrites an update's right-hand side under any
modality (`LineRw.lawUpdEq`); the read of a write, member-wise, is covered as
the write it reads back is (`Upd.covers`). -/

/-- `select(s, r)`'s run on the state `s` leaves: that state with the struct
at the root `r` for its storage (`Op1.eval`). -/
def State.selectRoot (r : Name) (τ : State) : Res State := do
  match ← τ.findStorage r [] with
  | .struct fields => pure { τ with storage := fields }
  | .prim _ | .array .. | .map .. => .error .stuck

theorem STerm.select_eval (σ : State) (s : STerm C) (r : Name) :
    (STerm.select s r).eval σ = (s.eval σ >>= State.selectRoot r) := rfl

/-- The frame `F`: the state with the struct at `r₁.r₂…` for its storage. -/
def State.frameOf : List Name → State → Res State
  | [], τ => .ok τ
  | r :: F, τ => State.selectRoot r τ >>= State.frameOf F

theorem State.frameOf_append (F G : List Name) (τ : State) :
    State.frameOf (F ++ G) τ = (State.frameOf F τ >>= State.frameOf G) := by
  induction F generalizing τ with
  | nil => rfl
  | cons r F ih =>
    simp only [List.cons_append, State.frameOf]
    cases State.selectRoot r τ with
    | error e => rfl
    | ok τ' => exact ih τ'

/-- In the frame at `r`, a read at `g.segs` is the read at `r.g.segs` outside it. -/
theorem State.findStorage_selectRoot {r : Name} {τ τ' : State} (h : State.selectRoot r τ = .ok τ')
    (g : Name) (segs : List Seg) : τ'.findStorage g segs = τ.findStorage r (.field g :: segs) := by
  unfold State.selectRoot at h
  simp only [State.findStorage] at h
  cases hv : lookupBy r τ.storage with
  | none =>
    rw [hv] at h
    simp [bind, Except.bind] at h
  | some V =>
    rw [hv] at h
    cases V with
    | struct fields =>
      simp only [SVal.find, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [State.findStorage, hv, SVal.find]
    | prim _ | array _ _ _ | map _ _ => simp [SVal.find, bind, Except.bind] at h

/-- In the frame at `r`, a write at `g.rest` is the write at `r.g.rest` outside
it, the frame taken after: the two runs end alike. -/
theorem State.saveStorage_selectRoot (r : Name) (τ : State) (g : Name) (rest : List Seg) (new : SVal) :
    (τ.saveStorage r (.field g :: rest) new >>= State.selectRoot r) =
      (State.selectRoot r τ >>= fun τ' => τ'.saveStorage g rest new) := by
  unfold State.selectRoot State.saveStorage
  simp only [State.findStorage]
  cases hv : lookupBy r τ.storage with
  | none => simp [bind, Except.bind]
  | some V =>
    cases V with
    | prim _ | array _ _ _ | map _ _ => simp [SVal.save, SVal.find, bind, Except.bind]
    | struct fields =>
      cases hg : lookupBy g fields with
      | none => simp [SVal.save, SVal.find, hg, bind, Except.bind, pure, Except.pure]
      | some old =>
        cases hs : old.save rest new with
        | error e => simp [SVal.save, SVal.find, hg, hs, bind, Except.bind, pure, Except.pure]
        | ok upd =>
          simp [SVal.save, SVal.find, hg, hs, bind, Except.bind, pure, Except.pure, lookupBy_setBy_self]

/-- Where a run returns, the other returns the same: the two agree but for
how they halt. -/
def Res.OkEq {α : Type} (a b : Res α) : Prop := ∀ x, a = .ok x ↔ b = .ok x

theorem Res.OkEq.refl {α : Type} (a : Res α) : Res.OkEq a a := fun _ => Iff.rfl
theorem Res.OkEq.symm {α : Type} {a b : Res α} (h : Res.OkEq a b) : Res.OkEq b a :=
  fun x => (h x).symm
theorem Res.OkEq.trans {α : Type} {a b c : Res α} (h : Res.OkEq a b) (h' : Res.OkEq b c) :
    Res.OkEq a c := fun x => (h x).trans (h' x)
theorem Res.OkEq.of_eq {α : Type} {a b : Res α} (h : a = b) : Res.OkEq a b := h ▸ Res.OkEq.refl a
theorem Res.OkEq.le {α : Type} {a b : Res α} (h : Res.OkEq a b) : Res.Le a b := fun x => (h x).1
theorem Res.OkEq.ge {α : Type} {a b : Res α} (h : Res.OkEq a b) : Res.Le b a := fun x => (h x).2

theorem Res.OkEq.bind {α β : Type} {a a' : Res α} {f f' : α → Res β} (ha : Res.OkEq a a')
    (hf : ∀ x, Res.OkEq (f x) (f' x)) : Res.OkEq (a >>= f) (a' >>= f') := fun y => by
  constructor
  · intro h
    obtain ⟨x, hx, hy⟩ := bind_ok_inv h
    rw [(ha x).1 hx]
    exact (hf x y).1 hy
  · intro h
    obtain ⟨x, hx, hy⟩ := bind_ok_inv h
    rw [(ha x).2 hx]
    exact (hf x y).2 hy

/-- In the frame at `r`, a write of a value at `g.rest` is the write at
`r.g.rest` outside it, the frame taken after. -/
theorem State.writeStorage_selectRoot (r : Name) (τ : State) (g : Name) (rest : List Seg) (new : SVal) :
    Res.OkEq (τ.writeStorage r (.field g :: rest) new >>= State.selectRoot r)
      (State.selectRoot r τ >>= fun τ' => τ'.writeStorage g rest new) := by
  have key : ∀ x : SVal, Res.OkEq
      ((τ.findStorage r (.field g :: rest) >>= fun cur =>
        τ.saveStorage r (.field g :: rest) (cur.overlay x)) >>= State.selectRoot r)
      (State.selectRoot r τ >>= fun τ' => τ'.findStorage g rest >>= fun cur =>
        τ'.saveStorage g rest (cur.overlay x)) := by
    intro x
    cases hs : State.selectRoot r τ with
    | ok τ' =>
      simp only [bind, Except.bind]
      rw [State.findStorage_selectRoot hs]
      cases τ.findStorage r (.field g :: rest) with
      | error e => exact Res.OkEq.refl _
      | ok cur =>
        have e := State.saveStorage_selectRoot r τ g rest (cur.overlay x)
        rw [hs] at e
        simp only [bind, Except.bind] at e
        exact Res.OkEq.of_eq e
    | error e =>
      -- the root is no struct: the write outside halts too
      intro y
      constructor
      · intro h
        obtain ⟨τ₁, h₁, h₂⟩ := bind_ok_inv h
        obtain ⟨cur, -, h₁⟩ := bind_ok_inv h₁
        have e' := State.saveStorage_selectRoot r τ g rest (cur.overlay x)
        rw [hs, h₁] at e'
        simp only [bind, Except.bind] at e'
        rw [e'] at h₂
        cases h₂
      · intro h
        simp [bind, Except.bind] at h
  cases new with
  | prim _ => exact Res.OkEq.of_eq (State.saveStorage_selectRoot r τ g rest _)
  | struct fs => exact key (.struct fs)
  | array a b c => exact key (.array a b c)
  | map a b => exact key (.map a b)

/-- `delete` at `g.segs`: the slot read, then written to its default. -/
def _root_.Solidity.Semantics.State.delAtAt (τ : State) (g : Name) (segs : List Seg) : Res State :=
  τ.findStorage g segs >>= fun cur => τ.saveStorage g segs cur.defaultOf

theorem STerm.delAt_eval' (σ : State) (s : STerm C) (p : PTerm C) :
    (STerm.delAt s p).eval σ = (do
      let τ ← s.eval σ
      let (r, segs) ← p.eval σ
      τ.delAtAt r segs) := rfl

/-- Two paths whose shapes diverge, when both resolve, have different roots
or divergent tails.  Unlike `PTerm.diverges_eval`, the paths may contain
index checks. -/
theorem PTerm.diverges_eval_any {p q : PTerm C} {σ : State} {r r' : Name}
    {segs segs' : List Seg} (hd : p.diverges q = true)
    (hp : p.eval σ = .ok (r, segs)) (hq : q.eval σ = .ok (r', segs')) :
    r' ≠ r ∨ Close.Diverge segs segs' := by
  have hd' := PTerm.diverges_denote hd σ
  rw [PTerm.denote_eval hp, PTerm.denote_eval hq] at hd'
  rcases Diverge_of_diverges _ _ hd' with h | h
  · exact Or.inl fun e => h (by rw [e])
  · exact Or.inr h

/-- Paths equal with their explicit checks erased resolve alike whenever both
resolve. -/
theorem PTerm.sameSegs_eval {p q : PTerm C} {σ : State} {r r' : Name}
    {segs segs' : List Seg} (heq : p.sameSegs q = true)
    (hp : p.eval σ = .ok (r, segs)) (hq : q.eval σ = .ok (r', segs')) :
    r = r' ∧ segs = segs' := by
  have heq' := PTerm.sameSegs_denote σ p q heq
  rw [PTerm.denote_eval hp, PTerm.denote_eval hq] at heq'
  exact ⟨Seg.field.inj (List.cons.inj heq').1, (List.cons.inj heq').2⟩

/-- A storage word and its default either both fail to be words, or read as
the value and its primitive default. -/
theorem SVal.defaultOf_asValue_primDefault (v : SVal) :
    v.defaultOf.asValue = (do pure (Theory.StValue.primDefault (← v.asValue))) := by
  cases v with
  | prim p => cases p <;> rfl
  | struct _ | map _ _ => rfl
  | array _ _ fx => cases fx <;> rfl

/-- A write below an array keeps its length. -/
theorem Close.arrLen_save_cons {a : Seg} {rest : List Seg} {old new upd : SVal}
    (h : old.save (a :: rest) new = .ok upd) : Close.arrLen upd = Close.arrLen old := by
  cases old with
  | prim _ => cases a <;> simp [SVal.save] at h
  | struct fields =>
    cases a with
    | «at» _ => simp [SVal.save] at h
    | field n =>
      simp only [SVal.save] at h
      split at h
      · obtain ⟨u, _, h⟩ := bind_ok_inv h
        cases h
        rfl
      · simp at h
  | array elems shadow fx =>
    cases a with
    | field _ => simp [SVal.save] at h
    | «at» i =>
      simp only [SVal.save] at h
      split at h
      · obtain ⟨u, _, h⟩ := bind_ok_inv h
        cases h
        have hlen : (((elems ++ shadow).set i.toNat u).take elems.length).length =
            elems.length := by simp
        simp only [Close.arrLen, hlen]
      · simp at h
  | map entries dflt =>
    cases a with
    | field _ => simp [SVal.save] at h
    | «at» i =>
      simp only [SVal.save] at h
      split at h <;> (obtain ⟨u, _, h⟩ := bind_ok_inv h; cases h; rfl)

/-- Reading an array length above or apart from a write gives its old
length. -/
theorem Close.find_save_arrLen : ∀ {p q : List Seg} {old new upd : SVal},
    old.save p new = .ok upd → ¬ Close.Prefix p q →
      (upd.find q >>= Close.arrLen) = (old.find q >>= Close.arrLen)
  | [], _, _, _, _, _, hq => (hq trivial).elim
  | _ :: _, [], _, _, _, hs, _ => by
      simp only [SVal.find_nil, bind, Except.bind]
      exact Close.arrLen_save_cons hs
  | a :: p, b :: q, old, upd, new, hs, hq => by
      by_cases hab : a = b
      · subst hab
        have hq' : ¬ Close.Prefix p q := fun h => hq ⟨rfl, h⟩
        obtain ⟨c, u, hu, hf⟩ := Close.save_cons_find hs
        rw [(hf q).1, (hf q).2]
        exact Close.find_save_arrLen hu hq'
      · rw [Close.find_save_diverge (show Close.Diverge (a :: p) (b :: q) from Or.inl hab) hs]

/-- `find_save_arrLen` at a root of the storage. -/
theorem Close.arrayLen_saveStorage_frame {σ τ : State} {r r' : Name} {p q : List Seg}
    {v : SVal} (h : σ.saveStorage r p v = .ok τ)
    (hq : r' ≠ r ∨ ¬ Close.Prefix p q) : arrayLen τ r' q = arrayLen σ r' q := by
  rw [Close.arrayLen_eq, Close.arrayLen_eq]
  unfold State.saveStorage at h
  split at h
  · rename_i old hl
    obtain ⟨u, hu, h⟩ := bind_ok_inv h
    cases h
    by_cases hr : r' = r
    · subst hr
      simp only [State.findStorage, lookupBy_setBy_self, hl]
      exact Close.find_save_arrLen hu (hq.resolve_left (· rfl))
    · simp only [State.findStorage, lookupBy_setBy_ne hr]
  · simp at h

/-- A divergent path is not a prefix of the path it diverges from. -/
theorem Close.Diverge.not_prefix : ∀ {p q : List Seg}, Close.Diverge p q → ¬ Close.Prefix p q
  | _ :: _, _ :: _, h => fun hp => by
      rcases h with h | h
      · exact h hp.1
      · exact h.not_prefix hp.2

/-- A prefix remains a prefix when the path on the right is extended. -/
theorem Close.Prefix.right_append : ∀ {p q : List Seg}, Close.Prefix p q → (tail : List Seg) →
    Close.Prefix p (q ++ tail)
  | [], _, _, _ => trivial
  | _ :: _, _ :: _, h, tail => ⟨h.1, h.2.right_append tail⟩

/-- `q` leaving `p.length`, when both paths resolve, says that the write at
`q` is at another root or is not above `p`. -/
theorem PTerm.divergesLen_eval {q p : PTerm C} {σ : State} {r r' : Name}
    {segs segs' : List Seg} (hd : q.divergesLen p = true)
    (hq : q.eval σ = .ok (r, segs)) (hp : p.eval σ = .ok (r', segs')) :
    r' ≠ r ∨ ¬ Close.Prefix segs segs' := by
  have hd' := PTerm.divergesLen_denote hd σ
  rw [PTerm.denote_eval hq, PTerm.denote_eval hp] at hd'
  rcases Diverge_of_diverges _ _ hd' with h | h
  · exact Or.inl fun e => h (by rw [e])
  · exact Or.inr fun hp' => h.not_prefix (hp'.right_append [.field "length"])

theorem Term.len_eval (σ : State) (s : STerm C) (p : PTerm C) :
    (Term.len s p).eval σ = (do
      let τ ← s.eval σ
      let (r, segs) ← p.eval σ
      arrayLen τ r segs) := rfl

/-- A length read away from a returned write evaluates exactly as the read
before the write. -/
theorem Term.len_save_frame_eval {s : STerm C} {q p : PTerm C} {v : SValT C} {σ τ : State}
    (hd : q.divergesLen p = true) (he : (STerm.save s q v).eval σ = .ok τ) :
    (Term.len (.save s q v) p).eval σ = (Term.len s p).eval σ := by
  have hterm := he
  simp only [tm_eval] at he
  obtain ⟨sv, -, he⟩ := bind_ok_inv he
  obtain ⟨τs, hs, he⟩ := bind_ok_inv he
  obtain ⟨⟨r, segs⟩, hq, hsave⟩ := bind_ok_inv he
  obtain ⟨x, hsave'⟩ := State.writeStorage_ok hsave
  rw [Term.len_eval, Term.len_eval, hterm, hs, Res.ok_bind', Res.ok_bind']
  cases hp : p.eval σ with
  | error _ => rfl
  | ok rp =>
    obtain ⟨r', segs'⟩ := rp
    simp only [bind, Except.bind]
    rw [Close.arrayLen_saveStorage_frame hsave' (PTerm.divergesLen_eval hd hq hp)]

/-- A length read away from a returned delete evaluates exactly as the read
before the delete. -/
theorem Term.len_delAt_frame_eval {s : STerm C} {q p : PTerm C} {σ τ : State}
    (hd : q.divergesLen p = true) (he : (STerm.delAt s q).eval σ = .ok τ) :
    (Term.len (.delAt s q) p).eval σ = (Term.len s p).eval σ := by
  have hterm := he
  rw [STerm.delAt_eval'] at he
  obtain ⟨τs, hs, he⟩ := bind_ok_inv he
  obtain ⟨⟨r, segs⟩, hq, he⟩ := bind_ok_inv he
  unfold State.delAtAt at he
  obtain ⟨cur, -, hsave⟩ := bind_ok_inv he
  rw [Term.len_eval, Term.len_eval, hterm, hs, Res.ok_bind', Res.ok_bind']
  cases hp : p.eval σ with
  | error _ => rfl
  | ok rp =>
    obtain ⟨r', segs'⟩ := rp
    simp only [bind, Except.bind]
    rw [Close.arrayLen_saveStorage_frame hsave (PTerm.divergesLen_eval hd hq hp)]

/-- A read away from a returned delete evaluates exactly as the read before
the delete. -/
theorem Term.find_delAt_frame_eval {s : STerm C} {p q : PTerm C} {σ τ : State}
    (hd : p.diverges q = true) (he : (STerm.delAt s p).eval σ = .ok τ) :
    (Term.find (.delAt s p) q).eval σ = (Term.find s q).eval σ := by
  have hterm := he
  rw [STerm.delAt_eval'] at he
  obtain ⟨τs, hs, he⟩ := bind_ok_inv he
  obtain ⟨⟨r, segs⟩, hp, he⟩ := bind_ok_inv he
  unfold State.delAtAt at he
  obtain ⟨cur, -, hsave⟩ := bind_ok_inv he
  rw [Term.find_eval, Term.find_eval, hterm, hs, Res.ok_bind', Res.ok_bind']
  cases hq : q.eval σ with
  | error _ => rfl
  | ok rq =>
    obtain ⟨r', segs'⟩ := rq
    simp only [bind, Except.bind]
    rw [Close.findStorage_saveStorage_apart hsave (PTerm.diverges_eval_any hd hp hq)]

/-- A read away from a returned write evaluates exactly as the read before
the write. -/
theorem Term.find_save_frame_eval {s : STerm C} {p q : PTerm C} {v : SValT C} {σ τ : State}
    (hd : p.diverges q = true) (he : (STerm.save s p v).eval σ = .ok τ) :
    (Term.find (.save s p v) q).eval σ = (Term.find s q).eval σ := by
  have hterm := he
  simp only [tm_eval] at he
  obtain ⟨sv, -, he⟩ := bind_ok_inv he
  obtain ⟨τs, hs, he⟩ := bind_ok_inv he
  obtain ⟨⟨r, segs⟩, hp, hsave⟩ := bind_ok_inv he
  obtain ⟨x, hsave'⟩ := State.writeStorage_ok hsave
  rw [Term.find_eval, Term.find_eval, hterm, hs, Res.ok_bind', Res.ok_bind']
  cases hq : q.eval σ with
  | error _ => rfl
  | ok rq =>
    obtain ⟨r', segs'⟩ := rq
    simp only [bind, Except.bind]
    rw [Close.findStorage_saveStorage_apart hsave' (PTerm.diverges_eval_any hd hp hq)]

/-- A read at a returned delete evaluates as the primitive default of the
word before the delete, even when its path carries another explicit check. -/
theorem Term.find_delAt_value_eval {s : STerm C} {p q : PTerm C} {σ τ : State}
    (heq : p.sameSegs q = true) (he : (STerm.delAt s p).eval σ = .ok τ) :
    (Term.find (.delAt s p) q).eval σ = (Term.delValue (Term.find s q)).eval σ := by
  have hterm := he
  rw [STerm.delAt_eval'] at he
  obtain ⟨τs, hs, he⟩ := bind_ok_inv he
  obtain ⟨⟨r, segs⟩, hp, he⟩ := bind_ok_inv he
  unfold State.delAtAt at he
  obtain ⟨cur, hcur, hsave⟩ := bind_ok_inv he
  rw [Term.find_eval, hterm, Res.ok_bind']
  simp only [tm_eval, Op1.eval, hs, Res.ok_bind']
  cases hq : q.eval σ with
  | error _ => rfl
  | ok rq =>
    obtain ⟨r', segs'⟩ := rq
    obtain ⟨rfl, rfl⟩ := PTerm.sameSegs_eval heq hp hq
    simp only [bind, Except.bind]
    rw [State.findStorage_saveStorage_same hsave, hcur]
    change cur.defaultOf.asValue = (do pure (Theory.StValue.primDefault (← cur.asValue)))
    exact SVal.defaultOf_asValue_primDefault cur

/-- The storage laws whose two sides evaluate alike once their storage
operation returns.  These are the laws that may rewrite a covered update
under either modality even though their right side is not total. -/
inductive TermTaclet.RefLaw : {t t' : Term C} → TermTaclet t t' → Prop where
  | findOnSaveFrame {s : STerm C} {p q : PTerm C} {v : SValT C}
      (hd : p.diverges q = true) :
      RefLaw (TermTaclet.findOnSaveFrame (s := s) (p := p) (q := q) (v := v) hd)
  | findOnDelAtValue {s : STerm C} {p q : PTerm C} (hp : p.hasSeg = true)
      (hq : p.sameSegs q = true) :
      RefLaw (TermTaclet.findOnDelAtValue (s := s) (p := p) (q := q) hp hq)
  | findOnDelAtFrame {s : STerm C} {p q : PTerm C} (hd : p.diverges q = true) :
      RefLaw (TermTaclet.findOnDelAtFrame (s := s) (p := p) (q := q) hd)
  | lenOnSaveFrame {s : STerm C} {q p : PTerm C} {v : SValT C}
      (hd : q.divergesLen p = true) :
      RefLaw (TermTaclet.lenOnSaveFrame (s := s) (q := q) (p := p) (v := v) hd)
  | lenOnDelAtFrame {s : STerm C} {q p : PTerm C} (hd : q.divergesLen p = true) :
      RefLaw (TermTaclet.lenOnDelAtFrame (s := s) (q := q) (p := p) hd)

/-- A reference law keeps every value returned by its left side. -/
theorem TermTaclet.RefLaw.evalRefines {r : TermTaclet t t'} : RefLaw r →
    Term.EvalRefines t t'
  | .findOnSaveFrame hd => fun σ x hx => by
      have hx' := hx
      rw [Term.find_eval] at hx
      obtain ⟨τ, hτ, -⟩ := bind_ok_inv hx
      rw [Term.find_save_frame_eval hd hτ] at hx'
      exact hx'
  | .findOnDelAtValue _ hq => fun σ x hx => by
      have hx' := hx
      rw [Term.find_eval] at hx
      obtain ⟨τ, hτ, -⟩ := bind_ok_inv hx
      rw [Term.find_delAt_value_eval hq hτ] at hx'
      exact hx'
  | .findOnDelAtFrame hd => fun σ x hx => by
      have hx' := hx
      rw [Term.find_eval] at hx
      obtain ⟨τ, hτ, -⟩ := bind_ok_inv hx
      rw [Term.find_delAt_frame_eval hd hτ] at hx'
      exact hx'
  | .lenOnSaveFrame hd => fun σ x hx => by
      have hx' := hx
      rw [Term.len_eval] at hx
      obtain ⟨τ, hτ, -⟩ := bind_ok_inv hx
      rw [Term.len_save_frame_eval hd hτ] at hx'
      exact hx'
  | .lenOnDelAtFrame hd => fun σ x hx => by
      have hx' := hx
      rw [Term.len_eval] at hx
      obtain ⟨τ, hτ, -⟩ := bind_ok_inv hx
      rw [Term.len_delAt_frame_eval hd hτ] at hx'
      exact hx'

/-- In the frame at `r`, a delete at `g.rest` is the delete at `r.g.rest`
outside it, the frame taken after. -/
theorem State.delAtAt_selectRoot (r : Name) (τ : State) (g : Name) (rest : List Seg) :
    Res.OkEq (τ.delAtAt r (.field g :: rest) >>= State.selectRoot r)
      (State.selectRoot r τ >>= fun τ' => τ'.delAtAt g rest) := by
  unfold State.delAtAt
  cases hs : State.selectRoot r τ with
  | ok τ' =>
    simp only [bind, Except.bind]
    rw [State.findStorage_selectRoot hs]
    cases τ.findStorage r (.field g :: rest) with
    | error e => exact Res.OkEq.refl _
    | ok cur =>
      have e := State.saveStorage_selectRoot r τ g rest cur.defaultOf
      rw [hs] at e
      simp only [bind, Except.bind] at e
      exact Res.OkEq.of_eq e
  | error e =>
    intro x
    constructor
    · intro h
      obtain ⟨τ₁, h₁, h₂⟩ := bind_ok_inv h
      obtain ⟨cur, -, h₁⟩ := bind_ok_inv h₁
      have e' := State.saveStorage_selectRoot r τ g rest cur.defaultOf
      rw [hs, h₁] at e'
      simp only [bind, Except.bind] at e'
      rw [e'] at h₂
      cases h₂
    · intro h
      simp [bind, Except.bind] at h

/-- The root of a path: `alice` of `alice.account.balance`; `none` through an
alias. -/
def Tm.rootName? : Tm C u → Option Name
  | .app0 (.root r) => some r
  | .app1 (.field _) p => Tm.rootName? p
  | .app1 .next p => Tm.rootName? p
  | .app2 .at p _ => Tm.rootName? p
  | _ => none

/-- A path of a root and members only: no alias, no index, no push slot. -/
def Tm.isFields : Tm C u → Bool
  | .app0 (.root _) => true
  | .app1 (.field _) p => Tm.isFields p
  | _ => false

/-- A member path resolves in every state, to its root and its members. -/
theorem Tm.isFields_eval (σ : State) : (p : PTerm C) → Tm.isFields p = true →
    ∃ f segs, p.eval σ = .ok (f, segs) ∧ segs.all Seg.isField = true
  | .app0 (.root f), _ => ⟨f, [], rfl, rfl⟩
  | .app1 (.field g) p, h => by
    obtain ⟨f, segs, hp, hf⟩ := Tm.isFields_eval σ p h
    refine ⟨f, segs ++ [.field g], ?_, ?_⟩
    · rw [Tm.app1_eval, hp]; rfl
    · simp only [List.all_append, hf, List.all_cons, List.all_nil, Seg.isField, Bool.and_self]
  | .pvP _, h | .app1 .next _, h | .app2 .at _ _, h | .app2 .nextIn _ _, h
  | .app3 .atIn _ _ _, h => nomatch h

/-- The path under the root `r`: `age` under `alice` is `alice.age`.  A path
through an alias is left as it is. -/
def Tm.prefixRoot (r : Name) : Tm C u → Tm C u
  | .app0 (.root f) => .app1 (.field f) (.app0 (.root r))
  | .app1 (.field f) p => .app1 (.field f) (p.prefixRoot r)
  | .app2 .at p i => .app2 .at (p.prefixRoot r) i
  | t => t

theorem Tm.prefixRoot_isFields (r : Name) : (p : PTerm C) → Tm.isFields p = true →
    Tm.isFields (p.prefixRoot r) = true
  | .app0 (.root _), _ => rfl
  | .app1 (.field _) p, h => Tm.prefixRoot_isFields r p h
  | .pvP _, h | .app1 .next _, h | .app2 .at _ _, h | .app2 .nextIn _ _, h
  | .app3 .atIn _ _ _, h => nomatch h

/-- `r.p` resolves as the member path `p` does, one segment on. -/
theorem Tm.prefixRoot_eval {σ : State} (r : Name) : (p : PTerm C) → Tm.isFields p = true →
    ∀ {f : Name} {segs : List Seg}, p.eval σ = .ok (f, segs) →
      (p.prefixRoot r).eval σ = .ok (r, .field f :: segs)
  | .app0 (.root g), _, f, segs, h => by
    simp only [tm_eval, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .app1 (.field g) p, hf, f, segs, h => by
    rw [Tm.app1_eval] at h
    cases hp : p.eval σ with
    | error e => rw [hp] at h; cases h
    | ok fs =>
      obtain ⟨f', segs'⟩ := fs
      rw [hp] at h
      simp only [Op1.eval, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      show (Tm.app1 (.field g) (p.prefixRoot r)).eval σ = _
      rw [Tm.app1_eval, Tm.prefixRoot_eval r p hf hp]
      rfl
  | .pvP _, hf, _, _, _ | .app1 .next _, hf, _, _, _ | .app2 .at _ _, hf, _, _, _
  | .app2 .nextIn _ _, hf, _, _, _ | .app3 .atIn _ _ _, hf, _, _, _ => nomatch hf

/-- The member path `p` under the frame `F`: `p` itself at the top, else
`F.p`, which resolves as `p` does in the frame.  `none` for a path through
an alias or an index, or at the `length` member, which an array could tell
apart from `p` in the frame (`Term.base_eval`). -/
def PTerm.under? (F : List Name) (p : PTerm C) : Option (PTerm C) :=
  match F with
  | [] => some p
  | _ :: _ =>
    if Tm.isFields p && (Tm.rootName? p != some "length") then some (F.foldr Tm.prefixRoot p)
    else none

/-- `F.p` resolves to `F`'s members, then `p`'s root and members. -/
theorem PTerm.foldr_prefixRoot_eval {σ : State} (p : PTerm C) (hf : Tm.isFields p = true)
    {f : Name} {segs : List Seg} (hp : p.eval σ = .ok (f, segs)) :
    (F : List Name) → ∃ r rest, (F.foldr Tm.prefixRoot p).eval σ = .ok (r, rest) ∧
      (Seg.field r :: rest) = F.map Seg.field ++ (Seg.field f :: segs)
  | [] => ⟨f, segs, hp, rfl⟩
  | r :: F => by
    obtain ⟨r', rest', h, e⟩ := PTerm.foldr_prefixRoot_eval p hf hp F
    have hf' : Tm.isFields (F.foldr Tm.prefixRoot p) = true := by
      clear h e
      induction F with
      | nil => exact hf
      | cons r F ih => exact Tm.prefixRoot_isFields r _ ih
    refine ⟨r, .field r' :: rest', ?_, ?_⟩
    · exact Tm.prefixRoot_eval r _ hf' h
    · simp only [List.map_cons, List.cons_append, e]

/-- A storage term read member-wise, as the term it reads and the frame it
reads it in: `save(select(s, r), p, v)` reads `save(s, r.p, v)` in the frame
`[r]`; `s` alone reads itself at the top. -/
def Tm.baseAny : Tm C u → Option (Tm C u × List Name)
  | .app1 (.select r) s => (Tm.baseAny s).map fun (b, F) => (b, F ++ [r])
  | .app3 .save s p v =>
    (Tm.baseAny s).bind fun (b, F) => (PTerm.under? F p).map fun p' => (STerm.save b p' v, F)
  | .app2 .delAt s p =>
    (Tm.baseAny s).bind fun (b, F) => (PTerm.under? F p).map fun p' => (STerm.delAt b p', F)
  | s => some (s, [])

@[inherit_doc Tm.baseAny]
def STerm.base? (s : STerm C) : Option (STerm C × List Name) := Tm.baseAny s

/-- A read, member-wise, as the read it is: `find(select(s, r), p)` is
`find(s, r.p)`. -/
def Term.base? : Term C → Option (Term C)
  | .find s q => (STerm.base? s).bind fun (b, F) => (PTerm.under? F q).map fun q' => .find b q'
  | _ => none

theorem Res.bind_assoc {α β γ : Type} (x : Res α) (f : α → Res β) (g : β → Res γ) :
    ((x >>= f) >>= g) = (x >>= fun a => f a >>= g) := by cases x <;> rfl


/-- A member path's root. -/
theorem Tm.rootName?_eval {σ : State} : (p : PTerm C) → Tm.isFields p = true →
    ∀ {f : Name} {segs : List Seg}, p.eval σ = .ok (f, segs) → Tm.rootName? p = some f
  | .app0 (.root g), _, f, segs, h => by
    simp only [tm_eval, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl
  | .app1 (.field g) p, hf, f, segs, h => by
    rw [Tm.app1_eval] at h
    cases hp : p.eval σ with
    | error e => rw [hp] at h; cases h
    | ok fs =>
      obtain ⟨f', segs'⟩ := fs
      rw [hp] at h
      simp only [Op1.eval, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact Tm.rootName?_eval p hf hp
  | .pvP _, hf, _, _, _ | .app1 .next _, hf, _, _, _ | .app2 .at _ _, hf, _, _, _
  | .app2 .nextIn _ _, hf, _, _, _ | .app3 .atIn _ _ _, hf, _, _, _ => nomatch hf

/-- A read of a word through a node that is no struct halts, but at the
`length` of an array with nothing after it. -/
theorem SVal.find_field_of_nonStruct {V : SVal} (hV : ∀ fields, V ≠ .struct fields) {g : Name}
    {segs : List Seg} (hg : g = "length" → segs ≠ []) {x : SVal} :
    V.find (.field g :: segs) ≠ .ok x := by
  cases V with
  | struct fields => exact absurd rfl (hV fields)
  | prim _ => simp [SVal.find]
  | map _ _ => simp [SVal.find]
  | array elems sh fx =>
    by_cases h : g = "length"
    · subst h
      cases fx with
      | true => simp [SVal.find]
      | false =>
        cases segs with
        | nil => exact absurd rfl (hg rfl)
        | cons _ _ => simp [SVal.find]
    · simp [SVal.find]

theorem Res.bind_pure_ok {α : Type} (x : Res α) : (x >>= fun a => (Except.ok a : Res α)) = x := by
  cases x <;> rfl

/-- A read in the frame `F` is the read outside it, at `F`'s members then the
path, where the path's root is not an array's `length`. -/
theorem State.frameOf_findStorage (r₁ : Name) (g : Name) (segs : List Seg) (hg : g ≠ "length") :
    (F' : List Name) → (τ : State) →
      Res.OkEq (State.frameOf (r₁ :: F') τ >>= fun τ' => τ'.findStorage g segs)
        (τ.findStorage r₁ (F'.map Seg.field ++ (.field g :: segs)))
  | [], τ => by
    show Res.OkEq ((State.selectRoot r₁ τ >>= fun x => (Except.ok x : Res State)) >>= fun τ' =>
      τ'.findStorage g segs) _
    rw [Res.bind_pure_ok]
    simp only [List.map_nil, List.nil_append]
    cases hs : State.selectRoot r₁ τ with
    | ok τ' =>
      rw [Res.ok_bind']
      exact Res.OkEq.of_eq (State.findStorage_selectRoot hs g segs)
    | error e =>
      intro x
      constructor
      · intro h; simp [bind, Except.bind] at h
      · intro h
        exfalso
        unfold State.selectRoot at hs
        simp only [State.findStorage] at hs h
        cases hv : lookupBy r₁ τ.storage with
        | none => rw [hv] at h; cases h
        | some V =>
          rw [hv] at hs h
          cases V with
          | struct fields => simp [SVal.find, bind, Except.bind, pure, Except.pure] at hs
          | prim _ | map _ _ | array _ _ _ =>
            exact SVal.find_field_of_nonStruct (by intro _ h; cases h) (fun h' _ => hg h') h
  | r₂ :: F'', τ => by
    show Res.OkEq ((State.selectRoot r₁ τ >>= State.frameOf (r₂ :: F'')) >>= fun τ' =>
      τ'.findStorage g segs) _
    simp only [List.map_cons, List.cons_append]
    cases hs : State.selectRoot r₁ τ with
    | ok τ' =>
      rw [Res.ok_bind']
      exact (State.frameOf_findStorage r₂ g segs hg F'' τ').trans
        (Res.OkEq.of_eq (State.findStorage_selectRoot hs _ _))
    | error e =>
      intro x
      constructor
      · intro h; simp [bind, Except.bind] at h
      · intro h
        exfalso
        unfold State.selectRoot at hs
        simp only [State.findStorage] at hs h
        cases hv : lookupBy r₁ τ.storage with
        | none => rw [hv] at h; cases h
        | some V =>
          rw [hv] at hs h
          cases V with
          | struct fields => simp [SVal.find, bind, Except.bind, pure, Except.pure] at hs
          | prim _ | map _ _ | array _ _ _ =>
            exact SVal.find_field_of_nonStruct (by intro _ h; cases h)
              (fun _ h' => by simp at h') h

/-- A write in the frame `F` is the write outside it, the frame taken after. -/
theorem State.frameOf_writeStorage (r₁ : Name) (g : Name) (segs : List Seg) (sv : SVal) :
    (F' : List Name) → (τ : State) →
      Res.OkEq (τ.writeStorage r₁ (F'.map Seg.field ++ (.field g :: segs)) sv >>= State.frameOf (r₁ :: F'))
        (State.frameOf (r₁ :: F') τ >>= fun τ' => τ'.writeStorage g segs sv)
  | [], τ => by
    show Res.OkEq (τ.writeStorage r₁ ([].map Seg.field ++ (.field g :: segs)) sv >>= fun x =>
        State.selectRoot r₁ x >>= fun x => (Except.ok x : Res State))
      ((State.selectRoot r₁ τ >>= fun x => (Except.ok x : Res State)) >>= fun τ' =>
        τ'.writeStorage g segs sv)
    simp only [Res.bind_pure_ok, List.map_nil, List.nil_append]
    exact State.writeStorage_selectRoot r₁ τ g segs sv
  | r₂ :: F'', τ => by
    show Res.OkEq (τ.writeStorage r₁ ((r₂ :: F'').map Seg.field ++ (.field g :: segs)) sv >>= fun x =>
        State.selectRoot r₁ x >>= State.frameOf (r₂ :: F''))
      ((State.selectRoot r₁ τ >>= State.frameOf (r₂ :: F'')) >>= fun τ' => τ'.writeStorage g segs sv)
    simp only [List.map_cons, List.cons_append]
    rw [← Res.bind_assoc, Res.bind_assoc (State.selectRoot r₁ τ)]
    refine Res.OkEq.trans (Res.OkEq.bind (State.writeStorage_selectRoot r₁ τ r₂ _ sv)
      fun _ => Res.OkEq.refl _) ?_
    rw [Res.bind_assoc]
    exact Res.OkEq.bind (Res.OkEq.refl _) fun τ' => State.frameOf_writeStorage r₂ g segs sv F'' τ'

/-- A delete in the frame `F` is the delete outside it, the frame taken after. -/
theorem State.frameOf_delAtAt (r₁ : Name) (g : Name) (segs : List Seg) :
    (F' : List Name) → (τ : State) →
      Res.OkEq (τ.delAtAt r₁ (F'.map Seg.field ++ (.field g :: segs)) >>= State.frameOf (r₁ :: F'))
        (State.frameOf (r₁ :: F') τ >>= fun τ' => τ'.delAtAt g segs)
  | [], τ => by
    show Res.OkEq (τ.delAtAt r₁ ([].map Seg.field ++ (.field g :: segs)) >>= fun x =>
        State.selectRoot r₁ x >>= fun x => (Except.ok x : Res State))
      ((State.selectRoot r₁ τ >>= fun x => (Except.ok x : Res State)) >>= fun τ' => τ'.delAtAt g segs)
    simp only [Res.bind_pure_ok, List.map_nil, List.nil_append]
    exact State.delAtAt_selectRoot r₁ τ g segs
  | r₂ :: F'', τ => by
    show Res.OkEq (τ.delAtAt r₁ ((r₂ :: F'').map Seg.field ++ (.field g :: segs)) >>= fun x =>
        State.selectRoot r₁ x >>= State.frameOf (r₂ :: F''))
      ((State.selectRoot r₁ τ >>= State.frameOf (r₂ :: F'')) >>= fun τ' => τ'.delAtAt g segs)
    simp only [List.map_cons, List.cons_append]
    rw [← Res.bind_assoc, Res.bind_assoc (State.selectRoot r₁ τ)]
    refine Res.OkEq.trans (Res.OkEq.bind (State.delAtAt_selectRoot r₁ τ r₂ _)
      fun _ => Res.OkEq.refl _) ?_
    rw [Res.bind_assoc]
    exact Res.OkEq.bind (Res.OkEq.refl _) fun τ' => State.frameOf_delAtAt r₂ g segs F'' τ'

/-- A save at `r.g.rest` that returned went through the struct at `r`, before
and after: the save at `g.rest` in that frame. -/
theorem State.saveStorage_field_ok {r g : Name} {rest : List Seg} {new : SVal} {τ τ₁ : State}
    (h : τ.saveStorage r (.field g :: rest) new = .ok τ₁) :
    ∃ τ' τ₁', State.selectRoot r τ = .ok τ' ∧ State.selectRoot r τ₁ = .ok τ₁' ∧
      τ'.saveStorage g rest new = .ok τ₁' := by
  have e := State.saveStorage_selectRoot r τ g rest new
  rw [h, Res.ok_bind'] at e
  obtain ⟨V, up, hV, hs, rfl⟩ := State.saveStorage_ok_inv h
  cases V with
  | prim _ | array _ _ _ | map _ _ => simp [SVal.save] at hs
  | struct fields =>
    have hsel : State.selectRoot r τ = .ok { τ with storage := fields } := by
      unfold State.selectRoot
      simp [State.findStorage, hV, SVal.find, bind, Except.bind, pure, Except.pure]
    rw [hsel, Res.ok_bind'] at e
    simp only [SVal.save] at hs
    cases hg : lookupBy g fields with
    | none => simp [hg] at hs
    | some old =>
      simp only [hg] at hs
      cases hs' : old.save rest new with
      | error _ => simp [hs', bind, Except.bind] at hs
      | ok u' =>
        simp only [hs', bind, Except.bind, Except.ok.injEq] at hs
        subst hs
        have inner : State.saveStorage { τ with storage := fields } g rest new =
            .ok { τ with storage := setBy g u' fields } := by
          unfold State.saveStorage
          simp [hg, hs', bind, Except.bind]
        exact ⟨_, _, hsel, by rw [e]; exact inner, inner⟩

/-- The frame `F` of a save at `F.g.segs` that returned exists, before and after it. -/
theorem State.frameOf_of_saveStorage (r₁ g : Name) (segs : List Seg) (new : SVal) :
    (F' : List Name) → (τ τ₁ : State) →
      τ.saveStorage r₁ (F'.map Seg.field ++ (.field g :: segs)) new = .ok τ₁ →
      (∃ τ', State.frameOf (r₁ :: F') τ = .ok τ') ∧ ∃ τ₁', State.frameOf (r₁ :: F') τ₁ = .ok τ₁'
  | [], τ, τ₁, h => by
    obtain ⟨τ', τ₁', hs, hs₁, -⟩ := State.saveStorage_field_ok h
    refine ⟨⟨τ', ?_⟩, ⟨τ₁', ?_⟩⟩
    · show (State.selectRoot r₁ τ >>= State.frameOf []) = _
      rw [hs]; rfl
    · show (State.selectRoot r₁ τ₁ >>= State.frameOf []) = _
      rw [hs₁]; rfl
  | r₂ :: F'', τ, τ₁, h => by
    obtain ⟨τ', τ₁', hs, hs₁, h'⟩ := State.saveStorage_field_ok h
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := State.frameOf_of_saveStorage r₂ g segs new F'' τ' τ₁' h'
    refine ⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩
    · show (State.selectRoot r₁ τ >>= State.frameOf (r₂ :: F'')) = _
      rw [hs, Res.ok_bind']; exact ha
    · show (State.selectRoot r₁ τ₁ >>= State.frameOf (r₂ :: F'')) = _
      rw [hs₁, Res.ok_bind']; exact hb

theorem STerm.save_eval' (σ : State) (s : STerm C) (p : PTerm C) (v : SValT C) :
    (STerm.save s p v).eval σ = (do
      let sv ← v.eval σ
      let τ ← s.eval σ
      let (r, segs) ← p.eval σ
      τ.writeStorage r segs sv) := rfl

/-- The frame `F` of `F.p` and `p`: where `p` resolves, `F.p` resolves to the
frame's members, then `p`'s. -/
theorem PTerm.under?_eval {σ : State} {r₁ : Name} {F' : List Name} {p p' : PTerm C}
    (h : PTerm.under? (r₁ :: F') p = some p') :
    ∃ g segs, p.eval σ = .ok (g, segs) ∧ g ≠ "length" ∧
      p'.eval σ = .ok (r₁, F'.map Seg.field ++ (.field g :: segs)) := by
  simp only [PTerm.under?] at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
    obtain ⟨hf, hl⟩ := hc
    obtain ⟨g, segs, hpe, -⟩ := Tm.isFields_eval σ p hf
    have hroot := Tm.rootName?_eval p hf hpe
    refine ⟨g, segs, hpe, fun e => hl (by rw [hroot, e]), ?_⟩
    obtain ⟨r, rest, hp'e, he⟩ := PTerm.foldr_prefixRoot_eval p hf hpe (r₁ :: F')
    simp only [List.map_cons, List.cons_append, List.cons.injEq, Seg.field.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact hp'e
  · nomatch h

/-- **A storage term read member-wise runs as the term it reads, in its
frame.** -/
theorem STerm.base_eval : (s : STerm C) → {b : STerm C} → {F : List Name} →
    STerm.base? s = some (b, F) → ∀ σ, Res.OkEq (s.eval σ) (b.eval σ >>= State.frameOf F)
  | .app1 (.select r) s, b, F, h, σ => by
    simp only [STerm.base?, Tm.baseAny, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨b₀, F₀⟩, hb, rfl, rfl⟩ := h
    rw [STerm.select_eval]
    refine Res.OkEq.trans (Res.OkEq.bind (STerm.base_eval s hb σ) fun _ => Res.OkEq.refl _) ?_
    rw [Res.bind_assoc]
    refine Res.OkEq.of_eq (congrArg _ (funext fun τ => ?_))
    rw [State.frameOf_append]
    simp only [State.frameOf, Res.bind_pure_ok]
  | .app3 .save s p v, b, F, h, σ => by
    simp only [STerm.base?, Tm.baseAny, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨b₀, F₀⟩, hb, p', hp, rfl, rfl⟩ := h
    have ih := STerm.base_eval s hb σ
    rw [STerm.save_eval', STerm.save_eval']
    cases F₀ with
    | nil =>
      simp only [PTerm.under?, Option.some.injEq] at hp
      subst hp
      simp only [State.frameOf, Res.bind_pure_ok] at ih ⊢
      refine Res.OkEq.bind (Res.OkEq.refl _) fun sv => Res.OkEq.bind ih fun τ => Res.OkEq.refl _
    | cons r₁ F' =>
      obtain ⟨g, segs, hpe, -, hp'e⟩ := PTerm.under?_eval (σ := σ) hp
      rw [hpe, hp'e]
      simp only [Res.ok_bind', Res.bind_assoc]
      refine Res.OkEq.bind (Res.OkEq.refl _) fun sv => ?_
      refine Res.OkEq.trans (Res.OkEq.bind ih fun _ => Res.OkEq.refl _) ?_
      simp only [Res.bind_assoc]
      refine Res.OkEq.bind (Res.OkEq.refl _) fun τb => ?_
      exact (State.frameOf_writeStorage r₁ g segs sv F' τb).symm
  | .app2 .delAt s p, b, F, h, σ => by
    simp only [STerm.base?, Tm.baseAny, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨b₀, F₀⟩, hb, p', hp, rfl, rfl⟩ := h
    have ih := STerm.base_eval s hb σ
    rw [STerm.delAt_eval', STerm.delAt_eval']
    cases F₀ with
    | nil =>
      simp only [PTerm.under?, Option.some.injEq] at hp
      subst hp
      simp only [State.frameOf, Res.bind_pure_ok] at ih ⊢
      exact Res.OkEq.bind ih fun τ => Res.OkEq.refl _
    | cons r₁ F' =>
      obtain ⟨g, segs, hpe, -, hp'e⟩ := PTerm.under?_eval (σ := σ) hp
      rw [hpe, hp'e]
      simp only [Res.ok_bind', Res.bind_assoc]
      refine Res.OkEq.trans (Res.OkEq.bind ih fun _ => Res.OkEq.refl _) ?_
      simp only [Res.bind_assoc]
      refine Res.OkEq.bind (Res.OkEq.refl _) fun τb => ?_
      exact (State.frameOf_delAtAt r₁ g segs F' τb).symm
  | .pvS _, b, F, h, σ | .app0 .storage, b, F, h, σ | .app2 (.pushSlot _) _ _, b, F, h, σ
  | .app2 .pop _ _, b, F, h, σ | .app2 .shrink _ _, b, F, h, σ | .app2 (.extend _) _ _, b, F, h, σ
  | .app3 .push _ _ _, b, F, h, σ => by
    simp only [STerm.base?, Tm.baseAny, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [State.frameOf, Res.bind_pure_ok]
    exact Res.OkEq.refl _

/-- **A read, member-wise, returns where the read it is returns**, the same
value. -/
theorem Term.base_eval : (t : Term C) → {t' : Term C} → Term.base? t = some t' →
    ∀ σ, Res.OkEq (t.eval σ) (t'.eval σ)
  | .app2 .find s q, t', h, σ => by
    simp only [Term.base?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨b, F⟩, hb, q', hq, rfl⟩ := h
    have ih := STerm.base_eval s hb σ
    rw [Term.find_eval, Term.find_eval]
    cases F with
    | nil =>
      simp only [PTerm.under?, Option.some.injEq] at hq
      subst hq
      simp only [State.frameOf, Res.bind_pure_ok] at ih
      exact Res.OkEq.bind ih fun τ => Res.OkEq.refl _
    | cons r₁ F' =>
      obtain ⟨g, segs, hqe, hg, hq'e⟩ := PTerm.under?_eval (σ := σ) hq
      rw [hqe, hq'e]
      simp only [Res.ok_bind']
      refine Res.OkEq.trans (Res.OkEq.bind ih fun _ => Res.OkEq.refl _) ?_
      simp only [Res.bind_assoc]
      refine Res.OkEq.bind (Res.OkEq.refl _) fun τb => ?_
      rw [← Res.bind_assoc]
      exact Res.OkEq.bind (State.frameOf_findStorage r₁ g segs hg F' τb) fun _ => Res.OkEq.refl _
  | .pvV _, _, h, _ | .app0 _, _, h, _ | .app1 _ _, _, h, _ | .app3 _ _ _ _, _, h, _
  | .app2 (.binop _ _) _ _, _, h, _ | .app2 .len _ _, _, h, _ | .app2 .read _ _, _, h, _
  | .app2 .mlen _ _, _, h, _ => nomatch h

/-- A write of the frame `F` at `F.p` that returned leaves the frame in place. -/
theorem State.frameOf_of_writeStorage {r₁ g : Name} {segs : List Seg} {sv : SVal} {F' : List Name}
    {τ τ₁ : State} (h : τ.writeStorage r₁ (F'.map Seg.field ++ (.field g :: segs)) sv = .ok τ₁) :
    ∃ τ₁', State.frameOf (r₁ :: F') τ₁ = .ok τ₁' := by
  obtain ⟨x, hx⟩ := State.writeStorage_ok h
  exact (State.frameOf_of_saveStorage r₁ g segs x F' τ τ₁ hx).2

theorem State.frameOf_of_delAtAt {r₁ g : Name} {segs : List Seg} {F' : List Name} {τ τ₁ : State}
    (h : τ.delAtAt r₁ (F'.map Seg.field ++ (.field g :: segs)) = .ok τ₁) :
    ∃ τ₁', State.frameOf (r₁ :: F') τ₁ = .ok τ₁' := by
  obtain ⟨cur, -, hx⟩ := bind_ok_inv h
  exact (State.frameOf_of_saveStorage r₁ g segs cur.defaultOf F' τ τ₁ hx).2

/-- A save read member-wise returns where the save it reads returns. -/
theorem STerm.save_returns_of_base {s : STerm C} {p : PTerm C} {v : SValT C} {b : STerm C}
    {F : List Name} (h : STerm.base? (.save s p v) = some (b, F)) {σ τ₁ : State}
    (hb : b.eval σ = .ok τ₁) : ∃ τ, (STerm.save s p v).eval σ = .ok τ := by
  simp only [STerm.base?, Tm.baseAny, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨b₀, F₀⟩, hb₀, p', hp, rfl, rfl⟩ := h
  dsimp only at hp hb
  have e := STerm.base_eval (.save s p v) (b := .save b₀ p' v) (F := F₀) (by
    simp only [STerm.base?, Tm.baseAny, hb₀, Option.bind_some, hp, Option.map_some]) σ
  have hres : ∃ τ, ((STerm.save b₀ p' v).eval σ >>= State.frameOf F₀) = .ok τ := by
    rw [hb, Res.ok_bind']
    cases F₀ with
    | nil => exact ⟨τ₁, rfl⟩
    | cons r₁ F' =>
      obtain ⟨g, segs, -, -, hp'e⟩ := PTerm.under?_eval (σ := σ) hp
      rw [STerm.save_eval'] at hb
      obtain ⟨sv, -, hb⟩ := bind_ok_inv hb
      obtain ⟨τb, -, hb⟩ := bind_ok_inv hb
      rw [hp'e] at hb
      simp only [Res.ok_bind'] at hb
      exact State.frameOf_of_writeStorage hb
  obtain ⟨τ, hτ⟩ := hres
  exact ⟨τ, (e τ).2 hτ⟩

/-- A delete read member-wise returns where the delete it reads returns. -/
theorem STerm.delAt_returns_of_base {s : STerm C} {p : PTerm C} {b : STerm C} {F : List Name}
    (h : STerm.base? (.delAt s p) = some (b, F)) {σ τ₁ : State} (hb : b.eval σ = .ok τ₁) :
    ∃ τ, (STerm.delAt s p).eval σ = .ok τ := by
  simp only [STerm.base?, Tm.baseAny, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨b₀, F₀⟩, hb₀, p', hp, rfl, rfl⟩ := h
  dsimp only at hp hb
  have e := STerm.base_eval (.delAt s p) (b := .delAt b₀ p') (F := F₀) (by
    simp only [STerm.base?, Tm.baseAny, hb₀, Option.bind_some, hp, Option.map_some]) σ
  have hres : ∃ τ, ((STerm.delAt b₀ p').eval σ >>= State.frameOf F₀) = .ok τ := by
    rw [hb, Res.ok_bind']
    cases F₀ with
    | nil => exact ⟨τ₁, rfl⟩
    | cons r₁ F' =>
      obtain ⟨g, segs, -, -, hp'e⟩ := PTerm.under?_eval (σ := σ) hp
      rw [STerm.delAt_eval'] at hb
      obtain ⟨τb, -, hb⟩ := bind_ok_inv hb
      rw [hp'e] at hb
      simp only [Res.ok_bind'] at hb
      exact State.frameOf_of_delAtAt hb
  obtain ⟨τ, hτ⟩ := hres
  exact ⟨τ, (e τ).2 hτ⟩

/-- `U` writes the storage with a term on whose spine the write `w` reads
member-wise lies (`STerm.base?`): `w` returns wherever `U` does. -/
def Upd.holdsWrite (U : Upd C) (w : STerm C) : Bool :=
  match STerm.base? w with
  | some (b, _) => U.any fun e => match e with
    | .storage S => S.onSpine b
    | _ => false
  | none => false

theorem Upd.holdsWrite_eval {U : Upd C} {w : STerm C} (h : U.holdsWrite w = true) {σ τ : State}
    (hU : U.apply σ = .ok τ) : ∃ b F, STerm.base? w = some (b, F) ∧ ∃ τ₁, b.eval σ = .ok τ₁ := by
  unfold Upd.holdsWrite at h
  split at h
  · rename_i b F hb
    simp only [List.any_eq_true] at h
    obtain ⟨e, he, hs⟩ := h
    cases e with
    | storage S =>
      obtain ⟨τ', hS⟩ := Upd.storage_eval_of_apply hU he
      refine ⟨b, F, hb, ?_⟩
      cases hbe : b.eval σ with
      | ok τ₁ => exact ⟨τ₁, rfl⟩
      | error e' =>
        obtain ⟨e'', hS'⟩ := Tm.onSpine_error hbe S hs
        rw [hS'] at hS
        cases hS
    | val _ _ | path _ _ | mref _ _ | store _ _ | memory _ | selfBalance _ _ | net _ _ _ | pay _ _
    | saveNet _ =>
      nomatch hs
  · nomatch h

/-- `U` returns only where the rewrite `q` is exact: `q.1` reads back a
storage write `U` holds (`Upd.holdsWrite`) — `find(save(s, p, v), p)` over
`storage := save(s, p, v)`, or a word at or below a deleted node where the
storage deleted writes the word at the member path read (`STerm.findLitF?`),
over `storage := delAt(s, p)` — each read member-wise too — so `q.1` returns
wherever `U` does.  Syntactic, so that `rfl` decides it. -/
def Upd.covers (U : Upd C) : Term C × Term C → Bool
  | (.find (.save s p (.val (.lit v))) p', _) =>
    p' == p && U.holdsWrite (.save s p (.val (.lit v)))
  | (.find (.delAt s p) q, _) =>
    U.holdsWrite (.delAt s p) && q.atOrBelow p && (STerm.findLitF? s q).isSome
  | _ => false

/-- Where the update returns, the term a covered rewrite replaces returns. -/
theorem Upd.covers_eval {q : Term C × Term C} {U : Upd C} (hc : U.covers q = true) {σ τ : State}
    (hU : U.apply σ = .ok τ) : ∃ y, q.1.eval σ = .ok y := by
  unfold Upd.covers at hc
  split at hc
  · rename_i s p v p' heq
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨rfl, hw⟩ := hc
    obtain ⟨b, F, hb, τ₁, hbe⟩ := Upd.holdsWrite_eval hw hU
    obtain ⟨τ', hs⟩ := STerm.save_returns_of_base hb hbe
    obtain ⟨r, segs, hp, hf⟩ := STerm.save_lit_eval hs
    refine ⟨v, ?_⟩
    rw [Term.find_eval, hs, hp]
    simp only [bind, Except.bind, hf]
    cases v <;> rfl
  · rename_i s p q' heq
    simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hc
    obtain ⟨⟨hwr, hb⟩, w, hw⟩ := hc
    obtain ⟨b, F, hbase, τ₁, hbe⟩ := Upd.holdsWrite_eval hwr hU
    obtain ⟨τ'', hd⟩ := STerm.delAt_returns_of_base hbase hbe
    exact Upd.delAtBelow_eval hb hw hd
  · nomatch hc

/-- Where the update returns, a covered rewrite is exact: its replacement
returns what the replaced term returns. -/
theorem Upd.covers_le {q : Term C × Term C} (hq : Term.EvalRefines q.1 q.2) {U : Upd C}
    (hc : U.covers q = true) {σ τ : State} (hU : U.apply σ = .ok τ) :
    Res.Le (q.2.eval σ) (q.1.eval σ) := fun x hx => by
  obtain ⟨y, hy⟩ := Upd.covers_eval hc hU
  rw [hq σ y hy] at hx
  obtain rfl := Except.ok.inj hx
  exact hy

/-! ### A reference law in an update's right-hand side

The frame and delete-value laws may leave a storage read on their right.
That read is not total, but once the update returns its storage operation
has returned; the two sides then evaluate identically. -/

/-- A covered reference law's storage operation is held by the update. -/
def Upd.coversRef (U : Upd C) : Term C × Term C → Bool
  | (.find (.save s p v) _, _) => U.holdsWrite (.save s p v)
  | (.find (.delAt s p) _, _) => U.holdsWrite (.delAt s p)
  | (.len (.save s p v) _, _) => U.holdsWrite (.save s p v)
  | (.len (.delAt s p) _, _) => U.holdsWrite (.delAt s p)
  | _ => false

/-- Wherever a covered update returns, a reference law also refines in the
reverse direction. -/
theorem TermTaclet.RefLaw.back {r : TermTaclet t t'} (hr : RefLaw r) {U : Upd C}
    (hc : U.coversRef (t, t') = true) {σ τ : State} (hU : U.apply σ = .ok τ) :
    Res.Le (t'.eval σ) (t.eval σ) := by
  cases hr with
  | findOnSaveFrame hd =>
      simp only [Upd.coversRef] at hc
      obtain ⟨b, F, hb, τ₁, hbe⟩ := Upd.holdsWrite_eval hc hU
      obtain ⟨τ', hs⟩ := STerm.save_returns_of_base hb hbe
      rw [Term.find_save_frame_eval hd hs]
      exact Res.Le.refl _
  | findOnDelAtValue _ hq =>
      simp only [Upd.coversRef] at hc
      obtain ⟨b, F, hb, τ₁, hbe⟩ := Upd.holdsWrite_eval hc hU
      obtain ⟨τ', hs⟩ := STerm.delAt_returns_of_base hb hbe
      rw [Term.find_delAt_value_eval hq hs]
      exact Res.Le.refl _
  | findOnDelAtFrame hd =>
      simp only [Upd.coversRef] at hc
      obtain ⟨b, F, hb, τ₁, hbe⟩ := Upd.holdsWrite_eval hc hU
      obtain ⟨τ', hs⟩ := STerm.delAt_returns_of_base hb hbe
      rw [Term.find_delAt_frame_eval hd hs]
      exact Res.Le.refl _
  | lenOnSaveFrame hd =>
      simp only [Upd.coversRef] at hc
      obtain ⟨b, F, hb, τ₁, hbe⟩ := Upd.holdsWrite_eval hc hU
      obtain ⟨τ', hs⟩ := STerm.save_returns_of_base hb hbe
      rw [Term.len_save_frame_eval hd hs]
      exact Res.Le.refl _
  | lenOnDelAtFrame hd =>
      simp only [Upd.coversRef] at hc
      obtain ⟨b, F, hb, τ₁, hbe⟩ := Upd.holdsWrite_eval hc hU
      obtain ⟨τ', hs⟩ := STerm.delAt_returns_of_base hb hbe
      rw [Term.len_delAt_frame_eval hd hs]
      exact Res.Le.refl _

/-- A reference law in the right-hand sides of `{U}_m φ`, when the
rewritten update holds its storage operation. -/
def Fml.rwUpdRefTop (q : Term C × Term C) (m : Modality) (U : Upd C) (φ : Fml C) :
    Option (Fml C) :=
  if (U.rw q != U && (U.rw q).coversRef q) = true then some (.upd m (U.rw q) φ) else none

theorem Fml.rwUpdRefTop_sound {q : Term C × Term C} {r : TermTaclet q.1 q.2}
    (hr : TermTaclet.RefLaw r) {m : Modality} {U : Upd C} {φ ψ : Fml C}
    (h : Fml.rwUpdRefTop q m U φ = some ψ) (σ : State) (hψ : holds σ ψ) :
    holds σ (.upd m U φ) := by
  unfold Fml.rwUpdRefTop at h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true] at hc
    exact (Upd.rw_holds hr.evalRefines (fun _ _ hU => hr.back hc.2 hU) m φ σ).1 hψ
  · nomatch h

/-- A reference law in the update at position `i`. -/
def Fml.rwUpdRefAt (q : Term C × Term C) (i : Nat) : Fml C → Option (Fml C) :=
  Fml.atSpine (Fml.rwUpdRefTop q) i

/-- The law on the right-hand sides of `{U}_m φ` under any `m`, if it rewrites
one and both its terms read member-wise what one read is (`Term.base?`): the
two return alike in every state (`Term.base_eval`). -/
def Fml.rwUpdEqTop (q : Term C × Term C) (m : Modality) (U : Upd C) (φ : Fml C) : Option (Fml C) :=
  if (U.rw q != U && (Term.base? q.1).isSome && (Term.base? q.1 == Term.base? q.2)) = true then
    some (.upd m (U.rw q) φ)
  else none

theorem Fml.rwUpdEqTop_sound {q : Term C × Term C} {m : Modality} {U : Upd C} {φ ψ : Fml C}
    (h : Fml.rwUpdEqTop q m U φ = some ψ) (σ : State) (hψ : holds σ ψ) : holds σ (.upd m U φ) := by
  unfold Fml.rwUpdEqTop at h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at hc
    obtain ⟨⟨-, t', ht'⟩, he⟩ := hc
    have e1 := Term.base_eval q.1 ht'
    have e2 := Term.base_eval q.2 (he ▸ ht')
    exact (Upd.rw_holds (fun σ => ((e1 σ).trans (e2 σ).symm).le)
      (fun σ _ _ => ((e1 σ).trans (e2 σ).symm).ge) m φ σ).1 hψ
  · nomatch h

/-- The law on the right-hand sides of the update at position `i`, under any
modality, where its two terms are one read member-wise. -/
def Fml.rwUpdEqAt (q : Term C × Term C) (i : Nat) : Fml C → Option (Fml C) :=
  Fml.atSpine (Fml.rwUpdEqTop q) i

/-! ## The laws of memory reads

A memory read (`read`, `copyMem`, `copySt`) denotes its run (`Op2.opaque`),
so a law of one is no Theory equation (`TermTaclet`) but a refinement of the
interpreter: where the read returns, its replacement returns the same
(`Term.EvalRefines`, `EvalLaw.sound`).  Three resolve the copy examples:
`readOnWrite` (`readAddr_writeAddr_same`); `findCopyMem`, a member read out
of a memory object just copied into storage is read out of memory
(`copyMem_member`); and `readCopySt`, a member read out of a copy of a
storage struct is read out of storage (`copyStToM_member`).  Inside an update
over any modality the replacement may halt where the read did not, so the
update has to hold the write the law reads back (`Upd.coversEval`, as
`Upd.covers` for the storage laws): then the two return alike wherever the
update returns (`EvalLaw.back`). -/

section EvalLaws

variable (σ : State)

theorem Term.lit_eval (v : Value) : (Term.lit v : Term C).eval σ = .ok v := rfl
theorem Term.read_eval (m : MTerm C) (a : MAddr C) : (Term.read m a).eval σ = (do
    let τ ← m.eval σ
    let ad ← a.eval σ
    (← readAddr τ ad).asValue) := rfl
theorem MTerm.write_eval (m : MTerm C) (a : MAddr C) (v : MValT C) :
    (MTerm.write m a v).eval σ = (do
      let mv ← v.eval σ
      let τ ← m.eval σ
      let ad ← a.eval σ
      writeAddr τ mv ad) := rfl
theorem MValT.val_eval (t : Term C) : (MValT.val t).eval σ = (do pure (← t.eval σ).toMVal) := rfl
theorem SValT.copyMem_eval (m : MTerm C) (i : ITerm C) : (SValT.copyMem m i).eval σ = (do
    let τ ← m.eval σ
    let id ← i.eval σ
    Semantics.copyMem τ (.ref id)) := rfl
theorem MTerm.copySt_eval (m : MTerm C) (v : SValT C) : (MTerm.copySt m v).eval σ = (do
    let sv ← v.eval σ
    let τ ← m.eval σ
    return (← copyStToM τ sv).1) := rfl
theorem ITerm.copy_eval (m : MTerm C) (v : SValT C) : (ITerm.copy m v).eval σ = (do
    let sv ← v.eval σ
    let τ ← m.eval σ
    (← copyStToM τ sv).2.asRef) := rfl
theorem MAddr.field_eval (i : ITerm C) (f : Name) :
    (MAddr.field i f).eval σ = (do pure (.memoryField (← i.eval σ) f)) := rfl
theorem SValT.find_eval (s : STerm C) (p : PTerm C) : (SValT.find s p).eval σ = (do
    let τ ← s.eval σ
    let (r, segs) ← p.eval σ
    τ.findStorage r segs) := rfl
theorem PTerm.field_eval (p : PTerm C) (f : Name) : (PTerm.field p f).eval σ = (do
    let (r, segs) ← p.eval σ
    pure (r, segs ++ [.field f])) := rfl

theorem ITerm.alloc_eval (m : MTerm C) (R : RefTy) : (ITerm.alloc m R).eval σ = (do
    let τ ← m.eval σ
    return (← allocDefault τ R).2) := rfl
theorem MTerm.addM_eval (m : MTerm C) (R : RefTy) : (MTerm.addM m R).eval σ = (do
    let τ ← m.eval σ
    return (← allocDefault τ R).1) := rfl
theorem ITerm.read_eval (m : MTerm C) (a : MAddr C) : (ITerm.read m a).eval σ = (do
    let τ ← m.eval σ
    let ad ← a.eval σ
    (← readAddr τ ad).asRef) := rfl
theorem MAddr.at_eval (i : ITerm C) (k : Term C) : (MAddr.at i k).eval σ = (do
    let id ← i.eval σ
    pure (.memoryIndex id (← (← k.eval σ).asInt))) := rfl
theorem MValT.ref_eval (i : ITerm C) : (MValT.ref i).eval σ = (do pure (.ref (← i.eval σ))) := rfl


end EvalLaws

theorem Value.toMVal_asValue (v : Value) : v.toMVal.asValue = .ok v := by cases v <;> rfl

theorem PrimVal.asValue_eq (p : PrimVal) : (SVal.prim p).asValue = (MVal.prim p).asValue := by
  cases p <;> rfl

theorem SVal.strip_asValue (v : SVal) : v.strip.asValue = v.asValue := by cases v <;> rfl

theorem SVal.overlay_asValue (old new : SVal) : (old.overlay new).asValue = new.asValue := by
  cases old <;> cases new <;> first | rfl | exact SVal.strip_asValue _

theorem Close.layAt_asValue (old : SVal) (q : List Seg) (v : SVal) :
    (Close.layAt old q v).asValue = v.asValue := by
  induction q generalizing old with
  | nil => simp only [Close.layAt]; exact SVal.overlay_asValue old v
  | cons sg q ih =>
    cases sg with
    | «at» _ => cases old <;> simp only [Close.layAt] <;> exact SVal.strip_asValue v
    | field f =>
      cases old with
      | struct ofs =>
        simp only [Close.layAt]
        cases lookupBy f ofs with
        | none => exact SVal.strip_asValue v
        | some o => exact ih o
      | prim _ | array _ _ _ | map _ _ => simp only [Close.layAt]; exact SVal.strip_asValue v

/-- A member read at a word below a storage write reads the word written
there, whatever the write copied over. -/
theorem State.writeStorage_find_field {σ τ : State} {r : Name} {segs : List Seg} {sv : SVal}
    (h : σ.writeStorage r segs sv = .ok τ) (f : Name) :
    (τ.findStorage r (segs ++ [.field f]) >>= SVal.asValue) = (sv.find [.field f] >>= SVal.asValue) := by
  rw [State.findStorage_append]
  unfold State.writeStorage at h
  cases sv with
  | prim p =>
    rw [State.findStorage_saveStorage_same h]
    rfl
  | struct _ | array _ _ _ | map _ _ =>
    simp only [bind, Except.bind] at h
    cases hc : σ.findStorage r segs with
    | error e => rw [hc] at h; cases h
    | ok cur =>
      rw [hc] at h
      rw [State.findStorage_saveStorage_same h, Res.ok_bind', Close.find_overlay_fields _ _ _ rfl]
      cases SVal.find _ [Seg.field f] with
      | error _ => rfl
      | ok v => simp only [bind, Except.bind, Close.layAt_asValue]

/-- A member copied out of memory reads as the member in memory: a word as
the word, a reference as no word. -/
theorem Close.copyLeaf_asValue (σ : State) (id : Nat) (mv : MVal) (x : Value) :
    (Close.copyLeaf σ id mv >>= SVal.asValue) = .ok x ↔ mv.asValue = .ok x := by
  cases mv with
  | prim p => rw [Close.copyLeaf_prim, Res.ok_bind', PrimVal.asValue_eq]
  | ref id' =>
    unfold Close.copyLeaf
    rw [copyMToSt.eq_def]
    simp only
    constructor
    · intro h
      exfalso
      split at h
      · split at h
        · rename_i hmem _ fields hg
          rcases hcf : copyMFields σ (((List.map Prod.fst σ.heap).erase id).erase id') fields with _ | sf <;>
            simp [hcf, bind, Except.bind, SVal.asValue] at h
        · rename_i hmem _ elems fx hg
          rcases hcf : copyMElems σ (((List.map Prod.fst σ.heap).erase id).erase id') elems with _ | se <;>
            simp [hcf, bind, Except.bind, SVal.asValue] at h
        · simp [bind, Except.bind] at h
      · simp [bind, Except.bind] at h
    · intro h; cases h

/-! ### A rewrite at any sort, in every right-hand side

`Upd.rw` rewrites value terms and never enters a memory read, which is what
a Theory equation licenses.  A law of a memory read licenses more: it is a
refinement of the interpreter at its own sort, so it rewrites inside a
memory read and in a memory or identity right-hand side too (`Tm.rwEv`),
with the same two directions as `Upd.rw_holds`. -/

section RwEvUpd

variable {u : Srt} {q : Tm C u × Tm C u}

/-- Every right-hand side of an update, rewritten at the sort of `q` (`Tm.rwEv`). -/
def Upd.rwEv (q : Tm C u × Tm C u) (U : Upd C) : Upd C :=
  U.map (·.mapTm fun {_} t => t.rwEv q)

theorem UpdElem.mapTm_write_le (hq : Tm.EvalRefinesAt q.1 q.2) (σ₀ τ : State) :
    (e : UpdElem C) → Res.Le (e.write σ₀ τ) ((e.mapTm fun {_} t => t.rwEv q).write σ₀ τ)
  | .val _ t | .path _ t | .mref _ t | .storage t | .store _ t | .memory t =>
    Res.Le.bind (Tm.rwEv_eval hq t σ₀) fun _ => Res.Le.refl _
  | .net r _ a | .pay r a =>
    Res.Le.bind (Tm.rwEv_eval hq r σ₀) fun _ => Res.Le.bind (Res.Le.refl _) fun _ =>
      Res.Le.bind (Tm.rwEv_eval hq a σ₀) fun _ => Res.Le.refl _
  | .selfBalance _ a => Res.Le.bind (Tm.rwEv_eval hq a σ₀) fun _ => Res.Le.refl _
  | .saveNet _ => Res.Le.refl _

theorem UpdElem.mapTm_write_rev {σ₀ : State} (hq : Srt.Le u (q.2.eval σ₀) (q.1.eval σ₀))
    (τ : State) :
    (e : UpdElem C) → Res.Le ((e.mapTm fun {_} t => t.rwEv q).write σ₀ τ) (e.write σ₀ τ)
  | .val _ t | .path _ t | .mref _ t | .storage t | .store _ t | .memory t =>
    Res.Le.bind (Tm.rwEv_eval_rev hq t) fun _ => Res.Le.refl _
  | .net r _ a | .pay r a =>
    Res.Le.bind (Tm.rwEv_eval_rev hq r) fun _ => Res.Le.bind (Res.Le.refl _) fun _ =>
      Res.Le.bind (Tm.rwEv_eval_rev hq a) fun _ => Res.Le.refl _
  | .selfBalance _ a => Res.Le.bind (Tm.rwEv_eval_rev hq a) fun _ => Res.Le.refl _
  | .saveNet _ => Res.Le.refl _

theorem Upd.rwEv_foldl (hq : Tm.EvalRefinesAt q.1 q.2) (σ₀ : State) :
    (U : Upd C) → ∀ ρ, Res.Le (U.foldlM (fun τ e => e.write σ₀ τ) ρ)
      ((U.rwEv q).foldlM (fun τ e => e.write σ₀ τ) ρ)
  | [], _ => Res.Le.refl _
  | e :: U, ρ => by
    simp only [Upd.rwEv, List.map_cons, List.foldlM_cons]
    exact Res.Le.bind (UpdElem.mapTm_write_le hq σ₀ ρ e) fun ρ' => Upd.rwEv_foldl hq σ₀ U ρ'

theorem Upd.rwEv_foldl_rev {σ₀ : State} (hq : Srt.Le u (q.2.eval σ₀) (q.1.eval σ₀)) :
    (U : Upd C) → ∀ ρ, Res.Le ((U.rwEv q).foldlM (fun τ e => e.write σ₀ τ) ρ)
      (U.foldlM (fun τ e => e.write σ₀ τ) ρ)
  | [], _ => Res.Le.refl _
  | e :: U, ρ => by
    simp only [Upd.rwEv, List.map_cons, List.foldlM_cons]
    exact Res.Le.bind (UpdElem.mapTm_write_rev hq ρ e) fun ρ' => Upd.rwEv_foldl_rev hq U ρ'

theorem Upd.rwEv_apply (hq : Tm.EvalRefinesAt q.1 q.2) (U : Upd C) (σ : State) :
    Res.Le (U.apply σ) ((U.rwEv q).apply σ) :=
  Upd.rwEv_foldl hq σ U σ

theorem Upd.rwEv_apply_rev {σ : State} (hq : Srt.Le u (q.2.eval σ) (q.1.eval σ)) (U : Upd C) :
    Res.Le ((U.rwEv q).apply σ) (U.apply σ) :=
  Upd.rwEv_foldl_rev hq U σ

/-- **A rewrite at any sort inside an update, under any modality**
(`Upd.rw_holds` for `Tm.rwEv`): `q.2` returns what `q.1` returns, and
wherever the rewritten update returns, `q.1` returns what `q.2` does. -/
theorem Upd.rwEv_holds (hq : Tm.EvalRefinesAt q.1 q.2) {U : Upd C}
    (hb : ∀ σ τ, (U.rwEv q).apply σ = .ok τ → Srt.Le u (q.2.eval σ) (q.1.eval σ))
    (m : Modality) (ψ : Fml C) (σ : State) :
    holds σ (.upd m (U.rwEv q) ψ) ↔ holds σ (.upd m U ψ) := by
  simp only [holds]
  cases hU : U.apply σ with
  | ok τ => rw [Upd.rwEv_apply hq U σ τ hU]
  | error e =>
    cases hU' : (U.rwEv q).apply σ with
    | ok τ' =>
      rw [Upd.rwEv_apply_rev (hb σ τ' hU') U τ' hU'] at hU
      cases hU
    | error e' => exact Iff.rfl

end RwEvUpd

/-- The law on the right-hand sides of `{U}_m φ` under any `m`, inside a memory
term too (`Upd.rwEv`), if it rewrites one and the rewritten update holds the
write the law reads back. -/
def Fml.rwUpdCoveredTop (q : Term C × Term C) (m : Modality) (U : Upd C) (φ : Fml C) :
    Option (Fml C) :=
  if (U.rwEv q != U && (U.rwEv q).covers q) = true then some (.upd m (U.rwEv q) φ) else none

theorem Fml.rwUpdCoveredTop_sound {q : Term C × Term C} (hq : Term.EvalRefines q.1 q.2)
    {m : Modality} {U : Upd C} {φ ψ : Fml C} (h : Fml.rwUpdCoveredTop q m U φ = some ψ)
    (σ : State) (hψ : holds σ ψ) : holds σ (.upd m U φ) := by
  unfold Fml.rwUpdCoveredTop at h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true] at hc
    exact (Upd.rwEv_holds (u := .val) hq.at (fun _ _ hU => Upd.covers_le hq hc.2 hU) m φ σ).1 hψ
  · nomatch h

/-- The law on the right-hand sides of the update at position `i`, under any
modality, where that update holds the write the law reads back. -/
def Fml.rwUpdCoveredAt (q : Term C × Term C) (i : Nat) : Fml C → Option (Fml C) :=
  Fml.atSpine (Fml.rwUpdCoveredTop q) i

/-! ### The side conditions of the memory laws

A read below a fresh allocation `addM(m, R)` resolves syntactically: the
path at which the address reads below the fresh root (`Tm.freshPath?`)
names the member, and the declared type at that path (`RefTy.memberTy`)
says what the default copy holds there (`copyStToM_default_readPath`,
`Calculus/ReadWrite.lean`).  A read that does not look into the fresh
object is one whose identity was allocated strictly earlier on the memory
spine (`Tm.boundedIn`), and a read past a write at an address that never
meets it (`MAddr.apart?`).  Each is a `Bool`, so that `rfl` decides it where
a law is applied, with a soundness lemma by sort. -/

/-- The path at which a term reads below the root `addM(m, R)` allocates:
`freshId(addM(m, R))` is the root, `read(addM(m, R), i.f)` the member `f` of
what `i` reads, `i.f` and `i[k]` (a literal `k`) the path one step down. -/
def Tm.freshPath? : Tm C u → MTerm C → RefTy → Option (List Seg)
  | .app1 (.alloc R') m', m, R => if m' == m && R' == R then some [] else none
  | .app2 .iread M a, m, R => if M == MTerm.addM m R then a.freshPath? m R else none
  | .app1 (.mfield f) i, m, R => (i.freshPath? m R).map (· ++ [.field f])
  | .app2 .mat i (.app0 (.lit (.int k))), m, R => (i.freshPath? m R).map (· ++ [.at k])
  | _, _, _ => none

/-- What a term at a fresh path reads, by sort: an identity is what the path
reads in the fresh object, and it reads where the declared type is a
reference; an address reads what the path reads, and it reads where the
path is declared. -/
def FreshRead (σ μ₁ : State) (root : Nat) (R : RefTy) (p : List Seg) : {u : Srt} → Tm C u → Prop
  | .ident, t => (∀ id, t.eval σ = .ok id → μ₁.readPath root p = .ok (.ref id)) ∧
      (∀ R', (Ty.ref R).memberTy p = some (.ref R') → ∃ id, t.eval σ = .ok id)
  | .addr, t => (∀ ad, t.eval σ = .ok ad → readAddr μ₁ ad = μ₁.readPath root p) ∧
      (∀ T', (Ty.ref R).memberTy p = some T' → ∃ ad, t.eval σ = .ok ad)
  | _, _ => True

theorem Ty.memberTy_snoc_some {T T' : Ty} {p : List Seg} {s : Seg}
    (h : T.memberTy (p ++ [s]) = some T') : ∃ R', T.memberTy p = some (.ref R') := by
  rw [Ty.memberTy_append] at h
  cases hp : T.memberTy p with
  | none => simp [hp] at h
  | some T'' =>
    cases T'' with
    | prim q => simp [hp, Ty.memberTy, Ty.at_prim] at h
    | ref R' => exact ⟨R', rfl⟩

theorem Tm.freshPath_eval {m : MTerm C} {R : RefTy} {σ μ₀ μ₁ : State} {root : Nat}
    (hm : m.eval σ = .ok μ₀) (ha : allocDefault μ₀ R = .ok (μ₁, root)) (t : Tm C u) :
    ∀ {p : List Seg}, t.freshPath? m R = some p → FreshRead σ μ₁ root R p t := by
  induction t with
  | pvV x | pvP x | pvS x | pvI x | app0 o | app3 o a b c =>
    intro p h
    simp only [Tm.freshPath?] at h <;> nomatch h
  | app1 o a ih =>
    intro p h
    cases o with
    | alloc R' =>
      simp only [Tm.freshPath?] at h
      split at h
      · rename_i hmR
        simp only [Bool.and_eq_true, beq_iff_eq] at hmR
        obtain ⟨rfl, rfl⟩ := hmR
        cases h
        refine ⟨fun id hid => ?_, fun R' _ => ?_⟩
        · rw [ITerm.alloc_eval, hm, Res.ok_bind', ha] at hid
          cases hid
          rfl
        · exact ⟨root, by rw [ITerm.alloc_eval, hm, Res.ok_bind', ha]; rfl⟩
      · nomatch h
    | mfield f =>
      simp only [Tm.freshPath?, Option.map_eq_some_iff] at h
      obtain ⟨p', hp', rfl⟩ := h
      obtain ⟨ih1, ih2⟩ := ih hp'
      refine ⟨fun ad had => ?_, fun T' hT' => ?_⟩
      · rw [MAddr.field_eval] at had
        obtain ⟨id, hid, had⟩ := bind_ok_inv had
        simp only [pure, Except.pure, Except.ok.injEq] at had
        subst had
        have h1 : MVal.readPath μ₁ (.ref root) p' = .ok (.ref id) := ih1 id hid
        simp only [State.readPath, MVal.readPath_snoc, h1, Res.ok_bind']
        rfl
      · obtain ⟨R'', hR''⟩ := Ty.memberTy_snoc_some hT'
        obtain ⟨id, hid⟩ := ih2 R'' hR''
        exact ⟨_, by rw [MAddr.field_eval, hid]; rfl⟩
    | unop _ _ | net | netOf _ | field _ | next | select _ | sval | newArr _ | addM _ | mval | ref
    | delValue | wt _ =>
      simp only [Tm.freshPath?] at h <;> nomatch h
  | app2 o a b iha ihb =>
    intro p h
    cases o with
    | iread =>
      simp only [Tm.freshPath?] at h
      split at h
      · rename_i hM
        simp only [beq_iff_eq] at hM
        subst hM
        obtain ⟨ih1, ih2⟩ := ihb h
        have hμ : (MTerm.addM m R).eval σ = .ok μ₁ := by
          rw [MTerm.addM_eval, hm, Res.ok_bind', ha]; rfl
        refine ⟨fun id hid => ?_, fun R' hR' => ?_⟩
        · rw [ITerm.read_eval, hμ, Res.ok_bind'] at hid
          obtain ⟨ad, had, hid⟩ := bind_ok_inv hid
          rw [ih1 ad had] at hid
          obtain ⟨mv, hmv, hid⟩ := bind_ok_inv hid
          cases mv with
          | prim _ => simp [MVal.asRef] at hid
          | ref id' =>
            simp only [MVal.asRef, pure, Except.pure, Except.ok.injEq] at hid
            subst hid
            exact hmv
        · obtain ⟨ad, had⟩ := ih2 _ hR'
          obtain ⟨mv', hmv', hd⟩ :=
            (copyStToM_default_readPath p (Close.allocDefault_copy ha) (State.HeapExt.refl μ₁)).2 _ hR'
          obtain ⟨id, rfl, -⟩ := hd
          refine ⟨id, ?_⟩
          rw [ITerm.read_eval, hμ, Res.ok_bind', had, Res.ok_bind', ih1 ad had]
          simp only [State.readPath]
          rw [hmv']
          rfl
      · nomatch h
    | mat =>
      cases b with
      | app0 o' =>
        cases o' with
        | lit v =>
          cases v with
          | int k =>
            simp only [Tm.freshPath?, Option.map_eq_some_iff] at h
            obtain ⟨p', hp', rfl⟩ := h
            obtain ⟨ih1, ih2⟩ := iha hp'
            refine ⟨fun ad had => ?_, fun T' hT' => ?_⟩
            · rw [MAddr.at_eval] at had
              obtain ⟨id, hid, had⟩ := bind_ok_inv had
              simp only [Term.lit_eval, Res.ok_bind', Value.asInt, pure, Except.pure,
                Except.ok.injEq] at had
              subst had
              have h1 : MVal.readPath μ₁ (.ref root) p' = .ok (.ref id) := ih1 id hid
              simp only [State.readPath, MVal.readPath_snoc, h1, Res.ok_bind']
              rfl
            · obtain ⟨R'', hR''⟩ := Ty.memberTy_snoc_some hT'
              obtain ⟨id, hid⟩ := ih2 R'' hR''
              exact ⟨_, by rw [MAddr.at_eval, hid]; rfl⟩
          | bool _ => simp only [Tm.freshPath?] at h <;> nomatch h
        | env _ => simp only [Tm.freshPath?] at h <;> nomatch h
      | pvV _ | app1 _ _ | app2 _ _ _ | app3 _ _ _ _ => simp only [Tm.freshPath?] at h <;> nomatch h
    | binop _ _ | find | len | read | mlen | «at» | delAt | pushSlot _ | pop | shrink | extend _
    | sfind | copyMem | copy | copySt | nextIn =>
      simp only [Tm.freshPath?] at h <;> nomatch h

/-- A memory term on the memory spine of `t` leaves a counter `t` only advances. -/
theorem Tm.onMemSpine_nextId_le {s : MTerm C} {σ μs : State} (hs : s.eval σ = .ok μs) :
    (t : MTerm C) → t.onMemSpine s = true → ∀ {μt : State}, t.eval σ = .ok μt →
      μs.nextId ≤ μt.nextId
  | .app1 (.addM R) a, h, μt, ht => by
    simp only [Tm.onMemSpine, Tm.memSpineAny, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · rw [hs] at ht; cases ht; exact Nat.le_refl _
    · rw [MTerm.addM_eval] at ht
      obtain ⟨τ, hτ, ht⟩ := bind_ok_inv ht
      obtain ⟨⟨μ', id⟩, hal, ht⟩ := bind_ok_inv ht
      cases ht
      exact Nat.le_trans (Tm.onMemSpine_nextId_le hs a h hτ) (allocDefault_nextId hal)
  | .app2 .copySt a v, h, μt, ht => by
    simp only [Tm.onMemSpine, Tm.memSpineAny, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · rw [hs] at ht; cases ht; exact Nat.le_refl _
    · rw [MTerm.copySt_eval] at ht
      obtain ⟨sv, -, ht⟩ := bind_ok_inv ht
      obtain ⟨τ, hτ, ht⟩ := bind_ok_inv ht
      obtain ⟨⟨μ', mv⟩, hc, ht⟩ := bind_ok_inv ht
      cases ht
      exact Nat.le_trans (Tm.onMemSpine_nextId_le hs a h hτ) (copyStToM_nextId τ sv _ _ hc)
  | .app3 .write a p v, h, μt, ht => by
    simp only [Tm.onMemSpine, Tm.memSpineAny, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · rw [hs] at ht; cases ht; exact Nat.le_refl _
    · rw [MTerm.write_eval] at ht
      obtain ⟨mv, -, ht⟩ := bind_ok_inv ht
      obtain ⟨τ, hτ, ht⟩ := bind_ok_inv ht
      obtain ⟨ad, -, ht⟩ := bind_ok_inv ht
      rw [Close.writeAddr_nextId ht]
      exact Tm.onMemSpine_nextId_le hs a h hτ
  | .app0 .memory, h, μt, ht => by
    simp only [Tm.onMemSpine, Tm.memSpineAny, beq_iff_eq] at h
    subst h
    rw [hs] at ht; cases ht; exact Nat.le_refl _

/-- The identity a term reads is allocated strictly earlier on `M`'s memory
spine: a root `freshId(addM(m₀, R₀))` or `freshId(copySt(m₀, v))` whose
allocation `M` performs, or a reference member of a fresh root read out of
that allocation; an address is bounded where its identity is. -/
def Tm.boundedIn : Tm C u → MTerm C → Bool
  | .app1 (.alloc R₀) m₀, M => M.onMemSpine (.addM m₀ R₀)
  | .app2 .copy m₀ v, M => M.onMemSpine (.copySt m₀ v)
  | .app2 .iread (.app1 (.addM R₀) m₀) (.app1 (.mfield _) i), M =>
    M.onMemSpine (.addM m₀ R₀) && (i.freshPath? m₀ R₀).isSome
  | .app2 .iread (.app1 (.addM R₀) m₀) (.app2 .mat i _), M =>
    M.onMemSpine (.addM m₀ R₀) && (i.freshPath? m₀ R₀).isSome
  | .app1 (.mfield _) i, M => i.boundedIn M
  | .app2 .mat i _, M => i.boundedIn M
  | _, _ => false

/-- What a bounded term reads, by sort: an identity below the counter `M` leaves. -/
def BoundedRead (σ μ : State) : {u : Srt} → Tm C u → Prop
  | .ident, t => ∀ id, t.eval σ = .ok id → id < μ.nextId
  | .addr, t => ∀ ad, t.eval σ = .ok ad → ad.id < μ.nextId
  | _, _ => True

/-- A reference member of a fresh root, read out of the allocation, is below
the counter the allocation leaves. -/
theorem freshRoot_read_lt {m₀ : MTerm C} {R₀ : RefTy} {i : ITerm C} {σ μ₁ : State}
    (hp : (i.freshPath? m₀ R₀).isSome = true) (hμ : (MTerm.addM m₀ R₀).eval σ = .ok μ₁)
    {id₀ : Nat} (hi : i.eval σ = .ok id₀) {s : Seg} {id : Nat}
    (hr : readAddr μ₁ (.ofSeg id₀ s) = .ok (.ref id)) : id < μ₁.nextId := by
  rw [MTerm.addM_eval] at hμ
  obtain ⟨μ₀, hm, hμ⟩ := bind_ok_inv hμ
  obtain ⟨⟨μ₁', root⟩, ha, hμ⟩ := bind_ok_inv hμ
  cases hμ
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hp
  have h1 := (Tm.freshPath_eval hm ha i hp).1 id₀ hi
  have hpath : μ₁'.readPath root (p ++ [s]) = .ok (.ref id) := by
    simp only [State.readPath, MVal.readPath_snoc] at h1 ⊢
    rw [h1, Res.ok_bind']
    exact hr
  obtain ⟨T', -, hd⟩ :=
    (copyStToM_default_readPath (p ++ [s]) (Close.allocDefault_copy ha) (State.HeapExt.refl μ₁')).1 _ hpath
  cases T' with
  | prim q => cases q <;> simp [DefaultMVal, PrimTy.default, Value.toMVal] at hd
  | ref _ =>
    obtain ⟨id', hid', hlt⟩ := hd
    cases hid'
    exact hlt

theorem Tm.boundedIn_eval {M : MTerm C} {σ μ : State} (hM : M.eval σ = .ok μ) (t : Tm C u) :
    t.boundedIn M = true → BoundedRead σ μ t := by
  induction t with
  | pvV x | pvP x | pvS x | pvI x | app0 o | app3 o a b c =>
    intro h
    simp only [Tm.boundedIn] at h <;> nomatch h
  | app1 o a ih =>
    intro h
    cases o with
    | alloc R₀ =>
      intro id hid
      simp only [Tm.boundedIn] at h
      rw [ITerm.alloc_eval] at hid
      obtain ⟨μ₀, hm, hid⟩ := bind_ok_inv hid
      obtain ⟨⟨μ₁, id'⟩, ha, hid⟩ := bind_ok_inv hid
      cases hid
      have hμ₁ : (MTerm.addM a R₀).eval σ = .ok μ₁ := by
        rw [MTerm.addM_eval, hm, Res.ok_bind', ha]; rfl
      exact Nat.lt_of_lt_of_le (allocDefault_id_lt ha) (Tm.onMemSpine_nextId_le hμ₁ M h hM)
    | mfield f =>
      intro ad had
      simp only [Tm.boundedIn] at h
      rw [MAddr.field_eval] at had
      obtain ⟨id, hi, had⟩ := bind_ok_inv had
      simp only [pure, Except.pure, Except.ok.injEq] at had
      subst had
      exact ih h id hi
    | unop _ _ | net | netOf _ | field _ | next | select _ | sval | newArr _ | addM _ | mval | ref
    | delValue | wt _ =>
      simp only [Tm.boundedIn] at h <;> nomatch h
  | app2 o a b iha ihb =>
    intro h
    cases o with
    | copy =>
      intro id hid
      simp only [Tm.boundedIn] at h
      rw [ITerm.copy_eval] at hid
      obtain ⟨sv, hv, hid⟩ := bind_ok_inv hid
      obtain ⟨μ₀, hm, hid⟩ := bind_ok_inv hid
      obtain ⟨⟨μ₁, mv⟩, hc, hid⟩ := bind_ok_inv hid
      cases mv with
      | prim _ => simp [MVal.asRef] at hid
      | ref id' =>
        simp only [MVal.asRef, pure, Except.pure, Except.ok.injEq] at hid
        subst hid
        have hμ₁ : (MTerm.copySt a b).eval σ = .ok μ₁ := by
          rw [MTerm.copySt_eval, hv, Res.ok_bind', hm, Res.ok_bind', hc]; rfl
        exact Nat.lt_of_lt_of_le (copyStToM_ref_lt hc) (Tm.onMemSpine_nextId_le hμ₁ M h hM)
    | mat =>
      intro ad had
      simp only [Tm.boundedIn] at h
      rw [MAddr.at_eval] at had
      obtain ⟨id, hi, had⟩ := bind_ok_inv had
      obtain ⟨kv, -, had⟩ := bind_ok_inv had
      obtain ⟨kn, -, had⟩ := bind_ok_inv had
      simp only [pure, Except.pure, Except.ok.injEq] at had
      subst had
      exact iha h id hi
    | iread =>
      intro id hid
      cases a with
      | app1 o₁ m₀ =>
        cases o₁ with
        | addM R₀ =>
          rw [ITerm.read_eval] at hid
          obtain ⟨μ₁, hμ₁, hid⟩ := bind_ok_inv hid
          obtain ⟨ad, had, hid⟩ := bind_ok_inv hid
          obtain ⟨mv, hmv, hid⟩ := bind_ok_inv hid
          cases mv with
          | prim _ => simp [MVal.asRef] at hid
          | ref id' =>
            simp only [MVal.asRef, pure, Except.pure, Except.ok.injEq] at hid
            subst hid
            cases b with
            | app0 o₀ => nomatch o₀
            | app3 o₃ _ _ _ => nomatch o₃
            | app1 o₂ i =>
              cases o₂ with
              | mfield f =>
                simp only [Tm.boundedIn, Bool.and_eq_true] at h
                rw [MAddr.field_eval] at had
                obtain ⟨id₀, hi, had⟩ := bind_ok_inv had
                simp only [pure, Except.pure, Except.ok.injEq] at had
                subst had
                exact Nat.lt_of_lt_of_le (freshRoot_read_lt h.2 hμ₁ hi (s := .field f) hmv)
                  (Tm.onMemSpine_nextId_le hμ₁ M h.1 hM)
            | app2 o₂ i k =>
              cases o₂ with
              | mat =>
                simp only [Tm.boundedIn, Bool.and_eq_true] at h
                rw [MAddr.at_eval] at had
                obtain ⟨id₀, hi, had⟩ := bind_ok_inv had
                obtain ⟨kv, -, had⟩ := bind_ok_inv had
                obtain ⟨kn, -, had⟩ := bind_ok_inv had
                simp only [pure, Except.pure, Except.ok.injEq] at had
                subst had
                exact Nat.lt_of_lt_of_le (freshRoot_read_lt h.2 hμ₁ hi (s := .at kn) hmv)
                  (Tm.onMemSpine_nextId_le hμ₁ M h.1 hM)
      | app0 _ | app2 _ _ _ | app3 _ _ _ _ => simp only [Tm.boundedIn] at h <;> nomatch h
    | binop _ _ | find | len | read | mlen | «at» | delAt | pushSlot _ | pop | shrink | extend _
    | sfind | copyMem | copySt | nextIn =>
      simp only [Tm.boundedIn] at h <;> nomatch h

/-- Two memory addresses that never meet: different members, a member and
an element, elements of one object at different literal indices. -/
def MAddr.apart? : MAddr C → MAddr C → Bool
  | .app1 (.mfield f) _, .app1 (.mfield g) _ => f != g
  | .app1 (.mfield _) _, .app2 .mat _ _ => true
  | .app2 .mat _ _, .app1 (.mfield _) _ => true
  | .app2 .mat i (.app0 (.lit (.int k))), .app2 .mat j (.app0 (.lit (.int k'))) => i == j && k != k'
  | _, _ => false

theorem MAddr.apart?_eval {σ : State} (a b : MAddr C) (h : a.apart? b = true) {ad bd : Addr}
    (ha : a.eval σ = .ok ad) (hb : b.eval σ = .ok bd) : Close.Apart ad bd := by
  unfold MAddr.apart? at h
  split at h
  · rename_i f i g j
    simp only [bne_iff_ne, ne_eq] at h
    rw [MAddr.field_eval] at ha hb
    obtain ⟨id, -, ha⟩ := bind_ok_inv ha
    obtain ⟨id', -, hb⟩ := bind_ok_inv hb
    simp only [pure, Except.pure, Except.ok.injEq] at ha hb
    subst ha hb
    exact Or.inr fun h' => h h'.symm
  · rename_i f i j k
    rw [MAddr.field_eval] at ha
    rw [MAddr.at_eval] at hb
    obtain ⟨id, -, ha⟩ := bind_ok_inv ha
    obtain ⟨id', -, hb⟩ := bind_ok_inv hb
    obtain ⟨kv, -, hb⟩ := bind_ok_inv hb
    obtain ⟨kn, -, hb⟩ := bind_ok_inv hb
    simp only [pure, Except.pure, Except.ok.injEq] at ha hb
    subst ha hb
    trivial
  · rename_i i k g j
    rw [MAddr.at_eval] at ha
    rw [MAddr.field_eval] at hb
    obtain ⟨id, -, ha⟩ := bind_ok_inv ha
    obtain ⟨kv, -, ha⟩ := bind_ok_inv ha
    obtain ⟨kn, -, ha⟩ := bind_ok_inv ha
    obtain ⟨id', -, hb⟩ := bind_ok_inv hb
    simp only [pure, Except.pure, Except.ok.injEq] at ha hb
    subst ha hb
    trivial
  · rename_i i k j k'
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    obtain ⟨rfl, hk⟩ := h
    rw [MAddr.at_eval] at ha hb
    obtain ⟨id, hi, ha⟩ := bind_ok_inv ha
    obtain ⟨id', hi', hb⟩ := bind_ok_inv hb
    rw [hi] at hi'
    cases hi'
    simp only [Term.lit_eval, Res.ok_bind', Value.asInt, pure, Except.pure, Except.ok.injEq] at ha hb
    subst ha hb
    exact Or.inr fun h' => hk h'.symm
  · nomatch h

/-- A law of a memory read, at the value or the identity sort: where the
read returns, the replacement returns the same (`EvalLaw.sound`). -/
inductive EvalLaw : {u : Srt} → Tm C u → Tm C u → Prop
  /-- **`readOnWrite`**: `read(write(m, a, v), a) ⇝ v` (`readAddr_writeAddr_same`). -/
  | readOnWrite {m : MTerm C} {a : MAddr C} {v : Value} :
      EvalLaw (Term.read (.write m a (.val (.lit v))) a) (Term.lit v)
  /-- **`findCopyMem`**: a member read out of a memory object copied into
  storage is read out of memory,
  `find(save(s, p, copyMem(mtSt, m, i)), p.f) ⇝ read(m, i.f)` (`copyMem_member`). -/
  | findCopyMem {s : STerm C} {p : PTerm C} {m : MTerm C} {i : ITerm C} {f : Name}
      (hf : (f == "length") = false := by rfl) :
      EvalLaw (Term.find (.save s p (.copyMem m i)) (.field p f)) (Term.read m (.field i f))
  /-- **`readCopySt`**: a member read out of a copy of a storage struct is
  read out of storage,
  `read(copySt(m, find(s, p)), freshId(copySt(m, find(s, p))).f) ⇝ find(s, p.f)`
  (`copyStToM_member`). -/
  | readCopySt {m : MTerm C} {s : STerm C} {p : PTerm C} {f : Name}
      (hf : (f == "length") = false := by rfl) :
      EvalLaw (Term.read (.copySt m (.find s p)) (.field (.copy m (.find s p)) f))
        (Term.find s (.field p f))
  /-- **`readAddEqual`**: a primitive member or fixed element of a fresh
  object holds its type's default, `read(addM(m, R), a) ⇝ default`, where
  `a` reads at a fresh path of the allocation whose declared type is the
  primitive (`copyStToM_default_readPath`). -/
  | readAddEqual {m : MTerm C} {R : RefTy} {a : MAddr C} {q : PrimTy}
      (h : (a.freshPath? m R).bind (Ty.ref R).memberTy = some (.prim q) := by rfl) :
      EvalLaw (Term.read (.addM m R) a) (Term.lit (PrimTy.default q))
  /-- **`readAddDifferent`**: an allocation leaves every object allocated
  before it, `read(addM(m, R), a) ⇝ read(m, a)` where `a`'s identity is
  allocated strictly earlier on `m`'s spine (`Tm.boundedIn`, `readAddr_heapExt`). -/
  | readAddDifferent {m : MTerm C} {R : RefTy} {a : MAddr C} (h : a.boundedIn m = true := by rfl) :
      EvalLaw (Term.read (.addM m R) a) (Term.read m a)
  /-- **`readAddDifferentIdentity`**: `readAddDifferent` at the identity sort. -/
  | readAddDifferentIdentity {m : MTerm C} {R : RefTy} {a : MAddr C}
      (h : a.boundedIn m = true := by rfl) :
      EvalLaw (ITerm.read (.addM m R) a) (ITerm.read m a)
  /-- **`readWriteDifferent`**: a write leaves every other address,
  `read(write(m, a, v), b) ⇝ read(m, b)` where `a` and `b` never meet
  (`MAddr.apart?`, `writeAddr_setObj`). -/
  | readWriteDifferent {m : MTerm C} {a b : MAddr C} {v : MValT C}
      (h : a.apart? b = true := by rfl) :
      EvalLaw (Term.read (.write m a v) b) (Term.read m b)
  /-- **`readWriteDifferentIdentity`**: `readWriteDifferent` at the identity sort. -/
  | readWriteDifferentIdentity {m : MTerm C} {a b : MAddr C} {v : MValT C}
      (h : a.apart? b = true := by rfl) :
      EvalLaw (ITerm.read (.write m a v) b) (ITerm.read m b)
  /-- **`readOnWriteIdentity`**: `readOnWrite` at the identity sort,
  `read(write(m, a, ref(i)), a) ⇝ i` (`readAddr_writeAddr_same`). -/
  | readOnWriteIdentity {m : MTerm C} {a : MAddr C} {i : ITerm C} :
      EvalLaw (ITerm.read (.write m a (.ref i)) a) i

section EvalLawSound

variable {σ : State}

theorem Res.ok_inj {α : Type} {a b : α} (h : (Except.ok a : Res α) = .ok b) : a = b :=
  Except.ok.inj h

theorem EvalLaw.readOnWrite_le {m : MTerm C} {a : MAddr C} {v : Value} {τ : State}
    (hw : (MTerm.write m a (.val (.lit v))).eval σ = .ok τ) :
    (Term.read (.write m a (.val (.lit v))) a).eval σ = .ok v := by
  rw [Term.read_eval, hw, Res.ok_bind']
  rw [MTerm.write_eval, MValT.val_eval, Term.lit_eval] at hw
  simp only [Res.ok_bind', pure, Except.pure] at hw
  obtain ⟨τ₀, -, hw⟩ := bind_ok_inv hw
  obtain ⟨ad, had, hw⟩ := bind_ok_inv hw
  rw [had, Res.ok_bind', Close.readAddr_writeAddr_same hw, Res.ok_bind', Value.toMVal_asValue]

theorem EvalLaw.findCopyMem_eval {s : STerm C} {p : PTerm C} {m : MTerm C} {i : ITerm C} {f : Name}
    (hf : (f == "length") = false) {τ : State}
    (hw : (STerm.save s p (.copyMem m i)).eval σ = .ok τ) :
    Res.Le ((Term.find (.save s p (.copyMem m i)) (.field p f)).eval σ)
        ((Term.read m (.field i f)).eval σ) ∧
      Res.Le ((Term.read m (.field i f)).eval σ)
        ((Term.find (.save s p (.copyMem m i)) (.field p f)).eval σ) := by
  have hf' : f ≠ "length" := by simpa using hf
  rw [Term.find_eval, hw, Res.ok_bind', PTerm.field_eval]
  rw [STerm.save_eval, SValT.copyMem_eval] at hw
  obtain ⟨sv, hsv, hw⟩ := bind_ok_inv hw
  obtain ⟨τm, hm, hsv⟩ := bind_ok_inv hsv
  obtain ⟨id, hi, hsv⟩ := bind_ok_inv hsv
  obtain ⟨τs, -, hw⟩ := bind_ok_inv hw
  obtain ⟨⟨r, segs⟩, hp, hw⟩ := bind_ok_inv hw
  rw [hp, Term.read_eval, hm, Res.ok_bind', MAddr.field_eval, hi]
  simp only [Res.ok_bind', pure, Except.pure]
  rw [State.writeStorage_find_field hw f, Close.copyMem_member hsv hf']
  cases readAddr τm (.memoryField id f) with
  | error _ => exact ⟨Res.Le.refl _, Res.Le.refl _⟩
  | ok mv =>
    simp only [Res.ok_bind']
    exact ⟨fun x hx => (Close.copyLeaf_asValue τm id mv x).1 hx,
      fun x hx => (Close.copyLeaf_asValue τm id mv x).2 hx⟩

theorem EvalLaw.readCopySt_eval {m : MTerm C} {s : STerm C} {p : PTerm C} {f : Name}
    (hf : (f == "length") = false) {μ : State}
    (hw : (MTerm.copySt m (.find s p)).eval σ = .ok μ) :
    Res.Le ((Term.read (.copySt m (.find s p)) (.field (.copy m (.find s p)) f)).eval σ)
        ((Term.find s (.field p f)).eval σ) ∧
      Res.Le ((Term.find s (.field p f)).eval σ)
        ((Term.read (.copySt m (.find s p)) (.field (.copy m (.find s p)) f)).eval σ) := by
  have hf' : f ≠ "length" := by simpa using hf
  rw [Term.read_eval, hw, Res.ok_bind', MAddr.field_eval, ITerm.copy_eval]
  rw [MTerm.copySt_eval] at hw
  obtain ⟨sv, hsv, hw⟩ := bind_ok_inv hw
  obtain ⟨τm, hm, hw⟩ := bind_ok_inv hw
  obtain ⟨⟨τc, mv⟩, hc, hw⟩ := bind_ok_inv hw
  simp only [pure, Except.pure, Except.ok.injEq] at hw
  subst hw
  rw [hsv, Res.ok_bind', hm, Res.ok_bind', hc, Res.ok_bind']
  rw [SValT.find_eval] at hsv
  obtain ⟨τs, hs, hsv⟩ := bind_ok_inv hsv
  obtain ⟨⟨r, segs⟩, hp, hsv⟩ := bind_ok_inv hsv
  dsimp only at hsv
  rw [Term.find_eval, hs, Res.ok_bind', PTerm.field_eval, hp]
  simp only [Res.ok_bind', pure, Except.pure]
  rw [State.findStorage_append, hsv, Res.ok_bind']
  cases mv with
  | prim q =>
    constructor
    · intro x hx
      simp only [MVal.asRef, bind, Except.bind] at hx
      nomatch hx
    · intro x hx
      exfalso
      cases sv with
      | prim _ => simp [SVal.find, bind, Except.bind] at hx
      | map _ _ => simp [copyStToM] at hc
      | struct fields =>
        rw [copyStToM] at hc
        rcases hcf : copyStFields τm fields with _ | ⟨s', mf⟩ <;>
          simp [hcf, bind, Except.bind, State.alloc] at hc
      | array elems _ _ =>
        rw [copyStToM] at hc
        rcases hcf : copyStElems τm elems with _ | ⟨s', me⟩ <;>
          simp [hcf, bind, Except.bind, State.alloc] at hc
  | ref id =>
    have this := Close.copyStToM_member hc hf'
    simp only [Close.readVal] at this
    simp only [MVal.asRef, Res.ok_bind', pure, Except.pure]
    have this' : (readAddr τc (.memoryField id f) >>= fun mv => mv.asValue) =
        (sv.find [.field f] >>= SVal.asValue) := this
    rw [this']
    exact ⟨Res.Le.refl _, Res.Le.refl _⟩

theorem EvalLaw.readAddEqual_eval {m : MTerm C} {R : RefTy} {a : MAddr C} {q : PrimTy}
    (h : (a.freshPath? m R).bind (Ty.ref R).memberTy = some (.prim q)) {μ₁ : State}
    (hw : (MTerm.addM m R).eval σ = .ok μ₁) :
    (Term.read (.addM m R) a).eval σ = .ok (PrimTy.default q) := by
  have hμ := hw
  rw [MTerm.addM_eval] at hw
  obtain ⟨μ₀, hm, hw⟩ := bind_ok_inv hw
  obtain ⟨⟨μ₁', root⟩, ha, hw⟩ := bind_ok_inv hw
  cases hw
  cases hp : a.freshPath? m R with
  | none => simp [hp] at h
  | some p =>
    simp only [hp, Option.bind] at h
    obtain ⟨h1, h2⟩ := Tm.freshPath_eval hm ha a hp
    obtain ⟨ad, had⟩ := h2 _ h
    obtain ⟨mv', hmv', hd⟩ :=
      (copyStToM_default_readPath p (Close.allocDefault_copy ha) (State.HeapExt.refl _)).2 _ h
    simp only [DefaultMVal] at hd
    subst hd
    rw [Term.read_eval, hμ, Res.ok_bind', had, Res.ok_bind', h1 ad had]
    simp only [State.readPath]
    rw [hmv', Res.ok_bind', Value.toMVal_asValue]

theorem EvalLaw.readAddDifferent_eval {m : MTerm C} {R : RefTy} {a : MAddr C}
    (h : a.boundedIn m = true) {μ₁ : State} (hw : (MTerm.addM m R).eval σ = .ok μ₁) :
    (Term.read (.addM m R) a).eval σ = (Term.read m a).eval σ := by
  have hμ := hw
  rw [MTerm.addM_eval] at hw
  obtain ⟨μ₀, hm, hw⟩ := bind_ok_inv hw
  obtain ⟨⟨μ₁', root⟩, ha, hw⟩ := bind_ok_inv hw
  cases hw
  rw [Term.read_eval, Term.read_eval, hμ, hm, Res.ok_bind', Res.ok_bind']
  cases had : a.eval σ with
  | error _ => rfl
  | ok ad =>
    simp only [Res.ok_bind']
    rw [readAddr_heapExt (allocDefault_heapExt ha) (Tm.boundedIn_eval hm a h ad had)]

theorem EvalLaw.readAddDifferentIdentity_eval {m : MTerm C} {R : RefTy} {a : MAddr C}
    (h : a.boundedIn m = true) {μ₁ : State} (hw : (MTerm.addM m R).eval σ = .ok μ₁) :
    (ITerm.read (.addM m R) a).eval σ = (ITerm.read m a).eval σ := by
  have hμ := hw
  rw [MTerm.addM_eval] at hw
  obtain ⟨μ₀, hm, hw⟩ := bind_ok_inv hw
  obtain ⟨⟨μ₁', root⟩, ha, hw⟩ := bind_ok_inv hw
  cases hw
  rw [ITerm.read_eval, ITerm.read_eval, hμ, hm, Res.ok_bind', Res.ok_bind']
  cases had : a.eval σ with
  | error _ => rfl
  | ok ad =>
    simp only [Res.ok_bind']
    rw [readAddr_heapExt (allocDefault_heapExt ha) (Tm.boundedIn_eval hm a h ad had)]

theorem EvalLaw.readWriteDifferent_eval {m : MTerm C} {a b : MAddr C} {v : MValT C}
    (h : a.apart? b = true) {τ : State} (hw : (MTerm.write m a v).eval σ = .ok τ) :
    (Term.read (.write m a v) b).eval σ = (Term.read m b).eval σ := by
  have hμ := hw
  rw [MTerm.write_eval] at hw
  obtain ⟨mv, hv, hw⟩ := bind_ok_inv hw
  obtain ⟨μ, hm, hw⟩ := bind_ok_inv hw
  obtain ⟨ad, had, hw⟩ := bind_ok_inv hw
  rw [Term.read_eval, Term.read_eval, hμ, hm, Res.ok_bind', Res.ok_bind']
  cases hbd : b.eval σ with
  | error _ => rfl
  | ok bd =>
    simp only [Res.ok_bind']
    obtain ⟨-, -, -, hfr⟩ := Close.writeAddr_setObj hw
    rw [hfr bd (MAddr.apart?_eval a b h had hbd)]

theorem EvalLaw.readWriteDifferentIdentity_eval {m : MTerm C} {a b : MAddr C} {v : MValT C}
    (h : a.apart? b = true) {τ : State} (hw : (MTerm.write m a v).eval σ = .ok τ) :
    (ITerm.read (.write m a v) b).eval σ = (ITerm.read m b).eval σ := by
  have hμ := hw
  rw [MTerm.write_eval] at hw
  obtain ⟨mv, hv, hw⟩ := bind_ok_inv hw
  obtain ⟨μ, hm, hw⟩ := bind_ok_inv hw
  obtain ⟨ad, had, hw⟩ := bind_ok_inv hw
  rw [ITerm.read_eval, ITerm.read_eval, hμ, hm, Res.ok_bind', Res.ok_bind']
  cases hbd : b.eval σ with
  | error _ => rfl
  | ok bd =>
    simp only [Res.ok_bind']
    obtain ⟨-, -, -, hfr⟩ := Close.writeAddr_setObj hw
    rw [hfr bd (MAddr.apart?_eval a b h had hbd)]

theorem EvalLaw.readOnWriteIdentity_eval {m : MTerm C} {a : MAddr C} {i : ITerm C} {τ : State}
    (hw : (MTerm.write m a (.ref i)).eval σ = .ok τ) :
    (ITerm.read (.write m a (.ref i)) a).eval σ = i.eval σ := by
  have hμ := hw
  rw [MTerm.write_eval, MValT.ref_eval] at hw
  obtain ⟨mv, hmv, hw⟩ := bind_ok_inv hw
  obtain ⟨id, hi, hmv⟩ := bind_ok_inv hmv
  simp only [pure, Except.pure, Except.ok.injEq] at hmv
  subst hmv
  obtain ⟨μ, hm, hw⟩ := bind_ok_inv hw
  obtain ⟨ad, had, hw⟩ := bind_ok_inv hw
  rw [ITerm.read_eval, hμ, Res.ok_bind', had, Res.ok_bind', Close.readAddr_writeAddr_same hw, hi]
  rfl

/-- **A law of a memory read refines evaluation**: where the read returns,
its replacement returns the same. -/
theorem EvalLaw.sound {u : Srt} {t t' : Tm C u} : EvalLaw t t' → Tm.EvalRefinesAt t t'
  | .readOnWrite => fun σ x hx => by
    have hx0 := hx
    rw [Term.read_eval] at hx
    obtain ⟨τ, hτ, -⟩ := bind_ok_inv hx
    rw [EvalLaw.readOnWrite_le hτ] at hx0
    obtain rfl := Res.ok_inj hx0
    rfl
  | .findCopyMem hf => fun σ x hx => by
    have hx0 := hx
    rw [Term.find_eval] at hx
    obtain ⟨τ, hτ, -⟩ := bind_ok_inv hx
    exact (EvalLaw.findCopyMem_eval hf hτ).1 x hx0
  | .readCopySt hf => fun σ x hx => by
    rw [Term.read_eval] at hx
    obtain ⟨μ, hμ, hx'⟩ := bind_ok_inv hx
    exact (EvalLaw.readCopySt_eval hf hμ).1 x hx
  | .readAddEqual h => fun σ x hx => by
    have hx0 := hx
    rw [Term.read_eval] at hx
    obtain ⟨μ₁, hμ, -⟩ := bind_ok_inv hx
    rw [EvalLaw.readAddEqual_eval h hμ] at hx0
    exact hx0.symm ▸ rfl
  | .readAddDifferent h => fun σ x hx => by
    have hx0 := hx
    rw [Term.read_eval] at hx
    obtain ⟨μ₁, hμ, -⟩ := bind_ok_inv hx
    rwa [EvalLaw.readAddDifferent_eval h hμ] at hx0
  | .readAddDifferentIdentity h => fun σ x hx => by
    have hx0 := hx
    rw [ITerm.read_eval] at hx
    obtain ⟨μ₁, hμ, -⟩ := bind_ok_inv hx
    rwa [EvalLaw.readAddDifferentIdentity_eval h hμ] at hx0
  | .readWriteDifferent h => fun σ x hx => by
    have hx0 := hx
    rw [Term.read_eval] at hx
    obtain ⟨τ, hτ, -⟩ := bind_ok_inv hx
    rwa [EvalLaw.readWriteDifferent_eval h hτ] at hx0
  | .readWriteDifferentIdentity h => fun σ x hx => by
    have hx0 := hx
    rw [ITerm.read_eval] at hx
    obtain ⟨τ, hτ, -⟩ := bind_ok_inv hx
    rwa [EvalLaw.readWriteDifferentIdentity_eval h hτ] at hx0
  | .readOnWriteIdentity => fun σ x hx => by
    have hx0 := hx
    rw [ITerm.read_eval] at hx
    obtain ⟨τ, hτ, -⟩ := bind_ok_inv hx
    rwa [EvalLaw.readOnWriteIdentity_eval hτ] at hx0

end EvalLawSound

/-- `U` writes the memory with a term on whose spine the write `w` lies: `w`
returns wherever `U` does. -/
def Upd.holdsMem (U : Upd C) (w : MTerm C) : Bool :=
  U.any fun e => match e with
    | .memory M => M.onMemSpine w
    | _ => false

/-- A memory write that is an element of an update that returns, returns. -/
theorem Upd.memory_eval_of_apply {U : Upd C} {σ τ : State} (h : U.apply σ = .ok τ) {M : MTerm C}
    (he : UpdElem.memory M ∈ U) : ∃ μ, M.eval σ = .ok μ := by
  obtain ⟨ρ, ρ', hw⟩ := Upd.apply_ok_elem h he
  rw [UpdElem.memory_write] at hw
  obtain ⟨μ, hm, -⟩ := bind_ok_inv hw
  exact ⟨μ, hm⟩

theorem Upd.holdsMem_eval {U : Upd C} {w : MTerm C} (h : U.holdsMem w = true) {σ τ : State}
    (hU : U.apply σ = .ok τ) : ∃ μ, w.eval σ = .ok μ := by
  simp only [Upd.holdsMem, List.any_eq_true] at h
  obtain ⟨e, he, hs⟩ := h
  cases e with
  | memory M =>
    obtain ⟨μ', hM⟩ := Upd.memory_eval_of_apply hU he
    cases hw : w.eval σ with
    | ok μ => exact ⟨μ, rfl⟩
    | error e' =>
      obtain ⟨e'', hM'⟩ := Tm.onMemSpine_error hw M hs
      rw [hM'] at hM
      cases hM
  | val _ _ | path _ _ | mref _ _ | storage _ | store _ _ | selfBalance _ _ | net _ _ _ | pay _ _
  | saveNet _ =>
    nomatch hs

/-- `U` returns only where the memory law is exact: `q.1` reads back a
write `U` holds — the memory write or allocation the read looks past
(`Upd.holdsMem`), the storage write of `findCopyMem` (`Upd.holdsWrite`).
By the sort of the law, then the shape of its read.  Syntactic, so that
`rfl` decides it. -/
def Upd.coversEval (U : Upd C) : {u : Srt} → Tm C u × Tm C u → Bool
  | .val, (Term.read (.write m a v) _, _) => U.holdsMem (.write m a v)
  | .val, (Term.find (.save s p (.copyMem m i)) (.field p' _), _) =>
    p' == p && U.holdsWrite (.save s p (.copyMem m i))
  | .val, (Term.read (.copySt m v) (.field (.copy m' v') _), _) =>
    m == m' && v == v' && U.holdsMem (.copySt m v)
  | .val, (Term.read (.addM m R) _, _) => U.holdsMem (.addM m R)
  | .ident, (ITerm.read (.write m a v) _, _) => U.holdsMem (.write m a v)
  | .ident, (ITerm.read (.addM m R) _, _) => U.holdsMem (.addM m R)
  | _, _ => false

/-- Where the update returns, a covered memory law is exact: its replacement
returns what the replaced term returns. -/
theorem EvalLaw.back {u : Srt} {t t' : Tm C u} (r : EvalLaw t t') {U : Upd C}
    (hc : U.coversEval (t, t') = true) {σ τ : State} (hU : U.apply σ = .ok τ) :
    Srt.Le u (t'.eval σ) (t.eval σ) := by
  cases r with
  | readOnWrite =>
    simp only [Upd.coversEval] at hc
    obtain ⟨τw, hw⟩ := Upd.holdsMem_eval hc hU
    intro x hx
    cases hx
    exact EvalLaw.readOnWrite_le hw
  | readAddEqual h =>
    simp only [Upd.coversEval] at hc
    obtain ⟨μ₁, hw⟩ := Upd.holdsMem_eval hc hU
    intro x hx
    cases hx
    exact EvalLaw.readAddEqual_eval h hw
  | readAddDifferent h =>
    simp only [Upd.coversEval] at hc
    obtain ⟨μ₁, hw⟩ := Upd.holdsMem_eval hc hU
    rw [EvalLaw.readAddDifferent_eval h hw]
    exact Res.Le.refl _
  | readAddDifferentIdentity h =>
    simp only [Upd.coversEval] at hc
    obtain ⟨μ₁, hw⟩ := Upd.holdsMem_eval hc hU
    rw [EvalLaw.readAddDifferentIdentity_eval h hw]
    exact Res.Le.refl _
  | readWriteDifferent h =>
    simp only [Upd.coversEval] at hc
    obtain ⟨τw, hw⟩ := Upd.holdsMem_eval hc hU
    rw [EvalLaw.readWriteDifferent_eval h hw]
    exact Res.Le.refl _
  | readWriteDifferentIdentity h =>
    simp only [Upd.coversEval] at hc
    obtain ⟨τw, hw⟩ := Upd.holdsMem_eval hc hU
    rw [EvalLaw.readWriteDifferentIdentity_eval h hw]
    exact Res.Le.refl _
  | readOnWriteIdentity =>
    simp only [Upd.coversEval] at hc
    obtain ⟨τw, hw⟩ := Upd.holdsMem_eval hc hU
    rw [EvalLaw.readOnWriteIdentity_eval hw]
    exact Res.Le.refl _
  | findCopyMem hf =>
    simp only [Upd.coversEval, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨b, F, hb, τ₁, hbe⟩ := Upd.holdsWrite_eval hc.2 hU
    obtain ⟨τ', hs⟩ := STerm.save_returns_of_base hb hbe
    exact (EvalLaw.findCopyMem_eval hf hs).2
  | readCopySt hf =>
    simp only [Upd.coversEval, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨μ, hw⟩ := Upd.holdsMem_eval hc.2 hU
    exact (EvalLaw.readCopySt_eval hf hw).2

/-- The memory law on the right-hand sides of `{U}_m φ` under any `m`, if it
rewrites one and the rewritten update holds the write the law reads back. -/
def Fml.rwUpdEvalTop {u : Srt} (q : Tm C u × Tm C u) (m : Modality) (U : Upd C) (φ : Fml C) :
    Option (Fml C) :=
  if (U.rwEv q != U && (U.rwEv q).coversEval q) = true then some (.upd m (U.rwEv q) φ) else none

theorem Fml.rwUpdEvalTop_sound {u : Srt} {q : Tm C u × Tm C u} (r : EvalLaw q.1 q.2)
    {m : Modality} {U : Upd C} {φ ψ : Fml C} (h : Fml.rwUpdEvalTop q m U φ = some ψ)
    (σ : State) (hψ : holds σ ψ) : holds σ (.upd m U φ) := by
  unfold Fml.rwUpdEvalTop at h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true] at hc
    exact (Upd.rwEv_holds r.sound (fun _ _ hU => r.back hc.2 hU) m φ σ).1 hψ
  · nomatch h

/-- The memory law on the right-hand sides of the update at position `i`,
under any modality, where that update holds the write the law reads back. -/
def Fml.rwUpdEvalAt {u : Srt} (q : Tm C u × Tm C u) (i : Nat) : Fml C → Option (Fml C) :=
  Fml.atSpine (Fml.rwUpdEvalTop q) i

/-! ## The rewrites, bundled -/

namespace LineRw

/-- `sequentialToParallel` on the updates at positions `i` and `i + 1`. -/
def mergeAt (i : Nat) : LineRw C := ⟨Fml.mergeAt i, fun h σ => (Fml.mergeAt_holds h σ).1⟩

/-- `sequentialToParallel` on the first `n + 1` updates, the innermost pair first. -/
def mergeSpine (n : Nat) : LineRw C :=
  ⟨Fml.mergeSpine n, fun h σ => (Fml.mergeSpine_holds n _ h σ).1⟩

/-- `sequentialToParallel` on the `n + 1` updates from position `i`, the innermost pair first. -/
def mergeRun (i n : Nat) : LineRw C :=
  ⟨Fml.mergeRun i n, fun h σ => (Fml.mergeRun_holds i n _ h σ).1⟩

/-- An update rule at position `i`: `applySkip`, `applyOnRigid`.
`sequentialToParallel` is `mergeAt`/`mergeSpine` and `simplifyUpdate` is
`simplify`/`simplifyFresh`; here they give no line. -/
def updRule (r : UpdRuleName) (i : Nat) : LineRw C :=
  ⟨Fml.updRuleAt r i, fun h σ => (Fml.updRuleAt_holds h σ).1⟩

/-- `simplifyUpdate` on the update at position `i`, reading the formula's variables. -/
def simplify (i : Nat) : LineRw C :=
  ⟨Fml.simplifyAt i, Fml.atSpine_sound (fun h σ => (Fml.simplifyWith_holds (fun _ h _ => h) h σ).1) i _⟩

/-- `simplifyUpdate` on the update at position `i`, reading the formula's
fresh variables. -/
def simplifyFresh (i : Nat) : LineRw C :=
  ⟨Fml.simplifyFreshAt i, Fml.atSpine_sound (fun h σ => (Fml.simplifyFreshTop_holds h σ).1) i _⟩

/-- `applyOnRigidFormula` on the update at position `i`, under the box or where it cannot halt. -/
def applyOnRigidBox (i : Nat) : LineRw C :=
  ⟨Fml.applyOnRigidBoxAt i, Fml.atSpine_sound Fml.applyOnRigidBoxTop_sound i _⟩

/-- `applyOnRigidFormula` on the box storage write at position `i`. -/
def applyStorageBox (i : Nat) : LineRw C :=
  ⟨Fml.applyStorageBoxAt i, Fml.atSpine_sound Fml.applyStorageBoxTop_sound i _⟩

/-- The term taclet `r` on every equation of the line. -/
def law {t t' : Term C} (r : TermTaclet t t') : LineRw C :=
  ⟨Fml.rwLaw (t, t'), fun hl σ => (Fml.rwLaw_holds r.sound hl σ).1⟩

/-- The term taclet `r`, onto a term that cannot halt, on the right-hand
sides of the box update at position `i`. -/
def lawUpd {t t' : Term C} (r : TermTaclet t t') (ht : t'.total = true) (i : Nat) : LineRw C :=
  ⟨Fml.rwUpdAt (t, t') i,
    Fml.atSpine_sound (Fml.rwUpdTop_sound (Term.EvalRefines.of_theq r.sound ht)) i _⟩

/-- The term taclet `r`, onto a term that cannot halt, on the right-hand
sides of the update at position `i` under any modality, where that update
holds the write `r` reads back (`Upd.covers`). -/
def lawUpdAny {t t' : Term C} (r : TermTaclet t t') (ht : t'.total = true) (i : Nat) : LineRw C :=
  ⟨Fml.rwUpdCoveredAt (t, t') i,
    Fml.atSpine_sound (Fml.rwUpdCoveredTop_sound (Term.EvalRefines.of_theq r.sound ht)) i _⟩

/-- A reference law on the right-hand sides of the update at position `i`
under any modality, where that update holds the storage operation. -/
def lawUpdRef {t t' : Term C} (r : TermTaclet t t') (hr : TermTaclet.RefLaw r)
    (i : Nat) : LineRw C :=
  ⟨Fml.rwUpdRefAt (t, t') i, Fml.atSpine_sound (Fml.rwUpdRefTop_sound hr) i _⟩

/-- The term taclet `r` on the right-hand sides of the update at position
`i` under any modality, where its two terms are one read member-wise
(`Term.base?`): the member-wise laws, `findMemberCons`, `selectOnSaveMember`,
`selectOnDelAtMember`.  Sound by `Term.base_eval` alone: the two return
alike, so the law is only the name of the step. -/
def lawUpdEq {t t' : Term C} (_r : TermTaclet t t') (i : Nat) : LineRw C :=
  ⟨Fml.rwUpdEqAt (t, t') i, Fml.atSpine_sound Fml.rwUpdEqTop_sound i _⟩

/-- The memory law `r` on the right-hand sides of the update at position `i`
under any modality, where that update holds the write `r` reads back
(`Upd.coversEval`). -/
def lawUpdEval {u : Srt} {t t' : Tm C u} (r : EvalLaw t t') (i : Nat) : LineRw C :=
  ⟨Fml.rwUpdEvalAt (t, t') i, Fml.atSpine_sound (Fml.rwUpdEvalTop_sound r) i _⟩

end LineRw

end Solidity
