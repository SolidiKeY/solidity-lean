import Solidity.Semantics.CtxEquiv.Behav

/-!
# Contextual equivalence at the ABI boundary (S1.1)

A **deployed contract** (`Deployed A E O`) is a program of some G01 language
(`Lang E O`) together with how an adversary `a : A` is read as that
language's environment, and which resource bounds count for it (the
admissible ones, possibly under a per-run premise such as G01's hash
premise).  Its behaviour against `a` is the set of prefixes its runs show at
counted bounds (`Deployed.behav`).

`CtxRefinesOn Adm c₁ c₂`: for every adversary allowed by `Adm`, every
prefix `c₁` shows is a prefix of one `c₂` shows (`Behav.Below`): a completed
one exactly, an unfinished one up to extension.  `CtxEquivOn` is refinement
both ways.  "Contextual" here is testing equivalence: the contexts are the
adversaries, there is no program-context syntax `C[·]`.

**What refinement allows.**  It is prefix (partial-correctness)
simulation: a side that shows only unfinished prefixes (stuck, silent
divergence) refines any side showing an extension of them, and a side
counting no bound refines everything (`CtxRefinesOn.of_empty`).
Equivalence keeps the completed observations (`CtxEquivOn.done_iff`), so
it separates divergence from completion for a deterministic side; over a
side whose resource choices may all fail (G01's failure points) it is
may-equivalence, and a data-free `revert` and a loop are equivalent there
(`Controls.failEmpty_ctxEquiv_loop`).  The nondeterminism of a side is its
resource choices; refinement lets the refining side have fewer.

**Honest contracts.**  A `Deployed` may read its adversary through any
`env`; `Contract.Faithful` asks that it read the whole session (an inverse
`session ∘ env = id`) and that allowed sessions give allowed environments.
Every contract this library builds is faithful (`srcContract`,
`SourceSpec.contract`, `EvmSpec.contract`, the controls').

**The G50 adversary.**  `Contract := Deployed SessionEnv Event Outcome` and
`CtxRefines`/`CtxEquiv` quantify over every allowed `SessionEnv`
(`SessionEnv.Allowed`): the deployer, value and constructor arguments, every
caller and transaction sequence (`requests`, a function of the whole
history), every callback strategy with unbounded reentrancy (`callee`),
code existence and opening balances.  The observations are G01's: the
events (each transaction's request with its outcome, so its return data or
revert data; calls, creations and payments the system makes and their
answers; callbacks and their outcomes; credits) and the final outcome.
**Logs are not observed**: G01's `Event` has no log constructor (G00
excludes them); the definitions are generic in the event type, so they
observe logs once X07 adds them.

**Final observable state.**  State is observed the only way the G01
adversary can: by later transactions and callbacks, which read the history
only.  A difference in final state that some function of the system returns
(or turns into an outcome or a call) shows in some adversary's events
(`Controls.store_not_ctxEquiv`).  External balances follow from the events
through the fixed ledger (G03).  Not observed: state no function exposes,
raw layout and gas values (G00), and what real code could read beside the
ABI, such as `BALANCE` of the system's own instances or their code hash.

Lemmas: preorder (`CtxRefines.refl`, `.trans`), equivalence
(`CtxEquiv.refl`, `.symm`, `.trans`), completion and safety transfer,
weakening of the adversary set (callback-free environments are a special
case, strictly weaker: `Controls.guard_ctxEquiv_noCallback`), and congruence
under sequencing of behaviours (`CtxRefinesOn.seq`, `Behav.seq`).
-/

namespace Solidity.CtxEquiv

open Solidity.Roadmap (Prefix Prefixes Lang SessionEnv Event Outcome)

/-- A deployed contract against adversaries `A`: a program of a G01 language,
the environment each adversary gives it, and the resource bounds that count
(admissible, possibly under a per-run premise). -/
structure Deployed (A E O : Type) where
  L : Lang E O
  prog : L.Prog
  env : A → L.Env
  Counts : A → L.Res → Prop

variable {A E O : Type}

/-- What a deployed contract shows one adversary: the prefixes of its runs at
counted bounds. -/
def Deployed.behav (c : Deployed A E O) (a : A) : Behav E O :=
  Behav.ofPrefixes (c.Counts a) (c.L.sem c.prog (c.env a))

/-- A contract counting every admissible bound. -/
def Deployed.mk' (L : Lang E O) (prog : L.Prog) (env : A → L.Env) : Deployed A E O :=
  ⟨L, prog, env, fun _ => L.Admissible⟩

/-- The same contract with a stronger counting condition. -/
def Deployed.restrict (c : Deployed A E O) (P : A → c.L.Res → Prop) : Deployed A E O :=
  { c with Counts := fun a r => c.Counts a r ∧ P a r }

/-- Counting fewer bounds shows less. -/
theorem Deployed.restrict_below (c : Deployed A E O) (P : A → c.L.Res → Prop) (a : A) :
    ((c.restrict P).behav a).Below (c.behav a) :=
  Behav.ofPrefixes_mono (fun _ h => h.1) _

/-- **Contextual refinement** over the adversaries `Adm` allows: every prefix
`c₁` shows such an adversary is a prefix of one `c₂` shows. -/
def CtxRefinesOn (Adm : A → Prop) (c₁ c₂ : Deployed A E O) : Prop :=
  ∀ a, Adm a → (c₁.behav a).Below (c₂.behav a)

/-- **Contextual equivalence** over `Adm`: refinement both ways. -/
def CtxEquivOn (Adm : A → Prop) (c₁ c₂ : Deployed A E O) : Prop :=
  CtxRefinesOn Adm c₁ c₂ ∧ CtxRefinesOn Adm c₂ c₁

section
variable {Adm : A → Prop}

theorem CtxRefinesOn.refl (c : Deployed A E O) : CtxRefinesOn Adm c c :=
  fun _ _ => Behav.Below.refl _

theorem CtxRefinesOn.trans {c₁ c₂ c₃ : Deployed A E O} (h₁ : CtxRefinesOn Adm c₁ c₂)
    (h₂ : CtxRefinesOn Adm c₂ c₃) : CtxRefinesOn Adm c₁ c₃ :=
  fun a ha => (h₁ a ha).trans (h₂ a ha)

theorem CtxEquivOn.refl (c : Deployed A E O) : CtxEquivOn Adm c c :=
  ⟨CtxRefinesOn.refl c, CtxRefinesOn.refl c⟩

theorem CtxEquivOn.symm {c₁ c₂ : Deployed A E O} (h : CtxEquivOn Adm c₁ c₂) :
    CtxEquivOn Adm c₂ c₁ :=
  ⟨h.2, h.1⟩

theorem CtxEquivOn.trans {c₁ c₂ c₃ : Deployed A E O} (h₁ : CtxEquivOn Adm c₁ c₂)
    (h₂ : CtxEquivOn Adm c₂ c₃) : CtxEquivOn Adm c₁ c₃ :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

/-- Equivalence is mutual refinement (by definition). -/
theorem ctxEquivOn_iff {c₁ c₂ : Deployed A E O} :
    CtxEquivOn Adm c₁ c₂ ↔ CtxRefinesOn Adm c₁ c₂ ∧ CtxRefinesOn Adm c₂ c₁ :=
  Iff.rfl

/-- Fewer adversaries keep refinement. -/
theorem CtxRefinesOn.mono {Adm' : A → Prop} (hA : ∀ a, Adm' a → Adm a)
    {c₁ c₂ : Deployed A E O} (h : CtxRefinesOn Adm c₁ c₂) : CtxRefinesOn Adm' c₁ c₂ :=
  fun a ha => h a (hA a ha)

theorem CtxEquivOn.mono {Adm' : A → Prop} (hA : ∀ a, Adm' a → Adm a)
    {c₁ c₂ : Deployed A E O} (h : CtxEquivOn Adm c₁ c₂) : CtxEquivOn Adm' c₁ c₂ :=
  ⟨h.1.mono hA, h.2.mono hA⟩

/-- **Completions transfer**: a run of `c₁` at a counted bound completing
with `o` is a run of `c₂` at a counted bound with the same events and
outcome. -/
theorem CtxRefinesOn.completes {c₁ c₂ : Deployed A E O} (h : CtxRefinesOn Adm c₁ c₂)
    {a : A} (ha : Adm a) {r : c₁.L.Res} (hr : c₁.Counts a r) {o : O}
    (ho : (c₁.L.sem c₁.prog (c₁.env a) r).final = some o) :
    ∃ r', c₂.Counts a r' ∧ c₂.L.sem c₂.prog (c₂.env a) r' = c₁.L.sem c₁.prog (c₁.env a) r :=
  (h a ha).completes ⟨r, hr, rfl⟩ ho

/-- **Safety transfers** from `c₂` to `c₁`. -/
theorem CtxRefinesOn.safety {c₁ c₂ : Deployed A E O} (h : CtxRefinesOn Adm c₁ c₂)
    (Φ : Prefix E O → Prop) (down : ∀ x y, x.Le y → Φ y → Φ x) {a : A} (ha : Adm a)
    (h₂ : ∀ r, c₂.Counts a r → Φ (c₂.L.sem c₂.prog (c₂.env a) r)) :
    ∀ r, c₁.Counts a r → Φ (c₁.L.sem c₁.prog (c₁.env a) r) := by
  intro r hr
  exact (h a ha).safety Φ down (fun _ ⟨r', hr', he⟩ => he ▸ h₂ r' hr') _ ⟨r, hr, rfl⟩

/-- Equivalent contracts complete with exactly the same events and
outcomes. -/
theorem CtxEquivOn.done_iff {c₁ c₂ : Deployed A E O} (h : CtxEquivOn Adm c₁ c₂) {a : A}
    (ha : Adm a) (evs : List E) (o : O) :
    (c₁.behav a).Done evs o ↔ (c₂.behav a).Done evs o :=
  ⟨(h.1 a ha).done, (h.2 a ha).done⟩

/-- **A negative criterion**: if `c₁` completes with an observation `c₂`
never shows, `c₁` does not refine `c₂`. -/
theorem not_ctxRefinesOn_of_done {c₁ c₂ : Deployed A E O} {a : A} (ha : Adm a)
    {evs : List E} {o : O} (h₁ : (c₁.behav a).Done evs o) (h₂ : ¬ (c₂.behav a).Done evs o) :
    ¬ CtxRefinesOn Adm c₁ c₂ :=
  fun h => h₂ ((h a ha).done h₁)

theorem not_ctxEquivOn_of_done {c₁ c₂ : Deployed A E O} {a : A} (ha : Adm a)
    {evs : List E} {o : O} (h₁ : (c₁.behav a).Done evs o) (h₂ : ¬ (c₂.behav a).Done evs o) :
    ¬ CtxEquivOn Adm c₁ c₂ :=
  fun h => not_ctxRefinesOn_of_done ha h₁ h₂ h.1

/-- **Vacuity, made explicit**: a contract counting no bound refines every
contract.  Faithfulness does not exclude it; the counting condition is part
of what a statement claims. -/
theorem CtxRefinesOn.of_empty {c₁ c₂ : Deployed A E O} (h : ∀ a r, ¬ c₁.Counts a r) :
    CtxRefinesOn Adm c₁ c₂ :=
  fun a _ _ ⟨r, hr, _⟩ => absurd hr (h a r)

end

/-! ## Sequencing -/

/-- A contract followed, on each completion, by a continuation behaviour that
reads the adversary and the history. -/
def Deployed.seqBehav (c : Deployed A E O) (K : A → List E → O → Behav E O) (a : A) :
    Behav E O :=
  (c.behav a).seq (K a)

/-- **Sequencing congruence**: refinement of the contracts and of every
continuation gives refinement of the sequenced behaviours, against every
allowed adversary. -/
theorem CtxRefinesOn.seq {Adm : A → Prop} {c₁ c₂ : Deployed A E O}
    {K₁ K₂ : A → List E → O → Behav E O}
    (h : CtxRefinesOn Adm c₁ c₂) (hK : ∀ a, Adm a → ∀ h o, (K₁ a h o).Below (K₂ a h o)) :
    ∀ a, Adm a → (c₁.seqBehav K₁ a).Below (c₂.seqBehav K₂ a) :=
  fun a ha => (h a ha).seq (hK a ha)

/-- Sequencing congruence for equivalence. -/
theorem CtxEquivOn.seq {Adm : A → Prop} {c₁ c₂ : Deployed A E O}
    {K₁ K₂ : A → List E → O → Behav E O}
    (h : CtxEquivOn Adm c₁ c₂)
    (hK : ∀ a, Adm a → ∀ h o, (K₁ a h o).Below (K₂ a h o) ∧ (K₂ a h o).Below (K₁ a h o)) :
    ∀ a, Adm a → (c₁.seqBehav K₁ a).Below (c₂.seqBehav K₂ a) ∧
      (c₂.seqBehav K₂ a).Below (c₁.seqBehav K₁ a) :=
  fun a ha => ⟨(h.1 a ha).seq fun h o => (hK a ha h o).1, (h.2 a ha).seq fun h o => (hK a ha h o).2⟩

/-! ## The G50 adversary -/

/-- A contract deployed against G01's session environments, observed through
G01's events and outcomes. -/
abbrev Contract := Deployed SessionEnv Event Outcome

/-- **Contextual refinement at the ABI boundary**: for every allowed session
environment (any deployer, caller, transaction sequence, callback strategy,
code existence and balances), every prefix `c₁` shows, `c₂` can show. -/
def CtxRefines (c₁ c₂ : Contract) : Prop := CtxRefinesOn SessionEnv.Allowed c₁ c₂

/-- **Contextual equivalence at the ABI boundary.** -/
def CtxEquiv (c₁ c₂ : Contract) : Prop := CtxEquivOn SessionEnv.Allowed c₁ c₂

/-- **A faithful contract** reads the whole session (`env` has a left inverse)
and is given an allowed environment by every allowed session. -/
def Contract.Faithful (c : Contract) : Prop :=
  (∀ s, s.Allowed → c.L.Allowed (c.env s)) ∧ ∃ f : c.L.Env → SessionEnv, ∀ s, f (c.env s) = s

theorem CtxRefines.refl (c : Contract) : CtxRefines c c := CtxRefinesOn.refl c

theorem CtxRefines.trans {c₁ c₂ c₃ : Contract} (h₁ : CtxRefines c₁ c₂) (h₂ : CtxRefines c₂ c₃) :
    CtxRefines c₁ c₃ :=
  CtxRefinesOn.trans h₁ h₂

theorem CtxEquiv.refl (c : Contract) : CtxEquiv c c := CtxEquivOn.refl c

theorem CtxEquiv.symm {c₁ c₂ : Contract} (h : CtxEquiv c₁ c₂) : CtxEquiv c₂ c₁ :=
  CtxEquivOn.symm h

theorem CtxEquiv.trans {c₁ c₂ c₃ : Contract} (h₁ : CtxEquiv c₁ c₂) (h₂ : CtxEquiv c₂ c₃) :
    CtxEquiv c₁ c₃ :=
  CtxEquivOn.trans h₁ h₂

theorem CtxEquiv.iff {c₁ c₂ : Contract} : CtxEquiv c₁ c₂ ↔ CtxRefines c₁ c₂ ∧ CtxRefines c₂ c₁ :=
  Iff.rfl

/-- The no-callback reading (`transferSemantics:noCallback`) is a special
case: refinement against every allowed environment holds against every
allowed callback-free one. -/
theorem CtxRefines.noCallback {c₁ c₂ : Contract} (h : CtxRefines c₁ c₂) :
    CtxRefinesOn (fun e => e.Allowed ∧ e.NoCallback) c₁ c₂ :=
  CtxRefinesOn.mono (fun _ h => h.1) h

theorem CtxEquiv.noCallback {c₁ c₂ : Contract} (h : CtxEquiv c₁ c₂) :
    CtxEquivOn (fun e => e.Allowed ∧ e.NoCallback) c₁ c₂ :=
  CtxEquivOn.mono (fun _ h => h.1) h

/-- Each allowed environment's callback-free version is allowed, so the
callback-free environments are inhabited wherever the allowed ones are. -/
theorem withoutCallbacks_adm {e : SessionEnv} (he : e.Allowed) :
    e.withoutCallbacks.Allowed ∧ e.withoutCallbacks.NoCallback :=
  ⟨he.withoutCallbacks, e.withoutCallbacks_noCallback⟩

end Solidity.CtxEquiv
