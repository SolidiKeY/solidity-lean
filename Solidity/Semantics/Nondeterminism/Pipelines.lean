import Solidity.Semantics.Nondeterminism.Split

/-!
# Theorems under both pipelines; D1's non-circularity at the parameter (S5.2)

**Both pipelines.** `SplitSpec.HoldsBoth art p Φ` is the statement form
"holds under both pipelines": for legacy and for via-IR, each at the artifact
that pipeline produces and at every gas oracle. `holdsBoth_iff_pair` reduces
it to the two cases. `holdsBoth_iff_settings` is the bookkeeping lemma that
reads the two pipelines as the pipelines of an input with each one set
(G01's `SourceSpec.setPipeline`). It does not relate a language to that
input's meaning.

**D1's non-circularity, checked against the parameter.** D1 makes the source
read the compiled artifact and a gas oracle. That is circular if the
parameter can make the source agree with any target. The check has two
parts.

1. *Confinement* (`SplitSpec.Confined`): for every program the language
   declares D1-free (`readsD1 p = false`), the artifact and the oracle change
   nothing. For such a program a wrong compiler stays wrong at every choice
   (`Confined.refutes`). Witnesses at the plain choice of each pipeline are
   witnesses at every choice (`Confined.nonVacuous`). A non-vacuous language
   refutes an always-reverting target at every choice (`NonVacuous.refutes`).
   For programs that do read a D1 value, confinement says nothing. What the
   oracle may change in them is X03's substitution obligation, not proved
   here.
2. *The oracle is the target's.* An `OracleTarget` is a target execution
   together with the oracle its own runs report. Soundness is stated at that
   oracle (`SoundAtOracle`), so the prover cannot pick it. For an
   oracle-blind program the oracle drops out (`soundAtOracle_iff_fixed`).
   For an oracle-reading program a wrong target is still refuted at the
   target's own oracle (`Controls.circular_refuted`).

The negative controls show why both parts are needed.

- `Controls.circular` reads the oracle for a program it declares D1-free,
  so it is not confined (`circular_not_confined`). Declaring the read
  honestly passes confinement vacuously and gives up the refutation for
  that program (`circularHonest_confined`).
- If each target may come with any oracle, an always-succeeding target and
  an always-reverting target are both sound for `circular`
  (`circular_rescues`). The oracle must therefore come from the target's
  definition (the EVM side), not from the statement.
- `Controls.orderToy` holds under legacy and fails via IR, so `HoldsBoth` is
  strictly stronger than one pipeline.
- `Controls.envToy` shows that the choice may not depend on the
  environment: each environment has a choice that works, but no single
  choice works for every environment. A compiler correctness statement
  provides one choice for all environments.
-/

namespace Solidity.Semantics.Nondeterminism

open Solidity.Roadmap

namespace SplitSpec

variable {L : SplitSpec}

/-! ## Both pipelines -/

/-- Under both pipelines is legacy and via-IR. -/
theorem holdsBoth_iff_pair {art : Pipeline → Artifact} {p : L.Prog} {Φ : Prefix Event Outcome → Prop} :
    L.HoldsBoth art p Φ ↔ L.HoldsFor .legacy (art .legacy) p Φ ∧ L.HoldsFor .viaIR (art .viaIR) p Φ := by
  constructor
  · intro h
    exact ⟨h .legacy, h .viaIR⟩
  · intro h q
    cases q
    · exact h.1
    · exact h.2

/-- Under both pipelines is every member of G01's `pipelines`. -/
theorem holdsBoth_iff_pipelines {art : Pipeline → Artifact} {p : L.Prog} {Φ : Prefix Event Outcome → Prop} :
    L.HoldsBoth art p Φ ↔ ∀ q, q ∈ pipelines → L.HoldsFor q (art q) p Φ :=
  ⟨fun h q _ => h q, fun h q => h q (mem_pipelines q)⟩

/-- Both pipelines give each one. -/
theorem HoldsBoth.holdsFor {art : Pipeline → Artifact} {p : L.Prog} {Φ : Prefix Event Outcome → Prop}
    (h : L.HoldsBoth art p Φ) (q : Pipeline) (g : GasOracle) : L.Holds ⟨q, art q, g⟩ p Φ :=
  h q g

/-- The choice an input's settings name: its pipeline, with an artifact and
an oracle. -/
def _root_.Solidity.Roadmap.SourceSpec.choice (S : SourceSpec) (i : S.Input) (art : Artifact)
    (g : GasOracle) : CompilerChoice :=
  ⟨S.pipeline i, art, g⟩

/-- Both pipelines are the pipelines of the input with each one set
(bookkeeping: `S` is not related to `L`). -/
theorem holdsBoth_iff_settings (S : SourceSpec) (i : S.Input) {art : Pipeline → Artifact}
    {p : L.Prog} {Φ : Prefix Event Outcome → Prop} :
    L.HoldsBoth art p Φ ↔ ∀ q g, L.Holds (S.choice (S.setPipeline i q) (art q) g) p Φ := by
  simp only [SourceSpec.choice, S.pipeline_set]
  exact Iff.rfl

/-! ## Confinement of the artifact and the oracle -/

/-- **D1's confinement**: for every program the language declares D1-free,
only the pipeline of the choice matters. -/
def Confined (L : SplitSpec) : Prop :=
  ∀ p, L.readsD1 p = false → ∀ c c' : CompilerChoice, c.pipeline = c'.pipeline → L.sem c p = L.sem c' p

theorem Confined.oracleBlind (hc : L.Confined) {p : L.Prog} (hp : L.readsD1 p = false) :
    L.OracleBlind p :=
  fun c _ => hc p hp _ c rfl

theorem Confined.artifactBlind (hc : L.Confined) {p : L.Prog} (hp : L.readsD1 p = false) :
    L.ArtifactBlind p :=
  fun c _ => hc p hp _ c rfl

/-- A language blind to the artifact and the oracle everywhere is confined. -/
theorem confined_of_blind (hO : ∀ p, L.OracleBlind p) (hA : ∀ p, L.ArtifactBlind p) :
    L.Confined := by
  intro p _ c c' hq
  rcases c with ⟨q, a, g⟩
  rcases c' with ⟨q', a', g'⟩
  cases hq
  have e₁ : L.sem ⟨q, a, g⟩ p = L.sem ⟨q, a', g⟩ p := (hA p ⟨q, a, g⟩ a').symm
  have e₂ : L.sem ⟨q, a', g⟩ p = L.sem ⟨q, a', g'⟩ p := (hO p ⟨q, a', g⟩ g').symm
  exact e₁.trans e₂

/-- **A wrong compiler stays wrong**: a D1-free program whose source
completes with `o` at one choice is refined, at every choice with the same
pipeline, by no target that never completes with `o`. -/
theorem Confined.refutes (hc : L.Confined) {p : L.Prog} (hp : L.readsD1 p = false)
    {c₀ : CompilerChoice} {e : L.Env} {rs : L.Res} (hrs : L.Admissible rs) {o : Outcome}
    (ho : (L.sem c₀ p e rs).final = some o) {RT : Type} {AT : RT → Prop}
    {t : Prefixes RT Event Outcome} (ht : ∀ rt, AT rt → (t rt).final ≠ some o)
    (c : CompilerChoice) (hq : c.pipeline = c₀.pipeline) :
    ¬ Refines L.Admissible AT (L.sem c p e) t := by
  intro href
  have e₀ : L.sem c p = L.sem c₀ p := hc p hp c c₀ hq
  rw [e₀] at href
  obtain ⟨rt, hrt, hfin, _⟩ := href.completes hrs ho
  exact ht rt hrt hfin

/-- **Non-vacuity at every choice**: a success with data and a revert, at
allowed environments and admissible bounds, whatever the compiler chose. -/
def NonVacuous (L : SplitSpec) : Prop :=
  (∃ p e rs d, L.Allowed e ∧ L.Admissible rs ∧ d ≠ [] ∧
    ∀ c, (L.sem c p e rs).final = some (.success d)) ∧
  (∃ p e rs d, L.Allowed e ∧ L.Admissible rs ∧ ∀ c, (L.sem c p e rs).final = some (.revert d))

/-- **No choice rescues an always-reverting target.** -/
theorem NonVacuous.refutes (hv : L.NonVacuous) {RT : Type} {AT : RT → Prop}
    (t : L.Prog → L.Env → Prefixes RT Event Outcome)
    (hrev : ∀ p e rt d, AT rt → (t p e rt).final ≠ some (.success d)) (c : CompilerChoice) :
    ∃ p e, L.Allowed e ∧ ¬ Refines L.Admissible AT (L.sem c p e) (t p e) := by
  obtain ⟨p, e, rs, d, he, hrs, _, hw⟩ := hv.1
  refine ⟨p, e, he, fun href => ?_⟩
  obtain ⟨rt, hrt, hfin, _⟩ := href.completes hrs (hw c)
  exact hrev p e rt d hrt hfin

/-- **Confinement turns witnesses at the plain choice of each pipeline into
witnesses at every choice**: D1-free programs with a success and a revert
witness under each pipeline. -/
theorem Confined.nonVacuous (hc : L.Confined)
    {ps pr : L.Prog} (hps : L.readsD1 ps = false) (hpr : L.readsD1 pr = false)
    (hs : ∃ e rs d, L.Allowed e ∧ L.Admissible rs ∧ d ≠ [] ∧
      ∀ q, (L.sem (CompilerChoice.plain q) ps e rs).final = some (.success d))
    (hr : ∃ e rs d, L.Allowed e ∧ L.Admissible rs ∧
      ∀ q, (L.sem (CompilerChoice.plain q) pr e rs).final = some (.revert d)) :
    L.NonVacuous := by
  constructor
  · obtain ⟨e, rs, d, he, hrs, hd, hw⟩ := hs
    refine ⟨ps, e, rs, d, he, hrs, hd, fun c => ?_⟩
    rw [hc ps hps c (CompilerChoice.plain c.pipeline) rfl]
    exact hw c.pipeline
  · obtain ⟨e, rs, d, he, hrs, hw⟩ := hr
    refine ⟨pr, e, rs, d, he, hrs, fun c => ?_⟩
    rw [hc pr hpr c (CompilerChoice.plain c.pipeline) rfl]
    exact hw c.pipeline

end SplitSpec

/-! ## The oracle the target supplies -/

/-- **A target that supplies the oracle**: its runs, its admissible bounds,
and the oracle each run reports. The oracle is part of the target's
definition (on the EVM, the gas, memory size and program counter at each
read), not an argument of the statement. -/
structure OracleTarget where
  Res : Type
  Admissible : Res → Prop
  sem : Prefixes Res Event Outcome
  oracle : Res → GasOracle

namespace SplitSpec

variable {L : SplitSpec}

/-- **Soundness at the target's oracle**: every admissible target prefix is
below a source prefix read at the oracle of that target run. -/
def SoundAtOracle (L : SplitSpec) (T : OracleTarget) (q : Pipeline) (art : Artifact) (p : L.Prog)
    (e : L.Env) : Prop :=
  ∀ rt, T.Admissible rt → ∃ rs, L.Admissible rs ∧ (T.sem rt).Le (L.sem ⟨q, art, T.oracle rt⟩ p e rs)

/-- For a program that reads no oracle value, the supplied oracle is any
fixed one. -/
theorem soundAtOracle_iff_fixed {p : L.Prog} (hb : L.OracleBlind p) (T : OracleTarget)
    (q : Pipeline) (art : Artifact) (e : L.Env) (g : GasOracle) :
    L.SoundAtOracle T q art p e ↔
      ∀ rt, T.Admissible rt → ∃ rs, L.Admissible rs ∧ (T.sem rt).Le (L.sem ⟨q, art, g⟩ p e rs) := by
  have key : ∀ rt, L.sem ⟨q, art, T.oracle rt⟩ p = L.sem ⟨q, art, g⟩ p := fun rt =>
    (hb ⟨q, art, g⟩ (T.oracle rt))
  simp only [SoundAtOracle, key]

end SplitSpec

/-! ## Witnesses and negative controls -/

namespace Controls

open SplitSpec

/-- A prefix with no events and one final outcome. -/
def done (o : Outcome) : Prefix Event Outcome := ⟨[], some o⟩

theorem done_consistent {R : Type} [LE R] (o : Outcome) :
    Prefixes.Consistent (fun _ : R => done o) :=
  fun _ _ _ => Prefix.Le.refl _

/-- The success outcome with data `[1]`. -/
def ok : Outcome := .success [1]
/-- The revert outcome with empty data. -/
def bad : Outcome := .revert []

/-- **A program that depends on the pipeline**: it succeeds under legacy
and reverts via IR (as `++x + x` gives 3 and 4). -/
abbrev orderToy : SplitSpec :=
  SplitSpec.ofFamily Unit Unit Nat (fun _ => True) (fun _ => True)
    (fun c _ _ _ => done (if c.pipeline = .legacy then ok else bad))
    (fun _ _ _ => done_consistent _) (fun _ => false)

def successful (x : Prefix Event Outcome) : Prop := x.final = some ok

theorem orderToy_legacy : orderToy.HoldsFor .legacy Artifact.empty () successful :=
  fun _ _ _ _ _ => rfl

/-- **Negative control**: under both pipelines fails for it. -/
theorem orderToy_not_both : ¬ orderToy.HoldsBoth (fun _ => Artifact.empty) () successful := by
  intro h
  have := h .viaIR (GasOracle.const ⟨0, by decide⟩) () trivial 0 trivial
  simp only [successful, done, ok, bad] at this
  cases this

/-- **An environment input is not a compiler choice**: the environment
names a pipeline, and the run succeeds when the choice matches it. -/
abbrev envToy : SplitSpec :=
  SplitSpec.ofFamily Unit Pipeline Nat (fun _ => True) (fun _ => True)
    (fun c _ e _ => done (if c.pipeline = e then ok else bad))
    (fun _ _ _ => done_consistent _) (fun _ => false)

/-- For each environment some choice works. -/
theorem envToy_each : ∀ e : Pipeline, ∃ c, successful (envToy.sem c () e 0) :=
  fun e => ⟨CompilerChoice.plain e, by simp only [successful, done,
    CompilerChoice.plain, if_true]⟩

/-- **Negative control**: no single choice works for every environment. -/
theorem envToy_no_choice : ¬ ∃ c, envToy.Holds c () successful := by
  intro ⟨c, h⟩
  have h₁ := h .legacy trivial 0 trivial
  have h₂ := h .viaIR trivial 0 trivial
  simp only [successful, done, ok, bad] at h₁ h₂
  cases hq : c.pipeline <;> simp only [hq] at h₁ h₂ <;> cases h₁ <;> cases h₂

/-- The outcome read off the oracle's first `gasleft`. -/
def byGas (g : GasOracle) : Outcome := if (g.read [] 0 .gasleft).val = 0 then ok else bad

/-- **A circular language**: the outcome is the oracle's `gasleft` read,
for a program it declares D1-free. -/
abbrev circular : SplitSpec :=
  SplitSpec.ofFamily Unit Unit Nat (fun _ => True) (fun _ => True)
    (fun c _ _ _ => done (byGas c.oracle)) (fun _ _ _ => done_consistent _) (fun _ => false)

/-- The same language declaring the read. -/
abbrev circularHonest : SplitSpec :=
  SplitSpec.ofFamily Unit Unit Nat (fun _ => True) (fun _ => True)
    (fun c _ _ _ => done (byGas c.oracle)) (fun _ _ _ => done_consistent _) (fun _ => true)

/-- **Negative control**: the circular language is not confined. -/
theorem circular_not_confined : ¬ circular.Confined := by
  intro h
  have e := h () rfl (CompilerChoice.plain .legacy)
    ⟨.legacy, Artifact.empty, GasOracle.const ⟨1, by decide⟩⟩ rfl
  have e' := congrArg (fun s => (s () 0).final) e
  simp only [done, byGas, CompilerChoice.plain, GasOracle.const, ok, bad] at e'
  cases e'

/-- Declaring the read passes confinement, vacuously for that program. -/
theorem circularHonest_confined : circularHonest.Confined :=
  fun _ h => by cases h

/-- The oracle that answers `0` exactly when `b`. -/
def pick (b : Bool) : GasOracle := GasOracle.const (if b then ⟨0, by decide⟩ else ⟨1, by decide⟩)

/-- A target with no events, final outcome `o`, and oracle `g` in every run. -/
def target (o : Outcome) (g : GasOracle) : OracleTarget := ⟨Nat, fun _ => True, fun _ => done o, fun _ => g⟩

/-- **Negative control**: if each target may come with any oracle, an
always-succeeding target and an always-reverting target are both sound. -/
theorem circular_rescues :
    circular.SoundAtOracle (target ok (pick true)) .legacy Artifact.empty () () ∧
      circular.SoundAtOracle (target bad (pick false)) .legacy Artifact.empty () () :=
  ⟨fun _ _ => ⟨0, trivial, Prefix.Le.refl _⟩, fun _ _ => ⟨0, trivial, Prefix.Le.refl _⟩⟩

/-- **At the target's own oracle a wrong target is refuted**: a target whose
runs report `gasleft = 0` but revert is not sound for the oracle-reading
language, which succeeds at that oracle. -/
theorem circular_refuted :
    ¬ circularHonest.SoundAtOracle (target bad (pick true)) .legacy Artifact.empty () () := by
  intro h
  obtain ⟨_, _, _, hle⟩ := h (0 : Nat) trivial
  rcases hle with hn | he
  · cases hn
  · simp only [done, byGas, pick, GasOracle.const, ok, bad, target] at he
    cases he

/-- **A confined language** (inhabited witness): it reads only the program,
succeeding for program `true` and reverting for `false`. -/
abbrev confinedToy : SplitSpec :=
  SplitSpec.ofFamily Bool Unit Nat (fun _ => True) (fun _ => True)
    (fun _ p _ _ => done (if p then ok else bad)) (fun _ _ _ => done_consistent _) (fun _ => false)

theorem confinedToy_confined : confinedToy.Confined :=
  confined_of_blind (fun _ _ _ => rfl) (fun _ _ _ => rfl)

theorem confinedToy_nonVacuous : confinedToy.NonVacuous :=
  ⟨⟨true, (), 0, [1], trivial, trivial, by decide, fun _ => rfl⟩,
   ⟨false, (), 0, [], trivial, trivial, fun _ => rfl⟩⟩

/-- The refutation fires: an always-reverting target fails at every choice. -/
theorem confinedToy_refutes (c : CompilerChoice) :
    ∃ p e, confinedToy.Allowed e ∧
      ¬ Refines confinedToy.Admissible (fun _ : Nat => True) (confinedToy.sem c p e)
        (fun _ => done bad) :=
  confinedToy_nonVacuous.refutes (fun _ _ _ => done bad)
    (fun _ _ _ _ _ h => by cases h) c

/-- `Confined.refutes` fires on the confined witness. -/
theorem confinedToy_wrong (c : CompilerChoice) :
    ¬ Refines confinedToy.Admissible (fun _ : Nat => True) (confinedToy.sem c true ())
      (fun _ => done bad) :=
  confinedToy_confined.refutes (p := true) rfl (c₀ := CompilerChoice.plain c.pipeline)
    (e := ()) (rs := 0) trivial (o := ok) rfl (fun _ _ h => by cases h) c rfl

end Controls

end Solidity.Semantics.Nondeterminism
/-- info: 'Solidity.Semantics.Nondeterminism.SplitSpec.holdsBoth_iff_pair' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.SplitSpec.holdsBoth_iff_pair
/-- info: 'Solidity.Semantics.Nondeterminism.SplitSpec.holdsBoth_iff_settings' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.SplitSpec.holdsBoth_iff_settings
/-- info: 'Solidity.Semantics.Nondeterminism.SplitSpec.Confined.refutes' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.SplitSpec.Confined.refutes
/-- info: 'Solidity.Semantics.Nondeterminism.SplitSpec.NonVacuous.refutes' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.SplitSpec.NonVacuous.refutes
/-- info: 'Solidity.Semantics.Nondeterminism.SplitSpec.Confined.nonVacuous' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.SplitSpec.Confined.nonVacuous
/-- info: 'Solidity.Semantics.Nondeterminism.SplitSpec.soundAtOracle_iff_fixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.SplitSpec.soundAtOracle_iff_fixed
/-- info: 'Solidity.Semantics.Nondeterminism.Controls.orderToy_not_both' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.Controls.orderToy_not_both
/-- info: 'Solidity.Semantics.Nondeterminism.Controls.envToy_no_choice' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.Controls.envToy_no_choice
/-- info: 'Solidity.Semantics.Nondeterminism.Controls.circular_not_confined' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.Controls.circular_not_confined
/-- info: 'Solidity.Semantics.Nondeterminism.Controls.circularHonest_confined' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.Controls.circularHonest_confined
/-- info: 'Solidity.Semantics.Nondeterminism.Controls.circular_rescues' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.Controls.circular_rescues
/-- info: 'Solidity.Semantics.Nondeterminism.Controls.circular_refuted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.Controls.circular_refuted
/-- info: 'Solidity.Semantics.Nondeterminism.Controls.confinedToy_refutes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.Controls.confinedToy_refutes
/-- info: 'Solidity.Semantics.Nondeterminism.Controls.confinedToy_wrong' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.Controls.confinedToy_wrong
