import Solidity.Hash.CollisionBridge

/-!
# Compiler corollaries of the hash bridge

These corollaries assume the existing PublicCorrectness contract. They do
not construct a compiler correctness proof. Target-premise runs preserve
all prefix observations; forward completion keeps the source restrictions.
The probability statement quantifies over a coherent hash-indexed family,
including the source fixed parameters, not a single fixed-hash contract.
-/

namespace Solidity.Hash.CollisionBridge.Compiler

open Solidity.Roadmap

/-- Backward refinement of one full target prefix. -/
def PrefixRefines (S : SourceSpec) (V : EvmSpec) (sp : S.lang.Prog) (vp : V.lang.Prog)
    (se : S.lang.Env) (ve : V.lang.Env) (rt : V.lang.Res) : Prop :=
  ∃ rs, S.lang.Admissible rs ∧ (V.lang.sem vp ve rt).Le (S.lang.sem sp se rs)

section Deterministic
variable {I : IntrinsicSpec} {S : SourceSpec} {V : EvmSpec}
  {compiler : S.Input → Option Artifact} {envAbs : V.lang.Env → S.lang.Env}
  {X : StateExport S I V}

/-- Full guarded refinement, with the guards spelled as their actual
per-run hash premises. Both directions and observations are unchanged. -/
theorem refines (h : PublicCorrectness S V compiler envAbs X)
    {i : S.Input} {r : S.Resolved} (adm : S.Admitted i r)
    (w : S.WellFormed r) (p : S.InProfile r) {art : Artifact}
    (hc : compiler i = some art) {e : V.lang.Env} (he : V.lang.Allowed e) :
    S.lang.Allowed (envAbs e) ∧
      RefinesUnder S.lang.Admissible V.lang.Admissible
        (S.lang.Forward (S.meaning r w p art) (envAbs e))
        (fun rs => HashPremise S.fixed
          (S.hashed (S.meaning r w p art) (envAbs e) rs)
          (S.slotHashed (S.meaning r w p art) (envAbs e) rs))
        (fun rt => HashPremise V.fixed
          (V.hashed (V.load art) e rt) (V.slotHashed (V.load art) e rt))
        (S.lang.sem (S.meaning r w p art) (envAbs e)) (V.lang.sem (V.load art) e) := by
  obtain ⟨hal, hf, hb⟩ := h.refines i r adm w p art hc e he
  exact ⟨hal, fun rs hrs hfor hp => hf rs hrs hfor ((S.guard_iff _ _ _).mpr hp),
    fun rt hrt hp => hb rt hrt ((V.guard_iff _ _ _).mpr hp)⟩

/-- The target premise supplies backward prefix refinement, without adding
a source-forward assumption to this direction. -/
theorem prefix_refines (h : PublicCorrectness S V compiler envAbs X)
    {i : S.Input} {r : S.Resolved} (adm : S.Admitted i r)
    (w : S.WellFormed r) (p : S.InProfile r) {art : Artifact}
    (hc : compiler i = some art) {e : V.lang.Env} (he : V.lang.Allowed e)
    {rt : V.lang.Res} (hrt : V.lang.Admissible rt)
    (hp : HashPremise V.fixed (V.hashed (V.load art) e rt) (V.slotHashed (V.load art) e rt)) :
    PrefixRefines S V (S.meaning r w p art) (V.load art) (envAbs e) e rt :=
  (h.refines i r adm w p art hc e he).2.2 rt hrt ((V.guard_iff _ _ _).mpr hp)

/-- The same guarded premise also gives the existing exact decoded-world
reachability statement, with no weakened observation. -/
theorem decode_reach (h : PublicCorrectness S V compiler envAbs X)
    {i : S.Input} {r : S.Resolved} (adm : S.Admitted i r)
    (w : S.WellFormed r) (p : S.InProfile r) {art : Artifact}
    (hc : compiler i = some art) {e : V.lang.Env} (he : V.lang.Allowed e)
    {rt : V.lang.Res} (hrt : V.lang.Admissible rt)
    (hp : HashPremise V.fixed (V.hashed (V.load art) e rt) (V.slotHashed (V.load art) e rt)) :
    ∃ ri, I.lang.Admissible ri ∧
      (V.worlds (V.load art) e rt).map (X.decode (V.hashed (V.load art) e rt)) =
        (I.worlds (I.ofWorld (X.lowering.lower r w p art)) (X.envAbs e) ri).map some :=
  h.decode_reach i r adm w p art hc e he rt hrt ((V.guard_iff _ _ _).mpr hp)

/-- Empty actual query lists discharge the hash premise via HashPremise.nil.
Admissibility and compilation are still the existing contract conditions. -/
theorem prefix_empty (h : PublicCorrectness S V compiler envAbs X)
    {i : S.Input} {r : S.Resolved} (adm : S.Admitted i r)
    (w : S.WellFormed r) (p : S.InProfile r) {art : Artifact}
    (hc : compiler i = some art) {e : V.lang.Env} (he : V.lang.Allowed e)
    {rt : V.lang.Res} (hrt : V.lang.Admissible rt)
    (hx : V.hashed (V.load art) e rt = []) (hy : V.slotHashed (V.load art) e rt = []) :
    PrefixRefines S V (S.meaning r w p art) (V.load art) (envAbs e) e rt := by
  apply prefix_refines h adm w p hc he hrt
  rw [hx, hy]
  exact HashPremise.nil V.fixed

end Deterministic

/-- The semantic failure event is a mathematical classifier, not an
executable decision procedure for compiler correctness. -/
noncomputable def failure (S : SourceSpec) (V : EvmSpec) (sp : S.lang.Prog) (vp : V.lang.Prog)
    (se : S.lang.Env) (ve : V.lang.Env) (rt : V.lang.Res) : Bool := by
  classical
  exact decide (¬ PrefixRefines S V sp vp se ve rt)

/-- Fraction of random oracles under which the bytes' full target prefix
can fail refinement. Correctness and run-model relations are required only
on sampled tuples; no correctness-for-new-hashes claim follows from one
fixed-hash instance. q counts ALL strategy queries, including offline ones. -/
theorem failure_le (F : Fixed) {s : List Nat → Bytes} {dom : List Bytes}
    (hs : ∀ t, s t ∈ dom) (hroots : ∀ r ∈ List.range F.rootSlots, r < 2 ^ 256) (q : Nat)
    (I : List Nat → IntrinsicSpec) (S : List Nat → SourceSpec) (V : List Nat → EvmSpec)
    (compiler : ∀ g, (S g).Input → Option Artifact)
    (envAbs : ∀ g, (V g).lang.Env → (S g).lang.Env)
    (X : ∀ g, StateExport (S g) (I g) (V g))
    (i : ∀ g, (S g).Input) (r : ∀ g, (S g).Resolved)
    (w : ∀ g, (S g).WellFormed (r g)) (p : ∀ g, (S g).InProfile (r g))
    (art : List Nat → Artifact) (e : ∀ g, (V g).lang.Env) (rt : ∀ g, (V g).lang.Res)
    (correct : ∀ g ∈ tuples (2 ^ 256) dom.length,
      PublicCorrectness (S g) (V g) (compiler g) (envAbs g) (X g))
    (fixed : ∀ g ∈ tuples (2 ^ 256) dom.length, (V g).fixed = oracleFixed F dom g)
    (adm : ∀ g ∈ tuples (2 ^ 256) dom.length, (S g).Admitted (i g) (r g))
    (hc : ∀ g ∈ tuples (2 ^ 256) dom.length, compiler g (i g) = some (art g))
    (he : ∀ g ∈ tuples (2 ^ 256) dom.length, (V g).lang.Allowed (e g))
    (hrt : ∀ g ∈ tuples (2 ^ 256) dom.length, (V g).lang.Admissible (rt g))
    (hx : ∀ g ∈ tuples (2 ^ 256) dom.length,
      ∀ b ∈ (V g).hashed ((V g).load (art g)) (e g) (rt g),
        b ∈ eagerQueries s (oracleOf dom g) q)
    (hy : ∀ g ∈ tuples (2 ^ 256) dom.length,
      ∀ b ∈ (V g).slotHashed ((V g).load (art g)) (e g) (rt g),
        b ∈ eagerQueries s (oracleOf dom g) q) :
    2 ^ (256 + 1) * (tuples (2 ^ 256) dom.length).countP (fun g =>
      failure (S g) (V g) ((S g).meaning (r g) (w g) (p g) (art g))
        ((V g).load (art g)) (envAbs g (e g)) (e g) (rt g)) ≤
      numerator q F.regionLen (List.range F.rootSlots).length * (2 ^ 256) ^ dom.length := by
  let xs := fun g => (V g).hashed ((V g).load (art g)) (e g) (rt g)
  let ys := fun g => (V g).slotHashed ((V g).load (art g)) (e g) (rt g)
  have hsub : (tuples (2 ^ 256) dom.length).countP (fun g =>
      failure (S g) (V g) ((S g).meaning (r g) (w g) (p g) (art g))
        ((V g).load (art g)) (envAbs g (e g)) (e g) (rt g)) ≤
      (tuples (2 ^ 256) dom.length).countP (runPremiseFails F dom xs ys) := by
    apply countP_le_of_imp
    intro g hg hbad
    simp only [failure, decide_eq_true_eq] at hbad
    apply decide_eq_true
    intro hp
    have hp' : HashPremise (V g).fixed (xs g) (ys g) := by
      rw [fixed g hg]
      exact hp
    exact hbad (prefix_refines (correct g hg) (adm g hg) (w g) (p g) (hc g hg) (he g hg) (hrt g hg) hp')
  apply scale_count_le hsub
  exact run_premise_le F hs hroots q xs ys hx hy

end Solidity.Hash.CollisionBridge.Compiler

/-- info: 'Solidity.Hash.CollisionBridge.Compiler.refines' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Hash.CollisionBridge.Compiler.refines
/-- info: 'Solidity.Hash.CollisionBridge.Compiler.failure_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CollisionBridge.Compiler.failure_le
