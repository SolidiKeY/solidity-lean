import Solidity.Hash.CollisionBound
import Solidity.Roadmap.Evm

/-!
# The roadmap's final theorem contracts (G01), as statements

`docs/coverage-plan.md` names six final proof obligations; G01 fixes their
types and relations.  This module states them as `Prop`s and structures over
intrinsic types, parameterized where the type does not exist yet (the
independent source semantics of S00–S04, the pinned Osaka EVM of G06,
whose interface is `Solidity/Roadmap/Evm.lean`).  Nothing here claims a
final theorem: the contracts are definitions.  The lemmas check the
contracts' shape only: refinement is a preorder that composes, it transfers
safety and completion, the environment set contains the no-callback
environments, and neither a compiler that compiles nothing nor one that
always reverts satisfies the public contract.
`docs/feature-work/roadmap-g01-interfaces.md` explains each definition, its
premises, why it is not circular, and the user decisions
(`docs/solidity-scope.md`, "User decisions (2026-10-29)" and "Second round
(2026-10-29)") it implements.

**Executions are consistent families of finite prefixes.**  A `Prefix` is
what a finite execution prefix shows: the events emitted so far and, when it
completed within its horizon, the final observation.  A resource bound is a
horizon plus the resource choices of the layer (the source's failure points,
the EVM's gas schedule).  Running out of gas never ends a session: the frame
that runs out reverts, its caller sees the revert, and the session
continues.  A prefix ends unfinished only at its horizon.

**Refinement is two-sided, under a per-run hash premise on the source.**
Every source prefix without resource failures, hashing fewer than
`hashBound` preimages that do not collide, is below some target prefix
(resource adequacy); every target prefix is below some source prefix, or
the source collided before the target's observations end (soundness).  The
premise reads the preimages the *source* run determines (G06's F7), so the
compiler cannot falsify it with hashes of its own.

**Environments are shared, not chosen.**  Every layer reads the same
session environment (`SessionEnv`: requests, a history-dependent callee
strategy with unbounded reentrancy, opening balances, code existence); the
public contract requires the source environment to be the EVM's.

The module stays below the elaborator and the compiler: it imports the
hash premises (`Solidity/Hash/CollisionBound.lean`) and the EVM interface
(`Solidity/Roadmap/Evm.lean`), each of which imports at most
`Solidity.Keccak`, so a source semantics may import it for `Artifact` (see
the non-circularity gate of the G01 document).
-/

namespace Solidity.Roadmap

/-! ## Words, addresses and the per-run hash premise -/

/-- An EVM word: a natural number below `2^256` (`Fin Solidity.Evm.W`). -/
abbrev Word := Fin (2 ^ 256)

/-- An account address: 160 bits. -/
abbrev Address := Fin (2 ^ 160)

/-- ABI bytes (`Roadmap.Evm.Bytes`). -/
abbrev Bytes := List UInt8

/-- Address 0. -/
def Address.zero : Address := ⟨0, by decide⟩

/-- The address holds an Osaka precompile (`Evm.Precompile`: `0x01`–`0x11`
and P256VERIFY at `0x100`).  Calls to it run fixed functions, never
environment code. -/
def Address.Precompile (a : Address) : Prop :=
  (Evm.Precompile.ofAddress? a.val).isSome

/-- The per-run collision premise: the hash-collision-bound task's
`Solidity.Hash.CollisionFree` (equal outputs imply equal inputs over `xs`). -/
abbrev CollisionFree {α β : Type} (f : α → β) (xs : List α) : Prop :=
  Solidity.Hash.CollisionFree f xs

/-- **Per run, not global**: every function is collision-free on a single
preimage, so the premise never asks for injectivity. -/
theorem CollisionFree.singleton {α β : Type} (f : α → β) (a : α) : CollisionFree f [a] :=
  Solidity.Hash.CollisionFree.singleton a

/-- How many distinct preimages a source run adequacy speaks of may hash: far
below the `2^256` at which a collision or an overlap of regions is forced by
counting. -/
def hashBound : Nat := 2 ^ 128

/-- The number of distinct preimages in a list (the `q` of the collision
bound; `(Solidity.Hash.dedup xs).length`, computed without choice). -/
def distinctCount : List Bytes → Nat
  | [] => 0
  | x :: xs => if xs.elem x then distinctCount xs else distinctCount xs + 1

/-! ## Finite prefixes and their order -/

/-- What a finite prefix of an execution shows: the events so far and, if it
completed within the prefix's horizon, its final observation. -/
structure Prefix (E O : Type) where
  events : List E
  final : Option O

/-- `a` is a prefix of `b`: its events lead `b`'s, and if `a` completed, `b`
is `a`. -/
def Prefix.Le {E O : Type} (a b : Prefix E O) : Prop :=
  a.events <+: b.events ∧ (a.final = none ∨ b = a)

theorem Prefix.Le.refl {E O : Type} (a : Prefix E O) : a.Le a :=
  ⟨List.prefix_refl _, .inr rfl⟩

theorem Prefix.Le.trans {E O : Type} {a b c : Prefix E O} (hab : a.Le b) (hbc : b.Le c) :
    a.Le c := by
  refine ⟨hab.1.trans hbc.1, ?_⟩
  rcases hab.2 with ha | hba
  · exact .inl ha
  · subst hba
    rcases hbc.2 with hb | hcb
    · exact .inl hb
    · exact .inr hcb

/-- A completed prefix is below only itself. -/
theorem Prefix.Le.final_eq {E O : Type} {a b : Prefix E O} {o : O} (h : a.Le b)
    (ha : a.final = some o) : b = a := by
  rcases h.2 with hn | hb
  · rw [hn] at ha; cases ha
  · exact hb

/-- One execution: a prefix at each resource bound. -/
abbrev Prefixes (R E O : Type) := R → Prefix E O

/-- A longer horizon extends a prefix; a completed prefix stays as it is.
The family of every language's semantics must be consistent (S03.04,
G46.06). -/
def Prefixes.Consistent {R E O : Type} [LE R] (p : Prefixes R E O) : Prop :=
  ∀ r r', r ≤ r' → (p r).Le (p r')

/-- The execution completes with `o` at some resource bound. -/
def Prefixes.Completes {R E O : Type} (p : Prefixes R E O) (o : O) : Prop :=
  ∃ r, (p r).final = some o

/-- No bound satisfying `A` lets the execution complete. -/
def Prefixes.Diverges {R E O : Type} (A : R → Prop) (p : Prefixes R E O) : Prop :=
  ∀ r, A r → (p r).final = none

/-! ## Languages, refinement and pass certificates -/

/-- A language at one layer of the pipeline, over the shared events `E` and
final observations `O`.  `Res` is a horizon together with the layer's
resource choices; `Admissible` is the approved resource profile of the layer.
`Forward` marks the bounds resource adequacy speaks of (at the source: no
resource failure, fewer than `hashBound` hashes), and `Guard` is the per-run
hash premise on a bound (at the source: the preimages the run determines do
not collide and their regions do not overlap).  A pass carries both to its
target; at the EVM, which is only a target, both are trivial.  Every
execution is a consistent family. -/
structure Lang (E O : Type) where
  Prog : Type
  Env : Type
  Res : Type
  resLE : LE Res
  Allowed : Env → Prop
  Admissible : Res → Prop
  sem : Prog → Env → Prefixes Res E O
  consistent : ∀ p e, @Prefixes.Consistent Res E O resLE (sem p e)
  Forward : Prog → Env → Res → Prop := fun _ _ _ => True
  Guard : Prog → Env → Res → Prop := fun _ _ _ => True

/-- Two-sided refinement of one execution at admissible resources. -/
def Refines {E O RS RT : Type} (AS : RS → Prop) (AT : RT → Prop)
    (s : Prefixes RS E O) (t : Prefixes RT E O) : Prop :=
  (∀ rs, AS rs → ∃ rt, AT rt ∧ (s rs).Le (t rt)) ∧
  (∀ rt, AT rt → ∃ rs, AS rs ∧ (t rt).Le (s rs))

/-- The source collided before `b`'s observations end: the source prefix at
`rs` is in the forward bounds, violates the premise, and its events lead
`b`'s. -/
def Collided {E O RS : Type} (FS G : RS → Prop) (s : Prefixes RS E O) (rs : RS)
    (b : Prefix E O) : Prop :=
  FS rs ∧ ¬ G rs ∧ (s rs).events <+: b.events

/-- Two-sided refinement under a per-run premise `G` on the **source** bound.
Forward: every admissible source bound in `FS` satisfying `G` names an
admissible target bound above it.  Backward: every admissible target prefix
is below an admissible source prefix, or the source collided before its
observations end. -/
def RefinesUnder {E O RS RT : Type} (AS : RS → Prop) (AT : RT → Prop) (FS G : RS → Prop)
    (s : Prefixes RS E O) (t : Prefixes RT E O) : Prop :=
  (∀ rs, AS rs → FS rs → G rs → ∃ rt, AT rt ∧ (s rs).Le (t rt)) ∧
  (∀ rt, AT rt → ∃ rs, AS rs ∧ ((t rt).Le (s rs) ∨ Collided FS G s rs (t rt)))

/-- The source premise up to a target prefix's observations: every source
prefix in the forward bounds whose events lead the target's satisfies `G`. -/
def NoCollisionUpTo {E O RS : Type} (AS FS G : RS → Prop) (s : Prefixes RS E O)
    (b : Prefix E O) : Prop :=
  ∀ rs, AS rs → FS rs → (s rs).events <+: b.events → G rs

theorem Refines.trans {E O R₁ R₂ R₃ : Type} {A₁ : R₁ → Prop} {A₂ : R₂ → Prop} {A₃ : R₃ → Prop}
    {p₁ : Prefixes R₁ E O} {p₂ : Prefixes R₂ E O} {p₃ : Prefixes R₃ E O}
    (h₁₂ : Refines A₁ A₂ p₁ p₂) (h₂₃ : Refines A₂ A₃ p₂ p₃) : Refines A₁ A₃ p₁ p₃ := by
  refine ⟨fun r₁ a₁ => ?_, fun r₃ a₃ => ?_⟩
  · obtain ⟨r₂, a₂, l₁₂⟩ := h₁₂.1 r₁ a₁
    obtain ⟨r₃, a₃, l₂₃⟩ := h₂₃.1 r₂ a₂
    exact ⟨r₃, a₃, l₁₂.trans l₂₃⟩
  · obtain ⟨r₂, a₂, l₃₂⟩ := h₂₃.2 r₃ a₃
    obtain ⟨r₁, a₁, l₂₁⟩ := h₁₂.2 r₂ a₂
    exact ⟨r₁, a₁, l₃₂.trans l₂₁⟩

/-- Unguarded refinement is refinement under any premise. -/
theorem Refines.under {E O RS RT : Type} {AS : RS → Prop} {AT : RT → Prop}
    {s : Prefixes RS E O} {t : Prefixes RT E O} (h : Refines AS AT s t) (FS G : RS → Prop) :
    RefinesUnder AS AT FS G s t :=
  ⟨fun rs hrs _ _ => h.1 rs hrs, fun rt hrt => (h.2 rt hrt).imp fun _ ⟨a, l⟩ => ⟨a, .inl l⟩⟩

/-- If every admissible source bound is in `FS` and satisfies `G`, guarded
refinement is refinement. -/
theorem RefinesUnder.refines {E O RS RT : Type} {AS : RS → Prop} {AT : RT → Prop}
    {FS G : RS → Prop} {s : Prefixes RS E O} {t : Prefixes RT E O}
    (h : RefinesUnder AS AT FS G s t) (hG : ∀ rs, AS rs → FS rs ∧ G rs) : Refines AS AT s t := by
  refine ⟨fun rs hrs => h.1 rs hrs (hG rs hrs).1 (hG rs hrs).2, fun rt hrt => ?_⟩
  obtain ⟨rs, hrs, hl⟩ := h.2 rt hrt
  rcases hl with l | ⟨_, hng, _⟩
  · exact ⟨rs, hrs, l⟩
  · exact absurd (hG rs hrs).2 hng

/-- **Non-vacuity of refinement.**  A source completion at an admissible bound
in `FS` satisfying `G` is a target completion with the same observation and
events: a target that never completes with `o` (always reverting, always out
of gas, `o` erased) refines no source that completes with `o` there. -/
theorem RefinesUnder.completes {E O RS RT : Type} {AS : RS → Prop} {AT : RT → Prop}
    {FS G : RS → Prop} {s : Prefixes RS E O} {t : Prefixes RT E O}
    (h : RefinesUnder AS AT FS G s t) {rs : RS} (hrs : AS rs) (hf : FS rs) (hg : G rs)
    {o : O} (ho : (s rs).final = some o) :
    ∃ rt, AT rt ∧ (t rt).final = some o ∧ (t rt).events = (s rs).events := by
  obtain ⟨rt, hrt, hle⟩ := h.1 rs hrs hf hg
  have heq : t rt = s rs := hle.final_eq ho
  exact ⟨rt, hrt, by rw [heq, ho], by rw [heq]⟩

/-- **Soundness of refinement.**  Whatever an admissible target prefix
completes with, an admissible source prefix completes with too, unless the
source collided before the target's observations end. -/
theorem RefinesUnder.sound {E O RS RT : Type} {AS : RS → Prop} {AT : RT → Prop}
    {FS G : RS → Prop} {s : Prefixes RS E O} {t : Prefixes RT E O}
    (h : RefinesUnder AS AT FS G s t) {rt : RT} (hrt : AT rt)
    (hn : NoCollisionUpTo AS FS G s (t rt)) {o : O} (ho : (t rt).final = some o) :
    ∃ rs, AS rs ∧ (s rs).final = some o ∧ (s rs).events = (t rt).events := by
  obtain ⟨rs, hrs, hl⟩ := h.2 rt hrt
  rcases hl with l | ⟨hf, hng, hp⟩
  · have heq : s rs = t rt := l.final_eq ho
    exact ⟨rs, hrs, by rw [heq, ho], by rw [heq]⟩
  · exact absurd (hn rs hrs hf hp) hng

/-- **Divergence transfers** to target prefixes up to whose observations the
source does not collide. -/
theorem RefinesUnder.diverges {E O RS RT : Type} {AS : RS → Prop} {AT : RT → Prop}
    {FS G : RS → Prop} {s : Prefixes RS E O} {t : Prefixes RT E O}
    (h : RefinesUnder AS AT FS G s t) (hs : s.Diverges AS) :
    t.Diverges fun rt => AT rt ∧ NoCollisionUpTo AS FS G s (t rt) := by
  intro rt ⟨hrt, hn⟩
  cases ho : (t rt).final with
  | none => rfl
  | some o =>
    obtain ⟨rs, hrs, hfin, _⟩ := h.sound hrt hn ho
    rw [hs rs hrs] at hfin
    cases hfin

/-- **Safety transfers.**  A prefix property closed downward (what a box
reads: no admissible prefix violates it) holds of every admissible target
prefix up to whose observations the source does not collide, if it holds of
the source. -/
theorem RefinesUnder.safety {E O RS RT : Type} {AS : RS → Prop} {AT : RT → Prop}
    {FS G : RS → Prop} {s : Prefixes RS E O} {t : Prefixes RT E O}
    (h : RefinesUnder AS AT FS G s t)
    (Φ : Prefix E O → Prop) (down : ∀ a b, a.Le b → Φ b → Φ a)
    (hs : ∀ rs, AS rs → Φ (s rs)) :
    ∀ rt, AT rt → NoCollisionUpTo AS FS G s (t rt) → Φ (t rt) := by
  intro rt hrt hn
  obtain ⟨rs, hrs, hl⟩ := h.2 rt hrt
  rcases hl with l | ⟨hf, hng, hp⟩
  · exact down _ _ l (hs rs hrs)
  · exact absurd (hn rs hrs hf hp) hng

/-- `RefinesUnder.completes` without a premise. -/
theorem Refines.completes {E O RS RT : Type} {AS : RS → Prop} {AT : RT → Prop}
    {s : Prefixes RS E O} {t : Prefixes RT E O} (h : Refines AS AT s t)
    {rs : RS} (hrs : AS rs) {o : O} (ho : (s rs).final = some o) :
    ∃ rt, AT rt ∧ (t rt).final = some o ∧ (t rt).events = (s rs).events :=
  (h.under (fun _ => True) fun _ => True).completes hrs trivial trivial ho

/-- `RefinesUnder.sound` without a premise. -/
theorem Refines.sound {E O RS RT : Type} {AS : RS → Prop} {AT : RT → Prop}
    {s : Prefixes RS E O} {t : Prefixes RT E O} (h : Refines AS AT s t)
    {rt : RT} (hrt : AT rt) {o : O} (ho : (t rt).final = some o) :
    ∃ rs, AS rs ∧ (s rs).final = some o ∧ (s rs).events = (t rt).events :=
  (h.under (fun _ => True) fun _ => True).sound hrt (fun _ _ _ _ => trivial) ho

/-- `RefinesUnder.diverges` without a premise. -/
theorem Refines.diverges {E O RS RT : Type} {AS : RS → Prop} {AT : RT → Prop}
    {s : Prefixes RS E O} {t : Prefixes RT E O} (h : Refines AS AT s t)
    (hs : s.Diverges AS) : t.Diverges AT :=
  fun rt hrt => (h.under (fun _ => True) fun _ => True).diverges hs rt
    ⟨hrt, fun _ _ _ _ => trivial⟩

/-- `RefinesUnder.safety` without a premise. -/
theorem Refines.safety {E O RS RT : Type} {AS : RS → Prop} {AT : RT → Prop}
    {s : Prefixes RS E O} {t : Prefixes RT E O} (h : Refines AS AT s t)
    (Φ : Prefix E O → Prop) (down : ∀ a b, a.Le b → Φ b → Φ a)
    (hs : ∀ rs, AS rs → Φ (s rs)) : ∀ rt, AT rt → Φ (t rt) :=
  fun rt hrt => (h.under (fun _ => True) fun _ => True).safety Φ down hs rt hrt
    fun _ _ _ _ => trivial

/-- A compiler pass from `L₁` to `L₂`.  `Dom` is the pass's input domain;
the composition lemma requires every output of the pass before to lie in it,
so a domain never survives as a restriction of the composed theorem. -/
structure Pass {E O : Type} (L₁ L₂ : Lang E O) where
  Dom : L₁.Prog → Prop
  run : (p : L₁.Prog) → Dom p → L₂.Prog
  envAbs : L₂.Env → L₁.Env

/-- **A pass certificate**: the target environments map to source ones and
reach all of them; resources are given constructively (`need`); a source
bound in the forward bounds satisfying the premise is below the target
prefix at `need`, which is again in the forward bounds and satisfies the
target's premise (the pass carries the preimages down); every admissible
target prefix is below an admissible source prefix or the source collided
first (`back`); and a target collision reflects a source one (`reflect`).
`need` is an explicit bound function; that the final one is computable (not
obtained by choice) is a check of the final theorems' axioms and
definitions (G49.03, G54), not something this type enforces. -/
structure Cert {E O : Type} {L₁ L₂ : Lang E O} (π : Pass L₁ L₂) where
  envSound : ∀ e, L₂.Allowed e → L₁.Allowed (π.envAbs e)
  envOnto : ∀ e, L₁.Allowed e → ∃ e', L₂.Allowed e' ∧ π.envAbs e' = e
  need : (p : L₁.Prog) → π.Dom p → L₂.Env → L₁.Res → L₂.Res
  need_ok : ∀ p (h : π.Dom p) e r, L₂.Allowed e → L₁.Admissible r →
    L₁.Forward p (π.envAbs e) r → L₁.Guard p (π.envAbs e) r →
    L₂.Admissible (need p h e r) ∧ L₂.Forward (π.run p h) e (need p h e r) ∧
      L₂.Guard (π.run p h) e (need p h e r) ∧
      (L₁.sem p (π.envAbs e) r).Le (L₂.sem (π.run p h) e (need p h e r))
  back : ∀ p (h : π.Dom p) e r, L₂.Allowed e → L₂.Admissible r →
    ∃ r', L₁.Admissible r' ∧ ((L₂.sem (π.run p h) e r).Le (L₁.sem p (π.envAbs e) r') ∨
      Collided (L₁.Forward p (π.envAbs e)) (L₁.Guard p (π.envAbs e)) (L₁.sem p (π.envAbs e)) r'
        (L₂.sem (π.run p h) e r))
  reflect : ∀ p (h : π.Dom p) e r, L₂.Allowed e → L₂.Admissible r →
    L₂.Forward (π.run p h) e r → ¬ L₂.Guard (π.run p h) e r →
    ∃ r', L₁.Admissible r' ∧
      Collided (L₁.Forward p (π.envAbs e)) (L₁.Guard p (π.envAbs e)) (L₁.sem p (π.envAbs e)) r'
        (L₂.sem (π.run p h) e r)

/-- What a certificate gives for one program and environment. -/
theorem Cert.refines {E O : Type} {L₁ L₂ : Lang E O} {π : Pass L₁ L₂} (c : Cert π)
    (p : L₁.Prog) (h : π.Dom p) (e : L₂.Env) (he : L₂.Allowed e) :
    RefinesUnder L₁.Admissible L₂.Admissible (L₁.Forward p (π.envAbs e))
      (L₁.Guard p (π.envAbs e)) (L₁.sem p (π.envAbs e)) (L₂.sem (π.run p h) e) :=
  ⟨fun r hr hf hg => ⟨c.need p h e r, (c.need_ok p h e r he hr hf hg).1,
      (c.need_ok p h e r he hr hf hg).2.2.2⟩,
    fun r hr => c.back p h e r he hr⟩

/-- Two passes in turn, the second defined on every output of the first. -/
def Pass.comp {E O : Type} {L₁ L₂ L₃ : Lang E O} (π₁ : Pass L₁ L₂) (π₂ : Pass L₂ L₃)
    (closed : ∀ p h, π₂.Dom (π₁.run p h)) : Pass L₁ L₃ where
  Dom := π₁.Dom
  run p h := π₂.run (π₁.run p h) (closed p h)
  envAbs e := π₁.envAbs (π₂.envAbs e)

/-- **The composition lemma**: certificates of two passes, the second total on
the first's outputs, give a certificate of their composition. -/
def Cert.comp {E O : Type} {L₁ L₂ L₃ : Lang E O} {π₁ : Pass L₁ L₂} {π₂ : Pass L₂ L₃}
    (c₁ : Cert π₁) (c₂ : Cert π₂) (closed : ∀ p h, π₂.Dom (π₁.run p h)) :
    Cert (π₁.comp π₂ closed) where
  envSound e he := c₁.envSound _ (c₂.envSound e he)
  envOnto e he := by
    obtain ⟨e₂, he₂, rfl⟩ := c₁.envOnto e he
    obtain ⟨e₃, he₃, rfl⟩ := c₂.envOnto e₂ he₂
    exact ⟨e₃, he₃, rfl⟩
  need p h e r := c₂.need (π₁.run p h) (closed p h) e (c₁.need p h (π₂.envAbs e) r)
  need_ok p h e r he hr hf hg := by
    have h₁ := c₁.need_ok p h (π₂.envAbs e) r (c₂.envSound e he) hr hf hg
    have h₂ := c₂.need_ok (π₁.run p h) (closed p h) e _ he h₁.1 h₁.2.1 h₁.2.2.1
    exact ⟨h₂.1, h₂.2.1, h₂.2.2.1, h₁.2.2.2.trans h₂.2.2.2⟩
  back p h e r he hr := by
    obtain ⟨r₂, hr₂, l₂⟩ := c₂.back (π₁.run p h) (closed p h) e r he hr
    rcases l₂ with l₃₂ | ⟨hf₂, hg₂, hp₂⟩
    · obtain ⟨r₁, hr₁, l₁⟩ := c₁.back p h (π₂.envAbs e) r₂ (c₂.envSound e he) hr₂
      refine ⟨r₁, hr₁, ?_⟩
      rcases l₁ with l₂₁ | ⟨hf₁, hg₁, hp₁⟩
      · exact .inl (l₃₂.trans l₂₁)
      · rcases l₃₂.2 with hn | heq
        · rcases List.prefix_or_prefix_of_prefix hp₁ l₃₂.1 with h₁₃ | h₃₁
          · exact .inr ⟨hf₁, hg₁, h₁₃⟩
          · exact .inl ⟨h₃₁, .inl hn⟩
        · have hp : (L₁.sem p (π₁.envAbs (π₂.envAbs e)) r₁).events <+:
              (L₃.sem (π₂.run (π₁.run p h) (closed p h)) e r).events := by
            rw [← heq]; exact hp₁
          exact .inr ⟨hf₁, hg₁, hp⟩
    · obtain ⟨r₁, hr₁, hf₁, hg₁, hp₁⟩ :=
        c₁.reflect p h (π₂.envAbs e) r₂ (c₂.envSound e he) hr₂ hf₂ hg₂
      exact ⟨r₁, hr₁, .inr ⟨hf₁, hg₁, hp₁.trans hp₂⟩⟩
  reflect p h e r he hr hf hg := by
    obtain ⟨r₂, hr₂, hf₂, hg₂, hp₂⟩ := c₂.reflect (π₁.run p h) (closed p h) e r he hr hf hg
    obtain ⟨r₁, hr₁, hf₁, hg₁, hp₁⟩ :=
      c₁.reflect p h (π₂.envAbs e) r₂ (c₂.envSound e he) hr₂ hf₂ hg₂
    exact ⟨r₁, hr₁, hf₁, hg₁, hp₁.trans hp₂⟩

/-! ## Shared observations at the transaction boundary

The observation types are fixed here so that no pass can choose a weaker one.
Bytes are the ABI bytes of the pinned encoding (S04.02); a panic is a revert
with `Panic(uint256)`'s data, a custom error its selector and arguments.
A frame that runs out of gas, or an external call refused at the call-depth
limit, is a revert with empty data that its caller sees.  Logs, gas and raw
layout are excluded observations (G00); their absence is deliberate, and
event arguments still execute. -/

/-- How a call frame or a transaction ends, as its caller sees it. -/
inductive Outcome where
  | success (returnData : Bytes)
  | revert (revertData : Bytes)
  deriving DecidableEq, Repr

/-- An observable event of a session: what the compiled system asks of the
environment and what the environment answers or asks of it.  The compiled
system is every contract and linked library of the compilation input: a call
between two of its instances, a linked library call (on its caller's
storage) and a call to a precompile (a fixed function) are internal to the
semantics, not events. -/
inductive Event where
  /-- The deployment of the selected contract, with its outcome and, on
  success, its address (`this`). -/
  | deploy (sender : Address) (value : Word) (args : Bytes) (outcome : Outcome)
      (address : Option Address)
  /-- A typed external call or payment to an account outside the system. -/
  | call (callee : Address) (value : Word) (input : Bytes) (static : Bool)
  /-- A creation by the system: `contract` is the created contract's position
  in the compilation input (a source identity), so neither side numbers code;
  the EVM side reads it off the artifact's table (`Artifact.contracts`). -/
  | create (value : Word) (contract : Nat) (args : Bytes)
  /-- The environment's answer to the newest pending call, or the address a
  creation produced (`none` when it failed). -/
  | answer (outcome : Outcome) (created : Option Address)
  /-- A completed transaction of a session, with its request and outcome. -/
  | tx (sender target : Address) (value timestamp : Word) (input : Bytes) (outcome : Outcome)
  /-- A callback: while a call of the system is pending, the environment calls
  an instance of the system, statically (`STATICCALL`) or not. -/
  | reenter (target sender : Address) (value : Word) (input : Bytes) (static : Bool)
  /-- The outcome of the newest callback, as the environment sees it. -/
  | reentered (outcome : Outcome)
  /-- Ether credited to an account without running its code: a block
  beneficiary's fee, a foreign `SELFDESTRUCT`, a withdrawal. -/
  | credit (target : Address) (value : Word)
  deriving DecidableEq, Repr

/-! ## The session environment

Every layer reads one environment type.  The callee strategy is a function
of the whole history, so callee answers depend on earlier calls, and it may
call back into the system at any depth.  The strategy answers whatever the
gas the system forwards (G01 Q7).  Payments to untyped recipients are calls
the strategy may accept or refuse. -/

/-- A transaction request. -/
structure Request where
  sender : Address
  target : Address
  value : Word
  timestamp : Word
  input : Bytes
  deriving DecidableEq, Repr

/-- What the environment does while a call of the system is pending. -/
inductive Move where
  /-- The pending call returns (a payment is accepted or refused). -/
  | answer (outcome : Outcome)
  /-- A callback into the system. -/
  | reenter (target sender : Address) (value : Word) (input : Bytes) (static : Bool)
  /-- A credit without a call (a foreign `SELFDESTRUCT`); the strategy is
  asked again after it. -/
  | credit (target : Address) (value : Word)
  deriving DecidableEq, Repr

/-- What the environment does between transactions. -/
inductive Action where
  | request (q : Request)
  /-- A credit without a call (a block beneficiary's fee, a withdrawal). -/
  | credit (target : Address) (value : Word)
  deriving DecidableEq, Repr

/-- A history-dependent callee strategy. -/
abbrev Strategy := List Event → Move

/-- The balance of an external account after a history, from the opening
balances: the G03 ledger, a fixed definition.  An external account's balance
moves only by events (payments to it, the value it sends, credits); value
moved between instances of the system is internal to the semantics. -/
abbrev Ledger := (Address → Word) → List Event → Address → Word

/-- The environment of a session.  `this` is the address the deployment
produces from `deployer` and `deployNonce` (`Fixed.createAddress`); the
system's own balance follows from the deployment value, the events (credits
included) and its internal transfers. -/
structure SessionEnv where
  deployer : Address
  deployNonce : Fin (2 ^ 64)
  deployValue : Word
  deployArgs : Bytes
  balance : Address → Word
  /-- Whether an account outside the system has code after a history (what
  `extcodesize` reads). -/
  hasCode : List Event → Address → Bool
  /-- The `i`-th action after a history, counting every action issued so far
  (a dropped request leaves the history unchanged); `none` ends the
  session. -/
  requests : List Event → Nat → Option Action
  callee : Strategy

/-- The fixed parameters both sides read, none of them an environment input:
G06's shared functions (`Evm.Fixed`: the hash, the precompiles and their
gas), the ledger, the length `regionLen` of the storage region a hashed slot
starts (an array's elements, a struct's fields) and the number `rootSlots`
of root slots `0, …, rootSlots - 1` of the static layout. -/
structure Fixed where
  evm : Evm.Fixed
  ledger : Ledger
  regionLen : Nat
  rootSlots : Nat

/-- The fixed hash, as a word. -/
def Fixed.hash (F : Fixed) (b : Bytes) : Word := ⟨F.evm.keccak b, F.evm.keccak_lt b⟩

/-- The address a creation by `sender` with `nonce` produces
(`Evm.Fixed.createAddress`). -/
def Fixed.createAddress (F : Fixed) (sender : Address) (nonce : Fin (2 ^ 64)) : Address :=
  ⟨F.evm.createAddress sender.val nonce.val, F.evm.createAddress_lt _ _⟩

/-- The region parameters are sane: regions of at least one and at most
`2^128` slots, at most `2^128` root slots.  Without it the region premise
fails on every hashing run (`rootSlots ≥ 2^256`) or vanishes
(`regionLen = 0`). -/
def Fixed.Sane (F : Fixed) : Prop :=
  1 ≤ F.regionLen ∧ F.regionLen ≤ 2 ^ 128 ∧ F.rootSlots ≤ 2 ^ 128

/-- **The hash premise over a list of preimages** (G01 Q3 and the second
round): the hash does not collide on them, and the regions of `regionLen`
slots their hashes start overlap neither each other nor a root slot
(`Solidity.Hash.RegionsDisjoint` modulo `2^256`). -/
def HashPremise (F : Fixed) (xs : List Bytes) : Prop :=
  Solidity.Hash.CollisionFree F.hash xs ∧
    Solidity.Hash.RegionsDisjoint (2 ^ 256) F.regionLen (fun b => (F.hash b).val)
      (List.range F.rootSlots) xs

/-- A run that hashes nothing meets the premise. -/
theorem HashPremise.nil (F : Fixed) : HashPremise F [] :=
  ⟨Solidity.Hash.CollisionFree.nil, Solidity.Hash.RegionsDisjoint.nil⟩

/-- Fewer preimages keep the premise. -/
theorem HashPremise.of_prefix {F : Fixed} {xs ys : List Bytes} (h : xs <+: ys)
    (hy : HashPremise F ys) : HashPremise F xs :=
  ⟨hy.1.of_prefix h, hy.2.of_prefix h⟩

/-- Every action's value is affordable: no transaction runs whose value
exceeds its sender's ledger balance (such a request is invalid and
dropped). -/
def Lang.Affordable (L : Lang Event Outcome) (F : Fixed) (session : L.Env → SessionEnv) :
    Prop :=
  ∀ p e r h s t v ts i o, h ++ [Event.tx s t v ts i o] <+: (L.sem p e r).events →
    v.val ≤ (F.ledger (session e).balance h s).val

/-- Address 0 has no code. -/
def SessionEnv.ZeroHasNoCode (e : SessionEnv) : Prop :=
  ∀ h, e.hasCode h Address.zero = false

/-- A precompile has no code (`extcodesize` reads 0 there). -/
def SessionEnv.PrecompilesHaveNoCode (e : SessionEnv) : Prop :=
  ∀ h a, Address.Precompile a → e.hasCode h a = false

/-- The session issues one action: the first request, and nothing after. -/
def SessionEnv.OneRequest (e : SessionEnv) : Prop :=
  ∀ h i, 1 ≤ i → e.requests h i = none

/-- A call to an account without code runs nothing: it succeeds at once with
no data. -/
def SessionEnv.CodelessSucceeds (e : SessionEnv) : Prop :=
  ∀ h a v i s, e.hasCode h a = false →
    e.callee (h ++ [.call a v i s]) = .answer (.success [])

/-- The allowed session environments: address 0 and the precompiles without
code, codeless accounts running nothing, and otherwise any requests and any
strategy
(unbounded reentrancy, any answer to any call or payment to an account with
code).  Unaffordable requests are allowed and dropped (`Lang.Affordable`). -/
def SessionEnv.Allowed (e : SessionEnv) : Prop :=
  e.ZeroHasNoCode ∧ e.PrecompilesHaveNoCode ∧ e.CodelessSucceeds

/-- The no-callback reading (`transferSemantics:noCallback`): the strategy
never calls back. -/
def SessionEnv.NoCallback (e : SessionEnv) : Prop :=
  ∀ h t s v i st, e.callee h ≠ .reenter t s v i st

/-- The same environment with every callback replaced by a refusal. -/
def SessionEnv.withoutCallbacks (e : SessionEnv) : SessionEnv :=
  { e with callee := fun h => match e.callee h with
    | .reenter _ _ _ _ _ => .answer (.revert [])
    | m => m }

theorem SessionEnv.withoutCallbacks_noCallback (e : SessionEnv) :
    e.withoutCallbacks.NoCallback := by
  intro h t s v i st
  simp only [SessionEnv.withoutCallbacks]
  cases e.callee h <;> simp

/-- **The no-callback reading is a special case**: the allowed environments
contain the no-callback ones, so a statement over every allowed environment
holds of them; it is never a premise. -/
theorem SessionEnv.Allowed.withoutCallbacks {e : SessionEnv} (he : e.Allowed) :
    e.withoutCallbacks.Allowed :=
  ⟨he.1, he.2.1, fun h a v i s hc => by
    simp only [SessionEnv.withoutCallbacks, he.2.2 h a v i s hc]⟩

/-- Every deployment the language reports produces the address `Fixed`
computes from the session's deployer and nonce: `this` comes from the
deployment. -/
def Lang.ThisFromDeployment (L : Lang Event Outcome) (F : Fixed)
    (session : L.Env → SessionEnv) : Prop :=
  ∀ p e r s v a o x, Event.deploy s v a o (some x) ∈ (L.sem p e r).events →
    x = F.createAddress (session e).deployer (session e).deployNonce

/-- No event of the language calls a precompile: precompiles are fixed
functions inside the semantics. -/
def Lang.PrecompilesFixed (L : Lang Event Outcome) : Prop :=
  ∀ p e r c v i s, Event.call c v i s ∈ (L.sem p e r).events → ¬ c.Precompile

/-! ## Settings -/

/-- solc's ABI coders. -/
inductive AbiCoder where
  | v1
  | v2
  deriving DecidableEq, Repr

/-- solc's two code-generation pipelines: legacy, with the ABI coder each
unit's pragma selects, and via-IR, with ABI coder v2. -/
inductive Pipeline where
  | legacy
  | viaIR
  deriving DecidableEq, Repr

/-- The two pipelines. -/
def pipelines : List Pipeline := [.legacy, .viaIR]

theorem mem_pipelines (q : Pipeline) : q ∈ pipelines := by
  cases q <;> simp [pipelines]

/-! ## Artifacts -/

/-- The code of one contract or library: creation and runtime bytes, with
the positions of its unresolved library references. -/
structure CodeUnit where
  initcode : Bytes
  runtime : Bytes
  /-- Byte offsets in `runtime` and the library (its position in
  `Artifact.contracts`) each must be linked to. -/
  links : List (Nat × Nat) := []

/-- The bytecode artifacts of one compilation: a unit per contract and
library of the input, by position, and the selected one.  The source
semantics takes it as a parameter: `type(C).creationCode` and
`type(C).runtimeCode` are the bytes it holds for `C` (G00 Q5). -/
structure Artifact where
  contracts : List CodeUnit
  main : Nat

/-- The creation bytes the table holds for the contract at position `k`. -/
def Artifact.initcode (art : Artifact) (k : Nat) : Bytes :=
  ((art.contracts[k]?).map CodeUnit.initcode).getD []

/-- No nonempty unit's creation bytes are a prefix of another's, so the
creation bytes of a `CREATE` name the unit they come from (interfaces and
abstract contracts have empty creation bytes and are never created). -/
def Artifact.PrefixFree (art : Artifact) : Prop :=
  ∀ j k, j < art.contracts.length → k < art.contracts.length → j ≠ k →
    art.initcode j ≠ [] → ¬ art.initcode j <+: art.initcode k

/-- The creations of a history: the position of the created contract and the
constructor arguments. -/
def createsOf (h : List Event) : List (Nat × Bytes) :=
  h.filterMap fun
    | .create _ c a => some (c, a)
    | _ => none

/-! ## The six contracts -/

/-- The source side, all independent of the compiler (S00–S05): raw input,
syntax, the resolved typed declaration graph, its judgments and the
transaction-sequence semantics.  `Input` is a whole compilation input (named
source units, the selected unit and the settings, its pipeline and an empty
library link map among them); a resolution records the pipeline and the
ABI coder of each unit.  `meaning` reads the artifact table only for
`creationCode` and `runtimeCode`, as bytes. -/
structure SourceSpec where
  Input : Type
  Syntax : Type
  Resolved : Type
  /-- The pinned grammar (S00), a relation, not the parser. -/
  Parses : Input → Syntax → Prop
  /-- Name resolution and static typing (S01), a relation. -/
  Resolves : Syntax → Resolved → Prop
  WellFormed : Resolved → Prop
  /-- The approved profile (G00), by features and their combinations. -/
  InProfile : Resolved → Prop
  /-- Deployment and transaction sequences (S03, S04.04). -/
  lang : Lang Event Outcome
  meaning : (r : Resolved) → WellFormed r → InProfile r → Artifact → lang.Prog
  /-- Some environment is allowed (G07 supplies nontrivial ones). -/
  inhabited : ∃ e, lang.Allowed e
  /-- The pipeline an input selects, and the input with the other one. -/
  pipeline : Input → Pipeline
  setPipeline : Input → Pipeline → Input
  pipeline_set : ∀ i q, pipeline (setPipeline i q) = q
  /-- The ABI coder the pragma of the input's `k`-th source unit selects,
  and the one that unit compiles with: the pragma's under legacy, v2 under
  via-IR (G05's per-unit `CoderMode`). -/
  pragmaCoder : Input → Nat → AbiCoder
  coder : Input → Nat → AbiCoder
  coder_legacy : ∀ i k, pipeline i = .legacy → coder i k = pragmaCoder i k
  coder_viaIR : ∀ i k, pipeline i = .viaIR → coder i k = .v2
  /-- The pipeline and per-unit ABI coders a resolution was resolved under,
  which the meaning reads. -/
  pipelineOf : Resolved → Pipeline
  coderOf : Resolved → Nat → AbiCoder
  /-- The settings' library link map (library name, address). -/
  linkMap : Input → List (String × Address)
  /-- The source cost rule (compiler-independent, cold EIP-2929 costs):
  whether the `receive` or fallback body of the contract at a position of
  the input fits the 2300-gas stipend of a `transfer` or `send` to an
  instance of it; the source fails the payment otherwise. -/
  stipendFits : Resolved → Nat → Bool
  /-- The fixed parameters. -/
  fixed : Fixed
  /-- The environment is the session environment, exactly. -/
  session : lang.Env → SessionEnv
  ofSession : SessionEnv → lang.Env
  session_of : ∀ s, session (ofSession s) = s
  of_session : ∀ e, ofSession (session e) = e
  allowed_iff : ∀ e, lang.Allowed e ↔ (session e).Allowed
  /-- The resource failures of a bound (G06's `FailurePoints`: each
  request's fate, dropped or run with its post-fee sender balance and an
  optional failure point, and each external frame's), and those without a
  failure. -/
  Failures : Type
  failures : lang.Res → Failures
  withFailures : lang.Res → Failures → lang.Res
  failures_with : ∀ r x, failures (withFailures r x) = x
  NoFail : Failures → Prop
  /-- The preimages a source prefix determines (G06's F7), in order: every
  hash the source semantics evaluates (`keccak256`, selectors computed at
  run time, indexed dynamic event arguments) and the slot preimages, under
  the pinned storage layout, of every storage object it touches (reads,
  writes, `delete`, `push`, `pop`). -/
  hashed : lang.Prog → lang.Env → lang.Res → List Bytes
  hashed_consistent : ∀ p e r r', lang.resLE.le r r' → hashed p e r <+: hashed p e r'
  /-- Adequacy speaks of the runs without resource failures hashing fewer
  than `hashBound` distinct preimages; the premise is the hash premise on
  them. -/
  forward_iff : ∀ p e r, lang.Forward p e r ↔
    NoFail (failures r) ∧ distinctCount (hashed p e r) < hashBound
  guard_iff : ∀ p e r, lang.Guard p e r ↔ HashPremise fixed (hashed p e r)

/-- The source is idealized: every bound is admissible (unbounded fuel and
recursion, every failure point), so its prefixes are all of its behaviour
(G01 Q1). -/
def SourceSpec.Idealized (S : SourceSpec) : Prop := ∀ r, S.lang.Admissible r

/-- A bound without resource failures: the run as if gas were unbounded
(only the call-depth limit and the stipend rule fail frames, as on the
EVM). -/
def SourceSpec.NoFailure (S : SourceSpec) (r : S.lang.Res) : Prop := S.NoFail (S.failures r)

/-- The source's judgments are functions where the contract needs them: an
input has one parse, a parse one resolution. -/
def SourceSpec.Unambiguous (S : SourceSpec) : Prop :=
  (∀ i s s', S.Parses i s → S.Parses i s' → s = s') ∧
  (∀ s r r', S.Resolves s r → S.Resolves s r' → r = r')

/-- The admitted source inputs, with their resolution. -/
def SourceSpec.Admitted (S : SourceSpec) (i : S.Input) (r : S.Resolved) : Prop :=
  ∃ s, S.Parses i s ∧ S.Resolves s r ∧ S.WellFormed r ∧ S.InProfile r

/-- Both pipelines are settings: an admitted input stays admitted under
each (G00 Q4, second round). -/
def SourceSpec.AllPipelines (S : SourceSpec) : Prop :=
  ∀ i q, (∃ r, S.Admitted i r) → ∃ r, S.Admitted (S.setPipeline i q) r

/-- A resolution records the settings of its input. -/
def SourceSpec.SettingsResolved (S : SourceSpec) : Prop :=
  ∀ i r, S.Admitted i r → S.pipelineOf r = S.pipeline i ∧ ∀ k, S.coderOf r k = S.coder i k

/-- Only the empty library link map is admitted. -/
def SourceSpec.NoLinkMap (S : SourceSpec) : Prop :=
  ∀ i r, S.Admitted i r → S.linkMap i = []

/-- The source's approved readings: idealized, precompiles fixed, `this`
from the deployment, values affordable, settings recorded, only the empty
link map, and sane region parameters. -/
def SourceSpec.Approved (S : SourceSpec) : Prop :=
  S.Idealized ∧ S.lang.PrecompilesFixed ∧ S.lang.ThisFromDeployment S.fixed S.session ∧
    S.lang.Affordable S.fixed S.session ∧ S.SettingsResolved ∧ S.NoLinkMap ∧ S.fixed.Sane

/-- **Non-vacuity of a source definition** (G07, S05): inputs the source
admits whose meanings, at allowed environments, in the forward bounds and
under the premise (say, hashing nothing), complete with a success carrying
data and complete with a revert, and one whose single request (or
deployment) diverges without resource failures, whatever the artifact
table.  Each witness starts from an
admitted input, so a `SourceSpec` with an empty input type, `Parses :=
False` or `InProfile := False` has none. -/
def SourceSpec.NonVacuous (S : SourceSpec) : Prop :=
  (∃ i r w p e rs d, S.Admitted i r ∧ S.lang.Allowed e ∧ S.lang.Admissible rs ∧ d ≠ [] ∧
    ∀ art, S.lang.Forward (S.meaning r w p art) e rs ∧ S.lang.Guard (S.meaning r w p art) e rs ∧
      (S.lang.sem (S.meaning r w p art) e rs).final = some (.success d)) ∧
  (∃ i r w p e rs d, S.Admitted i r ∧ S.lang.Allowed e ∧ S.lang.Admissible rs ∧
    ∀ art, S.lang.Forward (S.meaning r w p art) e rs ∧ S.lang.Guard (S.meaning r w p art) e rs ∧
      (S.lang.sem (S.meaning r w p art) e rs).final = some (.revert d)) ∧
  (∃ i r w p e, S.Admitted i r ∧ S.lang.Allowed e ∧ (S.session e).OneRequest ∧
    ∀ art, (S.lang.sem (S.meaning r w p art) e).Diverges
      fun rs => S.lang.Admissible rs ∧ S.NoFailure rs)

/-- **Contract 1, source admission and parsing.**  The frontend accepts
exactly the well-formed in-profile inputs, with their resolution.  A
proof-producing frontend instantiates `frontend` by its checked certificate
(`checked`: the checker's acceptance implies the relation). -/
structure Admission (S : SourceSpec) where
  frontend : S.Input → Option S.Resolved
  sound : ∀ i r, frontend i = some r → S.Admitted i r
  complete : ∀ i r, S.Admitted i r → frontend i = some r

/-- A frontend whose result carries a certificate checked in Lean. -/
structure CheckedFrontend (S : SourceSpec) where
  Cert : Type
  produce : S.Input → Option (S.Resolved × Cert)
  check : S.Input → S.Resolved → Cert → Bool
  checked : ∀ i r c, check i r c = true → S.Admitted i r
  accepted : ∀ i r c, produce i = some (r, c) → check i r c = true
  complete : ∀ i r, S.Admitted i r → ∃ c, produce i = some (r, c)

/-- The intrinsic layer: typed contract worlds (`Contract`, `Prog C Γ Γ'`,
`State C Γ` and a world of typed instances), with their own semantics.
`ofWorld` runs the sessions from a world; `worlds` lists the worlds a prefix
reaches at its transaction boundaries.  Like the source, it reads the
session environment exactly, and its `Forward` and `Guard` are pinned: runs
without resource failure hashing fewer than `hashBound` distinct preimages,
and the hash premise on them, where the preimages of a run resumed from a
world include the keys the world stores. -/
structure IntrinsicSpec where
  World : Type
  lang : Lang Event Outcome
  ofWorld : World → lang.Prog
  worlds : lang.Prog → lang.Env → lang.Res → List World
  fixed : Fixed
  session : lang.Env → SessionEnv
  ofSession : SessionEnv → lang.Env
  session_of : ∀ s, session (ofSession s) = s
  of_session : ∀ e, ofSession (session e) = e
  allowed_iff : ∀ e, lang.Allowed e ↔ (session e).Allowed
  NoFail : lang.Res → Prop
  hashed : lang.Prog → lang.Env → lang.Res → List Bytes
  forward_iff : ∀ p e r, lang.Forward p e r ↔
    NoFail r ∧ distinctCount (hashed p e r) < hashBound
  guard_iff : ∀ p e r, lang.Guard p e r ↔ HashPremise fixed (hashed p e r)

/-- **Contract 2, lowering.**  Total on admitted source (the proofs are
arguments: no `Option`), for every artifact table, and the source meaning
refines the lowered world's, in both directions, at every allowed
environment. -/
structure Lowering (S : SourceSpec) (I : IntrinsicSpec) where
  lower : (r : S.Resolved) → S.WellFormed r → S.InProfile r → Artifact → I.World
  pass : Pass S.lang I.lang
  dom : ∀ r w p art, pass.Dom (S.meaning r w p art)
  agrees : ∀ r w p art, pass.run (S.meaning r w p art) (dom r w p art) = I.ofWorld (lower r w p art)
  cert : Cert pass

/-- The pinned Osaka EVM (G06): accounts with code, executing transactions
from bytes, with every account outside the system played by the session
environment's strategy.  `pin` is G06's `Evm.Pin`.  A bound is a horizon and
a gas schedule (`gas`: the gas of the frame the system starts after a
history, a transaction's limit or what the environment forwards into a
callback); a frame out of gas reverts and the session continues.  Every gas
schedule is admissible: the per-transaction cap (EIP-7825) and the block gas
limit are a recorded idealization, as are the code-size limits (EIP-170,
EIP-3860), so code size is not a resource; nor are stack and memory:
internal calls keep their frames in memory, so recursion is bounded only by
gas. -/
structure EvmSpec where
  lang : Lang Event Outcome
  /-- A deployment session of the artifact: install the selected unit's
  creation bytes with the libraries linked, then run transactions. -/
  load : Artifact → lang.Prog
  pin : Evm.Pin
  fixed : Fixed
  session : lang.Env → SessionEnv
  ofSession : SessionEnv → lang.Env
  session_of : ∀ s, session (ofSession s) = s
  of_session : ∀ e, ofSession (session e) = e
  allowed_iff : ∀ e, lang.Allowed e ↔ (session e).Allowed
  gas : lang.Res → List Event → Nat
  withGas : lang.Res → (List Event → Nat) → lang.Res
  gas_with : ∀ r g, gas (withGas r g) = g
  /-- The `KECCAK256` preimages a prefix hashes, in order. -/
  hashed : lang.Prog → lang.Env → lang.Res → List Bytes
  /-- The creation bytes (with constructor arguments) of each `CREATE` the
  system executes in a prefix, in order. -/
  created : lang.Prog → lang.Env → lang.Res → List Bytes
  /-- EVM worlds (accounts, code, storage, balances) at transaction
  boundaries, their balances, and the sessions from one. -/
  World : Type
  worlds : lang.Prog → lang.Env → lang.Res → List World
  balances : World → Address → Word
  resume : World → lang.Prog

/-- The EVM's approved readings: the Osaka pin with its idealizations
(`Evm.pinned`), sane region parameters, every horizon and gas schedule admissible, no premise or
forward restriction of its own (it is only a target), precompiles fixed
functions, `this` from the deployment, and values affordable. -/
def EvmSpec.Approved (V : EvmSpec) : Prop :=
  V.pin = Evm.pinned ∧ V.fixed.Sane ∧ (∀ r, V.lang.Admissible r) ∧
    (∀ p e r, V.lang.Forward p e r ∧ V.lang.Guard p e r) ∧ V.lang.PrecompilesFixed ∧
    V.lang.ThisFromDeployment V.fixed V.session ∧ V.lang.Affordable V.fixed V.session

/-- The fixed parameters are the real ones: Keccak-256 (G06's `keccakWord`)
and sane regions.  The public statement quantifies over the hash and
instantiates it here. -/
def Fixed.Keccak (F : Fixed) : Prop := (∀ b, F.evm.keccak b = Evm.keccakWord b) ∧ F.Sane

/-- **Contract 3, compilation.**  Every lowered world has an artifact (total),
through a chain of certified passes from the intrinsic language to an
assembly language whose programs are instruction lists. -/
structure Compilation (I : IntrinsicSpec) (Asm : Lang Event Outcome) where
  compile : I.World → Asm.Prog
  pass : Pass I.lang Asm
  dom : ∀ w, pass.Dom (I.ofWorld w)
  agrees : ∀ w, pass.run (I.ofWorld w) (dom w) = compile w
  cert : Cert pass

/-- **Contract 4, EVM execution.**  Assembly, encoding and the pinned EVM:
every assembly program has bytes whose execution refines it. -/
structure Execution (Asm : Lang Event Outcome) (V : EvmSpec) where
  assemble : Asm.Prog → Artifact
  pass : Pass Asm V.lang
  dom : ∀ a, pass.Dom a
  agrees : ∀ a, pass.run a (dom a) = V.load (assemble a)
  cert : Cert pass

/-- An EVM prefix is matched by a source prefix in the forward bounds that
meets the premise: the state export speaks of these.  The premise is the
source's, so the compiler cannot make it fail (by hashing a known collision
pair, or the same preimage `2^128` times). -/
def Matched (S : SourceSpec) (p : S.lang.Prog) (e : S.lang.Env) (b : Prefix Event Outcome) :
    Prop :=
  ∃ rs, S.lang.Admissible rs ∧ S.lang.Forward p e rs ∧ S.lang.Guard p e rs ∧
    b.Le (S.lang.sem p e rs)

/-- The state export of the public theorem (G01 Q6): the lowering whose
worlds are decoded, the decoding of EVM worlds given the preimages hashed so
far (a slot is decoded through the preimage it was hashed from, never by
inverting the hash), and the environment map to the intrinsic layer. -/
structure StateExport (S : SourceSpec) (I : IntrinsicSpec) (V : EvmSpec) where
  lowering : Lowering S I
  decode : List Bytes → V.World → Option I.World
  envAbs : V.lang.Env → I.lang.Env

/-- **Contract 5, composition: the public theorem.**  For every admitted
input, under both pipelines, the compiler produces bytes whose creations
come from its own table and whose hashes are preimages the source
determines; the source reads the EVM's own session environment and fixed
parameters; for every allowed EVM environment the source meaning, at the
artifact table the compiler produced, refines the deployed bytes' sessions
under the per-run hash premise on the source; and `decode` maps every EVM
world the sessions reach to the intrinsic world the lowered program reaches,
with the same observations from there on.  The approved readings
(`SourceSpec.Approved`, `EvmSpec.Approved`, `Fixed.Keccak`) are separate
conjuncts of the final statement. -/
structure PublicCorrectness {I : IntrinsicSpec} (S : SourceSpec) (V : EvmSpec)
    (compiler : S.Input → Option Artifact) (envAbs : V.lang.Env → S.lang.Env)
    (X : StateExport S I V) : Prop where
  coverage : ∀ i, (∃ r, S.Admitted i r) ↔ (compiler i).isSome
  bothPipelines : S.AllPipelines
  envOnto : ∀ e, S.lang.Allowed e → ∃ e', V.lang.Allowed e' ∧ envAbs e' = e
  fixed : S.fixed = V.fixed
  session : ∀ e, S.session (envAbs e) = V.session e
  envAbs_agrees : ∀ e, X.lowering.pass.envAbs (X.envAbs e) = envAbs e
  /-- The intrinsic layer reads the same environment and fixed parameters. -/
  ifixed : I.fixed = V.fixed
  isession : ∀ e, I.session (X.envAbs e) = V.session e
  /-- `type(C).creationCode` is what `new C` deploys: every `CREATE` runs the
  table's creation bytes for the contract its event names. -/
  creates_table : ∀ i art, compiler i = some art → art.PrefixFree ∧
    ∀ e rt, V.created (V.load art) e rt =
      (createsOf (V.lang.sem (V.load art) e rt).events).map fun ca => art.initcode ca.1 ++ ca.2
  /-- The bytes hash only preimages the source determines (each at some
  source bound: a failing transaction may hash before it fails). -/
  hashes_source : ∀ i r, S.Admitted i r → ∀ (w : S.WellFormed r) (p : S.InProfile r) art,
    compiler i = some art → ∀ e rt, V.lang.Allowed e → V.lang.Admissible rt →
      ∀ b, b ∈ V.hashed (V.load art) e rt →
        ∃ rs, S.lang.Admissible rs ∧ b ∈ S.hashed (S.meaning r w p art) (envAbs e) rs
  refines : ∀ i r, S.Admitted i r → ∀ (w : S.WellFormed r) (p : S.InProfile r) art,
    compiler i = some art → ∀ e, V.lang.Allowed e → S.lang.Allowed (envAbs e) ∧
      RefinesUnder S.lang.Admissible V.lang.Admissible
        (S.lang.Forward (S.meaning r w p art) (envAbs e))
        (S.lang.Guard (S.meaning r w p art) (envAbs e))
        (S.lang.sem (S.meaning r w p art) (envAbs e)) (V.lang.sem (V.load art) e)
  decode_reach : ∀ i r, S.Admitted i r → ∀ (w : S.WellFormed r) (p : S.InProfile r) art,
    compiler i = some art → ∀ e, V.lang.Allowed e → ∀ rt, V.lang.Admissible rt →
      Matched S (S.meaning r w p art) (envAbs e) (V.lang.sem (V.load art) e rt) →
      ∃ ri, I.lang.Admissible ri ∧
        (V.worlds (V.load art) e rt).map (X.decode (V.hashed (V.load art) e rt)) =
          (I.worlds (I.ofWorld (X.lowering.lower r w p art)) (X.envAbs e) ri).map some
  decode_commutes : ∀ i r, S.Admitted i r → ∀ (w : S.WellFormed r) (p : S.InProfile r) art,
    compiler i = some art → ∀ e rt, V.lang.Allowed e → V.lang.Admissible rt →
      Matched S (S.meaning r w p art) (envAbs e) (V.lang.sem (V.load art) e rt) →
      ∀ ω, ω ∈ V.worlds (V.load art) e rt →
      ∀ ω', X.decode (V.hashed (V.load art) e rt) ω = some ω' →
      ∀ e', V.lang.Allowed e' → (V.session e').balance = V.balances ω →
        I.lang.Allowed (X.envAbs e') ∧
        RefinesUnder I.lang.Admissible V.lang.Admissible
          (I.lang.Forward (I.ofWorld ω') (X.envAbs e')) (I.lang.Guard (I.ofWorld ω') (X.envAbs e'))
          (I.lang.sem (I.ofWorld ω') (X.envAbs e')) (V.lang.sem (V.resume ω) e')

/-- **Contract 6, specification transfer.**  A source specification, read on
the source's prefixes, holds of the bytes: a safety specification at every
admissible prefix up to whose observations the source does not collide, a
completion in the forward bounds and under the premise at some admissible
prefix.  `Proves` derivations reach it through G51's bridge from `⊨` to
`holdsSafe`. -/
def SpecTransfer (S : SourceSpec) (V : EvmSpec) (compiler : S.Input → Option Artifact)
    (envAbs : V.lang.Env → S.lang.Env) : Prop :=
  ∀ i r, S.Admitted i r → ∀ (w : S.WellFormed r) (p : S.InProfile r) art, compiler i = some art →
    ∀ e, V.lang.Allowed e →
      (∀ Φ : Prefix Event Outcome → Prop, (∀ a b, a.Le b → Φ b → Φ a) →
        (∀ rs, S.lang.Admissible rs → Φ (S.lang.sem (S.meaning r w p art) (envAbs e) rs)) →
        ∀ rt, V.lang.Admissible rt →
          NoCollisionUpTo S.lang.Admissible (S.lang.Forward (S.meaning r w p art) (envAbs e))
            (S.lang.Guard (S.meaning r w p art) (envAbs e))
            (S.lang.sem (S.meaning r w p art) (envAbs e)) (V.lang.sem (V.load art) e rt) →
          Φ (V.lang.sem (V.load art) e rt)) ∧
      (∀ o, (∃ rs, S.lang.Admissible rs ∧ S.lang.Forward (S.meaning r w p art) (envAbs e) rs ∧
          S.lang.Guard (S.meaning r w p art) (envAbs e) rs ∧
          (S.lang.sem (S.meaning r w p art) (envAbs e) rs).final = some o) →
        ∃ rt, V.lang.Admissible rt ∧ (V.lang.sem (V.load art) e rt).final = some o)

section
variable {I : IntrinsicSpec} {S : SourceSpec} {V : EvmSpec}
  {compiler : S.Input → Option Artifact} {envAbs : V.lang.Env → S.lang.Env}
  {X : StateExport S I V}

/-- Public correctness gives specification transfer: the sixth contract's
semantic half needs nothing beyond the fifth. -/
theorem PublicCorrectness.transfer (h : PublicCorrectness S V compiler envAbs X) :
    SpecTransfer S V compiler envAbs := by
  intro i r adm w p art hc e he
  have href := (h.refines i r adm w p art hc e he).2
  refine ⟨fun Φ down hs => href.safety Φ down hs, fun o ⟨rs, hrs, hf, hg, ho⟩ => ?_⟩
  obtain ⟨rt, hrt, hfin, _⟩ := href.completes hrs hf hg ho
  exact ⟨rt, hrt, hfin⟩

/-- Every admitted input compiles under both pipelines. -/
theorem PublicCorrectness.allPipelines (h : PublicCorrectness S V compiler envAbs X)
    {i : S.Input} (hi : ∃ r, S.Admitted i r) (q : Pipeline) :
    (compiler (S.setPipeline i q)).isSome :=
  (h.coverage _).1 (h.bothPipelines i q hi)

/-- **A never-compiling compiler fails**: given a non-vacuous source, the
public contract makes the compiler produce an artifact. -/
theorem PublicCorrectness.compiles (h : PublicCorrectness S V compiler envAbs X)
    (hv : S.NonVacuous) : ∃ i art, compiler i = some art := by
  obtain ⟨i, r, _, _, _, _, _, adm, _⟩ := hv.1
  have hs := (h.coverage i).1 ⟨r, adm⟩
  cases hc : compiler i with
  | none => rw [hc] at hs; cases hs
  | some art => exact ⟨i, art, hc⟩

/-- The source's success witness is a success of the compiled bytes at an
allowed environment and an admissible bound, with no premise on the bytes'
own hashes. -/
theorem PublicCorrectness.succeeds (h : PublicCorrectness S V compiler envAbs X)
    (hv : S.NonVacuous) : ∃ i art e rt d, compiler i = some art ∧ V.lang.Allowed e ∧
      V.lang.Admissible rt ∧ d ≠ [] ∧
      (V.lang.sem (V.load art) e rt).final = some (.success d) := by
  obtain ⟨i, r, w, p, e, rs, d, adm, hal, hrs, hd, hw⟩ := hv.1
  have hs := (h.coverage i).1 ⟨r, adm⟩
  cases hc : compiler i with
  | none => rw [hc] at hs; cases hs
  | some art =>
    obtain ⟨e', he', rfl⟩ := h.envOnto e hal
    obtain ⟨hf, hg, hfin⟩ := hw art
    obtain ⟨rt, hrt, ht, _⟩ := (h.refines i r adm w p art hc e' he').2.completes hrs hf hg hfin
    exact ⟨i, art, e', rt, d, hc, he', hrt, hd, ht⟩

/-- **An always-reverting compiler fails**: compiled bytes that never complete
with a success at an allowed environment and admissible bound satisfy the
public contract for no non-vacuous source, whatever they hash. -/
theorem PublicCorrectness.not_alwaysRevert (h : PublicCorrectness S V compiler envAbs X)
    (hv : S.NonVacuous)
    (hrev : ∀ i art e rt d, compiler i = some art → V.lang.Allowed e → V.lang.Admissible rt →
      (V.lang.sem (V.load art) e rt).final ≠ some (.success d)) : False := by
  obtain ⟨i, art, e, rt, d, hc, he, hrt, _, ht⟩ := h.succeeds hv
  exact hrev i art e rt d hc he hrt ht

/-- The source environment is allowed exactly when the EVM's is: both read
the same session environment. -/
theorem PublicCorrectness.allowed_iff (h : PublicCorrectness S V compiler envAbs X)
    (e : V.lang.Env) : S.lang.Allowed (envAbs e) ↔ V.lang.Allowed e := by
  rw [S.allowed_iff, V.allowed_iff, h.session]

/-- `envAbs` is forced: it reads the EVM environment as the same session
environment. -/
theorem PublicCorrectness.envAbs_eq (h : PublicCorrectness S V compiler envAbs X)
    (e : V.lang.Env) : envAbs e = S.ofSession (V.session e) := by
  rw [← h.session e, S.of_session]

end

end Solidity.Roadmap

/-- info: 'Solidity.Roadmap.Cert.comp' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Roadmap.Cert.comp
/-- info: 'Solidity.Roadmap.PublicCorrectness.transfer' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Roadmap.PublicCorrectness.transfer
