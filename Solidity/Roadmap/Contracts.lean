import Solidity.Semantics.RunFuel
import Solidity.Semantics.Lifetime
import Solidity.Evm.Machine

/-!
# The roadmap's final theorem contracts (G01), as statements

`docs/coverage-plan.md` names six final proof obligations; G01 fixes their
types and relations.  This module states them as `Prop`s and structures over
intrinsic types, parameterized where the type does not exist yet (the
independent source semantics of S00–S04, the pinned EVM of G06).  Nothing
here claims a final theorem: the contracts are definitions.  The few lemmas
are checks of the contracts' shape only: refinement is a preorder that
composes, it transfers safety and completion, and a target that never
completes the way a source does (an always-reverting compiler, an erased
observation) cannot refine it.  `docs/feature-work/roadmap-g01-interfaces.md`
explains each definition, its premises, why it is not circular, and how the
existing theorems plug in.

**Executions are consistent families of resourced finite prefixes.**  A
`Prefix` is what a finite execution prefix shows: the events emitted so far
and, when it completed within its resources, the final observation.  Running
out of resources is not an observation: it ends the prefix with `final =
none`, the same as a prefix still running.  Divergence is a family no member
of which completes; no single finite-gas run is claimed to diverge.

**Refinement is two-sided at admissible resources.**  Every admissible
source prefix is below some admissible target prefix (resource adequacy, with
the target's resources given by a function: `Cert.need`); every admissible
target prefix is below some admissible source prefix (functional soundness).
"Below" (`Prefix.Le`) keeps the events a prefix and a completed prefix
exactly, so a success cannot become a failure, a failure cannot become a
success, and no observation can be dropped: the observation types are
shared by both sides and fixed by the contract, not chosen by a pass.

**Environments are quantified, not chosen.**  A pass maps every allowed
target environment to an allowed source environment (`envAbs`, `envSound`)
and reaches every allowed source environment (`envOnto`), so a compiler
cannot be correct by realizing only environments in which nothing happens.

The module stays below the elaborator: it imports the typed run, the
lifetime layer and the EVM machine only.
-/

namespace Solidity.Roadmap

/-! ## Finite prefixes and their order -/

/-- What a finite prefix of an execution shows: the events so far and, if it
completed within the prefix's resources, its final observation. -/
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

/-- More resources extend a prefix; a completed prefix stays as it is.  The
family of every language's semantics must be consistent (S03.04, G46.06). -/
def Prefixes.Consistent {R E O : Type} [LE R] (p : Prefixes R E O) : Prop :=
  ∀ r r', r ≤ r' → (p r).Le (p r')

/-- The execution completes with `o` within some resource bound. -/
def Prefixes.Completes {R E O : Type} (p : Prefixes R E O) (o : O) : Prop :=
  ∃ r, (p r).final = some o

/-- No resource bound lets the execution complete: divergence, or a run the
admitted resources never finish. -/
def Prefixes.Diverges {R E O : Type} (A : R → Prop) (p : Prefixes R E O) : Prop :=
  ∀ r, A r → (p r).final = none

/-- The events the execution emits within some admitted bound. -/
def Prefixes.Emits {R E O : Type} (A : R → Prop) (p : Prefixes R E O) (es : List E) : Prop :=
  ∃ r, A r ∧ es <+: (p r).events

/-! ## Languages, refinement and pass certificates -/

/-- A language at one layer of the pipeline, over the shared events `E` and
final observations `O`.  `Admissible` is the approved resource abstraction of
this layer: every bound for an idealized source, the bounds the approved
profile permits for the EVM (open scope question Q3 of the G01 document). -/
structure Lang (E O : Type) where
  Prog : Type
  Env : Type
  Res : Type
  Allowed : Env → Prop
  Admissible : Res → Prop
  sem : Prog → Env → Prefixes Res E O

/-- Two-sided refinement of one execution at admissible resources. -/
def Refines {E O RS RT : Type} (AS : RS → Prop) (AT : RT → Prop)
    (s : Prefixes RS E O) (t : Prefixes RT E O) : Prop :=
  (∀ rs, AS rs → ∃ rt, AT rt ∧ (s rs).Le (t rt)) ∧
  (∀ rt, AT rt → ∃ rs, AS rs ∧ (t rt).Le (s rs))

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

/-- **Non-vacuity of refinement.**  A source completion at an admissible bound
is a target completion with the same observation at an admissible bound: a
target that never completes with `o` (always reverting, always exhausted,
`o` erased) refines no source that completes with `o`. -/
theorem Refines.completes {E O RS RT : Type} {AS : RS → Prop} {AT : RT → Prop}
    {s : Prefixes RS E O} {t : Prefixes RT E O} (h : Refines AS AT s t)
    {rs : RS} (hrs : AS rs) {o : O} (ho : (s rs).final = some o) :
    ∃ rt, AT rt ∧ (t rt).final = some o ∧ (t rt).events = (s rs).events := by
  obtain ⟨rt, hrt, hle⟩ := h.1 rs hrs
  have heq : t rt = s rs := hle.final_eq ho
  exact ⟨rt, hrt, by rw [heq, ho], by rw [heq]⟩

/-- **Soundness of refinement.**  Whatever an admissible target prefix
completes with, an admissible source prefix completes with too. -/
theorem Refines.sound {E O RS RT : Type} {AS : RS → Prop} {AT : RT → Prop}
    {s : Prefixes RS E O} {t : Prefixes RT E O} (h : Refines AS AT s t)
    {rt : RT} (hrt : AT rt) {o : O} (ho : (t rt).final = some o) :
    ∃ rs, AS rs ∧ (s rs).final = some o ∧ (s rs).events = (t rt).events := by
  obtain ⟨rs, hrs, hle⟩ := h.2 rt hrt
  have heq : s rs = t rt := hle.final_eq ho
  exact ⟨rs, hrs, by rw [heq, ho], by rw [heq]⟩

/-- **Divergence transfers**: a source no admissible bound completes has a
target no admissible bound completes. -/
theorem Refines.diverges {E O RS RT : Type} {AS : RS → Prop} {AT : RT → Prop}
    {s : Prefixes RS E O} {t : Prefixes RT E O} (h : Refines AS AT s t)
    (hs : s.Diverges AS) : t.Diverges AT := by
  intro rt hrt
  cases ho : (t rt).final with
  | none => rfl
  | some o =>
    obtain ⟨rs, hrs, hfin, _⟩ := h.sound hrt ho
    rw [hs rs hrs] at hfin
    cases hfin

/-- **Safety transfers.**  A prefix property closed downward (what a box
reads: no admissible prefix violates it) holds of the target if it holds of
the source. -/
theorem Refines.safety {E O RS RT : Type} {AS : RS → Prop} {AT : RT → Prop}
    {s : Prefixes RS E O} {t : Prefixes RT E O} (h : Refines AS AT s t)
    (Φ : Prefix E O → Prop) (down : ∀ a b, a.Le b → Φ b → Φ a)
    (hs : ∀ rs, AS rs → Φ (s rs)) : ∀ rt, AT rt → Φ (t rt) := by
  intro rt hrt
  obtain ⟨rs, hrs, hle⟩ := h.2 rt hrt
  exact down _ _ hle (hs rs hrs)

/-- A compiler pass from `L₁` to `L₂`.  `Dom` is the pass's input domain;
the composition lemma requires every output of the pass before to lie in it,
so a domain never survives as a restriction of the composed theorem. -/
structure Pass {E O : Type} (L₁ L₂ : Lang E O) where
  Dom : L₁.Prog → Prop
  run : (p : L₁.Prog) → Dom p → L₂.Prog
  envAbs : L₂.Env → L₁.Env

/-- **A pass certificate**: the target environments map to source ones and
reach all of them; resources are given constructively (`need`); every
admissible source prefix is below the target prefix at `need`, and every
admissible target prefix below an admissible source prefix. -/
structure Cert {E O : Type} {L₁ L₂ : Lang E O} (π : Pass L₁ L₂) where
  envSound : ∀ e, L₂.Allowed e → L₁.Allowed (π.envAbs e)
  envOnto : ∀ e, L₁.Allowed e → ∃ e', L₂.Allowed e' ∧ π.envAbs e' = e
  need : (p : L₁.Prog) → π.Dom p → L₂.Env → L₁.Res → L₂.Res
  need_ok : ∀ p (h : π.Dom p) e r, L₂.Allowed e → L₁.Admissible r →
    L₂.Admissible (need p h e r) ∧ (L₁.sem p (π.envAbs e) r).Le (L₂.sem (π.run p h) e (need p h e r))
  back : ∀ p (h : π.Dom p) e r, L₂.Allowed e → L₂.Admissible r →
    ∃ r', L₁.Admissible r' ∧ (L₂.sem (π.run p h) e r).Le (L₁.sem p (π.envAbs e) r')

/-- What a certificate gives for one program and environment. -/
theorem Cert.refines {E O : Type} {L₁ L₂ : Lang E O} {π : Pass L₁ L₂} (c : Cert π)
    (p : L₁.Prog) (h : π.Dom p) (e : L₂.Env) (he : L₂.Allowed e) :
    Refines L₁.Admissible L₂.Admissible (L₁.sem p (π.envAbs e)) (L₂.sem (π.run p h) e) :=
  ⟨fun r hr => ⟨c.need p h e r, (c.need_ok p h e r he hr).1, (c.need_ok p h e r he hr).2⟩,
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
  need_ok p h e r he hr := by
    have h₁ := c₁.need_ok p h (π₂.envAbs e) r (c₂.envSound e he) hr
    have h₂ := c₂.need_ok (π₁.run p h) (closed p h) e _ he h₁.1
    exact ⟨h₂.1, h₁.2.trans h₂.2⟩
  back p h e r he hr := by
    obtain ⟨r₂, hr₂, l₃₂⟩ := c₂.back (π₁.run p h) (closed p h) e r he hr
    obtain ⟨r₁, hr₁, l₂₁⟩ := c₁.back p h (π₂.envAbs e) r₂ (c₂.envSound e he) hr₂
    exact ⟨r₁, hr₁, l₃₂.trans l₂₁⟩

/-! ## Shared observations at the transaction boundary

The observation types are fixed here so that no pass can choose a weaker one.
Bytes are the ABI bytes of the pinned encoding (S04.02); a panic is a revert
with `Panic(uint256)`'s data, a custom error its selector and arguments.
Exhaustion of excluded resources is not an observation (it ends a prefix).
Logs, gas and raw layout are excluded observations (G00); their absence is
deliberate, and event arguments still execute. -/

/-- How a call frame or a transaction ends, as its caller sees it. -/
inductive Outcome where
  | success (returnData : List UInt8)
  | revert (revertData : List UInt8)
  deriving DecidableEq, Repr

/-- An observable event inside a transaction: what the contract asks of the
environment and what the environment answers.  Addresses and values are
EVM words read as natural numbers below `2^256` (`Evm.W`); `input` is the
ABI-encoded call data. -/
inductive Event where
  /-- A typed external call, payment or library call leaving the contract. -/
  | call (callee : Nat) (value : Nat) (input : List UInt8) (static : Bool)
  /-- A creation leaving the contract, with its initcode's arguments. -/
  | create (value : Nat) (code : Nat) (args : List UInt8)
  /-- The environment's answer to the newest pending call or creation. -/
  | answer (outcome : Outcome) (created : Option Nat)
  /-- A completed transaction of a session, with its request and outcome. -/
  | tx (sender value timestamp : Nat) (input : List UInt8) (outcome : Outcome)
  deriving DecidableEq, Repr

/-! ## The six contracts -/

/-- The source side, all independent of the compiler (S00–S05): raw input,
syntax, the resolved typed declaration graph, its judgments and the
transaction-sequence semantics.  `Input` is a whole compilation input (named
source units, the selected unit and the pinned settings). -/
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
  meaning : (r : Resolved) → WellFormed r → InProfile r → lang.Prog
  /-- Some environment is allowed (G07 supplies nontrivial ones). -/
  inhabited : ∃ e, lang.Allowed e

/-- The source is idealized: every bound is admissible, so its prefixes are
all of its behaviour.  The proposed default; a source-side resource (say a
recursion depth) instead is an open scope question (Q1 of the G01 document)
and would replace this by the approved `Admissible`. -/
def SourceSpec.Idealized (S : SourceSpec) : Prop := ∀ r, S.lang.Admissible r

/-- The source's judgments are functions where the contract needs them: an
input has one parse, a parse one resolution. -/
def SourceSpec.Unambiguous (S : SourceSpec) : Prop :=
  (∀ i s s', S.Parses i s → S.Parses i s' → s = s') ∧
  (∀ s r r', S.Resolves s r → S.Resolves s r' → r = r')

/-- The admitted source inputs, with their resolution. -/
def SourceSpec.Admitted (S : SourceSpec) (i : S.Input) (r : S.Resolved) : Prop :=
  ∃ s, S.Parses i s ∧ S.Resolves s r ∧ S.WellFormed r ∧ S.InProfile r

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
`State C Γ` and a world of typed instances), with their own semantics. -/
structure IntrinsicSpec where
  World : Type
  lang : Lang Event Outcome
  ofWorld : World → lang.Prog

/-- **Contract 2, lowering.**  Total on admitted source (the proofs are
arguments: no `Option`), and the source meaning refines the lowered world's,
in both directions, at every allowed environment. -/
structure Lowering (S : SourceSpec) (I : IntrinsicSpec) where
  lower : (r : S.Resolved) → S.WellFormed r → S.InProfile r → I.World
  pass : Pass S.lang I.lang
  dom : ∀ r w p, pass.Dom (S.meaning r w p)
  agrees : ∀ r w p, pass.run (S.meaning r w p) (dom r w p) = I.ofWorld (lower r w p)
  cert : Cert pass

/-- The bytecode artifacts of one compilation: creation and runtime bytes. -/
structure Artifact where
  initcode : List UInt8
  runtime : List UInt8

/-- The pinned EVM (G06): accounts with code, executing transactions from
bytes.  Its resources are gas, memory and stack; `Admissible` is the
approved resource profile. -/
structure EvmSpec where
  lang : Lang Event Outcome
  /-- A deployment session of the artifact: install, then run transactions. -/
  load : Artifact → lang.Prog

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

/-- **Contract 5, composition: the public theorem.**  For every admitted
input the compiler produces bytes, and for every allowed EVM environment the
source meaning, read in the environment that one abstracts to, refines the
deployed bytes' sessions; every allowed source environment is reached. -/
def PublicCorrectness (S : SourceSpec) (V : EvmSpec)
    (compiler : S.Input → Option Artifact) (envAbs : V.lang.Env → S.lang.Env) : Prop :=
  (∀ i, (∃ r, S.Admitted i r) ↔ (compiler i).isSome) ∧
  (∀ e, S.lang.Allowed e → ∃ e', V.lang.Allowed e' ∧ envAbs e' = e) ∧
  ∀ i r, S.Admitted i r → ∀ (w : S.WellFormed r) (p : S.InProfile r) art, compiler i = some art →
    ∀ e, V.lang.Allowed e → S.lang.Allowed (envAbs e) ∧
      Refines S.lang.Admissible V.lang.Admissible
        (S.lang.sem (S.meaning r w p) (envAbs e)) (V.lang.sem (V.load art) e)

/-- **Contract 6, specification transfer.**  A source specification, read on
the source's prefixes, holds of the bytes: a safety specification at every
admissible prefix, a completion specification at some admissible prefix.
`Proves` derivations reach it through G51's bridge from `⊨` to `holdsSafe`. -/
def SpecTransfer (S : SourceSpec) (V : EvmSpec) (compiler : S.Input → Option Artifact)
    (envAbs : V.lang.Env → S.lang.Env) : Prop :=
  ∀ i r, S.Admitted i r → ∀ (w : S.WellFormed r) (p : S.InProfile r) art, compiler i = some art →
    ∀ e, V.lang.Allowed e →
      (∀ Φ : Prefix Event Outcome → Prop, (∀ a b, a.Le b → Φ b → Φ a) →
        (∀ rs, S.lang.Admissible rs → Φ (S.lang.sem (S.meaning r w p) (envAbs e) rs)) →
        ∀ rt, V.lang.Admissible rt → Φ (V.lang.sem (V.load art) e rt)) ∧
      (∀ o, (∃ rs, S.lang.Admissible rs ∧ (S.lang.sem (S.meaning r w p) (envAbs e) rs).final = some o) →
        ∃ rt, V.lang.Admissible rt ∧ (V.lang.sem (V.load art) e rt).final = some o)

/-- Public correctness gives specification transfer: the sixth contract's
semantic half needs nothing beyond the fifth. -/
theorem PublicCorrectness.transfer {S : SourceSpec} {V : EvmSpec}
    {compiler : S.Input → Option Artifact} {envAbs : V.lang.Env → S.lang.Env}
    (h : PublicCorrectness S V compiler envAbs) : SpecTransfer S V compiler envAbs := by
  intro i r adm w p art hc e he
  have href := (h.2.2 i r adm w p art hc e he).2
  refine ⟨fun Φ down hs => href.safety Φ down hs, fun o ⟨rs, hrs, ho⟩ => ?_⟩
  obtain ⟨rt, hrt, hfin, _⟩ := href.completes hrs ho
  exact ⟨rt, hrt, hfin⟩

/-! ## How the existing typed run reads as a resourced family

The fuelled typed run (`Prog.runF`, `Semantics/RunFuel.lean`) is a family
indexed by loop fuel: its `diverge` at fuel `n` ends the prefix unfinished,
and every other result completes it.  This only shows the plug: the
intrinsic language of contract 2 still needs events, the transaction
boundary and a call semantics without the fixed recursion unrolling
(`recDepth`); see the reuse map of the G01 document. -/

/-- One typed run as a resourced family with no events, completing with the
typed result. -/
def typedRunPrefixes {C : Contract} {Γ Γ' : Ctx} (P : Prog C Γ Γ') (σ : State C Γ) :
    Prefixes Nat Unit (TRes (State C Γ')) := fun n =>
  match Prog.runF n P σ with
  | .error .diverge => ⟨[], none⟩
  | .error e => ⟨[], some (.error e)⟩
  | .ok o => ⟨[], some (.ok o.st)⟩

end Solidity.Roadmap

/-- info: 'Solidity.Roadmap.Cert.comp' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Roadmap.Cert.comp
/-- info: 'Solidity.Roadmap.PublicCorrectness.transfer' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Roadmap.PublicCorrectness.transfer
