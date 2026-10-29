import Solidity.Roadmap.Contracts

/-!
# Inhabited and negative controls for the roadmap contracts (G07)

G01's contracts (`Solidity/Roadmap/Contracts.lean`) are statements; this
module checks that they are neither vacuous nor too weak, on a deliberately
small but complete instance.

**The inhabited control.**  A toy source language (`toySource`) whose inputs
are bytes naming one of three programs (succeed with data, revert with data,
loop forever), a toy EVM (`toyEvm`) that decodes the selected unit's runtime
bytes, an intrinsic layer equal to the source, and a compiler that encodes
the parsed program (`toyCompiler`).  Every field of `PublicCorrectness` is
proved for them (`toy_publicCorrectness`), with `SourceSpec.NonVacuous`,
`SourceSpec.Approved` and `EvmSpec.Approved`: the public contract can be met.

**The negative controls.**  On the same source and EVM, the public contract
refutes

- an always-reverting compiler (`not_publicCorrectness_revertCompiler`,
  through `PublicCorrectness.not_alwaysRevert`), and one that reverts
  whenever the source hashes (`not_publicCorrectness_hashRevertCompiler`:
  the toy's successes hash their data, and `SourceSpec.NonVacuous` demands
  a hashing success);
- altered bytecode: correct output with one byte appended
  (`not_publicCorrectness_alteredCompiler`), and output whose revert data is
  erased (`not_publicCorrectness_erasingCompiler`), both through
  `PublicCorrectness.observes`;
- a compiler that accepts malformed source
  (`not_publicCorrectness_sloppyCompiler`, through
  `PublicCorrectness.rejects`), and a frontend that does
  (`not_admission_sloppy`);
- and a source definition that admits nothing is never non-vacuous
  (`SourceSpec.not_nonVacuous_of_no_parse`), so a malformed or empty source
  semantics cannot meet the final statement's `NonVacuous` conjunct.

The toy source hashes the data of a success (`Toy.hashes`), with Keccak-256
(`Evm.withKeccak`) and sane regions (`Fixed.Sane`), so the forward bounds and
the hash premise are exercised on a real preimage.  The toy languages emit
no events, so these controls exercise the
observation (`Outcome`), coverage and settings fields; event-level controls
on real programs belong to G49.03.  The module imports the contracts only,
the whitelist of G01's non-circularity gate (`scripts/check-noncircular.mjs`).
-/

namespace Solidity.Roadmap.Controls

open Solidity.Roadmap

/-! ## Generic consequences of the contracts -/

section
variable {I : IntrinsicSpec} {S : SourceSpec} {V : EvmSpec}
  {compiler : S.Input → Option Artifact} {envAbs : V.lang.Env → S.lang.Env}
  {X : StateExport S I V}

/-- **Observations are preserved**: a completion of an admitted source
meaning, at an allowed environment and an admissible bound in the forward
bounds (no resource failure, fewer than `hashBound` preimages) meeting the
source's hash premise, is a completion of the compiled bytes with the same
outcome and events.  Nothing is assumed of the bytes' own hashes. -/
theorem _root_.Solidity.Roadmap.PublicCorrectness.observes
    (h : PublicCorrectness S V compiler envAbs X) {i : S.Input} {r : S.Resolved}
    (adm : S.Admitted i r) (w : S.WellFormed r) (p : S.InProfile r) {art : Artifact}
    (hc : compiler i = some art) {e : V.lang.Env} (he : V.lang.Allowed e) {rs : S.lang.Res}
    (hrs : S.lang.Admissible rs) (hf : S.lang.Forward (S.meaning r w p art) (envAbs e) rs)
    (hg : S.lang.Guard (S.meaning r w p art) (envAbs e) rs) {o : Outcome}
    (ho : (S.lang.sem (S.meaning r w p art) (envAbs e) rs).final = some o) :
    ∃ rt, V.lang.Admissible rt ∧ (V.lang.sem (V.load art) e rt).final = some o ∧
      (V.lang.sem (V.load art) e rt).events =
        (S.lang.sem (S.meaning r w p art) (envAbs e) rs).events :=
  (h.refines i r adm w p art hc e he).2.completes hrs hf hg ho

/-- **What the bytes observe, the source allows**: a completion of the
compiled bytes at an allowed environment and an admissible bound, up to
whose observations the source does not collide, is a completion of the
source meaning at an admissible bound, with the same outcome. -/
theorem _root_.Solidity.Roadmap.PublicCorrectness.observedBySource
    (h : PublicCorrectness S V compiler envAbs X) {i : S.Input} {r : S.Resolved}
    (adm : S.Admitted i r) (w : S.WellFormed r) (p : S.InProfile r) {art : Artifact}
    (hc : compiler i = some art) {e : V.lang.Env} (he : V.lang.Allowed e) {rt : V.lang.Res}
    (hrt : V.lang.Admissible rt)
    (hg : NoCollisionUpTo S.lang.Admissible (S.lang.Guard (S.meaning r w p art) (envAbs e))
      (S.lang.sem (S.meaning r w p art) (envAbs e)) (V.lang.sem (V.load art) e rt)) {o : Outcome}
    (ho : (V.lang.sem (V.load art) e rt).final = some o) :
    ∃ rs, S.lang.Admissible rs ∧ (S.lang.sem (S.meaning r w p art) (envAbs e) rs).final = some o := by
  obtain ⟨rs, hrs, hfin, _⟩ := (h.refines i r adm w p art hc e he).2.sound hrt hg ho
  exact ⟨rs, hrs, hfin⟩

/-- **Malformed source is refused**: an input the source does not accept has
no artifact. -/
theorem _root_.Solidity.Roadmap.PublicCorrectness.rejects
    (h : PublicCorrectness S V compiler envAbs X) {i : S.Input}
    (hi : ¬ ∃ r, S.Admitted i r) : compiler i = none := by
  cases hc : compiler i with
  | none => rfl
  | some art =>
    have hs : (compiler i).isSome = true := by rw [hc]; rfl
    exact absurd ((h.coverage i).2 hs) hi

end

/-- A non-vacuous source admits an input. -/
theorem _root_.Solidity.Roadmap.SourceSpec.NonVacuous.admits {S : SourceSpec}
    (hv : S.NonVacuous) : ∃ i r, S.Admitted i r := by
  obtain ⟨i, r, _, _, _, _, _, adm, _⟩ := hv.1
  exact ⟨i, r, adm⟩

/-- **A source whose grammar accepts nothing is vacuous**: it fails
`SourceSpec.NonVacuous`, so it cannot meet the final statement. -/
theorem _root_.Solidity.Roadmap.SourceSpec.not_nonVacuous_of_no_parse {S : SourceSpec}
    (hp : ∀ i s, ¬ S.Parses i s) : ¬ S.NonVacuous := by
  intro hv
  obtain ⟨i, _, s, hs, _⟩ := hv.admits
  exact hp i s hs

/-- A sound frontend accepts no input the source does not accept. -/
theorem _root_.Solidity.Roadmap.Admission.rejects {S : SourceSpec} (A : Admission S)
    {i : S.Input} (hi : ¬ ∃ r, S.Admitted i r) : A.frontend i = none := by
  cases hf : A.frontend i with
  | none => rfl
  | some r => exact absurd ⟨r, A.sound i r hf⟩ hi

/-! ## The toy programs and their bounds -/

/-- The three toy programs. -/
inductive Toy where
  | succeed (d : Bytes)
  | fail (d : Bytes)
  | loop
  deriving DecidableEq, Repr

/-- A source bound: a horizon and whether the transaction's frame fails as
if out of gas (its resource failure). -/
structure Bound where
  horizon : Nat
  exhausted : Bool

instance : LE Bound := ⟨fun a b => a.horizon ≤ b.horizon ∧ a.exhausted = b.exhausted⟩

/-- An EVM bound: a horizon and a gas schedule. -/
structure EvmBound where
  horizon : Nat
  gas : List Event → Nat

instance : LE EvmBound := ⟨fun a b => a.horizon ≤ b.horizon⟩

/-- A toy program's prefix: an exhausted frame reverts with no data; a loop
never completes.  No program emits events. -/
def Toy.run : Toy → Bool → Prefix Event Outcome
  | _, true => ⟨[], some (.revert [])⟩
  | .succeed d, false => ⟨[], some (.success d)⟩
  | .fail d, false => ⟨[], some (.revert d)⟩
  | .loop, false => ⟨[], none⟩

theorem Toy.run_events (t : Toy) (b : Bool) : (t.run b).events = [] := by
  cases b <;> cases t <;> rfl

/-- The preimages a toy program hashes: a success hashes its data (as a
`keccak256` of the return value would), the others nothing. -/
def Toy.hashes : Toy → List Bytes
  | .succeed d => [d]
  | _ => []

/-- The source text of a toy program: a tag byte, then the data. -/
def Toy.text : Toy → Bytes
  | .succeed d => 0 :: d
  | .fail d => 1 :: d
  | .loop => [2]

/-- The toy grammar: `0 d…` succeeds with `d`, `1 d…` reverts with `d`, `2`
loops; every other text is malformed. -/
def parse : Bytes → Option Toy
  | [] => none
  | b :: d => if b = 0 then some (.succeed d) else if b = 1 then some (.fail d)
      else if b = 2 ∧ d = [] then some .loop else none

theorem parse_text (t : Toy) : parse t.text = some t := by
  cases t <;> rfl

/-- The toy bytecode: the same tags, anything else runs forever. -/
def decode : Bytes → Toy
  | [] => .loop
  | b :: d => if b = 0 then .succeed d else if b = 1 then .fail d else .loop

theorem decode_text (t : Toy) : decode t.text = t := by
  cases t <;> rfl

/-! ## The fixed parameters and an allowed environment -/

/-- Fixed parameters: G06's Keccak-256 instance (`Evm.withKeccak`), a ledger
that ignores events, and one-slot regions with one root slot. -/
def toyFixed : Fixed where
  evm := Evm.withKeccak
  ledger := fun bal _ a => bal a
  regionLen := 1
  rootSlots := 1

theorem toyFixed_sane : toyFixed.Sane := ⟨Nat.le_refl _, by decide, by decide⟩

theorem toyFixed_keccak : toyFixed.Keccak := ⟨fun _ => rfl, toyFixed_sane⟩

/-- A session environment: no code anywhere, no requests, every call
succeeds at once. -/
def quietEnv : SessionEnv where
  deployer := Address.zero
  deployNonce := 0
  deployValue := 0
  deployArgs := []
  balance := fun _ => 0
  hasCode := fun _ _ => false
  requests := fun _ _ => none
  callee := fun _ => .answer (.success [])

theorem quietEnv_allowed : quietEnv.Allowed :=
  ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

/-- The toy hash premise on one preimage: no collision, and no slot
preimages. -/
theorem toy_premise (t : Toy) : HashPremise toyFixed t.hashes [] := by
  cases t with
  | succeed d => exact ⟨Solidity.Hash.CollisionFree.singleton d, Solidity.Hash.RegionsDisjoint.nil⟩
  | fail d => exact HashPremise.nil _
  | loop => exact HashPremise.nil _

theorem toy_count (t : Toy) : distinctCount t.hashes < hashBound := by
  cases t <;> simp only [Toy.hashes, distinctCount, hashBound, List.elem_nil, Bool.false_eq_true,
    if_false] <;> decide

/-! ## The toy source -/

/-- The source language: programs are toy programs, environments are session
environments, every bound is admissible; the forward bounds are the
unexhausted ones hashing fewer than `hashBound` preimages, the premise is the
hash premise on the program's preimages. -/
def toyLang : Lang Event Outcome where
  Prog := Toy
  Env := SessionEnv
  Res := Bound
  resLE := inferInstanceAs (LE Bound)
  Allowed := SessionEnv.Allowed
  Admissible := fun _ => True
  sem := fun p _ r => p.run r.exhausted
  consistent := fun p _ r r' h => by
    show (p.run r.exhausted).Le (p.run r'.exhausted)
    rw [h.2]
    exact Prefix.Le.refl _
  Forward := fun p _ r => r.exhausted = false ∧ distinctCount (Toy.hashes p) < hashBound
  Guard := fun p _ _ => HashPremise toyFixed (Toy.hashes p) []

/-- A toy compilation input: source bytes (one unit) and settings. -/
structure ToyInput where
  text : Bytes
  pipeline : Pipeline := .legacy
  pragmaCoder : AbiCoder := .v2
  links : List (String × Address) := []

/-- The ABI coder an input compiles with: the pragma's under legacy, v2
under via-IR. -/
def ToyInput.coder (i : ToyInput) : AbiCoder :=
  match i.pipeline with
  | .legacy => i.pragmaCoder
  | .viaIR => .v2

/-- A resolution: the program and the settings it was resolved under. -/
structure ToyRes where
  prog : Toy
  pipeline : Pipeline
  coder : AbiCoder

/-- The admitted resolution of an input, computed. -/
def accept (i : ToyInput) : Option ToyRes :=
  if i.links = [] then (parse i.text).map fun t => ⟨t, i.pipeline, i.coder⟩ else none

/-- The toy source specification. -/
def toySource : SourceSpec where
  Input := ToyInput
  Syntax := Toy × Pipeline × AbiCoder
  Resolved := ToyRes
  Parses := fun i s => i.links = [] ∧ (parse i.text).map (fun t => (t, i.pipeline, i.coder)) = some s
  Resolves := fun s r => r = ⟨s.1, s.2.1, s.2.2⟩
  WellFormed := fun _ => True
  InProfile := fun _ => True
  lang := toyLang
  meaning := fun r _ _ _ => r.prog
  inhabited := ⟨quietEnv, quietEnv_allowed⟩
  pipeline := ToyInput.pipeline
  setPipeline := fun i q => { i with pipeline := q }
  pipeline_set := fun _ _ => rfl
  pragmaCoder := fun i _ => i.pragmaCoder
  coder := fun i _ => i.coder
  coder_legacy := fun i _ h => by simp only [ToyInput.coder, h]
  coder_viaIR := fun i _ h => by simp only [ToyInput.coder, h]
  pipelineOf := ToyRes.pipeline
  coderOf := fun r _ => r.coder
  linkMap := ToyInput.links
  stipendFits := fun _ _ => true
  fixed := toyFixed
  session := id
  ofSession := id
  session_of := fun _ => rfl
  of_session := fun _ => rfl
  allowed_iff := fun _ => Iff.rfl
  Failures := Bool
  failures := Bound.exhausted
  withFailures := fun r x => { r with exhausted := x }
  failures_with := fun _ _ => rfl
  NoFail := fun x => x = false
  hashed := fun p _ _ => Toy.hashes p
  hashed_consistent := fun _ _ _ _ _ => List.prefix_refl _
  slotHashed := fun _ _ _ => []
  slotHashed_sub := fun _ _ _ _ h => nomatch h
  forward_iff := fun _ _ _ => Iff.rfl
  guard_iff := fun _ _ _ => Iff.rfl

theorem admitted_iff (i : ToyInput) (r : ToyRes) : toySource.Admitted i r ↔ accept i = some r := by
  constructor
  · rintro ⟨s, ⟨hl, hs⟩, hr, _, _⟩
    simp only [toySource] at hr
    subst hr
    simp only [accept, hl, if_true]
    cases hp : parse i.text with
    | none => rw [hp] at hs; cases hs
    | some t => rw [hp] at hs; cases hs; rfl
  · intro h
    simp only [accept] at h
    split at h
    · rename_i hl
      cases hp : parse i.text with
      | none => rw [hp] at h; cases h
      | some t =>
        rw [hp] at h
        cases h
        exact ⟨(t, i.pipeline, i.coder), ⟨hl, by rw [hp]; rfl⟩, rfl, trivial, trivial⟩
    · cases h

/-- The forward bound and premise of an unexhausted toy run. -/
theorem toy_forward (t : Toy) (e : SessionEnv) (h : Nat) :
    toySource.lang.Forward t e ⟨h, false⟩ ∧ toySource.lang.Guard t e ⟨h, false⟩ :=
  ⟨⟨rfl, toy_count t⟩, toy_premise t⟩

/-- **The toy source is non-vacuous**: `0 1` succeeds with `[1]`, hashing
`[1]`; `1 7` reverts with `[7]`; `2` diverges. -/
theorem toySource_nonVacuous : toySource.NonVacuous := by
  refine ⟨⟨{ text := [0, 1] }, ⟨.succeed [1], .legacy, .v2⟩, trivial, trivial, quietEnv, ⟨0, false⟩, [1],
      (admitted_iff _ _).2 rfl, quietEnv_allowed, trivial, List.cons_ne_nil _ _,
      fun _ => ⟨(toy_forward _ _ _).1, (toy_forward _ _ _).2, rfl⟩⟩,
    ⟨{ text := [0, 1] }, ⟨.succeed [1], .legacy, .v2⟩, trivial, trivial, quietEnv, ⟨0, false⟩, [1],
      (admitted_iff _ _).2 rfl, quietEnv_allowed, trivial,
      fun _ => ⟨List.cons_ne_nil _ _, (toy_forward _ _ _).1, (toy_forward _ _ _).2, rfl⟩⟩,
    ⟨{ text := [1, 7] }, ⟨.fail [7], .legacy, .v2⟩, trivial, trivial, quietEnv, ⟨0, false⟩, [7],
      (admitted_iff _ _).2 rfl, quietEnv_allowed, trivial,
      fun _ => ⟨(toy_forward _ _ _).1, (toy_forward _ _ _).2, rfl⟩⟩,
    ⟨{ text := [2] }, ⟨.loop, .legacy, .v2⟩, trivial, trivial, quietEnv,
      (admitted_iff _ _).2 rfl, quietEnv_allowed, fun _ _ _ => rfl, fun _ rs ⟨_, hno⟩ => ?_⟩⟩
  show (Toy.run .loop rs.exhausted).final = none
  have hx : rs.exhausted = false := hno
  rw [hx]
  rfl

/-- No toy run's events contain anything. -/
theorem toy_no_event {p : Toy} {r : Bound} {x : Event} (hm : x ∈ (Toy.run p r.exhausted).events) : False := by
  rw [Toy.run_events] at hm
  cases hm

/-- The toy source meets the approved readings. -/
theorem toySource_approved : toySource.Approved := by
  refine ⟨fun _ => trivial, fun p _ r _ _ _ _ hm _ => toy_no_event hm,
    fun p _ r _ _ _ _ _ hm => (toy_no_event hm).elim, fun p _ r h _ _ _ _ _ _ hm => ?_, ?_, ?_,
    toyFixed_sane⟩
  · have hm' : h ++ _ <+: (Toy.run p r.exhausted).events := hm
    rw [Toy.run_events] at hm'
    have := hm'.length_le
    simp only [List.length_append, List.length_singleton, List.length_nil] at this
    omega
  · intro i r adm
    have h := (admitted_iff i r).1 adm
    simp only [accept] at h
    split at h
    · cases hp : parse i.text with
      | none => rw [hp] at h; cases h
      | some t => rw [hp] at h; cases h; exact ⟨rfl, fun _ => rfl⟩
    · cases h
  · intro i r adm
    have h := (admitted_iff i r).1 adm
    simp only [accept] at h
    split at h
    · assumption
    · cases h

/-- A malformed text is refused: the empty input. -/
theorem malformed_not_admitted : ¬ ∃ r, toySource.Admitted (⟨[], .legacy, .v2, []⟩ : ToyInput) r := by
  rintro ⟨r, h⟩
  cases (admitted_iff _ _).1 h

/-- Malformed: an unknown tag. -/
theorem badTag_not_admitted : ¬ ∃ r, toySource.Admitted ({ text := [3] } : ToyInput) r := by
  rintro ⟨r, h⟩
  cases (admitted_iff _ _).1 h

/-- Malformed: data after the loop tag. -/
theorem trailing_not_admitted : ¬ ∃ r, toySource.Admitted ({ text := [2, 0] } : ToyInput) r := by
  rintro ⟨r, h⟩
  cases (admitted_iff _ _).1 h

/-- Refused: a pre-assigned library address (decision G05 Q1). -/
theorem linked_not_admitted :
    ¬ ∃ r, toySource.Admitted ({ text := [2], links := [("L", Address.zero)] } : ToyInput) r := by
  rintro ⟨r, h⟩
  cases (admitted_iff _ _).1 h

/-! ## The intrinsic layer and the lowering -/

/-- The intrinsic layer: the toy language itself, without boundary worlds. -/
def toyIntrinsic : IntrinsicSpec where
  World := Toy
  lang := toyLang
  ofWorld := id
  worlds := fun _ _ _ => []
  fixed := toyFixed
  session := id
  ofSession := id
  session_of := fun _ => rfl
  of_session := fun _ => rfl
  allowed_iff := fun _ => Iff.rfl
  NoFail := fun r => r.exhausted = false
  hashed := fun p _ _ => Toy.hashes p
  slotHashed := fun _ _ _ => []
  forward_iff := fun _ _ _ => Iff.rfl
  guard_iff := fun _ _ _ => Iff.rfl

/-- The identity pass. -/
def idPass : Pass toyLang toyLang where
  Dom := fun _ => True
  run := fun p _ => p
  envAbs := id

/-- Its certificate: every bound maps to itself; a target collision is the
source's. -/
def idCert : Cert idPass where
  envSound := fun _ he => he
  envOnto := fun e he => ⟨e, he, rfl⟩
  need := fun _ _ _ r => r
  need_ok := fun _ _ _ _ _ _ hf hg => ⟨trivial, hf, hg, Prefix.Le.refl _⟩
  back := fun _ _ _ r _ _ => ⟨r, trivial, .inl (Prefix.Le.refl _)⟩
  reflect := fun _ _ _ r _ _ hng => ⟨r, trivial, hng, List.prefix_refl _⟩

/-- The lowering: the resolved program, unchanged. -/
def toyLowering : Lowering toySource toyIntrinsic where
  lower := fun r _ _ _ => r.prog
  pass := idPass
  dom := fun _ _ _ _ => trivial
  agrees := fun _ _ _ _ => rfl
  cert := idCert

/-! ## The toy EVM and the compiler -/

/-- The runtime bytes of an artifact's selected unit. -/
def mainRuntime (art : Artifact) : Bytes :=
  ((art.contracts[art.main]?).map CodeUnit.runtime).getD []

/-- The artifact holding one unit with the given runtime bytes. -/
def artOf (code : Bytes) : Artifact := ⟨[{ initcode := [], runtime := code }], 0⟩

theorem mainRuntime_artOf (code : Bytes) : mainRuntime (artOf code) = code := rfl

/-- The toy EVM language: it runs the selected unit's decoded bytes,
whatever the gas schedule; as a target, it has no premise or forward
restriction of its own. -/
def toyEvmLang : Lang Event Outcome where
  Prog := Artifact
  Env := SessionEnv
  Res := EvmBound
  resLE := inferInstanceAs (LE EvmBound)
  Allowed := SessionEnv.Allowed
  Admissible := fun _ => True
  sem := fun art _ _ => (decode (mainRuntime art)).run false
  consistent := fun _ _ _ _ _ => Prefix.Le.refl _

/-- The toy EVM: the Osaka pin, and no `KECCAK256` (its successes return
their data without hashing it). -/
def toyEvm : EvmSpec where
  lang := toyEvmLang
  load := id
  pin := Evm.pinned
  fixed := toyFixed
  session := id
  ofSession := id
  session_of := fun _ => rfl
  of_session := fun _ => rfl
  allowed_iff := fun _ => Iff.rfl
  gas := EvmBound.gas
  withGas := fun r g => { r with gas := g }
  gas_with := fun _ _ => rfl
  hashed := fun _ _ _ => []
  created := fun _ _ _ => []
  World := Unit
  worlds := fun _ _ _ => []
  balances := fun _ _ => 0
  resume := fun _ => artOf []

theorem toyEvm_no_event {art : Artifact} {x : Event}
    (hm : x ∈ ((decode (mainRuntime art)).run false).events) : False := by
  rw [Toy.run_events] at hm
  cases hm

theorem toyEvm_approved : toyEvm.Approved := by
  refine ⟨rfl, toyFixed_sane, fun _ => trivial, fun _ _ _ => ⟨trivial, trivial⟩,
    fun art _ _ _ _ _ _ hm _ => toyEvm_no_event hm, fun art _ _ _ _ _ _ _ hm => (toyEvm_no_event hm).elim,
    fun art _ _ h _ _ _ _ _ _ hm => ?_⟩
  have hm' : h ++ _ <+: ((decode (mainRuntime art)).run false).events := hm
  rw [Toy.run_events] at hm'
  have := hm'.length_le
  simp only [List.length_append, List.length_singleton, List.length_nil] at this
  omega

/-- The compiler that writes the text of `f p` for the admitted program `p`. -/
def compilerWith (f : Toy → Toy) (i : ToyInput) : Option Artifact :=
  (accept i).map fun r => artOf (f r.prog).text

/-- The toy compiler: the admitted program's text as the runtime bytes. -/
def toyCompiler : ToyInput → Option Artifact := compilerWith id

/-- The state export: nothing to decode, since no world is reached. -/
def toyExport : StateExport toySource toyIntrinsic toyEvm where
  lowering := toyLowering
  decode := fun _ _ => none
  envAbs := id

theorem PrefixFree_artOf (code : Bytes) : (artOf code).PrefixFree := by
  intro j k hj hk hne
  have hj' : j < 1 := hj
  have hk' : k < 1 := hk
  exact absurd (by omega : j = k) hne

/-- A translation of toy programs that refines in both directions: the
unexhausted source prefix is below the target's, and the target's is below
the source prefix at some exhaustion choice. -/
def Faithful (f : Toy → Toy) : Prop :=
  ∀ t, (t.run false).Le ((f t).run false) ∧ ∃ b, ((f t).run false).Le (t.run b)

/-- A faithful translation meets the public contract. -/
theorem publicCorrectness_of_faithful (f : Toy → Toy) (hf : Faithful f) :
    PublicCorrectness toySource toyEvm (compilerWith f) id toyExport where
  coverage := fun i => by
    show (∃ r, toySource.Admitted i r) ↔ ((accept i).map fun r => artOf (f r.prog).text).isSome
    constructor
    · rintro ⟨r, h⟩
      rw [(admitted_iff i r).1 h]
      rfl
    · intro h
      cases ha : accept i with
      | none => rw [ha] at h; cases h
      | some r => exact ⟨r, (admitted_iff i r).2 ha⟩
  bothPipelines := fun i q ⟨r, h⟩ => by
    have ha := (admitted_iff i r).1 h
    refine ⟨⟨r.prog, q, ({ i with pipeline := q } : ToyInput).coder⟩, (admitted_iff _ _).2 ?_⟩
    show accept { i with pipeline := q } = _
    simp only [accept] at ha ⊢
    split at ha
    · rename_i hl
      cases hp : parse i.text with
      | none => rw [hp] at ha; cases ha
      | some t => rw [hp] at ha; cases ha; simp only [hl, if_true, Option.map_some]
    · cases ha
  envOnto := fun e he => ⟨e, he, rfl⟩
  fixed := rfl
  session := fun _ => rfl
  envAbs_agrees := fun _ => rfl
  ifixed := rfl
  isession := fun _ => rfl
  creates_table := fun i art hc => by
    cases ha : accept i with
    | none => simp only [compilerWith, ha, Option.map_none] at hc; cases hc
    | some r =>
      simp only [compilerWith, ha, Option.map_some, Option.some.injEq] at hc
      subst hc
      refine ⟨PrefixFree_artOf _, fun e rt => ?_⟩
      show [] = (createsOf ((decode (mainRuntime _)).run false).events).map _
      rw [Toy.run_events]
      rfl
  hashes_source := fun _ _ _ _ _ _ _ _ _ _ _ _ hb => nomatch hb
  refines := fun i r adm _ _ art hc e he => by
    have ha := (admitted_iff i r).1 adm
    simp only [compilerWith, ha, Option.map_some, Option.some.injEq] at hc
    subst hc
    obtain ⟨hfw, b, hbw⟩ := hf r.prog
    refine ⟨he, fun rs _ hfr _ => ⟨⟨rs.horizon, fun _ => 0⟩, trivial, ?_⟩,
      fun rt _ => ⟨⟨rt.horizon, b⟩, trivial, .inl ?_⟩⟩
    · show (r.prog.run rs.exhausted).Le ((decode (mainRuntime (artOf (f r.prog).text))).run false)
      have hx : rs.exhausted = false := hfr.1
      rw [hx, mainRuntime_artOf, decode_text]
      exact hfw
    · show ((decode (mainRuntime (artOf (f r.prog).text))).run false).Le (r.prog.run b)
      rw [mainRuntime_artOf, decode_text]
      exact hbw
  decode_reach := fun _ _ _ _ _ _ _ _ _ _ _ _ => ⟨⟨0, false⟩, trivial, rfl⟩
  decode_commutes := fun _ _ _ _ _ _ _ _ _ _ _ _ _ hω => nomatch hω

/-- **The inhabited control**: the toy compiler meets the public contract
for the toy source and EVM. -/
theorem toy_publicCorrectness :
    PublicCorrectness toySource toyEvm toyCompiler id toyExport :=
  publicCorrectness_of_faithful id fun _ => ⟨Prefix.Le.refl _, false, Prefix.Le.refl _⟩

/-- A loop compiled to a revert with empty data. -/
def loopToRevert : Toy → Toy
  | .loop => .fail []
  | t => t

/-- **Accepted by design**: a diverging transaction may compile to one that
reverts with empty data, since the source lets any transaction fail as if
out of gas (a resource failure).  The public contract does not distinguish
divergence from a resource failure at the source's failing bounds. -/
theorem toy_publicCorrectness_loopReverts :
    PublicCorrectness toySource toyEvm (compilerWith loopToRevert) id toyExport :=
  publicCorrectness_of_faithful loopToRevert fun t => by
    cases t with
    | loop => exact ⟨⟨List.prefix_refl _, .inl rfl⟩, true, Prefix.Le.refl _⟩
    | succeed d => exact ⟨Prefix.Le.refl _, false, Prefix.Le.refl _⟩
    | fail d => exact ⟨Prefix.Le.refl _, false, Prefix.Le.refl _⟩

/-! ## Negative controls

Each holds for every intrinsic layer, state export and environment map. -/

section
variable {I : IntrinsicSpec} {envAbs : toyEvm.lang.Env → toySource.lang.Env}

/-- The output of `compilerWith f` runs `f` of the admitted program. -/
theorem compilerWith_run {f : Toy → Toy} {i : ToyInput} {art : Artifact}
    (hc : compilerWith f i = some art) : ∃ r, accept i = some r ∧ art = artOf (f r.prog).text := by
  cases ha : accept i with
  | none => simp only [compilerWith, ha, Option.map_none] at hc; cases hc
  | some r =>
    simp only [compilerWith, ha, Option.map_some, Option.some.injEq] at hc
    exact ⟨r, rfl, hc.symm⟩

/-- A compiler whose output always reverts, on the inputs it accepts. -/
def revertCompiler : ToyInput → Option Artifact := compilerWith fun _ => .fail []

/-- **The always-revert control**: no state export makes the reverting
compiler meet the public contract. -/
theorem not_publicCorrectness_revertCompiler (X : StateExport toySource I toyEvm) :
    ¬ PublicCorrectness toySource toyEvm revertCompiler envAbs X := by
  intro h
  refine h.not_alwaysRevert toySource_nonVacuous (fun i art e rt d hc _ _ => ?_)
  obtain ⟨r, _, rfl⟩ := compilerWith_run hc
  show ((decode (mainRuntime (artOf (Toy.fail []).text))).run false).final ≠ _
  rw [mainRuntime_artOf, decode_text]
  intro hf
  cases hf

/-- A compiler that reverts exactly where the source hashes: a success
(which hashes its data) becomes a revert. -/
def hashRevert : Toy → Toy
  | .succeed _ => .fail []
  | t => t

/-- **The revert-on-hashing control**: the non-vacuity witness that hashes
and succeeds forces a success of the bytes, so a compiler reverting on every
hashing run fails the public contract, whatever the EVM hashes and without
any fact about Keccak's values (`PublicCorrectness.succeeds_hashing`). -/
theorem not_publicCorrectness_hashRevertCompiler (X : StateExport toySource I toyEvm) :
    ¬ PublicCorrectness toySource toyEvm (compilerWith hashRevert) envAbs X := by
  intro h
  refine h.not_alwaysRevert toySource_nonVacuous (fun i art e rt d hc _ _ => ?_)
  obtain ⟨r, _, rfl⟩ := compilerWith_run hc
  show ((decode (mainRuntime (artOf (hashRevert r.prog).text))).run false).final ≠ _
  rw [mainRuntime_artOf, decode_text]
  cases r.prog <;> intro hf <;> cases hf

/-- Altered bytecode: the correct output with one byte appended. -/
def alteredCompiler (i : ToyInput) : Option Artifact :=
  (accept i).map fun r => artOf (r.prog.text ++ [0])

/-- **The altered-bytecode control**: appending a byte changes the success
data of `0 1`, so no state export makes the altered output meet the public
contract. -/
theorem not_publicCorrectness_alteredCompiler (X : StateExport toySource I toyEvm) :
    ¬ PublicCorrectness toySource toyEvm alteredCompiler envAbs X := by
  intro h
  have adm : toySource.Admitted ({ text := [0, 1] } : ToyInput) ⟨.succeed [1], .legacy, .v2⟩ :=
    (admitted_iff _ _).2 rfl
  obtain ⟨rt, _, hfin, _⟩ := h.observes adm trivial trivial rfl quietEnv_allowed
    (rs := ⟨0, false⟩) trivial (toy_forward _ _ _).1 (toy_forward _ _ _).2 (o := .success [1]) rfl
  cases hfin

/-- Altered bytecode: revert data erased. -/
def erasingCompiler (i : ToyInput) : Option Artifact :=
  (accept i).map fun r => artOf (match r.prog with
    | .fail _ => (Toy.fail []).text
    | t => t.text)

/-- **The erased-observation control**: the revert data of `1 7` is
observed, so a compiler that erases it fails the public contract. -/
theorem not_publicCorrectness_erasingCompiler (X : StateExport toySource I toyEvm) :
    ¬ PublicCorrectness toySource toyEvm erasingCompiler envAbs X := by
  intro h
  have adm : toySource.Admitted ({ text := [1, 7] } : ToyInput) ⟨.fail [7], .legacy, .v2⟩ :=
    (admitted_iff _ _).2 rfl
  obtain ⟨rt, _, hfin, _⟩ := h.observes adm trivial trivial rfl quietEnv_allowed
    (rs := ⟨0, false⟩) trivial (toy_forward _ _ _).1 (toy_forward _ _ _).2 (o := .revert [7]) rfl
  cases hfin

/-- Altered bytecode: a loop compiled to a success. -/
def loopToSucceed : Toy → Toy
  | .loop => .succeed []
  | t => t

/-- **The backward (soundness) control**: a success the source never
produces, here from a loop (which hashes nothing, so never collides), fails
the public contract. -/
theorem not_publicCorrectness_loopToSucceed (X : StateExport toySource I toyEvm) :
    ¬ PublicCorrectness toySource toyEvm (compilerWith loopToSucceed) envAbs X := by
  intro h
  have adm : toySource.Admitted ({ text := [2] } : ToyInput) ⟨.loop, .legacy, .v2⟩ :=
    (admitted_iff _ _).2 rfl
  obtain ⟨rs, _, hfin⟩ := h.observedBySource adm trivial trivial rfl quietEnv_allowed
    (rt := ⟨0, fun _ => 0⟩) trivial (fun _ _ _ => HashPremise.nil _) (o := .success []) rfl
  have hfin' : (Toy.run .loop rs.exhausted).final = some (.success []) := hfin
  cases hx : rs.exhausted <;> rw [hx] at hfin' <;> cases hfin'

/-- A compiler that also accepts malformed text, compiling it to a loop. -/
def sloppyCompiler (i : ToyInput) : Option Artifact :=
  (toyCompiler i).orElse fun _ => some (artOf Toy.loop.text)

/-- **The malformed-source control**: accepting the empty text fails the
public contract's coverage. -/
theorem not_publicCorrectness_sloppyCompiler (X : StateExport toySource I toyEvm) :
    ¬ PublicCorrectness toySource toyEvm sloppyCompiler envAbs X := by
  intro h
  have hn := h.rejects malformed_not_admitted
  cases hn

/-- A compiler that ignores the settings' link map. -/
def linkBlindCompiler (i : ToyInput) : Option Artifact :=
  toyCompiler { i with links := [] }

/-- **The link-map control**: an input with a pre-assigned library address
is refused (decision G05 Q1), so a compiler ignoring it fails. -/
theorem not_publicCorrectness_linkBlindCompiler (X : StateExport toySource I toyEvm) :
    ¬ PublicCorrectness toySource toyEvm linkBlindCompiler envAbs X := by
  intro h
  have hn := h.rejects linked_not_admitted
  cases hn

end

/-- The toy frontend: sound and complete. -/
def toyAdmission : Admission toySource where
  frontend := accept
  sound := fun i r h => (admitted_iff i r).2 h
  complete := fun i r h => (admitted_iff i r).1 h

/-- A frontend that also accepts malformed text, as a loop. -/
def sloppyFrontend (i : ToyInput) : Option ToyRes :=
  (accept i).orElse fun _ => some ⟨.loop, i.pipeline, i.coder⟩

/-- **The malformed-source control for admission**: no sound admission
accepts the empty text (and one exists: `toyAdmission`). -/
theorem not_admission_sloppy (A : Admission toySource) : A.frontend ≠ sloppyFrontend := by
  intro hA
  have hn := A.rejects malformed_not_admitted
  rw [hA] at hn
  cases hn

/-- The empty source: nothing parses. -/
def emptySource : SourceSpec := { toySource with Parses := fun _ _ => False }

theorem not_nonVacuous_emptySource : ¬ emptySource.NonVacuous :=
  SourceSpec.not_nonVacuous_of_no_parse fun _ _ h => h

/-! ## The region parameters

With at least one slot per region and `2^256` root slots, no run with a
slot preimage meets the hash premise, which would leave `refines` with no
constraint after it; `Fixed.Sane` (a conjunct of both `SourceSpec.Approved`
and `EvmSpec.Approved`) rules such parameters out (`Fixed.Sane.rootSlots_lt`).
This was G07's first contract gap, closed by the final G01 revision. -/

theorem _root_.Solidity.Roadmap.HashPremise.not_of_rootSlots {F : Fixed} (hl : 1 ≤ F.regionLen)
    (hr : 2 ^ 256 ≤ F.rootSlots) (xs : List Bytes) (y : Bytes) (ys : List Bytes) :
    ¬ HashPremise F xs (y :: ys) := by
  intro ⟨_, _, hroot⟩
  have hlt : (F.hash y).val < 2 ^ 256 := (F.hash y).isLt
  have hmem : (F.hash y).val ∈ List.range F.rootSlots := List.mem_range.2 (by omega)
  refine hroot y (List.mem_cons_self ..) _ hmem (.inl ⟨Nat.le_refl _, ?_⟩)
  show (F.hash y).val < (F.hash y).val + F.regionLen
  omega

/-- Sane parameters have fewer root slots than words. -/
theorem _root_.Solidity.Roadmap.Fixed.Sane.rootSlots_lt {F : Fixed} (h : F.Sane) :
    F.rootSlots < 2 ^ 256 :=
  Nat.lt_of_le_of_lt h.2.2 (Nat.pow_lt_pow_right (by decide) (by decide))

end Solidity.Roadmap.Controls

/-- info: 'Solidity.Roadmap.Controls.toy_publicCorrectness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Roadmap.Controls.toy_publicCorrectness
/-- info: 'Solidity.Roadmap.Controls.toySource_nonVacuous' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Roadmap.Controls.toySource_nonVacuous
/-- info: 'Solidity.Roadmap.Controls.toySource_approved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Roadmap.Controls.toySource_approved
/-- info: 'Solidity.Roadmap.Controls.toyEvm_approved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Roadmap.Controls.toyEvm_approved
/-- info: 'Solidity.Roadmap.Controls.not_publicCorrectness_revertCompiler' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Roadmap.Controls.not_publicCorrectness_revertCompiler
/-- info: 'Solidity.Roadmap.Controls.not_publicCorrectness_alteredCompiler' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Roadmap.Controls.not_publicCorrectness_alteredCompiler
/-- info: 'Solidity.Roadmap.Controls.not_publicCorrectness_erasingCompiler' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Roadmap.Controls.not_publicCorrectness_erasingCompiler
/-- info: 'Solidity.Roadmap.Controls.not_publicCorrectness_sloppyCompiler' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Roadmap.Controls.not_publicCorrectness_sloppyCompiler
/-- info: 'Solidity.Roadmap.Controls.not_admission_sloppy' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Roadmap.Controls.not_admission_sloppy
/-- info: 'Solidity.Roadmap.Controls.not_nonVacuous_emptySource' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Roadmap.Controls.not_nonVacuous_emptySource
/-- info: 'Solidity.Roadmap.PublicCorrectness.observes' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Roadmap.PublicCorrectness.observes
/-- info: 'Solidity.Roadmap.PublicCorrectness.rejects' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Roadmap.PublicCorrectness.rejects
/-- info: 'Solidity.Roadmap.SourceSpec.not_nonVacuous_of_no_parse' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Roadmap.SourceSpec.not_nonVacuous_of_no_parse
/-- info: 'Solidity.Roadmap.Admission.rejects' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Roadmap.Admission.rejects
/-- info: 'Solidity.Roadmap.Controls.toy_publicCorrectness_loopReverts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Roadmap.Controls.toy_publicCorrectness_loopReverts
/-- info: 'Solidity.Roadmap.Controls.not_publicCorrectness_loopToSucceed' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Roadmap.Controls.not_publicCorrectness_loopToSucceed
/-- info: 'Solidity.Roadmap.Controls.not_publicCorrectness_linkBlindCompiler' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Roadmap.Controls.not_publicCorrectness_linkBlindCompiler
/-- info: 'Solidity.Roadmap.PublicCorrectness.observedBySource' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Roadmap.PublicCorrectness.observedBySource
/-- info: 'Solidity.Roadmap.SourceSpec.NonVacuous.admits' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Roadmap.SourceSpec.NonVacuous.admits
/-- info: 'Solidity.Roadmap.HashPremise.not_of_rootSlots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Roadmap.HashPremise.not_of_rootSlots
/-- info: 'Solidity.Roadmap.Controls.not_publicCorrectness_hashRevertCompiler' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Roadmap.Controls.not_publicCorrectness_hashRevertCompiler
