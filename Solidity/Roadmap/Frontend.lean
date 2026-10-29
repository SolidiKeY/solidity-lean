import Solidity.Frontend.SourceUnits
import Solidity.Syntax.Raw

/-!
# Checked frontend certificates (G05), as statements

G01's contract 1 (`Admission`, `CheckedFrontend` over a `SourceSpec`) asks
for a frontend whose acceptance implies the source relations.  This module
splits that certificate into its stages: the raw compilation input, its parse
(S00), its resolution (S01) and the resolved metadata with the profile and
settings checks (S01, G00).  It does not import `Solidity.Roadmap.Contracts`:
`FrontendSpec` repeats exactly the fields of `SourceSpec` the frontend reads,
and `docs/feature-work/roadmap-g05-frontend.md` maps each name.  Nothing here
is an instance: today's frontend (`solc_import`) is elaborator code whose
output the kernel re-checks for typing only.

**Digests prove identity only.**  A recorded digest names bytes; under the
per-run premise that the run's preimages do not collide (the form of the
hash-collision decision, here applied to input digests; never global
injectivity) equal digests mean equal bytes (`Digests.identity`).  No
statement below depends on it: the stage checkers read bytes, not digests.  A check that reads only a digest certifies only a
property that cannot tell two colliding inputs apart (`Digests.only_invariant`).
So a parse or a type is never established by a digest.

**Settings are part of the input.**  `Settings.Ok` does not read the
evaluation order, and the obligation `FrontendSpec.AllSettings` (admission is
blind to the semantic settings) gives every one of the eight `EvalOrder`
combinations (`FrontendSpec.admits_order`), so a public theorem over admitted
inputs quantifies over all of them.  The ABI coder is the per-unit pragma or
forced v2 (`CoderMode`), agreeing with the provenance reader per unit
(`CoderMode.agrees_atNode`).  Only the 0.8.38 profile compiler is admitted
(`Settings.ok_compiler`): a 0.8.34 fixture is a SolKey compatibility check
only.  Library link maps are recorded (`Link`, `LinksWellFormed`) and checked
against the resolved library declarations (`LinksResolved`); the admitted
profile takes the empty map, where the session deploys and links every
library itself.
-/

namespace Solidity.Roadmap.Frontend

open Solidity.Frontend.Source (Compiler AbiCoder Pipeline Provenance Compilation)

/-! ## Digests -/

/-- A digest function over bytes: SHA-256 for source units and compiler
binaries, FNV-1a 64 for the fixture staleness check (`Frontend.fnv1a64`). -/
structure Digests where
  Digest : Type
  digest : List UInt8 → Digest

/-- The per-run premise: no two of the run's preimages collide. -/
def Digests.CollisionFreeOn (D : Digests) (xs : List (List UInt8)) : Prop :=
  ∀ a, a ∈ xs → ∀ b, b ∈ xs → D.digest a = D.digest b → a = b

/-- Bytes with the digest recorded for them, recomputed by the checker. -/
structure Named (D : Digests) where
  bytes : List UInt8
  recorded : D.Digest
  recomputed : D.digest bytes = recorded

/-- **Identity**: two named byte strings with one recorded digest are equal
bytes, given that the run's preimages do not collide. -/
theorem Digests.identity {D : Digests} (a b : Named D) (same : a.recorded = b.recorded)
    (free : D.CollisionFreeOn [a.bytes, b.bytes]) : a.bytes = b.bytes :=
  free a.bytes (by simp) b.bytes (by simp) (by rw [a.recomputed, b.recomputed, same])

/-- **Only identity**: a check reading nothing but the digest, sound for `P`,
gives `P` of every input with that digest, so it certifies no property that
separates two colliding inputs. -/
theorem Digests.only_invariant {D : Digests} (check : D.Digest → Bool)
    (P : List UInt8 → Prop) (sound : ∀ b, check (D.digest b) = true → P b)
    {b b' : List UInt8} (same : D.digest b = D.digest b') (ok : check (D.digest b) = true) :
    P b' :=
  sound b' (by rw [← same]; exact ok)

/-- Digest lists recomputed over the units identify them, under the per-run
premise across both lists. -/
theorem Digests.identity_list {D : Digests} :
    ∀ (xs ys : List (List UInt8)),
      (∀ a, a ∈ xs → ∀ b, b ∈ ys → D.digest a = D.digest b → a = b) →
      xs.map D.digest = ys.map D.digest → xs = ys
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h
  | x :: xs, y :: ys, free, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    have hxy : x = y := free x (by simp) y (by simp) h.1
    have hrest : xs = ys := Digests.identity_list xs ys
      (fun a ha b hb => free a (by simp [ha]) b (by simp [hb])) h.2
    rw [hxy, hrest]

/-! ## Admitted settings -/

/-- The pinned EVM target (Osaka, G00 Q3): the only one admitted. -/
inductive EvmTarget where
  | osaka
  deriving DecidableEq, Repr

/-- How each source unit's ABI coder is chosen: its own pragma (solc's legacy
pipeline) or v2 for every unit (solc's via-IR pipeline). -/
inductive CoderMode where
  | pragma
  | forceV2
  deriving DecidableEq, Repr

/-- The coder a unit requesting `requested` gets. -/
def CoderMode.coderOf : CoderMode → AbiCoder → AbiCoder
  | .pragma, requested => requested
  | .forceV2, _ => .v2

/-- The coder mode of a solc pipeline. -/
def CoderMode.ofPipeline : Pipeline → CoderMode
  | .legacy => .pragma
  | .viaIR => .forceV2

/-- The provenance reader's effective coder of an analysed source is this
mode's coder for the unit's requested one. -/
theorem CoderMode.agrees (p : Provenance) (q : Pipeline) (s : String)
    (h : p.compilation = .analysed q s) :
    p.effectiveCoder = some ((CoderMode.ofPipeline q).coderOf p.requestedCoder) := by
  cases q <;> simp only [Provenance.effectiveCoder, h, CoderMode.ofPipeline, CoderMode.coderOf]

/-- Per source unit: the provenance at a node of any unit of a compilation
keeps the compilation and takes that unit's requested coder, so the same
mode gives that unit's effective coder. -/
theorem CoderMode.agrees_atNode (p : Provenance) (q : Pipeline) (s : String)
    (h : p.compilation = .analysed q s) (node : Lean.Json) :
    (p.atNode node).effectiveCoder =
      some ((CoderMode.ofPipeline q).coderOf (p.atNode node).requestedCoder) := by
  apply CoderMode.agrees _ q s
  simp only [Provenance.atNode]
  split <;> exact h

/-- The evaluation order an imported source gets by default from its solc
pipeline, as `solc_import` sets it.  The public theorem is not limited to
these two: `Settings.order` ranges over all eight. -/
def defaultOrder : Pipeline → EvalOrder
  | .legacy => {}
  | .viaIR => EvalOrder.viaIR

/-- One library link: the library `library` of the source unit `unit` at
`address`, as solc's `libraries` setting spells it. -/
structure Link where
  unit : String
  library : String
  address : Nat
  deriving DecidableEq, Repr

/-- The Osaka precompile addresses: `0x01`–`0x11` and P256VERIFY at `0x100`. -/
def Precompile (a : Nat) : Prop := (1 ≤ a ∧ a ≤ 0x11) ∨ a = 0x100

/-- Links are well formed: nonzero 160-bit addresses that are not
precompiles, one per library, no address shared. -/
def LinksWellFormed (ls : List Link) : Prop :=
  (∀ l, l ∈ ls → 0 < l.address ∧ l.address < 2 ^ 160 ∧ ¬ Precompile l.address) ∧
  (ls.map fun l => (l.unit, l.library)).Pairwise (· ≠ ·) ∧
  (ls.map Link.address).Pairwise (· ≠ ·)

/-- The settings of a compilation input.  `order` and `coder` are semantic
parameters of the source; `links` is deployment data; `compiler` names the
external analysis whose AST the frontend reads. -/
structure Settings where
  compiler : Compiler
  evm : EvmTarget := .osaka
  order : EvalOrder := {}
  coder : CoderMode := .pragma
  links : List Link := []

/-- The settings the public theorem admits: the profile compiler and no
pre-assigned link addresses (the session deploys and links every library;
a non-empty map is question Q1 of the G05 document).  Order and coder are
unconstrained here; that every one is admitted is `AllSettings`. -/
def Settings.Ok (s : Settings) : Prop :=
  s.compiler = .catalog0838 ∧ s.links = []

/-- What a recorded solc link map must satisfy even outside the admitted
profile (an oracle fixture's provenance). -/
def Settings.LinksRecorded (s : Settings) : Prop := LinksWellFormed s.links

/-- `Settings.Ok` does not read the order. -/
theorem Settings.ok_order {s : Settings} (h : s.Ok) (o : EvalOrder) :
    ({ s with order := o } : Settings).Ok := h

/-- `Settings.Ok` does not read the coder mode. -/
theorem Settings.ok_coder {s : Settings} (h : s.Ok) (m : CoderMode) :
    ({ s with coder := m } : Settings).Ok := h

/-- A 0.8.34 analysis is never an admitted input: SolKey compatibility only. -/
theorem Settings.ok_compiler {s : Settings} (h : s.Ok) : s.compiler ≠ .solkey0834 := by
  rw [h.1]; exact fun e => nomatch e

/-! ## Raw compilation input -/

/-- One original source unit: its name and its bytes. -/
structure SourceUnit where
  name : String
  bytes : List UInt8

/-- A whole compilation input: every source unit, the selected one and the
settings (G01's `SourceSpec.Input`). -/
structure Input where
  units : List SourceUnit
  main : String
  settings : Settings

/-- The raw input is well formed: distinct unit names, the selected unit
among them, admitted settings. -/
def Input.Ok (i : Input) : Prop :=
  (i.units.map SourceUnit.name).Pairwise (· ≠ ·) ∧
  i.main ∈ i.units.map SourceUnit.name ∧ i.settings.Ok

/-- The raw-input certificate: the units' digests, recomputed from the bytes
by the checker.  It identifies the input (`Digests.identity_list`), nothing
more. -/
def Input.Matches (D : Digests) (i : Input) (ds : List D.Digest) : Prop :=
  i.units.map (fun u => D.digest u.bytes) = ds

/-- Two inputs matching one digest list have the same unit bytes, under the
per-run premise. -/
theorem Input.Matches.identity {D : Digests} {i j : Input} {ds : List D.Digest}
    (hi : i.Matches D ds) (hj : j.Matches D ds)
    (free : ∀ a, a ∈ i.units.map SourceUnit.bytes → ∀ b, b ∈ j.units.map SourceUnit.bytes →
      D.digest a = D.digest b → a = b) :
    i.units.map SourceUnit.bytes = j.units.map SourceUnit.bytes := by
  apply Digests.identity_list _ _ free
  simp only [Input.Matches] at hi hj
  simp only [List.map_map]
  exact hi.trans hj.symm

/-! ## The frontend relations and their stage certificates -/

/-- What the frontend reads of G01's `SourceSpec`, over this module's
`Input`: syntax, resolution, well-formedness and the profile.  `settingsOf`
reads the settings a resolved input carries to its meaning. -/
structure FrontendSpec where
  Syntax : Type
  Resolved : Type
  Parses : Input → Syntax → Prop
  Resolves : Syntax → Resolved → Prop
  WellFormed : Resolved → Prop
  InProfile : Resolved → Prop
  settingsOf : Resolved → Settings
  /-- The library declarations of a resolved input, by unit and name. -/
  libraries : Resolved → List (String × String)

/-- `SourceSpec.Admitted`, over the frontend's fields. -/
def FrontendSpec.Admitted (F : FrontendSpec) (i : Input) (r : F.Resolved) : Prop :=
  ∃ s, F.Parses i s ∧ F.Resolves s r ∧ F.WellFormed r ∧ F.InProfile r

/-- Every link names a library declaration of the resolved input. -/
def LinksResolved (libs : List (String × String)) (ls : List Link) : Prop :=
  ∀ l, l ∈ ls → (l.unit, l.library) ∈ libs

/-- Obligations on the relations, not fields (owners S00, S01, G15): a
resolution carries the input's settings (to `SourceSpec.meaning`); the
profile includes the raw-input and link checks. -/
def FrontendSpec.SettingsRespected (F : FrontendSpec) : Prop :=
  (∀ i s r, F.Parses i s → F.Resolves s r → F.settingsOf r = i.settings) ∧
  (∀ i s r, F.Parses i s → F.Resolves s r → F.InProfile r →
    i.Ok ∧ LinksResolved (F.libraries r) (F.settingsOf r).links)

/-- **Admission is blind to the semantic settings**: an admitted input stays
admitted under every admitted settings value, with a resolution carrying the
new settings and the same library declarations.  This, not `Settings.ok_order`,
is what puts all eight `EvalOrder` combinations under the public theorem. -/
def FrontendSpec.AllSettings (F : FrontendSpec) : Prop :=
  ∀ i r, F.Admitted i r → ∀ st : Settings, st.Ok →
    ∃ r', F.Admitted { i with settings := st } r' ∧ F.settingsOf r' = st ∧
      F.libraries r' = F.libraries r

/-- Every evaluation order is admitted, given `AllSettings`. -/
theorem FrontendSpec.admits_order {F : FrontendSpec} (all : F.AllSettings)
    {i : Input} {r : F.Resolved} (h : F.Admitted i r) (ok : i.settings.Ok) (o : EvalOrder) :
    ∃ r', F.Admitted { i with settings := { i.settings with order := o } } r' ∧
      (F.settingsOf r').order = o := by
  obtain ⟨r', hr', hs, _⟩ := all i r h { i.settings with order := o } (Settings.ok_order ok o)
  exact ⟨r', hr', by rw [hs]⟩

/-- A checker of one judgment: acceptance implies it. -/
structure Checker (A B : Type) (J : A → B → Prop) where
  Cert : Type
  check : A → B → Cert → Bool
  sound : ∀ a b c, check a b c = true → J a b

/-- The four stage checkers: raw input, parse, resolution, and the resolved
metadata (well-formedness and profile, settings and links included). -/
structure Chain (F : FrontendSpec) where
  raw : Input → Bool
  raw_sound : ∀ i, raw i = true → i.Ok
  parse : Checker Input F.Syntax F.Parses
  resolve : Checker F.Syntax F.Resolved F.Resolves
  metadata : Checker F.Resolved Unit (fun r _ => F.WellFormed r ∧ F.InProfile r)

/-- A whole certificate: the syntax and each stage's certificate. -/
structure Chain.Cert {F : FrontendSpec} (ch : Chain F) where
  parsed : F.Syntax
  parse : ch.parse.Cert
  resolve : ch.resolve.Cert
  metadata : ch.metadata.Cert

/-- The composed check. -/
def Chain.check {F : FrontendSpec} (ch : Chain F) (i : Input) (r : F.Resolved)
    (c : ch.Cert) : Bool :=
  ch.raw i && ch.parse.check i c.parsed c.parse && ch.resolve.check c.parsed r c.resolve &&
    ch.metadata.check r () c.metadata

/-- **The composed check is sound**: acceptance gives a well-formed raw input
and its admitted resolution. -/
theorem Chain.checked {F : FrontendSpec} (ch : Chain F) (i : Input) (r : F.Resolved)
    (c : ch.Cert) (h : ch.check i r c = true) : i.Ok ∧ F.Admitted i r := by
  simp only [Chain.check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hr, hp⟩, hs⟩, hm⟩ := h
  have hwf := ch.metadata.sound r () c.metadata hm
  exact ⟨ch.raw_sound i hr,
    c.parsed, ch.parse.sound i c.parsed c.parse hp, ch.resolve.sound c.parsed r c.resolve hs, hwf⟩

/-- With the settings obligations, an accepted input has admitted settings
and its links name library declarations. -/
theorem Chain.checked_settings {F : FrontendSpec} (resp : F.SettingsRespected) (ch : Chain F)
    (i : Input) (r : F.Resolved) (c : ch.Cert) (h : ch.check i r c = true) :
    F.settingsOf r = i.settings ∧ i.settings.Ok ∧ LinksResolved (F.libraries r) i.settings.links := by
  obtain ⟨_, s, hp, hs, _, hi⟩ := ch.checked i r c h
  have hset := resp.1 i s r hp hs
  have hprof := resp.2 i s r hp hs hi
  rw [hset] at hprof
  exact ⟨hset, hprof.1.2.2, hprof.2⟩

/-- G01's `CheckedFrontend`, over the frontend's fields. -/
structure Checked (F : FrontendSpec) where
  Cert : Type
  produce : Input → Option (F.Resolved × Cert)
  check : Input → F.Resolved → Cert → Bool
  checked : ∀ i r c, check i r c = true → F.Admitted i r
  accepted : ∀ i r c, produce i = some (r, c) → check i r c = true
  complete : ∀ i r, F.Admitted i r → ∃ c, produce i = some (r, c)

/-- A chain and a producer whose outputs it accepts, complete on admitted
inputs, are a checked frontend.  The producer stays untrusted. -/
def Chain.frontend {F : FrontendSpec} (ch : Chain F) (produce : Input → Option (F.Resolved × ch.Cert))
    (accepted : ∀ i r c, produce i = some (r, c) → ch.check i r c = true)
    (complete : ∀ i r, F.Admitted i r → ∃ c, produce i = some (r, c)) : Checked F where
  Cert := ch.Cert
  produce := produce
  check := ch.check
  checked i r c h := (ch.checked i r c h).2
  accepted := accepted
  complete := complete

end Solidity.Roadmap.Frontend

/-- info: 'Solidity.Roadmap.Frontend.Chain.checked' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Roadmap.Frontend.Chain.checked
/-- info: 'Solidity.Roadmap.Frontend.Digests.identity_list' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Roadmap.Frontend.Digests.identity_list
