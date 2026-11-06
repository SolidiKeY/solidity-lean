import Solidity.Lowering.P8.CheckedSyntax
import Solidity.Lowering.P9.DeclarationIdentity
import Solidity.Source.WellFormed

/-! Checked settings-tagged per-unit Source resolutions. These are actual
Source.Resolves' judgments, not solc-JSON correspondence, global import typing,
complete profile admission or SourceSpec adequacy. -/
namespace Solidity.Lowering.P8.SourceResolutions
open Solidity.Roadmap.Frontend
open CheckedSyntax

private def orderDecEq : DecidableEq EvalOrder
  | ⟨a,b,c⟩, ⟨x,y,z⟩ => decidable_of_iff (a=x ∧ b=y ∧ c=z)
      (by simp only [EvalOrder.mk.injEq])
local instance : DecidableEq EvalOrder := orderDecEq
private def settingsDecEq : DecidableEq Settings
  | ⟨a,b,c,d,e⟩, ⟨v,w,x,y,z⟩ => decidable_of_iff (a=v ∧ b=w ∧ c=x ∧ d=y ∧ e=z)
      (by simp only [Settings.mk.injEq])
local instance : DecidableEq Settings := settingsDecEq
private def envDecEq : DecidableEq Source.Env
  | ⟨ds⟩, ⟨es⟩ => decidable_of_iff (ds=es) (by simp only [Source.Env.mk.injEq])
local instance : DecidableEq Source.Env := envDecEq
private def resolutionDecEq : DecidableEq Source.Resolution
  | ⟨u,e,p,c⟩, ⟨v,f,q,d⟩ => decidable_of_iff (u=v ∧ e=f ∧ p=q ∧ c=d)
      (by simp only [Source.Resolution.mk.injEq])
local instance : DecidableEq Source.Resolution := resolutionDecEq

/-- G05 admits only pragma/legacy and forceV2/viaIR pairs. Under Settings.Ok
this extraction agrees with the recorded evaluation order; it is not used to
invent semantics for an inadmissible settings combination. -/
def pipeline (s : Settings) : Solidity.Frontend.Source.Pipeline :=
  match s.coder with | .pragma => .legacy | .forceV2 => .viaIR

/-- Explicit bridges between the frontend and roadmap's distinct enums. -/
def sourcePipeline : Solidity.Frontend.Source.Pipeline → Roadmap.Pipeline
  | .legacy => .legacy | .viaIR => .viaIR

def sourceCoder : Solidity.Frontend.Source.AbiCoder → Roadmap.AbiCoder
  | .v1 => .v1 | .v2 => .v2

def frontendCoder : Roadmap.AbiCoder → Solidity.Frontend.Source.AbiCoder
  | .v1 => .v1 | .v2 => .v2

def sourceSettings (s : Settings) : Source.Settings := ⟨sourcePipeline (pipeline s), []⟩

theorem pipeline_ofPipeline (q : Solidity.Frontend.Source.Pipeline) :
    pipeline (Settings.ofPipeline q) = q := by cases q <;> rfl

theorem order_agrees {s : Settings} (h : s.Ok) : s.order = defaultOrder (pipeline s) := by
  obtain ⟨_, _, q, ho, hc⟩ := h
  rw [ho]
  cases q <;> simp only [pipeline, hc, CoderMode.ofPipeline]

theorem coder_agrees (s : Settings) (u : Source.Syn .unit) :
    (sourceSettings s).coder u = sourceCoder (s.coder.coderOf (frontendCoder u.pragmaCoder)) := by
  cases hc : s.coder <;> cases hu : u.pragmaCoder <;>
    simp only [sourceSettings, pipeline, hc, sourcePipeline, Source.Settings.coder,
      hu, sourceCoder, frontendCoder, CoderMode.coderOf]

structure Packet where
  settings : Settings
  main : String
  units : List (String × Source.Resolution)

/-- Every original unit is resolved in order, under the recorded pipeline.
Source environments are computed by Source.resolveUnit, never caller input. -/
def produce (p : Parsed) : Packet :=
  ⟨p.settings, p.main, p.units.map (fun u => (u.1, Source.resolveUnit (sourceSettings p.settings) u.2))⟩

def UnitResolves (s : Settings) (u : String × Source.Syn .unit)
    (r : String × Source.Resolution) : Prop :=
  r.1 = u.1 ∧ Source.Resolves' (sourceSettings s) u.2 r.2

/-- Structural relation preserves every input/output position, including
length and source name. It uses the actual per-unit Source relation. -/
def UnitsResolve (s : Settings) : List (String × Source.Syn .unit) →
    List (String × Source.Resolution) → Prop
  | [], [] => True
  | u :: us, r :: rs => UnitResolves s u r ∧ UnitsResolve s us rs
  | _, _ => False

def Resolves (p : Parsed) (r : Packet) : Prop :=
  r.settings = p.settings ∧ r.main = p.main ∧ UnitsResolve p.settings p.units r.units

private theorem units_iff (s : Settings) (us : List (String × Source.Syn .unit))
    (rs : List (String × Source.Resolution)) :
    UnitsResolve s us rs ↔
      rs = us.map (fun u => (u.1, Source.resolveUnit (sourceSettings s) u.2)) := by
  induction us generalizing rs with
  | nil =>
    cases rs with
    | nil => exact ⟨fun _ => rfl, fun _ => trivial⟩
    | cons r rs => exact ⟨fun h => False.elim h, fun h => by cases h⟩
  | cons u us ih =>
    cases rs with
    | nil => exact ⟨fun h => False.elim h, fun h => by cases h⟩
    | cons r rs =>
      rcases u with ⟨name, tree⟩
      rcases r with ⟨name', res⟩
      simp only [UnitsResolve, UnitResolves, Source.Resolves', sourceSettings,
        true_and, List.map_cons, List.cons.injEq, Prod.mk.injEq, ih]

def check (p : Parsed) (r : Packet) : Bool :=
  decide (r.settings = p.settings) && (r.main == p.main) &&
    decide (r.units = (produce p).units)

theorem check_iff (p : Parsed) (r : Packet) : check p r = true ↔ Resolves p r := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    Resolves, units_iff, produce]
  exact and_assoc

theorem produce_resolves (p : Parsed) : Resolves p (produce p) := by
  refine ⟨rfl, rfl, (units_iff _ _ _).mpr rfl⟩

theorem produce_checked (p : Parsed) : check p (produce p) = true :=
  (check_iff _ _).mpr (produce_resolves p)

def checker : Checker Parsed Packet Resolves where
  Cert := Unit
  check p r _ := check p r
  sound p r _ h := (check_iff p r).mp h

theorem unique {p : Parsed} {r r' : Packet} (h : Resolves p r) (h' : Resolves p r') : r = r' := by
  obtain ⟨hs, hm, hu⟩ := h
  obtain ⟨hs', hm', hu'⟩ := h'
  have hr := ((units_iff _ _ _).mp hu).trans ((units_iff _ _ _).mp hu').symm
  cases r; cases r'
  simp only [Packet.mk.injEq]
  exact ⟨hs.trans hs'.symm, hm.trans hm'.symm, hr⟩

theorem checked_tags {i : Input} {p : Parsed} {r : Packet}
    (hp : Parses i p) (hr : Resolves p r) : r.settings = i.settings ∧ r.main = i.main :=
  ⟨hr.1.trans hp.1, hr.2.1.trans hp.2.1⟩

theorem names_preserved {p : Parsed} {r : Packet} (h : Resolves p r) :
    r.units.map Prod.fst = p.units.map Prod.fst := by
  rw [(units_iff _ _ _).mp h.2.2]
  simp only [List.map_map, Function.comp_def]

theorem resolved_entry {p : Parsed} {r : Packet} (h : Resolves p r)
    {entry : String × Source.Resolution} (he : entry ∈ r.units) :
    ∃ u ∈ p.units, UnitResolves p.settings u entry := by
  rw [(units_iff _ _ _).mp h.2.2] at he
  obtain ⟨u, hu, he⟩ := List.mem_map.mp he
  subst entry
  exact ⟨u, hu, rfl, rfl, rfl⟩

/-- Raw-input admission, original-byte parsing, and exact per-unit source
resolution compose. No profile/typing/import-global/semantic conclusion is
claimed by this partial stage chain. -/
def checkInput (i : Input) (p : Parsed) (r : Packet) (c : CheckedSyntax.Cert) : Bool :=
  rawB i && CheckedSyntax.check i p c && check p r

theorem input_sound (i : Input) (p : Parsed) (r : Packet) (c : CheckedSyntax.Cert)
    (h : checkInput i p r c = true) : i.Ok ∧ Parses i p ∧ Resolves p r := by
  simp only [checkInput, Bool.and_eq_true] at h
  exact ⟨(rawB_iff i).mp h.1.1, CheckedSyntax.check_sound i p c h.1.2,
    (check_iff p r).mp h.2⟩

theorem checked_input_tags (i : Input) (p : Parsed) (r : Packet) (c : CheckedSyntax.Cert)
    (h : checkInput i p r c = true) : r.settings = i.settings ∧ r.main = i.main :=
  checked_tags (input_sound i p r c h).2.1 (input_sound i p r c h).2.2

/-- Per-unit Source.Resolves' uses empty source links. The composed raw stage
also checks the ORIGINAL input links are empty; projection alone does not
validate arbitrary caller-supplied settings. -/
theorem checked_input_links (i : Input) (p : Parsed) (r : Packet) (c : CheckedSyntax.Cert)
    (h : checkInput i p r c = true) : i.settings.links = [] := by
  have hs : i.settings.Ok := (input_sound i p r c h).1.2.2
  exact hs.2.1

#print axioms names_preserved
#print axioms resolved_entry
#print axioms input_sound
#print axioms check_iff
#print axioms produce_checked
#print axioms unique
#print axioms checked_tags
end Solidity.Lowering.P8.SourceResolutions
