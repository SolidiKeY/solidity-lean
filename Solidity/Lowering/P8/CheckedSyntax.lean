import Solidity.Frontend.Checked.Certificate

/-!
# G15 settings-tagged checked syntax

The G05 resolution relation sees only syntax. A syntax consisting of units
alone forgets the input settings and cannot satisfy SettingsRespected on an
inhabited resolution. Carry semantic settings and main selection through the
checked parse stage instead. This reuses the existing bytes/layout checker;
parser completeness, resolution and complete admission are not asserted.
-/
namespace Solidity.Lowering.P8.CheckedSyntax
open Solidity.Roadmap.Frontend

private def orderDecEq : DecidableEq EvalOrder
  | ⟨a,b,c⟩, ⟨x,y,z⟩ => decidable_of_iff (a=x ∧ b=y ∧ c=z)
      (by simp only [EvalOrder.mk.injEq])
local instance : DecidableEq EvalOrder := orderDecEq

private def settingsDecEq : DecidableEq Settings
  | ⟨a,b,c,d,e⟩, ⟨v,w,x,y,z⟩ => decidable_of_iff (a=v ∧ b=w ∧ c=x ∧ d=y ∧ e=z)
      (by simp only [Settings.mk.injEq])
local instance : DecidableEq Settings := settingsDecEq

/-- Settings and the selected unit are input data, not parser guesses. -/
structure Parsed where
  settings : Settings
  main : String
  units : Solidity.Frontend.Checked.Units

def Parses (i : Input) (s : Parsed) : Prop :=
  s.settings = i.settings ∧ s.main = i.main ∧ Solidity.Frontend.Checked.Parses i s.units

/-- Exact lexer pieces and grammar layout for one original source unit. -/
structure UnitCert where
  pieces : List Solidity.Frontend.Checked.Piece
  layout : List Solidity.Frontend.Checked.Choice

abbrev Cert := List UnitCert

def checkUnit (u : SourceUnit) (p : String × Source.Syn .unit) (c : UnitCert) : Bool :=
  (p.1 == u.name) && p.2.prec && decide (Solidity.Frontend.Checked.Lexed u.bytes c.pieces) &&
    (p.2.toks c.layout == some (Solidity.Frontend.Checked.tokensOf c.pieces))

theorem checkUnit_sound {u : SourceUnit} {p : String × Source.Syn .unit} {c : UnitCert}
    (h : checkUnit u p c = true) : p.1 = u.name ∧ Solidity.Frontend.Checked.UnitParses u.bytes p.2 := by
  simp only [checkUnit, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, c.pieces, h.1.2, ⟨c.layout,h.2⟩,h.1.1.2⟩

def checkUnits : List SourceUnit → Solidity.Frontend.Checked.Units → Cert → Bool
  | [], [], [] => true
  | u::us, p::ps, c::cs => checkUnit u p c && checkUnits us ps cs
  | _, _, _ => false

theorem checkUnits_sound : ∀ us ps cs, checkUnits us ps cs = true →
    Solidity.Frontend.Checked.UnitsParse us ps
  | [], [], [], _ => trivial
  | u::us, p::ps, c::cs, h => by
    simp only [checkUnits, Bool.and_eq_true] at h
    exact ⟨checkUnit_sound h.1, checkUnits_sound us ps cs h.2⟩
  | [], _::_, _, h => by cases h
  | [], [], _::_, h => by cases h
  | _::_, [], _, h => by cases h
  | _::_, _::_, [], h => by cases h

def check (i : Input) (s : Parsed) (c : Cert) : Bool :=
  decide (s.settings = i.settings) && (s.main == i.main) && checkUnits i.units s.units c

theorem check_sound (i : Input) (s : Parsed) (c : Cert)
    (h : check i s c = true) : Parses i s := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, checkUnits_sound i.units s.units c h.2⟩

def parseChecker : Checker Input Parsed Parses where
  Cert := Cert
  check := check
  sound := check_sound

/-- Candidate production is untrusted; the check reads source bytes directly. -/
def candidate (i : Input) : Option (Parsed × Cert) := do
  let p ← Solidity.Frontend.Checked.produceOpt i
  let pieces ← i.units.mapM fun u => (Solidity.Frontend.Checked.lex u.bytes).toOption
  return (⟨i.settings,i.main,p.1⟩, (pieces.zip p.2).map fun pair => ⟨pair.1,pair.2⟩)

def validate (i : Input) (p : Parsed × Cert) : Option (Parsed × Cert) :=
  if check i p.1 p.2 then some p else none

def produce (i : Input) : Option (Parsed × Cert) := (candidate i).bind (validate i)

theorem validate_accepted {i : Input} {p : Parsed × Cert} {s : Parsed} {c : Cert}
    (h : validate i p = some (s,c)) : check i s c = true := by
  unfold validate at h
  split at h
  · next hc =>
    have hp := Option.some.inj h
    cases hp
    exact hc
  · cases h

theorem produce_accepted {i : Input} {s : Parsed} {c : Cert}
    (h : produce i = some (s,c)) : check i s c = true := by
  unfold produce at h
  cases hp : candidate i with
  | none => rw [hp] at h; cases h
  | some p =>
    rw [hp] at h
    exact validate_accepted h

/-- A successful certificate records the actual input's semantic settings. -/
theorem settings_recorded {i : Input} {s : Parsed} {c : parseChecker.Cert}
    (h : check i s c = true) : s.settings = i.settings := (check_sound i s c h).1

theorem main_recorded {i : Input} {s : Parsed} {c : parseChecker.Cert}
    (h : check i s c = true) : s.main = i.main := (check_sound i s c h).2.1

/-- The old units-only parse relation ignores settings. This fact must not
be silently combined with a settings-respecting input-independent resolver. -/
theorem old_parse_ignores_settings {i : Input} {s : Solidity.Frontend.Checked.Units}
    (h : Solidity.Frontend.Checked.Parses i s) (st : Settings) : Solidity.Frontend.Checked.Parses {i with settings := st} s := h

/-- Two parses of identical syntax cannot resolve to the same result under
unequal settings in a settings-respecting frontend. -/
theorem unrecorded_settings_obstruction (F : FrontendSpec) (resp : F.SettingsRespected)
    (i j : Input) (s : F.Syntax) (r : F.Resolved)
    (hi : F.Parses i s) (hj : F.Parses j s) (hr : F.Resolves s r)
    (different : i.settings ≠ j.settings) : False :=
  different ((resp.1 i s r hi hr).symm.trans (resp.1 j s r hj hr))

/-- Concrete obstruction for the existing units-only FrontendSpec constructor:
any actual parse/resolution witness contradicts SettingsRespected. This does
not assert that an empty/vacuous resolver has such a witness. -/
theorem units_only_resolver_obstruction (R : Type)
    (Rs : Solidity.Frontend.Checked.Units → R → Prop) (W I : R → Prop)
    (st : R → Settings) (libs : R → List (String × String))
    {i : Input} {us : Solidity.Frontend.Checked.Units} {r : R}
    (hp : Solidity.Frontend.Checked.Parses i us) (hr : Rs us r)
    (resp : (Solidity.Frontend.Checked.FrontendSpec.ofParse R Rs W I st libs).SettingsRespected) : False := by
  have hl := resp.1 {i with settings := Settings.ofPipeline .legacy} us r hp hr
  have hv := resp.1 {i with settings := Settings.ofPipeline .viaIR} us r hp hr
  have contradiction := congrArg Settings.coder (hl.symm.trans hv)
  change CoderMode.pragma = CoderMode.forceV2 at contradiction
  cases contradiction

/-- The raw settings check is exactly G05's existing approved settings. -/
def settingsB (s : Settings) : Bool :=
  decide (s.compiler = .catalog0838) && s.links.isEmpty &&
    ((decide (s.order = defaultOrder .legacy) && decide (s.coder = .pragma)) ||
     (decide (s.order = defaultOrder .viaIR) && decide (s.coder = .forceV2)))

theorem settingsB_iff (s : Settings) : settingsB s = true ↔ s.Ok := by
  simp only [settingsB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.isEmpty_iff,
    Settings.Ok, Settings.Pipelined]
  constructor
  · rintro ⟨⟨hc,hl⟩, hp⟩
    rcases hp with hp | hp
    · exact ⟨hc,hl,.legacy,hp.1,hp.2⟩
    · exact ⟨hc,hl,.viaIR,hp.1,hp.2⟩
  · rintro ⟨hc,hl,q,ho,hm⟩
    cases q with
    | legacy => exact ⟨⟨hc,hl⟩, .inl ⟨ho,hm⟩⟩
    | viaIR => exact ⟨⟨hc,hl⟩, .inr ⟨ho,hm⟩⟩

def rawB (i : Input) : Bool :=
  decide ((i.units.map SourceUnit.name).Pairwise (· ≠ ·)) &&
    decide (i.main ∈ i.units.map SourceUnit.name) && settingsB i.settings

theorem rawB_iff (i : Input) : rawB i = true ↔ i.Ok := by
  simp only [rawB, Bool.and_eq_true, decide_eq_true_eq, settingsB_iff, Input.Ok, and_assoc]

namespace Controls

def input (q : Solidity.Frontend.Source.Pipeline) : Input := {
  units := [⟨"C.sol", [99,111,110,116,114,97,99,116,32,67,32,123,125]⟩]
  main := "C.sol"
  settings := Settings.ofPipeline q }

theorem legacy_raw : rawB (input .legacy) = true := by decide +kernel
theorem viaIR_raw : rawB (input .viaIR) = true := by decide +kernel

/-- Explicit source tree/layout certificates, checked against the source bytes.
The opaque untrusted producer is not evaluated by these kernel controls. -/
def tree : Source.Syn .unit := .unit (.cons (.contract false "C" .none .nil .nil) .nil)
def parsedInput (q : Solidity.Frontend.Source.Pipeline) : Parsed :=
  ⟨(input q).settings, "C.sol", [("C.sol", tree)]⟩
def pieces : List Solidity.Frontend.Checked.Piece := [
  ⟨.tok (.kw .contract), [99,111,110,116,114,97,99,116]⟩,
  ⟨.trivia .ws, [32]⟩,
  ⟨.tok (.ident "C"), [67]⟩,
  ⟨.trivia .ws, [32]⟩,
  ⟨.tok (.punct .lbrace), [123]⟩,
  ⟨.tok (.punct .rbrace), [125]⟩]
def layout : Cert := [⟨pieces,[]⟩]

theorem legacy_certificate_checked : check (input .legacy) (parsedInput .legacy) layout = true := by decide +kernel

theorem viaIR_certificate_checked : check (input .viaIR) (parsedInput .viaIR) layout = true := by decide +kernel

theorem wrong_pipeline_refused : check (input .viaIR) (parsedInput .legacy) layout = false := by decide +kernel

theorem wrong_main_refused : check {input .legacy with main := "Other.sol"}
    (parsedInput .legacy) layout = false := by decide +kernel

theorem wrong_source_refused : check {input .legacy with
    units := [⟨"C.sol", [99,111,110,116,114,97,99,116,32,68,32,123,125]⟩]} (parsedInput .legacy) layout = false := by decide +kernel

theorem historical_compiler_refused : rawB {input .legacy with
    settings := {(input .legacy).settings with compiler := .solkey0834}} = false := by decide +kernel

theorem missing_main_refused : rawB {input .legacy with main := "Other.sol"} = false := by decide +kernel

/-- The checker yields an inhabited independent grammar relation. -/
theorem actual_source_parses : Solidity.Frontend.Checked.Parses (input .legacy)
    [("C.sol",tree)] := (check_sound _ _ _ legacy_certificate_checked).2.2

theorem units_only_settings_refuted :
    ¬ (Solidity.Frontend.Checked.FrontendSpec.ofParse Unit (fun _ _ => True)
      (fun _ => True) (fun _ => True) (fun _ => Settings.ofPipeline .legacy)
      (fun _ => [])).SettingsRespected := by
  intro h
  exact units_only_resolver_obstruction Unit (fun _ _ => True) (fun _ => True)
    (fun _ => True) (fun _ => Settings.ofPipeline .legacy) (fun _ => [])
    (r := ()) actual_source_parses True.intro h

theorem missing_certificate_refused : check (input .legacy) (parsedInput .legacy) [] = false := by decide +kernel

theorem duplicate_unit_refused : rawB {input .legacy with
    units := (input .legacy).units ++ (input .legacy).units} = false := by decide +kernel

theorem nonpipeline_order_refused : rawB {input .legacy with
    settings := {(input .legacy).settings with order := ⟨true,false,false⟩}} = false := by decide +kernel

end Controls

/-- info: 'Solidity.Lowering.P8.CheckedSyntax.check_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms check_sound
/-- info: 'Solidity.Lowering.P8.CheckedSyntax.produce_accepted' depends on axioms: [propext] -/
#guard_msgs in #print axioms produce_accepted
/-- info: 'Solidity.Lowering.P8.CheckedSyntax.unrecorded_settings_obstruction' does not depend on any axioms -/
#guard_msgs in #print axioms unrecorded_settings_obstruction
/-- info: 'Solidity.Lowering.P8.CheckedSyntax.rawB_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms rawB_iff
end Solidity.Lowering.P8.CheckedSyntax

/-- info: 'Solidity.Lowering.P8.CheckedSyntax.units_only_resolver_obstruction' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Lowering.P8.CheckedSyntax.units_only_resolver_obstruction
/-- info: 'Solidity.Lowering.P8.CheckedSyntax.Controls.actual_source_parses' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Lowering.P8.CheckedSyntax.Controls.actual_source_parses
