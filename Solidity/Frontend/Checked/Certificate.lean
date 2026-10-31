import Solidity.Frontend.Checked.Check
import Solidity.Roadmap.Frontend

/-!
# The parse-stage certificate (G05 instance, G11)

G05's interface (`Solidity/Roadmap/Frontend.lean`, §2 of
`docs/feature-work/roadmap-g05-frontend.md`) asks for a parse checker
`Checker Input F.Syntax F.Parses`.  This module gives one:

* the syntax of an input is one S00 tree per source unit, with its name
  (`Units`);
* `Parses i s` holds when each unit's bytes lex and its tree derives the
  unit's tokens under some layout and is the precedence-selected tree
  (`UnitParses`, the relation `parse_derives` concludes);
* the certificate is the layouts, one per unit; `parseChecker.check`
  re-lexes each unit's bytes and compares the yield, and `parseChecker.sound`
  proves acceptance implies `Parses`;
* `produce` runs the parser on every unit and `produce_accepted` proves the
  checker accepts what it produces (G05's `accepted`; `produceOpt` is the
  `Option` form `Chain.frontend` takes).  G05's `complete` (every admitted
  input is produced) is not provided: the parser's completeness is open,
  and `Parses` is not proved functional (the precedence tree's uniqueness is
  open, `docs/feature-work/frontend-parse.md`).

The checker reads bytes, never a digest: G05's "digests prove identity
only".  `FrontendSpec.ofParse` builds a `FrontendSpec` whose syntax and parse
relation are these, for the resolution (S01, G12–G14) and metadata stages
(G15) to fill.
-/

namespace Solidity.Frontend.Checked

open Solidity.Source
open Solidity.Roadmap.Frontend (Input SourceUnit Checker FrontendSpec Settings)

/-- One tree per source unit, with the unit's name. -/
abbrev Units := List (String × Syn .unit)

/-- A unit's bytes parse to `t`: they lex, and `t` derives their tokens and
satisfies the precedence predicate. -/
def UnitParses (src : Bytes) (t : Syn .unit) : Prop :=
  ∃ ps, Lexed src ps ∧ t.Derives (tokensOf ps) ∧ t.prec = true

/-- Each unit, in order, parses to the tree recorded under its name. -/
def UnitsParse : List SourceUnit → Units → Prop
  | [], [] => True
  | u :: us, p :: ps => (p.1 = u.name ∧ UnitParses u.bytes p.2) ∧ UnitsParse us ps
  | _, _ => False

/-- **The parse relation** of an input. -/
def Parses (i : Input) (s : Units) : Prop := UnitsParse i.units s

/-- The check of one unit under a layout: the lexer's certificate of the
bytes, the yield and the precedence predicate. -/
def checkUnit (u : SourceUnit) (p : String × Syn .unit) (L : List Choice) : Bool :=
  p.1 == u.name && p.2.prec &&
    match lex u.bytes with
    | .ok ps => decide (Lexed u.bytes ps) && p.2.toks L == some (tokensOf ps)
    | .error _ => false

/-- The check of every unit, one layout each. -/
def checkUnits : List SourceUnit → Units → List (List Choice) → Bool
  | [], [], [] => true
  | u :: us, p :: ps, L :: Ls => checkUnit u p L && checkUnits us ps Ls
  | _, _, _ => false

theorem checkUnit_sound {u : SourceUnit} {p : String × Syn .unit} {L : List Choice}
    (h : checkUnit u p L = true) : p.1 = u.name ∧ UnitParses u.bytes p.2 := by
  simp only [checkUnit, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hn, hp⟩, hl⟩ := h
  refine ⟨hn, ?_⟩
  split at hl
  · next ps hps =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hl
    exact ⟨ps, hl.1, ⟨L, hl.2⟩, hp⟩
  · cases hl

theorem checkUnits_sound : ∀ (us : List SourceUnit) (s : Units) (Ls : List (List Choice)),
    checkUnits us s Ls = true → UnitsParse us s
  | [], [], [], _ => trivial
  | u :: us, p :: ps, L :: Ls, h => by
    simp only [checkUnits, Bool.and_eq_true] at h
    exact ⟨checkUnit_sound h.1, checkUnits_sound us ps Ls h.2⟩
  | [], _ :: _, _, h => by simp only [checkUnits, Bool.false_eq_true] at h
  | [], [], _ :: _, h => by simp only [checkUnits, Bool.false_eq_true] at h
  | _ :: _, [], _, h => by simp only [checkUnits, Bool.false_eq_true] at h
  | _ :: _, _ :: _, [], h => by simp only [checkUnits, Bool.false_eq_true] at h

/-- **The parse-stage checker** of G05's `Chain`: the certificate is one
layout per unit; acceptance implies `Parses`. -/
def parseChecker : Checker Input Units Parses where
  Cert := List (List Choice)
  check i s c := checkUnits i.units s c
  sound i s c h := checkUnits_sound i.units s c h

/-- The untrusted producer: parse every unit. -/
def produce (i : Input) : Except Error (Units × List (List Choice)) :=
  match i.units.mapM (fun u => (parseWithLayout u.bytes).map fun r => ((u.name, r.1), r.2)) with
  | .ok rs => .ok (rs.map Prod.fst, rs.map Prod.snd)
  | .error e => .error e

theorem checkUnit_of_parse {u : SourceUnit} {t : Syn .unit} {L : List Choice}
    (h : parseWithLayout u.bytes = .ok (t, L)) : checkUnit u (u.name, t) L = true := by
  obtain ⟨ps, hl, hlx, ht, hp⟩ := parse_sound h
  simp only [checkUnit, beq_self_eq_true, Bool.true_and, hp, hl, ht, decide_eq_true hlx]

theorem checkUnits_mapM : ∀ (us : List SourceUnit) (rs : List ((String × Syn .unit) × List Choice)),
    us.mapM (fun u => (parseWithLayout u.bytes).map fun r => ((u.name, r.1), r.2)) = .ok rs →
    checkUnits us (rs.map Prod.fst) (rs.map Prod.snd) = true
  | [], rs, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | u :: us, rs, h => by
    simp only [List.mapM_cons, bind, Except.bind, Except.map] at h
    split at h
    · cases h
    · next r hr =>
      split at h
      · cases h
      · next rs' hrs =>
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        split at hr
        · cases hr
        · next v hv =>
          simp only [Except.ok.injEq] at hr
          subst hr
          simp only [List.map_cons, checkUnits, Bool.and_eq_true]
          exact ⟨checkUnit_of_parse hv, checkUnits_mapM us rs' hrs⟩

/-- **The producer's output is accepted.** -/
theorem produce_accepted {i : Input} {s : Units} {c : List (List Choice)}
    (h : produce i = .ok (s, c)) : parseChecker.check i s c = true := by
  unfold produce at h
  split at h
  · next rs hrs =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact checkUnits_mapM i.units rs hrs
  · cases h

/-- `produce` as G05's `Chain.frontend` takes it (`Option`). -/
def produceOpt (i : Input) : Option (Units × List (List Choice)) := (produce i).toOption

theorem produceOpt_accepted {i : Input} {s : Units} {c : List (List Choice)}
    (h : produceOpt i = some (s, c)) : parseChecker.check i s c = true := by
  unfold produceOpt at h
  cases hp : produce i with
  | error e => rw [hp] at h; cases h
  | ok r =>
    rw [hp] at h
    simp only [Except.toOption, Option.some.injEq] at h
    subst h
    exact produce_accepted hp

/-- A `FrontendSpec` whose syntax and parse relation are the checked
parser's; the later stages supply the rest. -/
def FrontendSpec.ofParse (Resolved : Type) (Resolves : Units → Resolved → Prop)
    (WellFormed InProfile : Resolved → Prop) (settingsOf : Resolved → Settings)
    (libraries : Resolved → List (String × String)) : FrontendSpec where
  Syntax := Units
  Resolved := Resolved
  Parses := Parses
  Resolves := Resolves
  WellFormed := WellFormed
  InProfile := InProfile
  settingsOf := settingsOf
  libraries := libraries

/-- The parse checker is the parse stage of every such spec. -/
def FrontendSpec.ofParse_checker (R : Type) (Rs : Units → R → Prop) (W I : R → Prop)
    (st : R → Settings) (lb : R → List (String × String)) :
    Checker Input (FrontendSpec.ofParse R Rs W I st lb).Syntax
      (FrontendSpec.ofParse R Rs W I st lb).Parses :=
  parseChecker

end Solidity.Frontend.Checked

/-- info: 'Solidity.Frontend.Checked.produce_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Checked.produce_accepted
/-- info: 'Solidity.Frontend.Checked.checkUnits_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.Checked.checkUnits_sound
