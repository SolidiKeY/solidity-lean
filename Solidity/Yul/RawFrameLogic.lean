import Solidity.Yul.RawFrame
import Solidity.Yul.DirtyReadback
import Solidity.Yul.WordAdapterLogic

/-! Concrete word-calculus interpretation for the existing raw LOCAL frame.
The initial frame parameter supplies the clean backup/world retained by capture.
Box and diamond quantify actual interpreter completions. No Source statement,
compiler adequacy, new calculus rule or SolKey taclet is supplied.
Dirty-readback observations use the published decoder without changing the raw
frame; pipeline equality includes refused results and backup fallback. -/
namespace Solidity.Yul.RawFrame.Logic

def holds {ctx control} (mode : Solidity.Modality)
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (post : RawFrame.Outcome ctx control → Prop) (state : RawFrame.State ctx) : Prop :=
  match mode with
  | .box => ∀ fuel result, RawFrame.run code policy fuel state = some result → post result
  | .diamond => ∃ fuel result, RawFrame.run code policy fuel state = some result ∧ post result

def formula {ctx control} (mode : Solidity.Modality)
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (post : RawFrame.Outcome ctx control → Prop) (state : RawFrame.State ctx) :
    Solidity.Yul.Logic.Fml (0 + wordCellCount (localExternalTypes ctx)) :=
  WordAdapter.formula mode code policy (fun result => post (RawFrame.Outcome.ofWord state result))


/-- The existing word formula interprets actual completed raw-frame runs exactly. -/
theorem formula_iff : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control) (mode : Solidity.Modality)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code)
 (post : Solidity.Yul.RawFrame.Outcome ctx control → Prop) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawFrame.Logic.formula mode code policy post state).holds
 (Solidity.Yul.WordState.pack ⟨Fin.elim0,Solidity.Yul.RawFrame.view state⟩) ↔
 Solidity.Yul.RawFrame.Logic.holds mode code policy post state := by
  intro ctx control mode code policy post state
  unfold formula
  rw [WordAdapter.formula_iff]
  cases mode with
  | box =>
    constructor
    · intro valid fuel result done
      obtain ⟨wordResult,finished,captured⟩ :=
        (RawFrame.run_some_iff ctx control code policy fuel state result).mp done
      have actual := valid fuel wordResult finished
      change post (RawFrame.Outcome.ofWord state wordResult) at actual
      rw [captured] at actual
      exact actual
    · intro valid fuel result done
      exact valid fuel (RawFrame.Outcome.ofWord state result)
        ((RawFrame.run_some_iff ctx control code policy fuel state _).mpr ⟨result,done,rfl⟩)
  | diamond =>
    constructor
    · rintro ⟨fuel,result,done,valid⟩
      exact ⟨fuel,RawFrame.Outcome.ofWord state result,
        (RawFrame.run_some_iff ctx control code policy fuel state _).mpr ⟨result,done,rfl⟩,valid⟩
    · rintro ⟨fuel,result,done,valid⟩
      obtain ⟨wordResult,finished,captured⟩ :=
        (RawFrame.run_some_iff ctx control code policy fuel state result).mp done
      refine ⟨fuel,wordResult,finished,?_⟩
      change post (RawFrame.Outcome.ofWord state wordResult)
      rw [captured]
      exact valid

/-- Soundness for the displayed premise of a concrete existing Rule.
The shallow word calculus and every original Rule side condition are unchanged. -/
theorem rule_premise_sound : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control) (mode : Solidity.Modality)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code)
 (post : Solidity.Yul.RawFrame.Outcome ctx control → Prop) (state : Solidity.Yul.RawFrame.State ctx),
 ∀ (premise : Solidity.Yul.Logic.Fml (0 + Solidity.Yul.wordCellCount (Solidity.Yul.localExternalTypes ctx))),
 Solidity.Yul.Logic.Rule (Solidity.Yul.RawFrame.Logic.formula mode code policy post state) premise →
 (Solidity.Yul.RawFrame.Logic.holds mode code policy post state ↔
 premise.holds (Solidity.Yul.WordState.pack ⟨Fin.elim0,Solidity.Yul.RawFrame.view state⟩)) := by
  intro ctx control mode code policy post state premise rule
  exact (formula_iff ctx control mode code policy post state).symm.trans
    (Solidity.Yul.Logic.Rule.sound rule _)


/-- Deterministic completed outcomes let a successful diamond establish its box postcondition. -/
theorem diamond_implies_box : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code)
 (post : Solidity.Yul.RawFrame.Outcome ctx control → Prop) (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawFrame.Logic.holds .diamond code policy post state → Solidity.Yul.RawFrame.Logic.holds .box code policy post state := by
  intro ctx control code policy post state actual
  obtain ⟨chosen,out,finished,valid⟩ := actual
  intro fuel result done
  have same := RawFrame.run_completed_unique ctx control code policy state
    fuel chosen result out done finished
  rw [same]
  exact valid

/-- A false-postcondition box is exactly noncompletion at every fuel, never one finite timeout. -/
theorem box_false_iff_none : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code)
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawFrame.Logic.holds .box code policy (fun _ => False) state ↔ ∀ fuel, Solidity.Yul.RawFrame.run code policy fuel state = none := by
  intro ctx control code policy state
  constructor
  · intro valid fuel
    cases actual : RawFrame.run code policy fuel state with
    | none => rfl
    | some result => exact False.elim (valid fuel result actual)
  · intro all fuel result done
    rw [all fuel] at done
    cases done

/-- A diamond is termination plus its box postcondition for the actual deterministic raw interpreter. -/
theorem diamond_iff_termination_and_box : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code)
 (post : Solidity.Yul.RawFrame.Outcome ctx control → Prop) (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawFrame.Logic.holds .diamond code policy post state ↔ Solidity.Yul.RawFrame.Logic.holds .diamond code policy (fun _ => True) state ∧ Solidity.Yul.RawFrame.Logic.holds .box code policy post state := by
  intro ctx control code policy post state
  constructor
  · intro actual
    obtain ⟨fuel,result,done,valid⟩ := actual
    exact ⟨⟨fuel,result,done,True.intro⟩,
      diamond_implies_box ctx control code policy post state ⟨fuel,result,done,valid⟩⟩
  · rintro ⟨⟨fuel,result,done,_⟩,valid⟩
    exact ⟨fuel,result,done,valid fuel result done⟩


/-- A genuine completed raw run determines either modality's whole-outcome postcondition. -/
theorem holds_completed : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control) (mode : Solidity.Modality)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code)
 (post : Solidity.Yul.RawFrame.Outcome ctx control → Prop) (state : Solidity.Yul.RawFrame.State ctx)
 (fuel : Nat) (result : Solidity.Yul.RawFrame.Outcome ctx control),
 Solidity.Yul.RawFrame.run code policy fuel state = some result →
 (Solidity.Yul.RawFrame.Logic.holds mode code policy post state ↔ post result) := by
  intro ctx control mode code policy post state fuel result done
  cases mode with
  | box =>
    constructor
    · intro valid
      exact valid fuel result done
    · intro valid otherFuel other otherDone
      have same := RawFrame.run_completed_unique ctx control code policy state
        otherFuel fuel other result otherDone done
      rw [same]
      exact valid
  | diamond =>
    constructor
    · intro actual
      exact diamond_implies_box ctx control code policy post state actual fuel result done
    · intro valid
      exact ⟨fuel,result,done,valid⟩

/-- Conjunction distributes over both actual raw modalities. The diamond
reverse direction uses deterministic completed outcomes, without assuming termination. -/
theorem holds_and : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control) (mode : Solidity.Modality)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code)
 (first second : Solidity.Yul.RawFrame.Outcome ctx control → Prop)
 (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawFrame.Logic.holds mode code policy (fun result => first result ∧ second result) state ↔
 Solidity.Yul.RawFrame.Logic.holds mode code policy first state ∧
 Solidity.Yul.RawFrame.Logic.holds mode code policy second state := by
  intro ctx control mode code policy first second state
  cases mode with
  | box =>
    constructor
    · intro valid
      exact ⟨fun fuel result done => (valid fuel result done).1,
        fun fuel result done => (valid fuel result done).2⟩
    · rintro ⟨left,right⟩ fuel result done
      exact ⟨left fuel result done,right fuel result done⟩
  | diamond =>
    constructor
    · rintro ⟨fuel,result,done,left,right⟩
      exact ⟨⟨fuel,result,done,left⟩,⟨fuel,result,done,right⟩⟩
    · rintro ⟨⟨fuel,result,done,left⟩,right⟩
      have rightBox : holds .box code policy second state :=
        diamond_implies_box ctx control code policy second state right
      exact ⟨fuel,result,done,left,rightBox fuel result done⟩

/-- Disjunction distributes over actual raw modalities. For box, this uses
deterministic completed outcomes; noncompletion is treated as vacuity, not termination. -/
theorem holds_or : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control) (mode : Solidity.Modality)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code)
 (first second : Solidity.Yul.RawFrame.Outcome ctx control → Prop)
 (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawFrame.Logic.holds mode code policy (fun result => first result ∨ second result) state ↔
 Solidity.Yul.RawFrame.Logic.holds mode code policy first state ∨
 Solidity.Yul.RawFrame.Logic.holds mode code policy second state := by
  intro ctx control mode code policy first second state
  classical
  by_cases completed : ∃ fuel result, RawFrame.run code policy fuel state = some result
  · obtain ⟨fuel,result,done⟩ := completed
    rw [holds_completed ctx control mode code policy _ state fuel result done,
      holds_completed ctx control mode code policy first state fuel result done,
      holds_completed ctx control mode code policy second state fuel result done]
  · cases mode with
    | box =>
      have vacuous : ∀ post : RawFrame.Outcome ctx control → Prop,
          holds .box code policy post state := by
        intro post fuel result done
        exact False.elim (completed ⟨fuel,result,done⟩)
      exact ⟨fun _ => Or.inl (vacuous first),fun _ => vacuous _⟩
    | diamond =>
      have absent : ∀ post : RawFrame.Outcome ctx control → Prop,
          ¬ holds .diamond code policy post state := by
        intro post actual
        obtain ⟨fuel,result,done,_⟩ := actual
        exact completed ⟨fuel,result,done⟩
      constructor
      · intro actual
        exact False.elim (absent _ actual)
      · intro either
        cases either with
        | inl actual => exact False.elim (absent first actual)
        | inr actual => exact False.elim (absent second actual)

/-- Box negation excludes an actual diamond witness; no determinism is needed. -/
theorem box_not_iff_not_diamond : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code)
 (post : Solidity.Yul.RawFrame.Outcome ctx control → Prop)
 (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawFrame.Logic.holds .box code policy (fun result => ¬ post result) state ↔
 ¬ Solidity.Yul.RawFrame.Logic.holds .diamond code policy post state := by
  intro ctx control code policy post state
  simp only [holds, not_exists, not_and]

/-- Classical diamond negation is failure of the corresponding box over actual completions. -/
theorem diamond_not_iff_not_box : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code)
 (post : Solidity.Yul.RawFrame.Outcome ctx control → Prop)
 (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawFrame.Logic.holds .diamond code policy (fun result => ¬ post result) state ↔
 ¬ Solidity.Yul.RawFrame.Logic.holds .box code policy post state := by
  intro ctx control code policy post state
  classical
  constructor
  · rintro ⟨fuel,result,done,bad⟩ all
    exact bad (all fuel result done)
  · intro invalid
    apply Classical.byContradiction
    intro absent
    apply invalid
    intro fuel result done
    apply Classical.byContradiction
    intro bad
    exact absent ⟨fuel,result,done,bad⟩

/-- Whole-outcome implication is preserved by either actual raw modality.
No termination or coherence premise is needed. -/
theorem holds_mono : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control) (mode : Solidity.Modality)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code)
 (first second : Solidity.Yul.RawFrame.Outcome ctx control → Prop)
 (state : Solidity.Yul.RawFrame.State ctx),
 (∀ result, first result → second result) →
 Solidity.Yul.RawFrame.Logic.holds mode code policy first state →
 Solidity.Yul.RawFrame.Logic.holds mode code policy second state := by
  intro ctx control mode code policy first second state implication actual
  cases mode <;> simp only [holds] at * <;> grind

/-- Even skip captures a full raw snapshot; it does not preserve a sparse overlay as metadata. -/
theorem skip_run : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control)
 (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawFrame.run (.skip : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 True.intro 1 state =
 some ⟨Solidity.Yul.RawFrame.capture state (Solidity.Yul.RawFrame.view state),.normal⟩ := by
  intro ctx control state
  change some (RawFrame.Outcome.mk
    (RawFrame.capture state
      (WordState.unpack (WordState.pack ⟨Fin.elim0,RawFrame.view state⟩)).cells) .normal) = _
  rw [WordState.unpack_pack]

/-- Skip's modal postcondition observes its actual full snapshot, not sparse metadata identity. -/
theorem holds_skip : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control) (mode : Solidity.Modality)
 (post : Solidity.Yul.RawFrame.Outcome ctx control → Prop)
 (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawFrame.Logic.holds mode (.skip : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 True.intro post state ↔ post ⟨Solidity.Yul.RawFrame.capture state (Solidity.Yul.RawFrame.view state),.normal⟩ := by
  intro ctx control mode post state
  exact holds_completed ctx control mode .skip True.intro post state 1 _
    (skip_run ctx control state)

/-- Both raw modalities ignore pre-capture of the same authoritative word view,
while retaining arbitrary whole-outcome postconditions. -/
theorem holds_snapshot : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control) (mode : Solidity.Modality)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code)
 (post : Solidity.Yul.RawFrame.Outcome ctx control → Prop)
 (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawFrame.Logic.holds mode code policy post
 (Solidity.Yul.RawFrame.capture state (Solidity.Yul.RawFrame.view state)) ↔
 Solidity.Yul.RawFrame.Logic.holds mode code policy post state := by
  intro ctx control mode code policy post state
  cases mode <;> simp only [holds, RawFrame.run_snapshot]

/-- Explicit agreement of all retained frame components transports arbitrary
whole-outcome posts across either raw modality. -/
theorem holds_agrees : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control) (mode : Solidity.Modality)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code)
 (post : Solidity.Yul.RawFrame.Outcome ctx control → Prop)
 (first second : Solidity.Yul.RawFrame.State ctx),
 first.clean = second.clean → first.world = second.world →
 Solidity.Yul.RawFrame.view first = Solidity.Yul.RawFrame.view second →
 (Solidity.Yul.RawFrame.Logic.holds mode code policy post first ↔
 Solidity.Yul.RawFrame.Logic.holds mode code policy post second) := by
  intro ctx control mode code policy post first second cleanEq worldEq viewEq
  have same : ∀ fuel, RawFrame.run code policy fuel first = RawFrame.run code policy fuel second :=
    fun fuel => RawFrame.run_agrees ctx control code policy fuel first second cleanEq worldEq viewEq
  cases mode <;> simp only [holds, same]

/-- Every completed outcome has full snapshot metadata; this box does not assert completion. -/
theorem box_captured : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code)
 (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawFrame.Logic.holds .box code policy
 (fun result => Solidity.Yul.RawFrame.capture result.state
 (Solidity.Yul.RawFrame.view result.state) = result.state) state := by
  intro ctx control code policy state fuel result done
  exact RawFrame.run_captured ctx control code policy fuel state result done

/-- A sparse alleged target is excluded from every completed result.
This box allows actual completion at other, fully captured outcomes. -/
theorem box_not_sparse : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code)
 (state : Solidity.Yul.RawFrame.State ctx) (target : Solidity.Yul.RawFrame.Outcome ctx control)
 (cell : Solidity.Yul.WordCell (Solidity.Yul.localExternalTypes ctx)),
 target.state.raw cell = none →
 Solidity.Yul.RawFrame.Logic.holds .box code policy (fun result => result ≠ target) state := by
  intro ctx control code policy state target cell missing fuel result done equal
  cases equal
  exact RawFrame.run_not_sparse ctx control code policy fuel state target cell missing done

/-- A postcondition may be replaced when it agrees on every actual completed
whole outcome. Agreement on unreachable outcomes is unnecessary; neither side
asserts that the interpreter terminates. -/
theorem holds_congr_on_completed :
 ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control) (mode : Solidity.Modality)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code)
 (first second : Solidity.Yul.RawFrame.Outcome ctx control → Prop)
 (state : Solidity.Yul.RawFrame.State ctx),
 (∀ fuel result, Solidity.Yul.RawFrame.run code policy fuel state = some result →
   (first result ↔ second result)) →
 (Solidity.Yul.RawFrame.Logic.holds mode code policy first state ↔
  Solidity.Yul.RawFrame.Logic.holds mode code policy second state) := by
  intros ctx control mode code policy first second state agree
  cases mode with
  | box =>
    constructor
    · intro valid fuel result done
      exact (agree fuel result done).mp (valid fuel result done)
    · intro valid fuel result done
      exact (agree fuel result done).mpr (valid fuel result done)
  | diamond =>
    constructor
    · rintro ⟨fuel,result,done,valid⟩
      exact ⟨fuel,result,done,(agree fuel result done).mp valid⟩
    · rintro ⟨fuel,result,done,valid⟩
      exact ⟨fuel,result,done,(agree fuel result done).mpr valid⟩

/-- The published dirty-readback boundary agrees across pipelines on the full
optional locals/world result. Refusals remain refusals, untouched unsupported
locals retain the existing backup fallback, and raw words are not rewritten.
This is an observation law, not Source execution integration. -/
theorem frame_readback_pipelines :
 ∀ (ctx : Solidity.Source.Ctx) (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.DirtyReadback.frame .legacy state =
 Solidity.Yul.DirtyReadback.frame .viaIR state := by
  intro ctx state
  exact congrArg (fun result => result.map (fun locals => (locals, state.world)))
    (Solidity.Yul.DirtyReadback.readbackFrom_pipelines ctx.env ctx.tys state.clean
      (Solidity.Yul.RawFrame.materialize state).1)

/-- Every raw-frame modality observing the published optional readback has
the same meaning in both pipelines. This retains actual completions, whole
locals/world observations and refused readbacks without claiming Source execution. -/
theorem holds_readback_pipelines :
 ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control) (mode : Solidity.Modality)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code)
 (post : Option (Solidity.Source.Locals ctx.env.layout ctx.tys × Solidity.Source.St ctx.env) → Prop)
 (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawFrame.Logic.holds mode code policy
   (fun result => post (Solidity.Yul.DirtyReadback.frame .legacy result.state)) state ↔
 Solidity.Yul.RawFrame.Logic.holds mode code policy
   (fun result => post (Solidity.Yul.DirtyReadback.frame .viaIR result.state)) state := by
  intros ctx control mode code policy post state
  simp only [Solidity.Yul.RawFrame.Logic.frame_readback_pipelines]

end Solidity.Yul.RawFrame.Logic
