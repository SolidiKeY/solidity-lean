import Solidity.Yul.RawFrame
import Solidity.Yul.LocalOperations

/-! Explicit H11 LOCAL boundaries. These APIs model canonical bool/uint8
return-value reads, not all ordinary Solidity operations. Both pinned pipelines
use the same canonical return projection; unchecked uint8 addition separately
retains the existing H3 pipeline difference. No assembly write invokes them.
Compiler agreement is finite evidence, not asserted as a universal theorem. -/
namespace Solidity.Yul.RawFrame
abbrev Pipeline := LocalOperations.Pipeline

def boolWord {ctx} (state : State ctx) (index : Solidity.Source.Idx ctx.tys .bool) : Word :=
  LocalOperations.scalarWord ((materialize state).1.get index) (LocalOperations.boolShape ctx.env)

def u8Word {ctx} (state : State ctx)
    (index : Solidity.Source.Idx ctx.tys (.int Solidity.Source.IntTy.u8)) : Word :=
  LocalOperations.scalarWord ((materialize state).1.get index) (LocalOperations.u8Shape ctx.env)

def returnBool {ctx} (pipeline : Pipeline) (state : State ctx)
    (index : Solidity.Source.Idx ctx.tys .bool) : Solidity.Source.Val ctx.env.layout .bool :=
  match pipeline with
  | .legacy => LocalOperations.boolInput ((materialize state).1.get index)
  | .viaIR => LocalOperations.boolInput ((materialize state).1.get index)

def returnU8 {ctx} (pipeline : Pipeline) (state : State ctx)
    (index : Solidity.Source.Idx ctx.tys (.int Solidity.Source.IntTy.u8)) :
    Solidity.Source.Val ctx.env.layout (.int Solidity.Source.IntTy.u8) :=
  match pipeline with
  | .legacy => LocalOperations.u8Input ((materialize state).1.get index)
  | .viaIR => LocalOperations.u8Input ((materialize state).1.get index)

/-- Numeric characterization of the canonical Boolean return projection.
Its soundness equation is definitional; the raw frame retains the original word. -/
def BoolReturnD {ctx} (_pipeline : Pipeline) (state : State ctx)
    (index : Solidity.Source.Idx ctx.tys .bool) (value : Solidity.Source.Val ctx.env.layout .bool) : Prop :=
  value.key = some (if (boolWord state index).val != 0 then 1 else 0)

/-- Numeric characterization of the canonical uint8 return projection.
Its soundness equation is definitional; the raw frame retains the original word. -/
def U8ReturnD {ctx} (_pipeline : Pipeline) (state : State ctx)
    (index : Solidity.Source.Idx ctx.tys (.int Solidity.Source.IntTy.u8))
    (value : Solidity.Source.Val ctx.env.layout (.int Solidity.Source.IntTy.u8)) : Prop :=
  value.key = some (((u8Word state index).val % 256 : Nat) : Int)

theorem returnBool_sound {ctx} (pipeline : Pipeline) (state : State ctx)
    (index : Solidity.Source.Idx ctx.tys .bool) :
    BoolReturnD pipeline state index (returnBool pipeline state index) := by
  cases pipeline <;> rfl

theorem returnU8_sound {ctx} (pipeline : Pipeline) (state : State ctx)
    (index : Solidity.Source.Idx ctx.tys (.int Solidity.Source.IntTy.u8)) :
    U8ReturnD pipeline state index (returnU8 pipeline state index) := by
  cases pipeline <;> rfl

def uncheckedU8Add {ctx} (pipeline : Pipeline) (state : State ctx)
    (left right : Solidity.Source.Idx ctx.tys (.int Solidity.Source.IntTy.u8)) :
    Solidity.Source.R (LocalValue ctx.env (.int Solidity.Source.IntTy.u8)) :=
  LocalOperations.uncheckedU8Add pipeline
    ((materialize state).1.get left) ((materialize state).1.get right)

/-- Materialized scalar reads are determined by the authoritative word view. -/
theorem materialized_scalar_agrees : ∀ (ctx : Solidity.Source.Ctx) (first second : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawFrame.view first = Solidity.Yul.RawFrame.view second →
 ∀ (cell : Solidity.Yul.SourceScalarCell ctx),
 cell.wordRead (Solidity.Yul.RawFrame.materialize first).1 =
 cell.wordRead (Solidity.Yul.RawFrame.materialize second).1 := by
  intro ctx first second same cell
  obtain ⟨ref,selected⟩ := sourceScalarAt_surjective ctx cell
  rw [← selected]
  change localWordCells ctx (materialize first).1 (.scalar ref) =
    localWordCells ctx (materialize second).1 (.scalar ref)
  rw [materialize_view,materialize_view,same]

theorem boolWord_agrees : ∀ (ctx : Solidity.Source.Ctx) (first second : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawFrame.view first = Solidity.Yul.RawFrame.view second →
 ∀ (index : Solidity.Source.Idx ctx.tys .bool),
 Solidity.Yul.RawFrame.boolWord first index = Solidity.Yul.RawFrame.boolWord second index := by
  intro ctx first second same index
  exact materialized_scalar_agrees ctx first second same
    ⟨⟨index⟩,.boolean,LocalOperations.boolShape ctx.env⟩

theorem u8Word_agrees : ∀ (ctx : Solidity.Source.Ctx) (first second : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawFrame.view first = Solidity.Yul.RawFrame.view second →
 ∀ (index : Solidity.Source.Idx ctx.tys (.int Solidity.Source.IntTy.u8)),
 Solidity.Yul.RawFrame.u8Word first index = Solidity.Yul.RawFrame.u8Word second index := by
  intro ctx first second same index
  exact materialized_scalar_agrees ctx first second same
    ⟨⟨index⟩,.unsigned 0,LocalOperations.u8Shape ctx.env⟩

/-- Existing canonical return operations ignore raw-overlay and clean-backup representation. -/
theorem returnBool_agrees : ∀ (ctx : Solidity.Source.Ctx) (pipeline : Solidity.Roadmap.Pipeline)
 (first second : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawFrame.view first = Solidity.Yul.RawFrame.view second →
 ∀ (index : Solidity.Source.Idx ctx.tys .bool),
 Solidity.Yul.RawFrame.returnBool pipeline first index = Solidity.Yul.RawFrame.returnBool pipeline second index := by
  intro ctx pipeline first second same index
  have words := boolWord_agrees ctx first second same index
  cases pipeline <;>
    change (Solidity.Source.Val.bool ((boolWord first index).val != 0) :
      Solidity.Source.Val ctx.env.layout .bool) =
      Solidity.Source.Val.bool ((boolWord second index).val != 0)
  all_goals rw [words]

theorem returnU8_agrees : ∀ (ctx : Solidity.Source.Ctx) (pipeline : Solidity.Roadmap.Pipeline)
 (first second : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawFrame.view first = Solidity.Yul.RawFrame.view second →
 ∀ (index : Solidity.Source.Idx ctx.tys (.int Solidity.Source.IntTy.u8)),
 Solidity.Yul.RawFrame.returnU8 pipeline first index = Solidity.Yul.RawFrame.returnU8 pipeline second index := by
  intro ctx pipeline first second same index
  have words := u8Word_agrees ctx first second same index
  cases pipeline <;>
    change Solidity.Source.Val.int (D := ctx.env.layout)
      (((u8Word first index).val % 256 : Nat) : Int) _ = _
  all_goals
    congr 1
    exact congrArg (fun raw : Word => ((raw.val % 256 : Nat) : Int)) words


/-- Canonical return observation after admitted Yul execution depends only on its input word view.
The Option retains the execution's fuel exhaustion; this is not a Source return statement. -/
theorem run_returnBool_agrees : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code) (fuel : Nat)
 (pipeline : Solidity.Roadmap.Pipeline) (first second : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawFrame.view first = Solidity.Yul.RawFrame.view second →
 ∀ (index : Solidity.Source.Idx ctx.tys .bool),
 (Solidity.Yul.RawFrame.run code policy fuel first).map (fun result => Solidity.Yul.RawFrame.returnBool pipeline result.state index) =
 (Solidity.Yul.RawFrame.run code policy fuel second).map (fun result => Solidity.Yul.RawFrame.returnBool pipeline result.state index) := by
  intro ctx control code policy fuel pipeline first second same index
  unfold run
  rw [same]
  cases executed : WordAdapter.run code policy fuel ⟨Fin.elim0, view second⟩ with
  | none => rfl
  | some result =>
    change some (returnBool pipeline (capture first result.state.cells) index) =
      some (returnBool pipeline (capture second result.state.cells) index)
    exact congrArg some (returnBool_agrees ctx pipeline (capture first result.state.cells)
      (capture second result.state.cells) rfl index)

/-- Canonical return observation after admitted Yul execution depends only on its input word view.
The Option retains the execution's fuel exhaustion; this is not a Source return statement. -/
theorem run_returnU8_agrees : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code) (fuel : Nat)
 (pipeline : Solidity.Roadmap.Pipeline) (first second : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawFrame.view first = Solidity.Yul.RawFrame.view second →
 ∀ (index : Solidity.Source.Idx ctx.tys (.int Solidity.Source.IntTy.u8)),
 (Solidity.Yul.RawFrame.run code policy fuel first).map (fun result => Solidity.Yul.RawFrame.returnU8 pipeline result.state index) =
 (Solidity.Yul.RawFrame.run code policy fuel second).map (fun result => Solidity.Yul.RawFrame.returnU8 pipeline result.state index) := by
  intro ctx control code policy fuel pipeline first second same index
  unfold run
  rw [same]
  cases executed : WordAdapter.run code policy fuel ⟨Fin.elim0, view second⟩ with
  | none => rfl
  | some result =>
    change some (returnU8 pipeline (capture first result.state.cells) index) =
      some (returnU8 pipeline (capture second result.state.cells) index)
    exact congrArg some (returnU8_agrees ctx pipeline (capture first result.state.cells)
      (capture second result.state.cells) rfl index)

/-- The canonical Boolean return relation determines the entire intrinsic value. -/
theorem returnBool_complete : ∀ (ctx : Solidity.Source.Ctx) (pipeline : Solidity.Roadmap.Pipeline)
 (state : Solidity.Yul.RawFrame.State ctx)
 (index : Solidity.Source.Idx ctx.tys .bool)
 (value : Solidity.Source.Val ctx.env.layout .bool),
 Solidity.Yul.RawFrame.BoolReturnD pipeline state index value ↔
 value = Solidity.Yul.RawFrame.returnBool pipeline state index := by
  intro ctx pipeline state index value
  constructor
  · intro relation
    cases value with
    | bool b =>
      change some (if b then 1 else 0) = some (if (boolWord state index).val != 0 then 1 else 0) at relation
      have numeric := Option.some.inj relation
      cases pipeline <;>
        change Solidity.Source.Val.bool b =
          Solidity.Source.Val.bool ((boolWord state index).val != 0)
      all_goals
        cases b <;> cases truth : ((boolWord state index).val != 0) <;>
          simp only [truth, Bool.false_eq_true, if_false, if_true] at numeric ⊢
        all_goals contradiction
    | memRef h _ => cases h
    | storRef h _ => cases h
    | cdRef h _ _ => cases h
  · intro same
    rw [same]
    exact returnBool_sound pipeline state index

/-- The canonical uint8 return relation determines the entire intrinsic value. -/
theorem returnU8_complete : ∀ (ctx : Solidity.Source.Ctx) (pipeline : Solidity.Roadmap.Pipeline)
 (state : Solidity.Yul.RawFrame.State ctx)
 (index : Solidity.Source.Idx ctx.tys (.int Solidity.Source.IntTy.u8))
 (value : Solidity.Source.Val ctx.env.layout (.int Solidity.Source.IntTy.u8)),
 Solidity.Yul.RawFrame.U8ReturnD pipeline state index value ↔
 value = Solidity.Yul.RawFrame.returnU8 pipeline state index := by
  intro ctx pipeline state index value
  constructor
  · intro relation
    cases value with
    | int n range =>
      change some n = some (((u8Word state index).val % 256 : Nat) : Int) at relation
      have numeric := Option.some.inj relation
      cases pipeline <;>
        change Solidity.Source.Val.int n range =
          Solidity.Source.Val.int (((u8Word state index).val % 256 : Nat) : Int) _
      all_goals cases numeric; rfl
    | memRef h _ => cases h
    | storRef h _ => cases h
    | cdRef h _ _ => cases h
  · intro same
    rw [same]
    exact returnU8_sound pipeline state index

/-- Canonical readback preserves the intrinsic clean local under explicit authoritative-view agreement. -/
theorem returnBool_clean_view : ∀ (ctx : Solidity.Source.Ctx) (pipeline : Solidity.Roadmap.Pipeline)
 (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawFrame.view state =
 Solidity.Yul.localWordCells ctx (Solidity.Yul.LocalValues.ofClean state.clean) →

 ∀ (index : Solidity.Source.Idx ctx.tys .bool),
 Solidity.Yul.RawFrame.returnBool pipeline state index = state.clean.get index := by
  intro ctx pipeline state same index
  let cell : SourceScalarCell ctx := ⟨⟨index⟩,.boolean,LocalOperations.boolShape ctx.env⟩
  obtain ⟨ref,selected⟩ := sourceScalarAt_surjective ctx cell
  have words : cell.wordRead (materialize state).1 =
      cell.wordRead (LocalValues.ofClean state.clean) := by
    rw [← selected]
    change localWordCells ctx (materialize state).1 (.scalar ref) =
      localWordCells ctx (LocalValues.ofClean state.clean) (.scalar ref)
    rw [materialize_view,same]
  change LocalOperations.scalarWord ((materialize state).1.get index) (LocalOperations.boolShape ctx.env) =
    LocalOperations.scalarWord ((LocalValues.ofClean state.clean).get index) (LocalOperations.boolShape ctx.env) at words
  rw [LocalValues.get_ofClean] at words
  cases pipeline <;>
    change LocalOperations.boolInput ((materialize state).1.get index) = state.clean.get index
  all_goals
    unfold LocalOperations.boolInput
    rw [words]
    cases actual : state.clean.get index with
    | bool b => cases b <;> rfl
    | memRef h _ => cases h
    | storRef h _ => cases h
    | cdRef h _ _ => cases h

/-- Canonical readback preserves the intrinsic clean local under explicit authoritative-view agreement. -/
theorem returnU8_clean_view : ∀ (ctx : Solidity.Source.Ctx) (pipeline : Solidity.Roadmap.Pipeline)
 (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawFrame.view state =
 Solidity.Yul.localWordCells ctx (Solidity.Yul.LocalValues.ofClean state.clean) →

 ∀ (index : Solidity.Source.Idx ctx.tys (.int Solidity.Source.IntTy.u8)),
 Solidity.Yul.RawFrame.returnU8 pipeline state index = state.clean.get index := by
  intro ctx pipeline state same index
  let cell : SourceScalarCell ctx := ⟨⟨index⟩,.unsigned 0,LocalOperations.u8Shape ctx.env⟩
  obtain ⟨ref,selected⟩ := sourceScalarAt_surjective ctx cell
  have words : cell.wordRead (materialize state).1 =
      cell.wordRead (LocalValues.ofClean state.clean) := by
    rw [← selected]
    change localWordCells ctx (materialize state).1 (.scalar ref) =
      localWordCells ctx (LocalValues.ofClean state.clean) (.scalar ref)
    rw [materialize_view,same]
  change LocalOperations.scalarWord ((materialize state).1.get index) (LocalOperations.u8Shape ctx.env) =
    LocalOperations.scalarWord ((LocalValues.ofClean state.clean).get index) (LocalOperations.u8Shape ctx.env) at words
  rw [LocalValues.get_ofClean] at words
  cases pipeline <;>
    change LocalOperations.u8Input ((materialize state).1.get index) = state.clean.get index
  all_goals
    have inputs : LocalOperations.u8Input ((materialize state).1.get index) =
        LocalOperations.u8Input (.clean (state.clean.get index)) := by
      unfold LocalOperations.u8Input
      dsimp only
      congr 1
      exact congrArg (fun raw : Word => ((raw.val % 256 : Nat) : Int)) words
    rw [inputs]
    cases actual : state.clean.get index with
    | int n range => exact LocalOperations.u8Input_clean n range
    | memRef h _ => cases h
    | storRef h _ => cases h
    | cdRef h _ _ => cases h

/-- Unchecked addition depends on authoritative operand words within each fixed pipeline.
This preserves the legacy/viaIR distinction and asserts no compiler adequacy. -/
theorem uncheckedU8Add_agrees : ∀ (ctx : Solidity.Source.Ctx) (pipeline : Solidity.Roadmap.Pipeline)
 (first second : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawFrame.view first = Solidity.Yul.RawFrame.view second →
 ∀ (left right : Solidity.Source.Idx ctx.tys (.int Solidity.Source.IntTy.u8)),
 Solidity.Yul.RawFrame.uncheckedU8Add pipeline first left right =
 Solidity.Yul.RawFrame.uncheckedU8Add pipeline second left right := by
  intro ctx pipeline first second same left right
  cases pipeline with
  | legacy =>
    change (Except.ok (LocalValue.scalar (LocalOperations.u8Shape ctx.env)
      (word ((u8Word first left).val + (u8Word first right).val))) :
      Solidity.Source.R (LocalValue ctx.env (.int Solidity.Source.IntTy.u8))) =
      .ok (.scalar (LocalOperations.u8Shape ctx.env)
        (word ((u8Word second left).val + (u8Word second right).val)))
    rw [u8Word_agrees ctx first second same left,u8Word_agrees ctx first second same right]
  | viaIR =>
    change (Solidity.Source.binVal false .add (returnU8 .viaIR first left)
      (returnU8 .viaIR first right)).map LocalValue.clean =
      (Solidity.Source.binVal false .add (returnU8 .viaIR second left)
        (returnU8 .viaIR second right)).map LocalValue.clean
    rw [returnU8_agrees ctx .viaIR first second same left,
      returnU8_agrees ctx .viaIR first second same right]

/-- Exact unchecked arithmetic locality for arbitrary pairs of intrinsic operand indices.
Only the two read words agree; unrelated words, worlds and clean backups may differ. -/
theorem uncheckedU8Add_word_congr : ∀ (ctx : Solidity.Source.Ctx) (pipeline : Solidity.Roadmap.Pipeline)
 (first second : Solidity.Yul.RawFrame.State ctx)
 (leftFirst rightFirst leftSecond rightSecond : Solidity.Source.Idx ctx.tys (.int Solidity.Source.IntTy.u8)),
 Solidity.Yul.RawFrame.u8Word first leftFirst = Solidity.Yul.RawFrame.u8Word second leftSecond →
 Solidity.Yul.RawFrame.u8Word first rightFirst = Solidity.Yul.RawFrame.u8Word second rightSecond →
 Solidity.Yul.RawFrame.uncheckedU8Add pipeline first leftFirst rightFirst =
 Solidity.Yul.RawFrame.uncheckedU8Add pipeline second leftSecond rightSecond := by
  intro ctx pipeline first second leftFirst rightFirst leftSecond rightSecond leftWords rightWords
  cases pipeline with
  | legacy =>
    change (Except.ok (LocalValue.scalar (LocalOperations.u8Shape ctx.env)
      (word ((u8Word first leftFirst).val + (u8Word first rightFirst).val))) :
      Solidity.Source.R (LocalValue ctx.env (.int Solidity.Source.IntTy.u8))) =
      .ok (.scalar (LocalOperations.u8Shape ctx.env)
        (word ((u8Word second leftSecond).val + (u8Word second rightSecond).val)))
    rw [leftWords,rightWords]
  | viaIR =>
    have cleaned : ∀ one two, u8Word first one = u8Word second two →
        returnU8 .viaIR first one = returnU8 .viaIR second two := by
      intro one two words
      apply (returnU8_complete ctx .viaIR second two (returnU8 .viaIR first one)).mp
      change (returnU8 .viaIR first one).key = some (((u8Word second two).val % 256 : Nat) : Int)
      rw [← words]
      exact returnU8_sound .viaIR first one
    change (Solidity.Source.binVal false .add (returnU8 .viaIR first leftFirst)
      (returnU8 .viaIR first rightFirst)).map LocalValue.clean =
      (Solidity.Source.binVal false .add (returnU8 .viaIR second leftSecond)
        (returnU8 .viaIR second rightSecond)).map LocalValue.clean
    rw [cleaned leftFirst leftSecond leftWords,cleaned rightFirst rightSecond rightWords]

end Solidity.Yul.RawFrame
