import Solidity.Yul.DirectUpdates
import Solidity.Yul.Checks.ClosedRun
import Solidity.Yul.RawFrameLogic
import Solidity.Yul.RawCoherent
import Solidity.Yul.RawHorizon
import Solidity.Yul.RawBoundary
import Solidity.Yul.LocalBlock
import Solidity.Yul.Checks.LocalWordView
import Solidity.Source.Semantics
/-! Kernel controls for local-block raw words and scope boundaries.
The selected-local Source readback regression is guarded here: a dirty unsupported
neighbor must not block a supported read, cleanup must not rewrite raw bits,
and fuel exhaustion remains distinct from readback refusal. The empty-program
Source fixture below executes local reads only, not crypto or call agreement.
Snapshot capture must preserve the complete Source observation while retaining
the distinction between sparse and fully populated overlay metadata.
Generic integer laws below guard cleanup idempotence and preservation under
changes above the declared integer width; bool cleanup remains nonzero testing.
Integer and Boolean ABI-word cleanup must roundtrip complete intrinsic values. -/
namespace Solidity.Yul.Checks.LocalBlock
open Solidity.Source
def env : Solidity.Source.Env := ⟨[]⟩
def functionTy := LocalWordView.functionTy
def ctx : Solidity.Source.Ctx :=
  {env:=env,scope:=none,locals:=[("flag",.bool),("ptr1",functionTy),
    ("small",.int IntTy.u8),("ptr2",functionTy),("byte",.fixedBytes 1 (by decide))]}
abbrev X := localExternalTypes ctx
def locals : Solidity.Source.Locals env.layout ctx.tys :=
  .cons (.bool true) (.cons LocalWordView.functionValue
    (.cons CleanLocals.small (.cons (.externalFn ⟨22136,by decide⟩ [1,2,3,4] rfl)
      (.cons CleanLocals.byteValue .nil))))
def initial : LocalState env ctx.tys :=
  (LocalValues.ofClean locals,Solidity.Source.St.init env)
def flag : WordCell X := .scalar ⟨.boolean,.here⟩
def first : Member X .externalFunction := .there .here
def second : Member X .externalFunction := .there (.there (.there .here))
def small : WordCell X := .scalar ⟨.unsigned 0,.there (.there .here)⟩
def byte : WordCell X := .scalar ⟨.fixedBytes 0,.there (.there (.there (.there .here)))⟩
def addr1 : WordCell X := .address first
def sel2 : WordCell X := .selector second

def assign (cell : WordCell X) (value : Expr [] X 0 1) :
    Stmt [] X ⟨false,false⟩ 0 :=
  .assign (Fin.cases (.external cell.writeRef) Fin.elim0) value
def maxExpr : Expr [] X 0 1 := .builtin (.pure .not) (Fin.cases (.literal (word 0)) Fin.elim0)
def addExpr : Expr [] X 0 1 := .builtin (.pure .add)
  (Fin.cases (.external small.readRef) (Fin.cases (.literal (word 256)) Fin.elim0))
def code : Stmt [] X ⟨false,false⟩ 0 :=
  .seq (assign flag (.literal (word 2)))
    (.seq (assign addr1 maxExpr) (.seq (assign sel2 maxExpr) (assign small addExpr)))
def policy : Policy.StmtP .A code := (Policy.stmt_iff .A code).mp rfl

example : wordCellCount X = 7 := rfl
example : (sourceFunctionAt ctx first).position ≠ (sourceFunctionAt ctx second).position :=
  sourceFunctionAt_different ctx first second (by intro same; cases same)
example (raw : Word) :
    localWordCells ctx (writeLocalWord ctx initial.1 raw addr1) (.address second) =
      localWordCells ctx initial.1 (.address second) :=
  localWordCells_write_other ctx initial.1 addr1 (.address second) raw (by intro same; cases same)
example (raw : Word) :
    localWordCells ctx (writeLocalWord ctx initial.1 raw flag) (.selector first) =
      localWordCells ctx initial.1 (.selector first) :=
  localWordCells_write_other ctx initial.1 flag (.selector first) raw (by intro same; cases same)
example (values : WordCells X) :
    localWordCells ctx (writebackLocalWords ctx initial.1 values) = values :=
  writebackLocalWords_view ctx initial.1 values
example (fuel : Nat) :
    (runLocalBlock ctx code policy fuel initial).map LocalBlockOutcome.project =
      WordAdapter.run code policy fuel ⟨Fin.elim0,localWordCells ctx initial.1⟩ :=
  runLocalBlock_projection ctx code policy fuel initial

def snapshot (state : LocalState env ctx.tys) : List Nat :=
  (List.finRange (wordCellCount X)).map (fun i => (localWordCells ctx state.1 (wordCellAt X i)).val)

/-- info: LOCAL_BLOCK_COMPILED_PASS: dirty bool/u8/two Fn fields; seven-cell writeback and completed horizons -/
#guard_msgs in
#eval do
  let expected := [2,2^256-1,2309737967,257,22136,2^256-1,171*2^248]
  let some result := runLocalBlock ctx code policy 32 initial |
    throw (IO.userError "actual Source local block exhausted horizon32")
  unless snapshot result.state == expected && result.flow.isNormal do
    throw (IO.userError "actual Source local block dirty-word result mismatch")
  for fuel in [0,1,2,4,8,16,32] do
    match runLocalBlock ctx code policy fuel initial with
    | none => pure ()
    | some earlier =>
        unless snapshot earlier.state == expected && earlier.flow.isNormal do
          throw (IO.userError "actual Source completed horizon changed")
  let restored := writebackLocalWords ctx initial.1
    (fun cell => word (cell.slot.val+100))
  unless (List.finRange (wordCellCount X)).map
      (fun i => (localWordCells ctx restored (wordCellAt X i)).val) ==
        [100,101,102,103,104,105,106] do
    throw (IO.userError "actual full Source local writeback mismatch")
  IO.println "LOCAL_BLOCK_COMPILED_PASS: dirty bool/u8/two Fn fields; seven-cell writeback and completed horizons"

theorem code_completes : (runLocalBlock ctx code policy 32 initial).isSome = true := by decide
def completedWitness : Nonempty (LocalBlockOutcome ctx ⟨false,false⟩) :=
  ⟨(runLocalBlock ctx code policy 32 initial).get code_completes⟩

def memoryRef : SourceLocalRef LocalWordView.ctx := ⟨.there .here⟩
def memoryShape : DeclaredSourceTypeD LocalWordView.ctx.env memoryRef.ty .memory :=
  .basic (.reference .bytesMemory)
example (values : WordCells (localExternalTypes LocalWordView.ctx)) :
    (writebackLocalWords LocalWordView.ctx LocalWordView.extended values).get memoryRef.index =
      LocalWordView.extended.get memoryRef.index :=
  writebackLocalWords_zero LocalWordView.ctx LocalWordView.extended values memoryRef memoryShape rfl

def retagged := writebackLocalWords ctx initial.1 (localWordCells ctx initial.1)
example : localWordCells ctx retagged = localWordCells ctx initial.1 :=
  writebackLocalWords_view ctx initial.1 (localWordCells ctx initial.1)
example : ((initial.1.get .here).clean?).isSome = true := rfl
example : ((retagged.get .here).clean?).isNone = true := by decide

def completed := (runLocalBlock ctx code policy 32 initial).get code_completes
example : snapshot completed.state =
    [2,2^256-1,2309737967,257,22136,2^256-1,171*2^248] := by decide

def cellWitness : Nonempty (SourceFunctionCell ctx) := ⟨sourceFunctionAt ctx second⟩
def stateWitness : Nonempty (LocalState env ctx.tys) := ⟨initial⟩
#check @localWordCells_write
#check @writebackLocalWords_view
#check @writebackLocalWords_zero
#check @runLocalBlock_projection
#check @runLocalBlock_world
#check @runLocalBlock_stable
#print axioms localWordCells_write
#print axioms writebackLocalWords_view
#print axioms runLocalBlock_projection

/- Completed assembly retains dirty words; canonical return observers alone clean them.
These controls execute the existing intrinsically typed code and policy. -/
def rawInitial : RawFrame.State ctx := RawFrame.ofClean locals initial.2
def rawRun (fuel : Nat) := RawFrame.run code policy fuel rawInitial

#guard (rawRun 0).isNone
#guard (rawRun 32).isSome
#guard (rawRun 64).isSome
#guard (rawRun 32).map (fun result => (RawFrame.view result.state flag).val) = some 2
#guard (rawRun 32).map (fun result => (RawFrame.view result.state small).val) = some 257
#guard (rawRun 32).map (fun result => (RawFrame.returnBool (ctx := ctx) .legacy result.state (.here)).key) = some (some 1)
#guard (rawRun 32).map (fun result => (RawFrame.returnU8 (ctx := ctx) .legacy result.state (.there (.there .here))).key) = some (some 1)
#guard (rawRun 32).map (fun result => (RawFrame.returnBool (ctx := ctx) .viaIR result.state (.here)).key) = some (some 1)
#guard (rawRun 32).map (fun result => (RawFrame.returnU8 (ctx := ctx) .viaIR result.state (.there (.there .here))).key) = some (some 1)

/-- info: 'Solidity.Yul.RawFrame.run_returnBool_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.run_returnBool_agrees
/-- info: 'Solidity.Yul.RawFrame.run_returnU8_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.run_returnU8_agrees


/- Completed-horizon countercontrols observe all seven words and normal flow. -/
def rawSnapshot (result : RawFrame.Outcome ctx ⟨false,false⟩) : List Nat :=
  (List.finRange (wordCellCount X)).map (fun i => (RawFrame.view result.state (wordCellAt X i)).val)

#guard (rawRun 32).map rawSnapshot = (rawRun 64).map rawSnapshot
#guard (rawRun 64).map rawSnapshot =
  some [2,2^256-1,2309737967,257,22136,2^256-1,171*2^248]
#guard (rawRun 32).map (fun result => result.flow.isNormal) = some true
#guard (rawRun 64).map (fun result => result.flow.isNormal) = some true
/-- info: 'Solidity.Yul.RawFrame.run_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.run_stable
/-- info: 'Solidity.Yul.RawFrame.run_completed_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.run_completed_unique


/- Compare both concrete interpreters, including a failed finite horizon. -/
def wordRun (fuel : Nat) :=
  WordAdapter.run code policy fuel ⟨Fin.elim0, RawFrame.view rawInitial⟩
#guard (wordRun 0).isNone
#guard (wordRun 32).isSome
#guard (wordRun 32).map (fun result =>
  (List.finRange (wordCellCount X)).map (fun i => (result.state.cells (wordCellAt X i)).val)) =
  (rawRun 32).map rawSnapshot
#guard (wordRun 32).map (fun result => result.flow.isNormal) =
  (rawRun 32).map (fun result => result.flow.isNormal)
/-- info: 'Solidity.Yul.RawFrame.run_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.run_some_iff
/-- info: 'Solidity.Yul.RawFrame.run_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.run_none_iff


/- Actual S03 firstDone observes the same completed dirty frame. -/
def selectedRaw (bound : Nat) := Solidity.Source.firstDone
  (fun fuel => Closed.sourceResult (rawRun fuel)) bound
def selectedSnapshot (bound : Nat) : Option (List Nat) :=
  (selectedRaw bound).bind (fun chosen =>
    match chosen.2.1 with
    | .ok result => some (rawSnapshot result)
    | .error _ => none)
#guard (selectedRaw 0).isNone
#guard (selectedRaw 32).isSome
#guard selectedSnapshot 32 = (rawRun 32).map rawSnapshot
#guard selectedSnapshot 64 = selectedSnapshot 32
/-- info: 'Solidity.Yul.RawFrame.firstDone_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.firstDone_agrees
/-- info: 'Solidity.Yul.RawFrame.firstDone_none_iff_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.firstDone_none_iff_word


/- Finite selector failure agrees with actual execution at the existing horizons. -/
#guard ([0,1,2,4,8,16,32,64] : List Nat).all (fun fuel =>
  (selectedRaw fuel).isNone == (rawRun fuel).isNone)
#guard (selectedRaw 1).isNone
#guard (rawRun 1).isNone
#guard (selectedRaw 32).map Prod.fst = (selectedRaw 64).map Prod.fst
/-- info: 'Solidity.Yul.RawFrame.firstDone_none_iff_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.firstDone_none_iff_bound


/- The selected actual dirty frame feeds the existing canonical readback API. -/
#guard (selectedRaw 32).any (fun chosen => chosen.1 < 32)
#guard ((selectedRaw 32).bind (fun selected =>
  match selected.2.1 with
  | .ok result => (RawFrame.returnBool (ctx := ctx) .legacy result.state (.here)).key
  | .error _ => none)) = some 1
#guard ((selectedRaw 32).bind (fun selected =>
  match selected.2.1 with
  | .ok result => (RawFrame.returnU8 (ctx := ctx) .legacy result.state (.there (.there .here))).key
  | .error _ => none)) = some 1
#guard ((selectedRaw 32).bind (fun selected =>
  match selected.2.1 with
  | .ok result => (RawFrame.returnBool (ctx := ctx) .viaIR result.state (.here)).key
  | .error _ => none)) = some 1
#guard ((selectedRaw 32).bind (fun selected =>
  match selected.2.1 with
  | .ok result => (RawFrame.returnU8 (ctx := ctx) .viaIR result.state (.there (.there .here))).key
  | .error _ => none)) = some 1

/-- info: 'Solidity.Yul.RawFrame.run_some_iff_firstDone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.run_some_iff_firstDone


/- Nonvacuous least-horizon controls inspect every strict preceding raw run. -/
#guard (selectedRaw 32).any (fun selected =>
  (rawRun selected.1).isSome &&
    (List.range selected.1).all (fun fuel => (rawRun fuel).isNone))
#guard (selectedRaw 64).any (fun selected =>
  (rawRun selected.1).isSome &&
    (List.range selected.1).all (fun fuel => (rawRun fuel).isNone))
#guard (selectedRaw 32).any (fun selected => selected.1 > 0)
/-- info: 'Solidity.Yul.RawFrame.firstDone_minimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.firstDone_minimal


/- Independent return relations accept exactly the canonical intrinsic candidates.
Local decision instances permit numeric checks without changing the core APIs. -/
local instance (pipeline : RawFrame.Pipeline) (state : RawFrame.State ctx)
    (index : Solidity.Source.Idx ctx.tys .bool) (value : Solidity.Source.Val ctx.env.layout .bool) :
    Decidable (RawFrame.BoolReturnD pipeline state index value) :=
  inferInstanceAs (Decidable (value.key = some
    (if (RawFrame.boolWord state index).val != 0 then 1 else 0)))
local instance (pipeline : RawFrame.Pipeline) (state : RawFrame.State ctx)
    (index : Solidity.Source.Idx ctx.tys (.int IntTy.u8))
    (value : Solidity.Source.Val ctx.env.layout (.int IntTy.u8)) :
    Decidable (RawFrame.U8ReturnD pipeline state index value) :=
  inferInstanceAs (Decidable (value.key = some
    (((RawFrame.u8Word state index).val % 256 : Nat) : Int)))
#guard (rawRun 32).any (fun result => decide (RawFrame.BoolReturnD (ctx := ctx) .legacy result.state (.here) (.bool true)))
#guard (rawRun 32).any (fun result => decide (¬ (RawFrame.BoolReturnD (ctx := ctx) .legacy result.state (.here) (.bool false))))
#guard (rawRun 32).any (fun result => decide (RawFrame.U8ReturnD (ctx := ctx) .legacy result.state (.there (.there .here)) (CleanLocals.small)))
#guard (rawRun 32).any (fun result => decide (¬ (RawFrame.U8ReturnD (ctx := ctx) .legacy result.state (.there (.there .here)) (.int 0 (by decide)))))
#guard (rawRun 32).any (fun result => decide (RawFrame.BoolReturnD (ctx := ctx) .viaIR result.state (.here) (.bool true)))
#guard (rawRun 32).any (fun result => decide (¬ (RawFrame.BoolReturnD (ctx := ctx) .viaIR result.state (.here) (.bool false))))
#guard (rawRun 32).any (fun result => decide (RawFrame.U8ReturnD (ctx := ctx) .viaIR result.state (.there (.there .here)) (CleanLocals.small)))
#guard (rawRun 32).any (fun result => decide (¬ (RawFrame.U8ReturnD (ctx := ctx) .viaIR result.state (.there (.there .here)) (.int 0 (by decide)))))
/-- info: 'Solidity.Yul.RawFrame.returnBool_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.returnBool_complete
/-- info: 'Solidity.Yul.RawFrame.returnU8_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.returnU8_complete


/- Clean boundary identity is conditional; raw writes with a different value violate its premise. -/
def dirtyFalse := RawFrame.write rawInitial flag (word 0)
def dirtyTwo := RawFrame.write rawInitial small (word 258)
#guard RawCoherent.coherent rawInitial
#guard !RawCoherent.coherent dirtyFalse
#guard !RawCoherent.coherent dirtyTwo
#guard (RawFrame.returnBool (ctx := ctx) .legacy rawInitial (.here)).key = (locals.get (.here)).key
#guard (RawFrame.returnU8 (ctx := ctx) .legacy rawInitial (.there (.there .here))).key = (locals.get (.there (.there .here))).key
#guard (RawFrame.returnBool (ctx := ctx) .legacy dirtyFalse .here).key = some 0
#guard (RawFrame.returnU8 (ctx := ctx) .legacy dirtyTwo (.there (.there .here))).key = some 2
#guard (RawFrame.returnBool (ctx := ctx) .viaIR rawInitial (.here)).key = (locals.get (.here)).key
#guard (RawFrame.returnU8 (ctx := ctx) .viaIR rawInitial (.there (.there .here))).key = (locals.get (.there (.there .here))).key
#guard (RawFrame.returnBool (ctx := ctx) .viaIR dirtyFalse .here).key = some 0
#guard (RawFrame.returnU8 (ctx := ctx) .viaIR dirtyTwo (.there (.there .here))).key = some 2
/-- info: 'Solidity.Yul.RawFrame.returnBool_clean_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.returnBool_clean_view
/-- info: 'Solidity.Yul.RawFrame.returnU8_clean_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.returnU8_clean_view


/- Inhabited modal controls for actual dirty LOCAL execution. -/
theorem logicCompletes : (rawRun 32).isSome = true := by rfl
def logicResult : RawFrame.Outcome ctx ⟨false,false⟩ := (rawRun 32).get logicCompletes
def logicPost (result : RawFrame.Outcome ctx ⟨false,false⟩) : Prop :=
  RawFrame.view result.state flag = word 2 ∧
  RawFrame.view result.state small = word 257 ∧ result.flow.isNormal = true


theorem logicFinished : rawRun 32 = some logicResult := by rfl
theorem logicValid : logicPost logicResult := ⟨rfl,rfl,rfl⟩
theorem logicBox : RawFrame.Logic.holds .box code policy logicPost rawInitial := by
  intro fuel result done
  have same := RawFrame.run_completed_unique ctx ⟨false,false⟩ code policy rawInitial
    fuel 32 result logicResult done logicFinished
  rw [same]
  exact logicValid
theorem logicDiamond : RawFrame.Logic.holds .diamond code policy logicPost rawInitial :=
  ⟨32,logicResult,logicFinished,logicValid⟩
theorem logicFalseBox : ¬ RawFrame.Logic.holds .box code policy (fun _ => False) rawInitial := by
  intro invalid
  exact invalid 32 logicResult logicFinished
theorem logicFalseDiamond : ¬ RawFrame.Logic.holds .diamond code policy (fun _ => False) rawInitial := by
  rintro ⟨_,_,_,bad⟩
  exact bad


theorem logicPremiseWitness : ∀ mode : Solidity.Modality,
 ∃ premise : Solidity.Yul.Logic.Fml (0 + Solidity.Yul.wordCellCount Solidity.Yul.Checks.LocalBlock.X),
 Nonempty (Solidity.Yul.Logic.Rule
 (Solidity.Yul.RawFrame.Logic.formula mode Solidity.Yul.Checks.LocalBlock.code Solidity.Yul.Checks.LocalBlock.policy Solidity.Yul.Checks.LocalBlock.logicPost Solidity.Yul.Checks.LocalBlock.rawInitial) premise) ∧
 premise.holds (Solidity.Yul.WordState.pack ⟨Fin.elim0,Solidity.Yul.RawFrame.view Solidity.Yul.Checks.LocalBlock.rawInitial⟩) := by
  intro mode
  obtain ⟨premise,⟨rule⟩⟩ := WordAdapter.rule_exists mode code policy
    (fun result => logicPost (RawFrame.Outcome.ofWord rawInitial result))
  refine ⟨premise,⟨rule⟩,?_⟩
  apply (RawFrame.Logic.rule_premise_sound ctx ⟨false,false⟩ mode code policy
    logicPost rawInitial premise rule).mp
  cases mode with
  | box => exact logicBox
  | diamond => exact logicDiamond

/-- info: 'Solidity.Yul.RawFrame.Logic.formula_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.Logic.formula_iff
/-- info: 'Solidity.Yul.RawFrame.Logic.rule_premise_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.Logic.rule_premise_sound
/-- info: 'Solidity.Yul.Checks.LocalBlock.logicCompletes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.logicCompletes
/-- info: 'Solidity.Yul.Checks.LocalBlock.logicFinished' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.logicFinished
/-- info: 'Solidity.Yul.Checks.LocalBlock.logicValid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.logicValid
/-- info: 'Solidity.Yul.Checks.LocalBlock.logicBox' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.logicBox
/-- info: 'Solidity.Yul.Checks.LocalBlock.logicDiamond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.logicDiamond
/-- info: 'Solidity.Yul.Checks.LocalBlock.logicFalseBox' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.logicFalseBox
/-- info: 'Solidity.Yul.Checks.LocalBlock.logicFalseDiamond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.logicFalseDiamond
/-- info: 'Solidity.Yul.Checks.LocalBlock.logicPremiseWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.logicPremiseWitness


/- A genuine recursive function group, not a finite collection of failed horizons. -/
def recursiveCtx : Solidity.Source.Ctx := {env:=env,scope:=none,locals:=[]}
def recursiveCode : Stmt [] (localExternalTypes recursiveCtx) ⟨false,false⟩ 0 :=
  .functions [ClosedRun.divergeSig]
    (.cons (.discard (.call .here Fin.elim0)) .nil)
    (.discard (.call .here Fin.elim0))
def recursivePolicy : Policy.StmtP .A recursiveCode :=
  (Policy.stmt_iff .A recursiveCode).mp rfl
def recursiveInitial : RawFrame.State recursiveCtx :=
  RawFrame.ofClean .nil (Solidity.Source.St.init env)


theorem recursiveNone : ∀ (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.LocalBlock.recursiveCtx),
 Solidity.Yul.RawFrame.run Solidity.Yul.Checks.LocalBlock.recursiveCode Solidity.Yul.Checks.LocalBlock.recursivePolicy fuel state = none := by
  intro fuel state
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      unfold RawFrame.run WordAdapter.run
      change Option.map _ (Option.map _
        ((Closed.evalExpr fuel ClosedRun.divergeEnv ClosedRun.divergeEnvD.profile
          ClosedRun.divergeCall ClosedRun.divergeCallD.profile _).bind _)) = none
      rw [ClosedRun.diverge_all]
      rfl


theorem recursiveFalseBox : RawFrame.Logic.holds .box recursiveCode recursivePolicy
    (fun _ => False) recursiveInitial :=
  (RawFrame.Logic.box_false_iff_none recursiveCtx ⟨false,false⟩
    recursiveCode recursivePolicy recursiveInitial).mpr (fun fuel => recursiveNone fuel recursiveInitial)
theorem recursiveNoDiamond : ¬ RawFrame.Logic.holds .diamond recursiveCode recursivePolicy
    (fun _ => True) recursiveInitial := by
  rintro ⟨fuel,result,done,_⟩
  rw [recursiveNone fuel recursiveInitial] at done
  cases done
theorem recursiveNoSelection : ∀ bound, Solidity.Source.firstDone
    (fun fuel => Closed.sourceResult (RawFrame.run recursiveCode recursivePolicy fuel recursiveInitial))
    bound = none := by
  intro bound
  exact (RawFrame.firstDone_none_iff_bound recursiveCtx ⟨false,false⟩
    recursiveCode recursivePolicy recursiveInitial bound).mpr (recursiveNone bound recursiveInitial)
theorem logicFactored :
    RawFrame.Logic.holds .diamond code policy (fun _ => True) rawInitial ∧
    RawFrame.Logic.holds .box code policy logicPost rawInitial :=
  (RawFrame.Logic.diamond_iff_termination_and_box ctx ⟨false,false⟩
    code policy logicPost rawInitial).mp logicDiamond
theorem finiteTimeoutAndDiamond : RawFrame.run code policy 0 rawInitial = none ∧
    RawFrame.Logic.holds .diamond code policy (fun _ => True) rawInitial :=
  ⟨rfl,logicFactored.1⟩

/-- info: 'Solidity.Yul.RawFrame.Logic.diamond_implies_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.Logic.diamond_implies_box
/-- info: 'Solidity.Yul.RawFrame.Logic.box_false_iff_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.Logic.box_false_iff_none
/-- info: 'Solidity.Yul.RawFrame.Logic.diamond_iff_termination_and_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.Logic.diamond_iff_termination_and_box
/-- info: 'Solidity.Yul.Checks.LocalBlock.recursiveNone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.recursiveNone
/-- info: 'Solidity.Yul.Checks.LocalBlock.recursiveFalseBox' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.recursiveFalseBox
/-- info: 'Solidity.Yul.Checks.LocalBlock.recursiveNoDiamond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.recursiveNoDiamond
/-- info: 'Solidity.Yul.Checks.LocalBlock.recursiveNoSelection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.recursiveNoSelection
/-- info: 'Solidity.Yul.Checks.LocalBlock.logicFactored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.logicFactored
/-- info: 'Solidity.Yul.Checks.LocalBlock.finiteTimeoutAndDiamond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.finiteTimeoutAndDiamond


/- Legal transfers suppress the following actual recursive call. -/
def transferLeaveCode : Stmt [] X ⟨true,false⟩ 0 :=
  .functions [ClosedRun.divergeSig]
    (.cons (.discard (.call .here Fin.elim0)) .nil)
    (.seq .leave (.discard (.call .here Fin.elim0)))
def transferLeavePolicy : Policy.StmtP .A transferLeaveCode :=
  (Policy.stmt_iff .A transferLeaveCode).mp rfl
def transferBreakCode : Stmt [] X ⟨false,true⟩ 0 :=
  .functions [ClosedRun.divergeSig]
    (.cons (.discard (.call .here Fin.elim0)) .nil)
    (.seq .break_ (.discard (.call .here Fin.elim0)))
def transferBreakPolicy : Policy.StmtP .A transferBreakCode :=
  (Policy.stmt_iff .A transferBreakCode).mp rfl
def transferContinueCode : Stmt [] X ⟨false,true⟩ 0 :=
  .functions [ClosedRun.divergeSig]
    (.cons (.discard (.call .here Fin.elim0)) .nil)
    (.seq .continue_ (.discard (.call .here Fin.elim0)))
def transferContinuePolicy : Policy.StmtP .A transferContinueCode :=
  (Policy.stmt_iff .A transferContinueCode).mp rfl


theorem transferLeaveCompletes :
    (RawFrame.run transferLeaveCode transferLeavePolicy 3 logicResult.state).isSome = true := by rfl
def transferLeaveResult :=
  (RawFrame.run transferLeaveCode transferLeavePolicy 3 logicResult.state).get transferLeaveCompletes
theorem transferBreakCompletes :
    (RawFrame.run transferBreakCode transferBreakPolicy 3 logicResult.state).isSome = true := by rfl
def transferBreakResult :=
  (RawFrame.run transferBreakCode transferBreakPolicy 3 logicResult.state).get transferBreakCompletes
theorem transferContinueCompletes :
    (RawFrame.run transferContinueCode transferContinuePolicy 3 logicResult.state).isSome = true := by rfl
def transferContinueResult :=
  (RawFrame.run transferContinueCode transferContinuePolicy 3 logicResult.state).get transferContinueCompletes

def transferTag {control} : Closed.Flow control → Nat
  | .normal => 0
  | .leave_ _ => 1
  | .break_ _ => 2
  | .continue_ _ => 3
def transferPost {control} (tag : Nat) (result : RawFrame.Outcome ctx control) : Prop :=
  RawFrame.view result.state flag = word 2 ∧
  RawFrame.view result.state small = word 257 ∧ transferTag result.flow = tag


theorem transferFinished : Solidity.Yul.RawFrame.run Solidity.Yul.Checks.LocalBlock.transferLeaveCode Solidity.Yul.Checks.LocalBlock.transferLeavePolicy 3 Solidity.Yul.Checks.LocalBlock.logicResult.state = some Solidity.Yul.Checks.LocalBlock.transferLeaveResult ∧
Solidity.Yul.RawFrame.run Solidity.Yul.Checks.LocalBlock.transferBreakCode Solidity.Yul.Checks.LocalBlock.transferBreakPolicy 3 Solidity.Yul.Checks.LocalBlock.logicResult.state = some Solidity.Yul.Checks.LocalBlock.transferBreakResult ∧
Solidity.Yul.RawFrame.run Solidity.Yul.Checks.LocalBlock.transferContinueCode Solidity.Yul.Checks.LocalBlock.transferContinuePolicy 3 Solidity.Yul.Checks.LocalBlock.logicResult.state = some Solidity.Yul.Checks.LocalBlock.transferContinueResult := ⟨rfl,rfl,rfl⟩

theorem transferModal : ∀ mode : Solidity.Modality,
Solidity.Yul.RawFrame.Logic.holds mode Solidity.Yul.Checks.LocalBlock.transferLeaveCode Solidity.Yul.Checks.LocalBlock.transferLeavePolicy (Solidity.Yul.Checks.LocalBlock.transferPost 1) Solidity.Yul.Checks.LocalBlock.logicResult.state ∧
Solidity.Yul.RawFrame.Logic.holds mode Solidity.Yul.Checks.LocalBlock.transferBreakCode Solidity.Yul.Checks.LocalBlock.transferBreakPolicy (Solidity.Yul.Checks.LocalBlock.transferPost 2) Solidity.Yul.Checks.LocalBlock.logicResult.state ∧
Solidity.Yul.RawFrame.Logic.holds mode Solidity.Yul.Checks.LocalBlock.transferContinueCode Solidity.Yul.Checks.LocalBlock.transferContinuePolicy (Solidity.Yul.Checks.LocalBlock.transferPost 3) Solidity.Yul.Checks.LocalBlock.logicResult.state := by
  intro mode
  refine ⟨?_,?_,?_⟩
  · exact (RawFrame.Logic.holds_completed ctx ⟨true,false⟩ mode transferLeaveCode
      transferLeavePolicy (transferPost 1) logicResult.state 3 transferLeaveResult
      transferFinished.1).mpr ⟨rfl,rfl,rfl⟩
  · exact (RawFrame.Logic.holds_completed ctx ⟨false,true⟩ mode transferBreakCode
      transferBreakPolicy (transferPost 2) logicResult.state 3 transferBreakResult
      transferFinished.2.1).mpr ⟨rfl,rfl,rfl⟩
  · exact (RawFrame.Logic.holds_completed ctx ⟨false,true⟩ mode transferContinueCode
      transferContinuePolicy (transferPost 3) logicResult.state 3 transferContinueResult
      transferFinished.2.2).mpr ⟨rfl,rfl,rfl⟩

theorem transferRejectNormal : ∀ mode : Solidity.Modality,
¬ (Solidity.Yul.RawFrame.Logic.holds mode Solidity.Yul.Checks.LocalBlock.transferLeaveCode Solidity.Yul.Checks.LocalBlock.transferLeavePolicy (Solidity.Yul.Checks.LocalBlock.transferPost 0) Solidity.Yul.Checks.LocalBlock.logicResult.state) ∧
¬ (Solidity.Yul.RawFrame.Logic.holds mode Solidity.Yul.Checks.LocalBlock.transferBreakCode Solidity.Yul.Checks.LocalBlock.transferBreakPolicy (Solidity.Yul.Checks.LocalBlock.transferPost 0) Solidity.Yul.Checks.LocalBlock.logicResult.state) ∧
¬ (Solidity.Yul.RawFrame.Logic.holds mode Solidity.Yul.Checks.LocalBlock.transferContinueCode Solidity.Yul.Checks.LocalBlock.transferContinuePolicy (Solidity.Yul.Checks.LocalBlock.transferPost 0) Solidity.Yul.Checks.LocalBlock.logicResult.state) := by
  intro mode
  refine ⟨?_,?_,?_⟩
  · intro invalid
    have wrong := (RawFrame.Logic.holds_completed ctx ⟨true,false⟩ mode transferLeaveCode
      transferLeavePolicy (transferPost 0) logicResult.state 3 transferLeaveResult
      transferFinished.1).mp invalid
    have impossible : 1 = 0 := wrong.2.2
    cases impossible
  · intro invalid
    have wrong := (RawFrame.Logic.holds_completed ctx ⟨false,true⟩ mode transferBreakCode
      transferBreakPolicy (transferPost 0) logicResult.state 3 transferBreakResult
      transferFinished.2.1).mp invalid
    have impossible : 2 = 0 := wrong.2.2
    cases impossible
  · intro invalid
    have wrong := (RawFrame.Logic.holds_completed ctx ⟨false,true⟩ mode transferContinueCode
      transferContinuePolicy (transferPost 0) logicResult.state 3 transferContinueResult
      transferFinished.2.2).mp invalid
    have impossible : 3 = 0 := wrong.2.2
    cases impossible

/-- info: 'Solidity.Yul.RawFrame.Logic.holds_completed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.Logic.holds_completed
/-- info: 'Solidity.Yul.Checks.LocalBlock.transferLeaveCompletes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.transferLeaveCompletes
/-- info: 'Solidity.Yul.Checks.LocalBlock.transferBreakCompletes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.transferBreakCompletes
/-- info: 'Solidity.Yul.Checks.LocalBlock.transferContinueCompletes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.transferContinueCompletes
/-- info: 'Solidity.Yul.Checks.LocalBlock.transferFinished' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.transferFinished
/-- info: 'Solidity.Yul.Checks.LocalBlock.transferModal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.transferModal
/-- info: 'Solidity.Yul.Checks.LocalBlock.transferRejectNormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.transferRejectNormal


/- Actual root-control enclosures consume transfers rather than exposing a fragment's flow. -/
def rootLeaveCode : Stmt [] X ⟨false,false⟩ 0 :=
  .functions [ClosedRun.divergeSig]
    (.cons (.seq .leave (.discard (.call .here Fin.elim0))) .nil)
    (.discard (.call .here Fin.elim0))
def rootBreakPost : Stmt [] X ⟨false,false⟩ 0 :=
  assign small (.literal (word 777))
def rootContinuePost : Stmt [] X ⟨false,false⟩ 0 :=
  assign flag (.literal (word 0))
def rootBreakCode : Stmt [] X ⟨false,false⟩ 0 :=
  .for_ .skip (.literal (word 1)) rootBreakPost
    (.functions [ClosedRun.divergeSig]
      (.cons (.discard (.call .here Fin.elim0)) .nil)
      (.seq .break_ (.discard (.call .here Fin.elim0))))
def rootContinueCode : Stmt [] X ⟨false,false⟩ 0 :=
  .for_ .skip (.external flag.readRef) rootContinuePost
    (.functions [ClosedRun.divergeSig]
      (.cons (.discard (.call .here Fin.elim0)) .nil)
      (.seq .continue_ (.discard (.call .here Fin.elim0))))
def rootLeavePolicy : Policy.StmtP .A rootLeaveCode :=
  (Policy.stmt_iff .A rootLeaveCode).mp rfl
def rootBreakPolicy : Policy.StmtP .A rootBreakCode :=
  (Policy.stmt_iff .A rootBreakCode).mp rfl
def rootContinuePolicy : Policy.StmtP .A rootContinueCode :=
  (Policy.stmt_iff .A rootContinueCode).mp rfl


theorem rootLeaveCompletes :
    (RawFrame.run rootLeaveCode rootLeavePolicy 16 logicResult.state).isSome = true := by rfl
def rootLeaveResult :=
  (RawFrame.run rootLeaveCode rootLeavePolicy 16 logicResult.state).get rootLeaveCompletes
theorem rootBreakCompletes :
    (RawFrame.run rootBreakCode rootBreakPolicy 16 logicResult.state).isSome = true := by rfl
def rootBreakResult :=
  (RawFrame.run rootBreakCode rootBreakPolicy 16 logicResult.state).get rootBreakCompletes
theorem rootContinueCompletes :
    (RawFrame.run rootContinueCode rootContinuePolicy 16 logicResult.state).isSome = true := by rfl
def rootContinueResult :=
  (RawFrame.run rootContinueCode rootContinuePolicy 16 logicResult.state).get rootContinueCompletes

def rootSnapshotPost (flagValue smallValue : Nat) (result : RawFrame.Outcome ctx ⟨false,false⟩) : Prop :=
  rawSnapshot result = [flagValue,2^256-1,2309737967,smallValue,22136,2^256-1,171*2^248] ∧
  result.flow.isNormal = true
def rootBreakPostPolicy : Policy.StmtP .A rootBreakPost :=
  (Policy.stmt_iff .A rootBreakPost).mp rfl
def rootContinuePostPolicy : Policy.StmtP .A rootContinuePost :=
  (Policy.stmt_iff .A rootContinuePost).mp rfl
#guard (RawFrame.run rootBreakPost rootBreakPostPolicy 2 logicResult.state).map
  (fun result => (RawFrame.view result.state small).val) = some 777
#guard (RawFrame.run rootContinuePost rootContinuePostPolicy 2 logicResult.state).map
  (fun result => (RawFrame.view result.state flag).val) = some 0


theorem rootLeaveRun : ∀ state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.LocalBlock.ctx,
 Solidity.Yul.RawFrame.run Solidity.Yul.Checks.LocalBlock.rootLeaveCode Solidity.Yul.Checks.LocalBlock.rootLeavePolicy 16 state =
 some (⟨Solidity.Yul.RawFrame.capture state (Solidity.Yul.RawFrame.view state), .normal⟩ :
 Solidity.Yul.RawFrame.Outcome Solidity.Yul.Checks.LocalBlock.ctx ⟨false,false⟩) := by
  intro state
  unfold RawFrame.run WordAdapter.run
  change some (RawFrame.Outcome.ofWord state
    ⟨WordState.unpack ((⟨Fin.elim0,RawFrame.view state⟩ : WordState X 0).pack),.normal⟩) = _
  rw [WordState.unpack_pack]
  rfl
theorem rootBreakRun : ∀ state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.LocalBlock.ctx,
 Solidity.Yul.RawFrame.run Solidity.Yul.Checks.LocalBlock.rootBreakCode Solidity.Yul.Checks.LocalBlock.rootBreakPolicy 16 state =
 some (⟨Solidity.Yul.RawFrame.capture state (Solidity.Yul.RawFrame.view state), .normal⟩ :
 Solidity.Yul.RawFrame.Outcome Solidity.Yul.Checks.LocalBlock.ctx ⟨false,false⟩) := by
  intro state
  unfold RawFrame.run WordAdapter.run
  change some (RawFrame.Outcome.ofWord state
    ⟨WordState.unpack ((⟨Fin.elim0,RawFrame.view state⟩ : WordState X 0).pack),.normal⟩) = _
  rw [WordState.unpack_pack]
  rfl
theorem rootContinueRun : ∀ state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.LocalBlock.ctx,
 Solidity.Yul.RawFrame.view state Solidity.Yul.Checks.LocalBlock.flag = Solidity.Yul.word 2 →
Solidity.Yul.RawFrame.run Solidity.Yul.Checks.LocalBlock.rootContinueCode Solidity.Yul.Checks.LocalBlock.rootContinuePolicy 16 state =
 some (⟨Solidity.Yul.RawFrame.capture state ((Solidity.Yul.RawFrame.view state).write Solidity.Yul.Checks.LocalBlock.flag (Solidity.Yul.word 0)), .normal⟩ :
 Solidity.Yul.RawFrame.Outcome Solidity.Yul.Checks.LocalBlock.ctx ⟨false,false⟩) := by
  intro state guard
  unfold RawFrame.run WordAdapter.run
  change ((if (RawFrame.view state flag).val = 0 then
      some (⟨(⟨Fin.elim0,RawFrame.view state⟩ : WordState X 0).pack,.normal⟩ :
        Closed.Outcome ⟨false,false⟩ (0 + wordCellCount X))
    else some ⟨(fun position => if position = flag.slot then word 0 else
      (⟨Fin.elim0,RawFrame.view state⟩ : WordState X 0).pack position),.normal⟩).map
      (fun result => (⟨WordState.unpack result.vars,result.flow⟩ :
        WordAdapter.Outcome X ⟨false,false⟩ 0))).map
      (RawFrame.Outcome.ofWord state) = _
  rw [guard]
  change some (RawFrame.Outcome.ofWord state
    ⟨WordState.unpack (fun position => if position = flag.slot then word 0 else
      (⟨Fin.elim0,RawFrame.view state⟩ : WordState X 0).pack position),.normal⟩) = _
  change some (RawFrame.Outcome.ofWord state
    ⟨WordState.unpack (Closed.writeTarget
      (WordAdapter.target (.external flag.writeRef) True.intro
        (Fin.castAdd (wordCellCount X)) (fun cell => Fin.natAdd 0 cell.slot))
      (word 0) (⟨Fin.elim0,RawFrame.view state⟩ : WordState X 0).pack),.normal⟩) = _
  rw [← DirectUpdates.pack_write]
  change some (RawFrame.Outcome.ofWord state
    ⟨WordState.unpack ((⟨Fin.elim0,(RawFrame.view state).write flag (word 0)⟩ :
      WordState X 0).pack),.normal⟩) = _
  rw [WordState.unpack_pack]
  rfl


theorem rootFinished : Solidity.Yul.RawFrame.run Solidity.Yul.Checks.LocalBlock.rootLeaveCode Solidity.Yul.Checks.LocalBlock.rootLeavePolicy 16 Solidity.Yul.Checks.LocalBlock.logicResult.state = some Solidity.Yul.Checks.LocalBlock.rootLeaveResult ∧
Solidity.Yul.RawFrame.run Solidity.Yul.Checks.LocalBlock.rootBreakCode Solidity.Yul.Checks.LocalBlock.rootBreakPolicy 16 Solidity.Yul.Checks.LocalBlock.logicResult.state = some Solidity.Yul.Checks.LocalBlock.rootBreakResult ∧
Solidity.Yul.RawFrame.run Solidity.Yul.Checks.LocalBlock.rootContinueCode Solidity.Yul.Checks.LocalBlock.rootContinuePolicy 16 Solidity.Yul.Checks.LocalBlock.logicResult.state = some Solidity.Yul.Checks.LocalBlock.rootContinueResult := ⟨rfl,rfl,rfl⟩
theorem rootInputSnapshot : Solidity.Yul.Checks.LocalBlock.rawSnapshot Solidity.Yul.Checks.LocalBlock.logicResult = [2,2^256-1,2309737967,257,22136,2^256-1,171*2^248] := by rfl
theorem rootWriteSnapshot : ∀ cells : Solidity.Yul.WordCells Solidity.Yul.Checks.LocalBlock.X,
 (List.finRange (Solidity.Yul.wordCellCount Solidity.Yul.Checks.LocalBlock.X)).map
 (fun i => ((cells.write Solidity.Yul.Checks.LocalBlock.flag (Solidity.Yul.word 0)) (Solidity.Yul.wordCellAt Solidity.Yul.Checks.LocalBlock.X i)).val) =
 ((List.finRange (Solidity.Yul.wordCellCount Solidity.Yul.Checks.LocalBlock.X)).map
 (fun i => (cells (Solidity.Yul.wordCellAt Solidity.Yul.Checks.LocalBlock.X i)).val)).set 0 0 := by
  intro cells
  rfl

theorem rootValid : Solidity.Yul.Checks.LocalBlock.rootSnapshotPost 2 257 Solidity.Yul.Checks.LocalBlock.rootLeaveResult ∧
Solidity.Yul.Checks.LocalBlock.rootSnapshotPost 2 257 Solidity.Yul.Checks.LocalBlock.rootBreakResult ∧
Solidity.Yul.Checks.LocalBlock.rootSnapshotPost 0 257 Solidity.Yul.Checks.LocalBlock.rootContinueResult := by
  refine ⟨?_,?_,?_⟩
  · have same := Option.some.inj
      (rootFinished.1.symm.trans (rootLeaveRun logicResult.state))
    rw [same]
    exact ⟨rootInputSnapshot,rfl⟩
  · have same := Option.some.inj
      (rootFinished.2.1.symm.trans (rootBreakRun logicResult.state))
    rw [same]
    exact ⟨rootInputSnapshot,rfl⟩
  · have same := Option.some.inj
      (rootFinished.2.2.symm.trans (rootContinueRun logicResult.state logicValid.1))
    rw [same]
    constructor
    · change (List.finRange (wordCellCount X)).map
        (fun i => (((RawFrame.view logicResult.state).write flag (word 0))
          (wordCellAt X i)).val) = _
      rw [rootWriteSnapshot]
      change (rawSnapshot logicResult).set 0 0 = _
      rw [rootInputSnapshot]
      rfl
    · rfl

theorem rootModal : ∀ mode : Solidity.Modality,
Solidity.Yul.RawFrame.Logic.holds mode Solidity.Yul.Checks.LocalBlock.rootLeaveCode Solidity.Yul.Checks.LocalBlock.rootLeavePolicy (Solidity.Yul.Checks.LocalBlock.rootSnapshotPost 2 257) Solidity.Yul.Checks.LocalBlock.logicResult.state ∧
Solidity.Yul.RawFrame.Logic.holds mode Solidity.Yul.Checks.LocalBlock.rootBreakCode Solidity.Yul.Checks.LocalBlock.rootBreakPolicy (Solidity.Yul.Checks.LocalBlock.rootSnapshotPost 2 257) Solidity.Yul.Checks.LocalBlock.logicResult.state ∧
Solidity.Yul.RawFrame.Logic.holds mode Solidity.Yul.Checks.LocalBlock.rootContinueCode Solidity.Yul.Checks.LocalBlock.rootContinuePolicy (Solidity.Yul.Checks.LocalBlock.rootSnapshotPost 0 257) Solidity.Yul.Checks.LocalBlock.logicResult.state := by
  intro mode
  refine ⟨?_,?_,?_⟩
  · exact (RawFrame.Logic.holds_completed ctx ⟨false,false⟩ mode rootLeaveCode
      rootLeavePolicy (rootSnapshotPost 2 257) logicResult.state 16 rootLeaveResult
      rootFinished.1).mpr rootValid.1
  · exact (RawFrame.Logic.holds_completed ctx ⟨false,false⟩ mode rootBreakCode
      rootBreakPolicy (rootSnapshotPost 2 257) logicResult.state 16 rootBreakResult
      rootFinished.2.1).mpr rootValid.2.1
  · exact (RawFrame.Logic.holds_completed ctx ⟨false,false⟩ mode rootContinueCode
      rootContinuePolicy (rootSnapshotPost 0 257) logicResult.state 16 rootContinueResult
      rootFinished.2.2).mpr rootValid.2.2

theorem rootRejectWrong : ∀ mode : Solidity.Modality,
¬ Solidity.Yul.RawFrame.Logic.holds mode Solidity.Yul.Checks.LocalBlock.rootLeaveCode Solidity.Yul.Checks.LocalBlock.rootLeavePolicy (Solidity.Yul.Checks.LocalBlock.rootSnapshotPost 2 1) Solidity.Yul.Checks.LocalBlock.logicResult.state ∧
¬ Solidity.Yul.RawFrame.Logic.holds mode Solidity.Yul.Checks.LocalBlock.rootBreakCode Solidity.Yul.Checks.LocalBlock.rootBreakPolicy (Solidity.Yul.Checks.LocalBlock.rootSnapshotPost 2 777) Solidity.Yul.Checks.LocalBlock.logicResult.state ∧
¬ Solidity.Yul.RawFrame.Logic.holds mode Solidity.Yul.Checks.LocalBlock.rootContinueCode Solidity.Yul.Checks.LocalBlock.rootContinuePolicy (Solidity.Yul.Checks.LocalBlock.rootSnapshotPost 2 257) Solidity.Yul.Checks.LocalBlock.logicResult.state := by
  intro mode
  refine ⟨?_,?_,?_⟩
  · intro invalid
    have wrong := (RawFrame.Logic.holds_completed ctx ⟨false,false⟩ mode rootLeaveCode
      rootLeavePolicy (rootSnapshotPost 2 1) logicResult.state 16 rootLeaveResult
      rootFinished.1).mp invalid
    have impossible : 257 = 1 := congrArg
      (fun values : List Nat => values.getD 3 0) (rootValid.1.1.symm.trans wrong.1)
    omega
  · intro invalid
    have wrong := (RawFrame.Logic.holds_completed ctx ⟨false,false⟩ mode rootBreakCode
      rootBreakPolicy (rootSnapshotPost 2 777) logicResult.state 16 rootBreakResult
      rootFinished.2.1).mp invalid
    have impossible : 257 = 777 := congrArg
      (fun values : List Nat => values.getD 3 0) (rootValid.2.1.1.symm.trans wrong.1)
    omega
  · intro invalid
    have wrong := (RawFrame.Logic.holds_completed ctx ⟨false,false⟩ mode rootContinueCode
      rootContinuePolicy (rootSnapshotPost 2 257) logicResult.state 16 rootContinueResult
      rootFinished.2.2).mp invalid
    have impossible : 0 = 2 := congrArg
      (fun values : List Nat => values.getD 0 0) (rootValid.2.2.1.symm.trans wrong.1)
    omega


/-- info: 'Solidity.Yul.Checks.LocalBlock.rootLeaveCompletes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.rootLeaveCompletes
/-- info: 'Solidity.Yul.Checks.LocalBlock.rootBreakCompletes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.rootBreakCompletes
/-- info: 'Solidity.Yul.Checks.LocalBlock.rootContinueCompletes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.rootContinueCompletes
/-- info: 'Solidity.Yul.Checks.LocalBlock.rootLeaveRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.rootLeaveRun
/-- info: 'Solidity.Yul.Checks.LocalBlock.rootBreakRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.rootBreakRun
/-- info: 'Solidity.Yul.Checks.LocalBlock.rootContinueRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.rootContinueRun
/-- info: 'Solidity.Yul.Checks.LocalBlock.rootFinished' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.rootFinished
/-- info: 'Solidity.Yul.Checks.LocalBlock.rootInputSnapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.rootInputSnapshot
/-- info: 'Solidity.Yul.Checks.LocalBlock.rootWriteSnapshot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.rootWriteSnapshot
/-- info: 'Solidity.Yul.Checks.LocalBlock.rootValid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.rootValid
/-- info: 'Solidity.Yul.Checks.LocalBlock.rootModal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.rootModal
/-- info: 'Solidity.Yul.Checks.LocalBlock.rootRejectWrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.rootRejectWrong

/-- Conjunction preserves the concrete dirty program's whole captured outcome. -/
theorem logicConjoined : ∀ mode : Solidity.Modality,
 Solidity.Yul.RawFrame.Logic.holds mode Solidity.Yul.Checks.LocalBlock.code
 Solidity.Yul.Checks.LocalBlock.policy (fun result =>
 Solidity.Yul.Checks.LocalBlock.logicPost result ∧ result = Solidity.Yul.Checks.LocalBlock.logicResult)
 Solidity.Yul.Checks.LocalBlock.rawInitial := by
  intro mode
  apply (RawFrame.Logic.holds_and ctx ⟨false,false⟩ mode code policy
    logicPost (fun result => result = logicResult) rawInitial).mpr
  constructor
  · cases mode with
    | box => exact logicBox
    | diamond => exact logicDiamond
  · exact (RawFrame.Logic.holds_completed ctx ⟨false,false⟩ mode code policy
      (fun result => result = logicResult) rawInitial 32 logicResult logicFinished).mpr rfl

/-- All-fuel recursion keeps a vacuous conjunction box distinct from a diamond. -/
theorem recursiveConjunctionContrast : Solidity.Yul.RawFrame.Logic.holds .box Solidity.Yul.Checks.LocalBlock.recursiveCode
 Solidity.Yul.Checks.LocalBlock.recursivePolicy (fun _ => False ∧ True)
 Solidity.Yul.Checks.LocalBlock.recursiveInitial ∧
 ¬ Solidity.Yul.RawFrame.Logic.holds .diamond Solidity.Yul.Checks.LocalBlock.recursiveCode
 Solidity.Yul.Checks.LocalBlock.recursivePolicy (fun _ => False ∧ True)
 Solidity.Yul.Checks.LocalBlock.recursiveInitial := by
  constructor
  · intro fuel result done
    exact False.elim (recursiveFalseBox fuel result done)
  · intro actual
    exact recursiveNoDiamond
      ((RawFrame.Logic.holds_and recursiveCtx ⟨false,false⟩ .diamond recursiveCode
        recursivePolicy (fun _ => False) (fun _ => True) recursiveInitial).mp actual).2

/-- info: 'Solidity.Yul.RawFrame.Logic.holds_and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.Logic.holds_and
/-- info: 'Solidity.Yul.Checks.LocalBlock.logicConjoined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.logicConjoined
/-- info: 'Solidity.Yul.Checks.LocalBlock.recursiveConjunctionContrast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.recursiveConjunctionContrast

/-- A false alternative cannot replace the dirty program's exact successful result. -/
theorem logicDisjoined : ∀ mode : Solidity.Modality,
 Solidity.Yul.RawFrame.Logic.holds mode Solidity.Yul.Checks.LocalBlock.code
 Solidity.Yul.Checks.LocalBlock.policy (fun result =>
 False ∨ (Solidity.Yul.Checks.LocalBlock.logicPost result ∧ result = Solidity.Yul.Checks.LocalBlock.logicResult))
 Solidity.Yul.Checks.LocalBlock.rawInitial := by
  intro mode
  exact (RawFrame.Logic.holds_or ctx ⟨false,false⟩ mode code policy
    (fun _ => False) (fun result => logicPost result ∧ result = logicResult) rawInitial).mpr
      (Or.inr (logicConjoined mode))

/-- A disjunction of false posts is still vacuous for recursive boxes, never diamonds. -/
theorem recursiveDisjunctionContrast : Solidity.Yul.RawFrame.Logic.holds .box Solidity.Yul.Checks.LocalBlock.recursiveCode
 Solidity.Yul.Checks.LocalBlock.recursivePolicy (fun _ => False ∨ False)
 Solidity.Yul.Checks.LocalBlock.recursiveInitial ∧
 ¬ Solidity.Yul.RawFrame.Logic.holds .diamond Solidity.Yul.Checks.LocalBlock.recursiveCode
 Solidity.Yul.Checks.LocalBlock.recursivePolicy (fun _ => False ∨ False)
 Solidity.Yul.Checks.LocalBlock.recursiveInitial := by
  constructor
  · exact (RawFrame.Logic.holds_or recursiveCtx ⟨false,false⟩ .box recursiveCode
      recursivePolicy (fun _ => False) (fun _ => False) recursiveInitial).mpr
        (Or.inl recursiveFalseBox)
  · rintro ⟨_,_,_,either⟩
    cases either with
    | inl impossible => exact impossible
    | inr impossible => exact impossible

/-- info: 'Solidity.Yul.RawFrame.Logic.holds_or' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.Logic.holds_or
/-- info: 'Solidity.Yul.Checks.LocalBlock.logicDisjoined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.logicDisjoined
/-- info: 'Solidity.Yul.Checks.LocalBlock.recursiveDisjunctionContrast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.recursiveDisjunctionContrast

/-- The actual dirty result refutes negation of its validated whole-outcome post. -/
theorem logicNegatedPostRejected : ¬ Solidity.Yul.RawFrame.Logic.holds .box Solidity.Yul.Checks.LocalBlock.code
 Solidity.Yul.Checks.LocalBlock.policy (fun result => ¬ Solidity.Yul.Checks.LocalBlock.logicPost result)
 Solidity.Yul.Checks.LocalBlock.rawInitial ∧
 ¬ Solidity.Yul.RawFrame.Logic.holds .diamond Solidity.Yul.Checks.LocalBlock.code
 Solidity.Yul.Checks.LocalBlock.policy (fun result => ¬ Solidity.Yul.Checks.LocalBlock.logicPost result)
 Solidity.Yul.Checks.LocalBlock.rawInitial := by
  constructor
  · intro invalid
    exact ((RawFrame.Logic.box_not_iff_not_diamond ctx ⟨false,false⟩ code policy
      logicPost rawInitial).mp invalid) logicDiamond
  · intro invalid
    exact ((RawFrame.Logic.diamond_not_iff_not_box ctx ⟨false,false⟩ code policy
      logicPost rawInitial).mp invalid) logicBox

/-- Genuine noncompletion makes even a false negated box vacuous, without a diamond. -/
theorem recursiveNegationContrast : Solidity.Yul.RawFrame.Logic.holds .box Solidity.Yul.Checks.LocalBlock.recursiveCode
 Solidity.Yul.Checks.LocalBlock.recursivePolicy (fun _ => ¬ True)
 Solidity.Yul.Checks.LocalBlock.recursiveInitial ∧
 ¬ Solidity.Yul.RawFrame.Logic.holds .diamond Solidity.Yul.Checks.LocalBlock.recursiveCode
 Solidity.Yul.Checks.LocalBlock.recursivePolicy (fun _ => ¬ False)
 Solidity.Yul.Checks.LocalBlock.recursiveInitial := by
  constructor
  · exact (RawFrame.Logic.box_not_iff_not_diamond recursiveCtx ⟨false,false⟩
      recursiveCode recursivePolicy (fun _ => True) recursiveInitial).mpr recursiveNoDiamond
  · intro invalid
    exact ((RawFrame.Logic.diamond_not_iff_not_box recursiveCtx ⟨false,false⟩
      recursiveCode recursivePolicy (fun _ => False) recursiveInitial).mp invalid) recursiveFalseBox

/-- info: 'Solidity.Yul.RawFrame.Logic.box_not_iff_not_diamond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.Logic.box_not_iff_not_diamond
/-- info: 'Solidity.Yul.RawFrame.Logic.diamond_not_iff_not_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.Logic.diamond_not_iff_not_box
/-- info: 'Solidity.Yul.Checks.LocalBlock.logicNegatedPostRejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.logicNegatedPostRejected
/-- info: 'Solidity.Yul.Checks.LocalBlock.recursiveNegationContrast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.recursiveNegationContrast

/-- info: 'Solidity.Yul.RawFrame.Logic.holds_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.Logic.holds_mono

/- Skip retains represented bits but fills the raw overlay; zero fuel is still a timeout. -/
#guard (RawFrame.run (.skip : Stmt [] X ⟨false,false⟩ 0) True.intro 0 rawInitial).isNone
#guard rawInitial.raw flag = none
#guard (RawFrame.run (.skip : Stmt [] X ⟨false,false⟩ 0) True.intro 1 rawInitial).map
  (fun result => result.state.raw flag) = some (some (word 1))
#guard (RawFrame.run (.skip : Stmt [] X ⟨false,false⟩ 0) True.intro 1 logicResult.state).map
  (fun result => (RawFrame.view result.state flag).val) = some 2
#guard (RawFrame.run (.skip : Stmt [] X ⟨false,false⟩ 0) True.intro 1 logicResult.state).map
  (fun result => (RawFrame.view result.state small).val) = some 257

/-- info: 'Solidity.Yul.RawFrame.Logic.skip_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.Logic.skip_run
/-- info: 'Solidity.Yul.RawFrame.Logic.holds_skip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.Logic.holds_skip

/- Snapshot invariance concerns the same view, not arbitrary replacement words. -/
#guard (RawFrame.capture rawInitial (RawFrame.view rawInitial)).raw flag ≠ rawInitial.raw flag
#guard (RawFrame.run (.skip : Stmt [] X ⟨false,false⟩ 0) True.intro 1
  (RawFrame.capture rawInitial (fun _ => word 2))).map
  (fun result => (RawFrame.view result.state flag).val) = some 2
#guard (RawFrame.run (.skip : Stmt [] X ⟨false,false⟩ 0) True.intro 1 rawInitial).map
  (fun result => (RawFrame.view result.state flag).val) = some 1

/-- info: 'Solidity.Yul.RawFrame.run_snapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.run_snapshot
/-- info: 'Solidity.Yul.RawFrame.Logic.holds_snapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.Logic.holds_snapshot

/- Equal authoritative words alone do not identify the retained clean backup. -/
def otherCleanSameWords : RawFrame.State ctx :=
  { RawFrame.capture rawInitial (RawFrame.view rawInitial) with
    clean := locals.set .here (.bool false) }
#guard RawFrame.view otherCleanSameWords flag = word 1
#guard (RawFrame.run (.skip : Stmt [] X ⟨false,false⟩ 0) True.intro 1 otherCleanSameWords).map
  (fun result => match result.state.clean.get .here with | .bool value => value) = some false
#guard (RawFrame.run (.skip : Stmt [] X ⟨false,false⟩ 0) True.intro 1 rawInitial).map
  (fun result => match result.state.clean.get .here with | .bool value => value) = some true

/-- info: 'Solidity.Yul.RawFrame.run_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.run_agrees
/-- info: 'Solidity.Yul.RawFrame.Logic.holds_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.Logic.holds_agrees

/- Actual completion stores dirty values in the overlay itself, not only in fallback reads. -/
#guard logicResult.state.raw flag = some (word 2)
#guard logicResult.state.raw small = some (word 257)
#guard (logicResult.state.raw addr1).map (fun value => value.val) = some (2^256-1)

/-- info: 'Solidity.Yul.RawFrame.run_captured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.run_captured
/-- info: 'Solidity.Yul.RawFrame.Logic.box_captured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.Logic.box_captured

/-- Refusing a sparse claimed result does not imply execution never completes. -/
theorem sparseRefusalWithCompletion : (∀ fuel, Solidity.Yul.Checks.LocalBlock.rawRun fuel ≠
 some (Solidity.Yul.RawFrame.Outcome.mk Solidity.Yul.Checks.LocalBlock.rawInitial .normal)) ∧
 Solidity.Yul.Checks.LocalBlock.rawRun 32 = some Solidity.Yul.Checks.LocalBlock.logicResult := by
  constructor
  · intro fuel
    exact RawFrame.run_not_sparse ctx ⟨false,false⟩ code policy fuel rawInitial
      ⟨rawInitial,.normal⟩ flag rfl
  · exact logicFinished

/-- info: 'Solidity.Yul.RawFrame.run_not_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.run_not_sparse
/-- info: 'Solidity.Yul.RawFrame.Logic.box_not_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.RawFrame.Logic.box_not_sparse
/-- info: 'Solidity.Yul.Checks.LocalBlock.sparseRefusalWithCompletion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.sparseRefusalWithCompletion

/-- A concrete inhabited Source global for local-read controls only. No hash,
callee, storage or compiler correctness premise is asserted by this fixture. -/
def readbackGlob (pipeline : DirtyReadback.Pipeline) : Solidity.Source.Glob env :=
  { prog :=
      { body := fun _ => none
        consts := fun _ => none
        inits := fun _ => []
        ctor := fun _ => none
        ctorLocals := fun _ => []
        baseArgs := fun _ => []
        contracts := [] }
    pipeline := pipeline
    fixed :=
      { evm :=
          { keccak := fun _ => 0
            keccak_lt := fun _ => by decide
            precompile := fun _ _ => none
            precompileGas := fun _ _ => 0 }
        ledger := fun initial _ => initial
        regionLen := 1
        rootSlots := 0 }
    balance0 := fun _ => word 0
    hasCode := fun _ _ => false
    callee := fun _ => .answer (.success [])
    timestamp := word 0 }

def readbackFrame : Solidity.Source.Fr :=
  { this := ⟨0, by decide⟩, sender := ⟨0, by decide⟩, value := word 0,
    static := false, contract := "" }

def readbackSmallIndex : Solidity.Source.Idx ctx.tys (.int IntTy.u8) :=
  .there (.there .here)
def readbackByteIndex : Solidity.Source.Idx ctx.tys (.fixedBytes 1 (by decide)) :=
  .there (.there (.there (.there .here)))
def readback255 : Solidity.Source.Val env.layout (.int IntTy.u8) := .int 255 (by decide)
def selectedReadState : RawFrame.State ctx :=
  RawFrame.write (RawFrame.write rawInitial small (word 511)) byte (word 5)

/-- Selected-local readback regression: readbackSelectedLazy. -/
theorem readbackSelectedLazy :
 ∀ (pipeline : Solidity.Yul.DirtyReadback.Pipeline), Solidity.Yul.DirtyReadback.frame pipeline Solidity.Yul.Checks.LocalBlock.selectedReadState = none ∧ Solidity.Yul.DirtyReadback.readAt pipeline Solidity.Yul.Checks.LocalBlock.selectedReadState Solidity.Yul.Checks.LocalBlock.readbackSmallIndex = some Solidity.Yul.Checks.LocalBlock.readback255 := by
  intro pipeline; cases pipeline <;> constructor <;> rfl

/-- Selected-local readback regression: readbackSourceLocal. -/
theorem readbackSourceLocal :
 ∀ (pipeline : Solidity.Yul.DirtyReadback.Pipeline), Solidity.Yul.DirtyReadback.evalLocal (Solidity.Yul.Checks.LocalBlock.readbackGlob pipeline) Solidity.Yul.Checks.LocalBlock.readbackFrame 1 Solidity.Yul.Checks.LocalBlock.selectedReadState Solidity.Yul.Checks.LocalBlock.readbackSmallIndex = some ((.ok (.val Solidity.Yul.Checks.LocalBlock.readback255), (Solidity.Yul.Checks.LocalBlock.locals.set Solidity.Yul.Checks.LocalBlock.readbackSmallIndex Solidity.Yul.Checks.LocalBlock.readback255, Solidity.Yul.Checks.LocalBlock.initial.2)), Solidity.Yul.Checks.LocalBlock.selectedReadState) := by
  intro pipeline; cases pipeline <;> rfl

/-- Selected-local readback regression: readbackSourceTimeout. -/
theorem readbackSourceTimeout :
 ∀ (pipeline : Solidity.Yul.DirtyReadback.Pipeline), Solidity.Yul.DirtyReadback.evalLocal (Solidity.Yul.Checks.LocalBlock.readbackGlob pipeline) Solidity.Yul.Checks.LocalBlock.readbackFrame 0 Solidity.Yul.Checks.LocalBlock.selectedReadState Solidity.Yul.Checks.LocalBlock.readbackSmallIndex = some ((.error .timeout, (Solidity.Yul.Checks.LocalBlock.locals.set Solidity.Yul.Checks.LocalBlock.readbackSmallIndex Solidity.Yul.Checks.LocalBlock.readback255, Solidity.Yul.Checks.LocalBlock.initial.2)), Solidity.Yul.Checks.LocalBlock.selectedReadState) := by
  intro pipeline; cases pipeline <;> rfl

/-- Selected-local readback regression: readbackSourceRefusal. -/
theorem readbackSourceRefusal :
 ∀ (pipeline : Solidity.Yul.DirtyReadback.Pipeline), Solidity.Yul.DirtyReadback.evalLocal (Solidity.Yul.Checks.LocalBlock.readbackGlob pipeline) Solidity.Yul.Checks.LocalBlock.readbackFrame 1 Solidity.Yul.Checks.LocalBlock.selectedReadState Solidity.Yul.Checks.LocalBlock.readbackByteIndex = none := by
  intro pipeline; cases pipeline <;> rfl

/-- Selected-local readback regression: readbackSourceRaw. -/
theorem readbackSourceRaw :
 ∀ (pipeline : Solidity.Yul.DirtyReadback.Pipeline), (Solidity.Yul.DirtyReadback.evalLocal (Solidity.Yul.Checks.LocalBlock.readbackGlob pipeline) Solidity.Yul.Checks.LocalBlock.readbackFrame 1 Solidity.Yul.Checks.LocalBlock.selectedReadState Solidity.Yul.Checks.LocalBlock.readbackSmallIndex).map Prod.snd = some Solidity.Yul.Checks.LocalBlock.selectedReadState := by
  intro pipeline; cases pipeline <;> rfl

/-- Selected-local readback regression: readbackRawWords. -/
theorem readbackRawWords :
 (Solidity.Yul.RawFrame.view Solidity.Yul.Checks.LocalBlock.selectedReadState Solidity.Yul.Checks.LocalBlock.small).val = 511 ∧ (Solidity.Yul.RawFrame.view Solidity.Yul.Checks.LocalBlock.selectedReadState Solidity.Yul.Checks.LocalBlock.byte).val = 5 := by
  decide

/-- info: 'Solidity.Yul.DirtyReadback.locals_get_set' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.locals_get_set
/-- info: 'Solidity.Yul.DirtyReadback.evalLocal_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.evalLocal_refused
/-- info: 'Solidity.Yul.DirtyReadback.evalLocal_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.evalLocal_zero
/-- info: 'Solidity.Yul.DirtyReadback.evalLocal_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.evalLocal_success
/-- info: 'Solidity.Yul.DirtyReadback.evalLocal_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.evalLocal_raw
/-- info: 'Solidity.Yul.Checks.LocalBlock.readbackSelectedLazy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.readbackSelectedLazy
/-- info: 'Solidity.Yul.Checks.LocalBlock.readbackSourceLocal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.readbackSourceLocal
/-- info: 'Solidity.Yul.Checks.LocalBlock.readbackSourceTimeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.readbackSourceTimeout
/-- info: 'Solidity.Yul.Checks.LocalBlock.readbackSourceRefusal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.readbackSourceRefusal
/-- info: 'Solidity.Yul.Checks.LocalBlock.readbackSourceRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.readbackSourceRaw
/-- info: 'Solidity.Yul.Checks.LocalBlock.readbackRawWords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.readbackRawWords

/-- info: 'Solidity.Yul.DirtyReadback.locals_set_get' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.locals_set_get
/-- info: 'Solidity.Yul.DirtyReadback.evalLocal_readable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.evalLocal_readable
/-- info: 'Solidity.Yul.DirtyReadback.evalLocal_compatible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.evalLocal_compatible

/-- info: 'Solidity.Yul.DirtyReadback.readValue_pipelines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.readValue_pipelines
/-- info: 'Solidity.Yul.DirtyReadback.readLocal_pipelines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.readLocal_pipelines
/-- info: 'Solidity.Yul.DirtyReadback.readback_pipelines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.readback_pipelines
/-- info: 'Solidity.Yul.DirtyReadback.readbackFrom_pipelines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.readbackFrom_pipelines
/-- info: 'Solidity.Yul.DirtyReadback.readAt_pipelines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.readAt_pipelines
/-- info: 'Solidity.Yul.DirtyReadback.evalLocal_pipelines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.evalLocal_pipelines

/-- Capture preserves the Source observation without identifying sparse and full raw overlays. -/
theorem readbackCaptureMetadata :
 ∀ (pipeline : Solidity.Yul.DirtyReadback.Pipeline),
(Solidity.Yul.DirtyReadback.evalLocal (Solidity.Yul.Checks.LocalBlock.readbackGlob pipeline) Solidity.Yul.Checks.LocalBlock.readbackFrame 1 (Solidity.Yul.RawFrame.capture Solidity.Yul.Checks.LocalBlock.selectedReadState (Solidity.Yul.RawFrame.view Solidity.Yul.Checks.LocalBlock.selectedReadState)) Solidity.Yul.Checks.LocalBlock.readbackSmallIndex).map Prod.fst =
(Solidity.Yul.DirtyReadback.evalLocal (Solidity.Yul.Checks.LocalBlock.readbackGlob pipeline) Solidity.Yul.Checks.LocalBlock.readbackFrame 1 Solidity.Yul.Checks.LocalBlock.selectedReadState Solidity.Yul.Checks.LocalBlock.readbackSmallIndex).map Prod.fst ∧
Solidity.Yul.Checks.LocalBlock.selectedReadState.raw Solidity.Yul.Checks.LocalBlock.flag = none ∧ (Solidity.Yul.RawFrame.capture Solidity.Yul.Checks.LocalBlock.selectedReadState (Solidity.Yul.RawFrame.view Solidity.Yul.Checks.LocalBlock.selectedReadState)).raw Solidity.Yul.Checks.LocalBlock.flag = some (Solidity.Yul.RawFrame.view Solidity.Yul.Checks.LocalBlock.selectedReadState Solidity.Yul.Checks.LocalBlock.flag) := by
  intro pipeline
  constructor
  · exact Solidity.Yul.DirtyReadback.evalLocal_source_capture _ _ _ _ _ _ _ _
  · constructor <;> rfl

/-- info: 'Solidity.Yul.DirtyReadback.readAt_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.readAt_agrees
/-- info: 'Solidity.Yul.DirtyReadback.evalLocal_source_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.evalLocal_source_agrees
/-- info: 'Solidity.Yul.DirtyReadback.readAt_capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.readAt_capture
/-- info: 'Solidity.Yul.DirtyReadback.evalLocal_source_capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.evalLocal_source_capture
/-- info: 'Solidity.Yul.Checks.LocalBlock.readbackCaptureMetadata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.LocalBlock.readbackCaptureMetadata

/-- info: 'Solidity.Yul.DirtyReadback.wrapBits_emod' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.wrapBits_emod
/-- info: 'Solidity.Yul.DirtyReadback.wrapBits_congr' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.wrapBits_congr
/-- info: 'Solidity.Yul.DirtyReadback.wrapBits_idempotent' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.wrapBits_idempotent
/-- info: 'Solidity.Yul.DirtyReadback.intWrap_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.intWrap_idempotent
/-- info: 'Solidity.Yul.DirtyReadback.cleanWord_int_lowBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.cleanWord_int_lowBits

/-- info: 'Solidity.Yul.DirtyReadback.intWord_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.intWord_value
/-- info: 'Solidity.Yul.DirtyReadback.wrap_intWord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.wrap_intWord
/-- info: 'Solidity.Yul.DirtyReadback.cleanWord_int_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.cleanWord_int_encode
/-- info: 'Solidity.Yul.DirtyReadback.intWrap_of_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.intWrap_of_range
/-- info: 'Solidity.Yul.DirtyReadback.cleanWord_int_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.cleanWord_int_roundtrip
/-- info: 'Solidity.Yul.DirtyReadback.cleanWord_bool_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.cleanWord_bool_roundtrip

end Solidity.Yul.Checks.LocalBlock
