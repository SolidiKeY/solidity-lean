import Solidity.Yul.Compilation.Artifact
import Solidity.Yul.Compilation.CaseCompletion
import Solidity.Yul.Compilation.MultiSwitchCompilation

/-! Lossless finite-case transport in the original selector/default context.
The common source is an actual literal-selector switch. The adapter pushes
that selector, then runs the original emitted dispatcher. Original arm/default
horizons, code selection and compiler data remain explicit. -/
namespace Solidity.Yul.Compilation.H55Cases
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n fuel ff : Nat} {arms : Cases [] [] c n}
  {fallbackStmt : Stmt [] [] c n}

private def compareProgram (label : Solidity.Yul.Word) : Backend.Program :=
  [pushWord (BitVec.ofFin label), readSlot ⟨1, by decide⟩, .op .EQ]

private theorem compare_lowered (label : Solidity.Yul.Word) :
    (SwitchCompilation.comparison label).code 0 = some (compareProgram label) := rfl

private theorem compare_selected (label : Solidity.Yul.Word) :
    WordMachine.selectCode (compareProgram label) =
      some [.push (coreWord (BitVec.ofFin label)), .dup 2, .eq] := by
  change (WordMachine.selectInstr (pushWord (BitVec.ofFin label))).bind _ = _
  rw [WordMachine.select_pushWord]
  rfl

/-- All real case constructors retain selectable arm/default code. No desired
execution or source completion is a premise of code existence. -/
theorem emitted_code_exists (a : CaseCompilation.Compiled fuel arms)
    (fallback : ScopedControlCompilation.Artifact ff fallbackStmt) :
    ∃ (block : Backend.Block) (code : List Evm.Instr),
      a.emit fallback.block = some block ∧ WordControl.blockCode block = some code := by
  induction a with
  | nil fuel =>
    refine ⟨.seq (.code (popPrefix 1)) fallback.block, .pop :: fallback.code, rfl, ?_⟩
    change (WordMachine.selectCode (popPrefix 1)).bind
      (fun p => (WordControl.blockCode fallback.block).map (fun q => p ++ q)) = _
    rw [fallback.selected]
    rfl
  | @cons fuel label body rest arm tail ih =>
    obtain ⟨next, code, emitted, selected⟩ := ih
    have armCode : WordControl.blockCode (.seq (.code (popPrefix 1)) arm.block) =
        some (.pop :: arm.code) := by
      change (WordMachine.selectCode (popPrefix 1)).bind
        (fun p => (WordControl.blockCode arm.block).map (fun q => p ++ q)) = _
      rw [arm.selected]
      rfl
    refine ⟨.ite (compareProgram label) (.seq (.code (popPrefix 1)) arm.block) next,
      MachineControl.branchCode [.push (coreWord (BitVec.ofFin label)), .dup 2, .eq]
        (.pop :: arm.code) code, ?_, ?_⟩
    · change ((SwitchCompilation.comparison label).code 0).bind
        (fun p => (tail.emit fallback.block).bind
          (fun next => some (Backend.Block.ite p (.seq (.code (popPrefix 1)) arm.block) next))) = _
      rw [compare_lowered, emitted]
      rfl
    · change (WordMachine.selectCode (compareProgram label)).bind
        (fun p => (WordControl.blockCode (.seq (.code (popPrefix 1)) arm.block)).bind
          (fun yes => (WordControl.blockCode next).map
            (fun no => MachineControl.branchCode p yes no))) = _
      rw [compare_selected, armCode, selected]
      rfl

structure Selected (a : CaseCompilation.Compiled fuel arms)
    (fallback : ScopedControlCompilation.Artifact ff fallbackStmt) where
  block : Backend.Block
  code : List Evm.Instr
  emitted : a.emit fallback.block = some block
  selected : WordControl.blockCode block = some code

noncomputable def select (a : CaseCompilation.Compiled fuel arms)
    (fallback : ScopedControlCompilation.Artifact ff fallbackStmt) : Selected a fallback :=
  Classical.choice (show Nonempty (Selected a fallback) from by
    obtain ⟨block, code, emitted, selected⟩ := emitted_code_exists a fallback
    exact ⟨⟨block, code, emitted, selected⟩⟩)

noncomputable def encode (selector : Scalar.Word)
    (fallback : ScopedControlCompilation.Artifact ff fallbackStmt)
    (a : CaseCompilation.Compiled fuel arms) :
    Artifact 0 (.switch (.literal selector.toFin) arms fallbackStmt) where
  profile := ⟨True.intro, a.profile, fallback.compiled.profile⟩
  code := .push (coreWord selector) :: (select a fallback).code
  source_to_model := by
    intro horizon locals result ran newer m caller
    have empty : newer.toList = [] := List.length_eq_zero_iff.mp (by simp only [Vector.length_toList])
    cases horizon with
    | zero => cases ran
    | succ horizon =>
      cases horizon with
      | zero => cases ran
      | succ horizon =>
        change (do
          let chosen ← evalCases (horizon+1) .nil True.intro arms a.profile selector.toFin (sourceLocals locals)
          match chosen with
          | some result => pure result
          | none => evalStmt (horizon+1) .nil True.intro fallbackStmt fallback.compiled.profile (sourceLocals locals)) = some result at ran
        obtain ⟨out, same, target⟩ := CaseCompilation.source_to_model a fallback
          (select a fallback).block (select a fallback).code
          (select a fallback).emitted (select a fallback).selected
          selector (horizon+1) (horizon+1) locals result ran m caller
        refine ⟨out, same, ?_⟩
        simp only [empty, List.nil_append]
        change Evm.run ([.push (coreWord selector)] ++ (select a fallback).code) _ = _
        have pushed : Evm.run [.push (coreWord selector)]
            {m with stack := locals.toList.map coreWord ++ caller} =
            .ok {m with stack := coreWord selector :: (locals.toList.map coreWord ++ caller)} 0 := rfl
        rw [Evm.run_append_ok pushed]
        exact target
  model_to_source := by
    intro locals newer m final caller skip ran
    have empty : newer.toList = [] := List.length_eq_zero_iff.mp (by simp only [Vector.length_toList])
    simp only [empty, List.nil_append] at ran ⊢
    change Evm.run ([.push (coreWord selector)] ++ (select a fallback).code) _ = _ at ran
    have pushed : Evm.run [.push (coreWord selector)]
        {m with stack := locals.toList.map coreWord ++ caller} =
        .ok {m with stack := coreWord selector :: (locals.toList.map coreWord ++ caller)} 0 := rfl
    rw [Evm.run_append_ok pushed] at ran
    obtain ⟨hc, hf, out, chosen, casesRun, continued, done, frame⟩ :=
      CaseCompletion.model_to_source a fallback (select a fallback).block (select a fallback).code
        (select a fallback).emitted (select a fallback).selected selector locals m final caller skip ran
    have casesLater : evalCases (hc+hf+1) .nil True.intro arms a.profile selector.toFin
        (sourceLocals locals) = some chosen := by
      simpa only [Nat.add_assoc] using
        evalCases_refines_add hc (hf+1) .nil True.intro arms a.profile selector.toFin
          (sourceLocals locals) chosen casesRun
    have continuedLater : (match chosen with
        | some result => some result
        | none => evalStmt (hc+hf+1) .nil True.intro fallbackStmt fallback.compiled.profile
            (sourceLocals locals)) = some ⟨sourceLocals out, .normal⟩ := by
      cases chosen with
      | some result => exact continued
      | none =>
        exact evalStmt_stable (lo := hf) (hi := hc+hf+1) (by omega) .nil True.intro fallbackStmt
          fallback.compiled.profile (sourceLocals locals) continued
    refine ⟨hc+hf+1+1, out, ?_, done, frame⟩
    have selectedLater : evalCases (hc+hf+1) .nil True.intro arms a.profile
        ((literal 0 selector.toFin).value locals).toFin (sourceLocals locals) = some chosen := by
      simpa only [literal, BitVec.ofFin_toFin] using casesLater
    cases chosen with
    | none =>
      exact MultiSwitchCompilation.source_chosen (literal 0 selector.toFin) a.profile
        fallback.compiled.profile (hc+hf+1) locals none ⟨sourceLocals out, .normal⟩
        (by omega) selectedLater continuedLater
    | some value =>
      exact MultiSwitchCompilation.source_chosen (literal 0 selector.toFin) a.profile
        fallback.compiled.profile (hc+hf+1) locals (some value) ⟨sourceLocals out, .normal⟩
        (by omega) selectedLater continuedLater

abbrev Image (selector : Scalar.Word) (fallback : ScopedControlCompilation.Artifact ff fallbackStmt)
    (fuel : Nat) (arms : Cases [] [] c n) := Artifact.Image (encode selector fallback (fuel := fuel) (arms := arms))
noncomputable def toImage (selector : Scalar.Word) (fallback : ScopedControlCompilation.Artifact ff fallbackStmt)
    (a : CaseCompilation.Compiled fuel arms) : Image selector fallback fuel arms :=
  Artifact.toImage (encode selector fallback) a
def fromImage {selector : Scalar.Word} {fallback : ScopedControlCompilation.Artifact ff fallbackStmt}
    (image : Image selector fallback fuel arms) : CaseCompilation.Compiled fuel arms := Artifact.fromImage image

theorem source_roundtrip (selector : Scalar.Word) (fallback : ScopedControlCompilation.Artifact ff fallbackStmt)
    (a : CaseCompilation.Compiled fuel arms) : fromImage (toImage selector fallback a) = a := rfl

theorem image_roundtrip {selector : Scalar.Word} {fallback : ScopedControlCompilation.Artifact ff fallbackStmt}
    (image : Image selector fallback fuel arms) : toImage selector fallback (fromImage image) = image :=
  Artifact.image_roundtrip image

theorem code_preserved (selector : Scalar.Word) (fallback : ScopedControlCompilation.Artifact ff fallbackStmt)
    (a : CaseCompilation.Compiled fuel arms) : (toImage selector fallback a).artifact.code =
      .push (coreWord selector) :: (select a fallback).code := rfl

/-- Any original successful selection gives exactly the adapter's dispatch
code; classical witness extraction cannot choose a different emitted program. -/
theorem selected_code_unique (fallback : ScopedControlCompilation.Artifact ff fallbackStmt)
    (a : CaseCompilation.Compiled fuel arms) (block : Backend.Block) (code : List Evm.Instr)
    (emitted : a.emit fallback.block = some block) (selected : WordControl.blockCode block = some code) :
    (select a fallback).code = code := by
  have sameBlock : (select a fallback).block = block :=
    Option.some.inj ((select a fallback).emitted.symm.trans emitted)
  have atBlock := (select a fallback).selected
  rw [sameBlock] at atBlock
  exact Option.some.inj (atBlock.symm.trans selected)

theorem selected_code_preserved (selector : Scalar.Word)
    (fallback : ScopedControlCompilation.Artifact ff fallbackStmt)
    (a : CaseCompilation.Compiled fuel arms) (block : Backend.Block) (code : List Evm.Instr)
    (emitted : a.emit fallback.block = some block) (selected : WordControl.blockCode block = some code) :
    (toImage selector fallback a).artifact.code = .push (coreWord selector) :: code := by
  rw [code_preserved, selected_code_unique fallback a block code emitted selected]

namespace Controls
def skipSource : Stmt [] [] ⟨false, false⟩ 0 := .skip
def fallback : ScopedControlCompilation.Artifact 1 skipSource :=
  (ScopedControlCompilation.lower 1 skipSource).get (by rfl)
def emptyArms : Cases [] [] ⟨false, false⟩ 0 := .nil
def singleArms : Cases [] [] ⟨false, false⟩ 0 := .cons 0 skipSource .nil
def emptyProducer : CaseCompilation.Compiled 0 emptyArms :=
  (CaseCompilation.compile 0 emptyArms).get (by rfl)
def singleProducer : CaseCompilation.Compiled 2 singleArms :=
  (CaseCompilation.compile 2 singleArms).get (by rfl)

theorem inhabited_images (selector : Scalar.Word) :
    Nonempty (Image selector fallback 0 emptyArms) ∧
    Nonempty (Image selector fallback 2 singleArms) :=
  ⟨⟨toImage selector fallback emptyProducer⟩, ⟨toImage selector fallback singleProducer⟩⟩

-- Empty cases are accepted even at zero fuel; nonempty cases are not.
#guard (CaseCompilation.compile 0 emptyArms).isSome
#guard (CaseCompilation.compile 0 singleArms).isNone

theorem hit_source : evalStmt 4 .nil True.intro (.switch (.literal 0) singleArms skipSource)
    (encode 0 fallback singleProducer).profile (sourceLocals #v[]) =
    some ⟨sourceLocals #v[], .normal⟩ := rfl

theorem miss_source : evalStmt 4 .nil True.intro (.switch (.literal 1) singleArms skipSource)
    (encode 1 fallback singleProducer).profile (sourceLocals #v[]) =
    some ⟨sourceLocals #v[], .normal⟩ := rfl

theorem hit_model (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode 0 fallback singleProducer).code {m with stack := caller} =
      .ok {m with stack := caller} 0 := by
  simpa only [Vector.toList_empty, List.nil_append, List.map_nil] using
    (encode 0 fallback singleProducer).normal_to_model 4 #v[] #v[] hit_source #v[] m caller

theorem miss_model (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode 1 fallback singleProducer).code {m with stack := caller} =
      .ok {m with stack := caller} 0 := by
  simpa only [Vector.toList_empty, List.nil_append, List.map_nil] using
    (encode 1 fallback singleProducer).normal_to_model 4 #v[] #v[] miss_source #v[] m caller
/-- Hit and miss controls update the actual source local differently. -/
def effectArm : Stmt [] [] ⟨false, false⟩ 1 :=
  .assign (fun _ : Fin 1 => .local 0) (.literal 7)
def effectFallbackSource : Stmt [] [] ⟨false, false⟩ 1 :=
  .assign (fun _ : Fin 1 => .local 0) (.literal 9)
def effectArms : Cases [] [] ⟨false, false⟩ 1 := .cons 0 effectArm .nil
def effectFallback : ScopedControlCompilation.Artifact 3 effectFallbackSource :=
  (ScopedControlCompilation.lower 3 effectFallbackSource).get (by rfl)
def effectProducer : CaseCompilation.Compiled 4 effectArms :=
  (CaseCompilation.compile 4 effectArms).get (by rfl)

theorem effect_hit_source : evalStmt 4 .nil True.intro (.switch (.literal 0) effectArms effectFallbackSource)
    (encode 0 effectFallback effectProducer).profile (sourceLocals #v[4]) =
    some ⟨sourceLocals #v[7], .normal⟩ := by
  apply congrArg some
  apply congrArg (fun vars : Values 1 => (⟨vars, .normal⟩ : Outcome ⟨false, false⟩ 1))
  funext i
  have same : i = 0 := Fin.ext (by omega)
  cases same
  rfl

theorem effect_miss_source : evalStmt 4 .nil True.intro (.switch (.literal 1) effectArms effectFallbackSource)
    (encode 1 effectFallback effectProducer).profile (sourceLocals #v[4]) =
    some ⟨sourceLocals #v[9], .normal⟩ := by
  apply congrArg some
  apply congrArg (fun vars : Values 1 => (⟨vars, .normal⟩ : Outcome ⟨false, false⟩ 1))
  funext i
  have same : i = 0 := Fin.ext (by omega)
  cases same
  rfl

theorem effect_hit_model (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode 0 effectFallback effectProducer).code {m with stack := coreWord 4 :: caller} =
      .ok {m with stack := coreWord 7 :: caller} 0 := by
  simpa only [Vector.toList_empty, Vector.toList_singleton, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append] using
    (encode 0 effectFallback effectProducer).normal_to_model 4 #v[4] #v[7] effect_hit_source #v[] m caller

theorem effect_miss_model (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode 1 effectFallback effectProducer).code {m with stack := coreWord 4 :: caller} =
      .ok {m with stack := coreWord 9 :: caller} 0 := by
  simpa only [Vector.toList_empty, Vector.toList_singleton, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append] using
    (encode 1 effectFallback effectProducer).normal_to_model 4 #v[4] #v[9] effect_miss_source #v[] m caller

end Controls

#print axioms emitted_code_exists
#print axioms encode
#print axioms source_roundtrip
#print axioms image_roundtrip
#print axioms code_preserved
#print axioms selected_code_unique
#print axioms selected_code_preserved
#print axioms Controls.inhabited_images
#print axioms Controls.hit_source
#print axioms Controls.miss_source
#print axioms Controls.hit_model
#print axioms Controls.miss_model
#print axioms Controls.effect_hit_source
#print axioms Controls.effect_miss_source
#print axioms Controls.effect_hit_model
#print axioms Controls.effect_miss_model
end Solidity.Yul.Compilation.H55Cases
