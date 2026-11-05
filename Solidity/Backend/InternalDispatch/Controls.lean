import Solidity.Backend.InternalDispatch.Chain
import Solidity.Lowering.V08.SourceCallableControls

/-! Inhabited two-candidate source-call and actual machine-EQ controls.
The interpreter-valued ObservationModel below only witnesses that the contract
is inhabited; it is explicitly NOT the missing P1 physical frame compiler. -/
namespace Solidity.Backend.InternalDispatch.Controls
open Source
namespace Fixture
abbrev E := Lowering.V08.SourceCallableControls.E
abbrev firstDecl := Lowering.V08.SourceCallableControls.functionDecl
abbrev secondDecl := Lowering.V08.SourceCallableControls.decoyDecl
end Fixture
open Fixture

def first : Candidate E [.bool,.bool] [.bool] none :=
  ⟨firstDecl, Lowering.V08.SourceCallableControls.declaration_member,
    Lowering.V08.SourceCallableControls.signature, rfl, by decide +kernel⟩
def second : Candidate E [.bool,.bool] [.bool] none :=
  ⟨secondDecl, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    List.mem_cons_self)), rfl, rfl, by decide +kernel⟩

def table : Table E [.bool,.bool] [.bool] none where
  size := 2
  candidate := fun i => if i.val = 0 then first else second
  distinct := by
    intro i j h
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    by_cases iz : i.val = 0 <;> by_cases jz : j.val = 0
    · omega
    · have unequal : first.identity ≠ second.identity := by decide +kernel
      exact False.elim (unequal (by simpa only [if_pos iz, if_neg jz] using h))
    · have unequal : second.identity ≠ first.identity := by decide +kernel
      exact False.elim (unequal (by simpa only [if_neg iz, if_pos jz] using h))
    · omega
  capacity := by decide +kernel

def firstValue : Source.Val E.layout (.fn false [.bool,.bool] [.bool] none) :=
  .internalFn first.identity
def secondValue : Source.Val E.layout (.fn false [.bool,.bool] [.bool] none) :=
  .internalFn second.identity

theorem first_rep : table.Rep firstValue (Evm.wmod 1) :=
  ⟨⟨0, by decide +kernel⟩, rfl, rfl⟩
theorem second_rep : table.Rep secondValue (Evm.wmod 2) :=
  ⟨⟨1, by decide +kernel⟩, rfl, rfl⟩

theorem choose_second : table.decode (Evm.wmod 2) = some ⟨1, by decide +kernel⟩ := rfl
theorem zero_refused : table.decode (Evm.wmod 0) = none := rfl
theorem foreign_refused : table.decode (Evm.wmod 3) = none := rfl

theorem signature_refused :
    Candidate.check (ps := [.bool]) (rs := [.bool]) (qualifier := none)
      firstDecl Lowering.V08.SourceCallableControls.declaration_member = none := rfl
theorem qualifier_refused :
    Candidate.check (ps := [.bool,.bool]) (rs := [.bool]) (qualifier := some .view)
      firstDecl Lowering.V08.SourceCallableControls.declaration_member = none := rfl

theorem second_guard_true (machine : Evm.Machine) (tail : List Evm.Word) :
    Evm.Instr.step .eq {machine with stack := .val (Evm.wmod 2) :: .val (Evm.wmod 2) :: tail} =
      .ok {machine with stack := .val (Evm.bword true) :: tail} 0 :=
  table.eq_step secondValue (Evm.wmod 2) second_rep ⟨1, by decide +kernel⟩ machine tail

theorem wrong_guard_false (machine : Evm.Machine) (tail : List Evm.Word) :
    Evm.Instr.step .eq {machine with stack := .val (Evm.wmod 2) :: .val (Evm.wmod 1) :: tail} =
      .ok {machine with stack := .val (Evm.bword false) :: tail} 0 :=
  table.eq_step secondValue (Evm.wmod 2) second_rep ⟨0, by decide +kernel⟩ machine tail

/-- Contract inhabitation using the actual source evaluator, not P1 evidence. -/
def interpreterFrames (pipeline : Roadmap.Pipeline) (horizon : Nat) :
    ObservationModel E [.bool,.bool] [.bool] none
      (Lowering.V08.SourceCallableControls.global pipeline)
      Lowering.V08.SourceCallableControls.callerFrame horizon where
  State := Source.Vals E.layout [.bool,.bool] × Source.St E
  Result := SourceObservation E [.bool]
  input := fun args source target => target = (args, source)
  output := Eq
  invoke := fun candidate state => sourceCall
    (Lowering.V08.SourceCallableControls.global pipeline)
    Lowering.V08.SourceCallableControls.callerFrame horizon candidate state.1 state.2
  correct := by intro candidate args source target h; subst target; rfl

open Lowering.V08.SourceCallableControls in
theorem actual_source_and_selected_run (pipeline : Roadmap.Pipeline) (horizon : Nat)
    (a b : Bool) :
    table.execute (interpreterFrames pipeline (horizon+25)) (Evm.wmod 1)
      (params a b, populated) =
      some (.ok (.val (.bool a)), (Source.L0 Fixture.E, Lowering.V08.SourceKeccak.afterLiteral populated binary)) := by
  change some (sourceCall (global pipeline) callerFrame (horizon+25) first (params a b) populated) = _
  exact congrArg some (call_execute pipeline horizon a b)

/- A different candidate really has a different source result for these args. -/
open Lowering.V08.SourceCallableControls in
theorem actual_second_run (pipeline : Roadmap.Pipeline) :
    table.execute (interpreterFrames pipeline 25) (Evm.wmod 2)
      (params true false, populated) =
      some (.ok (.val (.bool false)), (Source.L0 Fixture.E, Lowering.V08.SourceKeccak.afterLiteral populated binary)) := rfl

open Lowering.V08.SourceCallableControls in
theorem timeout_preserved (pipeline : Roadmap.Pipeline) :
    table.execute (interpreterFrames pipeline 0) (Evm.wmod 1) (params true false, populated) =
      some (.error .timeout, (Source.L0 Fixture.E, populated)) := rfl

theorem same_arity_kind_refused :
    Candidate.check (ps := [.address false,.bool]) (rs := [.bool]) (qualifier := none)
      firstDecl Lowering.V08.SourceCallableControls.declaration_member = none := rfl

theorem wrong_return_refused :
    Candidate.check (ps := [.bool,.bool]) (rs := [.bool,.bool]) (qualifier := none)
      firstDecl Lowering.V08.SourceCallableControls.declaration_member = none := rfl

open Lowering.V08.SourceCallableControls in
theorem compiled_source_run (pipeline : Roadmap.Pipeline) (horizon : Nat) (a b : Bool) :
    table.runArms (interpreterFrames pipeline (horizon+25)) (Evm.wmod 1)
      (params a b, populated) table.code =
      some (.ok (.val (.bool a)),
        (Source.L0 Fixture.E, Lowering.V08.SourceKeccak.afterLiteral populated binary)) := by
  rw [table.code_agrees]
  exact actual_source_and_selected_run pipeline horizon a b

open Lowering.V08.SourceCallableControls in
theorem compiled_second_run (pipeline : Roadmap.Pipeline) :
    table.runArms (interpreterFrames pipeline 25) (Evm.wmod 2)
      (params true false, populated) table.code =
      some (.ok (.val (.bool false)),
        (Source.L0 Fixture.E, Lowering.V08.SourceKeccak.afterLiteral populated binary)) := by
  rw [table.code_agrees]
  exact actual_second_run pipeline

open Lowering.V08.SourceCallableControls in
theorem compiled_foreign_refused (pipeline : Roadmap.Pipeline) :
    table.runArms (interpreterFrames pipeline 25) (Evm.wmod 3)
      (params true false, populated) table.code = none := rfl

open Lowering.V08.SourceCallableControls in
theorem wrong_result_refuted (pipeline : Roadmap.Pipeline) :
    table.execute (interpreterFrames pipeline 25) (Evm.wmod 2)
      (params true false, populated) ≠
      some (.ok (.val (.bool true)),
        (Source.L0 Fixture.E, Lowering.V08.SourceKeccak.afterLiteral populated binary)) := by
  rw [actual_second_run]
  intro wrong
  cases wrong

/- A reference-valued full signature is admitted without primitive erasure.
This is metadata evidence, not a reference-frame implementation. -/
def referenceDecl : Source.Decl :=
  ⟨.function, "reference", none, true,
    .function (.ident "reference")
      (.cons (.param (.array (.elem .bool) .none) (some .memory) (some "xs")) .nil)
      (some .internal) none .nil false none
      (.cons (.param (.array (.elem .bool) .none) (some .memory) (some "ys")) .nil) .none⟩
def referenceEnv : Source.Env := ⟨[referenceDecl]⟩
def referenceCandidate : Candidate referenceEnv [.array .memory .bool none]
    [.array .memory .bool none] none :=
  ⟨referenceDecl, List.mem_cons_self, rfl, rfl, by decide +kernel⟩
theorem reference_signature : referenceCandidate.declaration.fnSig referenceEnv =
    some ([.array .memory .bool none], [.array .memory .bool none]) := rfl

open Lowering.V08.SourceCallableControls in
theorem compiled_zero_refused (pipeline : Roadmap.Pipeline) :
    table.runArms (interpreterFrames pipeline 25) (Evm.wmod 0)
      (params true false, populated) table.code = none := rfl

def externalDecl : Source.Decl :=
  ⟨.function, "choose", some "C", false,
    .function (.ident "choose")
      (.cons (.param (.elem .bool) none (some "first"))
        (.cons (.param (.elem .bool) none (some "second")) .nil))
      (some .external) none .nil false none
      (.cons (.param (.elem .bool) none (some "answer")) .nil) .none⟩
def externalEnv : Source.Env := ⟨[externalDecl]⟩
theorem external_refused :
    Candidate.check (E := externalEnv) (ps := [.bool,.bool]) (rs := [.bool])
      (qualifier := none) externalDecl List.mem_cons_self = none := rfl

theorem duplicate_identity_refused :
    ¬ Function.Injective (fun (_ : Fin 2) => first.identity) := by
  intro injective
  have different : (0 : Fin 2) = (1 : Fin 2) := injective rfl
  have impossible : (0 : Nat) = 1 := congrArg Fin.val different
  cases impossible

theorem tag_capacity_refused (t : Table E [.bool,.bool] [.bool] none)
    (tooLarge : Evm.W ≤ t.size) : False := by
  have capacity := t.capacity
  omega

#print axioms compiled_source_run
#print axioms compiled_second_run
#print axioms wrong_result_refuted
#print axioms actual_source_and_selected_run
#print axioms second_guard_true
#print axioms actual_second_run
end Solidity.Backend.InternalDispatch.Controls
