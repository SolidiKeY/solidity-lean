import Solidity.Correctness.Lowering.Checker.WhileBreak
import Solidity.Syntax.Splice

/-! H151 measured pilot against lowerLoops at the pinned base. The exact
accepted raw fragment is a singleton: RawProbe.input, its fixed incoming
state and actual captured output. This is deliberately not the larger raw
family recognized by checkRaw, nor a generic accepted-triple checker.
The concrete contract below exercises the real function-call elaboration
pipeline separately; its replay timing is not checker-wide soundness. -/
namespace Solidity.Correctness.Lowering.Checker.MeasuredPilot

/-- Total exact-shape recognizer. Unsupported syntax is visibly refused. -/
def check (output : List RawStmt) : Bool :=
  match output with
  | [.block [.decl (.named "bool") "brk1" (some (.bool false)),
      .loop ⟨[], none, none, false, []⟩
        (.binop .and (.unop .not (.name "brk1")) (.bool true))
        [.ite (.unop .not (.assign (.name "i") (.name "a")))
          [.assign (.name "brk1") (.bool true)] [],
         .ite (.unop .not (.name "brk1"))
          [.block [.assign (.name "brk1") (.bool true)]] []]]] => true
  | _ => false

/-- Completeness for the exact captured output, not arbitrary producer runs. -/
theorem complete (output : List RawStmt) (h : output = RawProbe.actual.raw) :
    check output = true := by
  cases h
  decide

/-- No different raw output is accepted by this singleton checker. -/
theorem accepts_iff (output : List RawStmt) :
    check output = true ↔ output = RawProbe.actual.raw := by
  constructor
  · intro h
    unfold check at h
    split at h
    · rfl
    · cases h
  · exact complete output

/-- Soundness reuses the existing mapped G19 bridge, including the actual
resolved Source conversion and actual intrinsic Prog. Input, context, memo
and counters are fixed by RawProbe/IntrinsicProbe, not freely quantified.
No association of an arbitrary supplied Prog with raw syntax is asserted. -/
theorem sound {E : Source.Env} (G : Source.Glob E) (F : Source.Fr)
    (fuel nps : Nat) (ph : Option (Source.Ph E)) (st : Source.St E)
    (choice : Bool) (output : List RawStmt) (h : check output = true) :
    output = RawProbe.actual.raw ∧ WhileBreak.MappedEndpoint G F fuel nps ph st choice := by
  exact ⟨(accepts_iff output).mp h,
    WhileBreak.prototype_mapped_sound G F fuel nps ph st choice⟩

/-- Corrupting the actual output is refused, not silently normalized. -/
theorem negative : check (RawProbe.corruptFlag RawProbe.actual.raw) = false := by
  decide

/-- Concrete Solidity contract, with a public scalar function and an actual
while/assignment/break leaf. This is a synthetic pilot fixture, not a claim
of coverage for a published third-party contract or storage effects. -/
def realContract : Contract := contract!{
  function pilot(bool a) public returns (bool r) {
    bool i = false;
    while ((i = a)) { break; }
    r = i;
  }
}

open Lean Elab Term in
elab "capture_pilot_contract_lowering%" : term => do
  let some (_, declaration) := realContract.funs.head? |
    throwError "pilot contract has no function"
  let scope : ElabScope := { funs := realContract.funs }
  let result := (((lowerLoops (some ["r"]) declaration.body).run scope).run
    ([("r", .val .bool), ("a", .val .bool)], 1)).run {}
  let .ok ((output, _), _) := result | throwError "lowerLoops refused pilot contract"
  let .ok quoted := RawProbe.quoteStmts output |
    throwError "pilot contract lowering is outside the refusing data quoter"
  return quoted

/-- Actual lowerLoops output for the contract function body, before the
subsequent return/call transformations. The kernel sees the captured data. -/
def contractLowered : List RawStmt := capture_pilot_contract_lowering%

/-- Coverage failure on the actual contract body: the singleton checker
refuses declarations and the post-loop assignment. This is decisive NO-GO
evidence for this pilot, not a proof that a broader P1 checker is impossible. -/
theorem rejects_contract : check contractLowered = false := by
  decide

/-- Each invocation is produced by actual contract/function elaboration,
which calls lowerLoops; no G19 code is substituted. -/
def invocation (choice : Bool) : Prog realContract [] [.val .bool] :=
  if choice then sol[realContract]{ bool result = pilot(true); }
  else sol[realContract]{ bool result = pilot(false); }

/-- Finite replay establishes successful return on both pilot paths. The
kernel checks this theorem; no native evaluator is used. -/
theorem contract_replay (choice : Bool) :
    (Prog.runFC 16 (invocation choice) (State.init realContract)).isOk = true := by
  cases choice <;> decide +kernel

/-- Return-value evidence, not merely successful execution. -/
theorem contract_replay_value (choice : Bool) :
    WhileBreak.successValue
      (fun out : Out realContract [] [.val .bool] => (TEnv.get .here out.st.env : Bool))
      (Prog.runFC 16 (invocation choice) (State.init realContract)) = some choice := by
  cases choice <;> decide +kernel

/-- Successful replay lifts to the actual unbounded model; 16 is a replay
budget, not physical gas, a Source horizon or a general termination bound. -/
theorem contract_value (choice : Bool) :
    WhileBreak.successValue
      (fun out : Out realContract [] [.val .bool] => (TEnv.get .here out.st.env : Bool))
      ((invocation choice).run (State.init realContract)) = some choice := by
  exact WhileBreak.replay_observation_sound (invocation choice) 16
    (State.init realContract) _ choice (contract_replay_value choice)

#print axioms contract_replay_value
#print axioms contract_value
#print axioms rejects_contract
#print axioms complete
#print axioms accepts_iff
#print axioms sound
#print axioms negative
#print axioms contract_replay
end Solidity.Correctness.Lowering.Checker.MeasuredPilot
