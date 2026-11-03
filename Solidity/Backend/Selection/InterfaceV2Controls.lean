import Solidity.Backend.Selection.FrameCapacityV2
import Solidity.Backend.Selection.PremisesV2

/-! Inhabited and negative V2 controls, including an actual 1025-PUSH
counterexample accepted by V1's gasless contract and excluded by V2. These
are contract controls, not a source/runtime agreement or a G49.02 proof. -/
namespace Solidity.Backend.Selection.V2.Controls

/-- The existing Osaka PUSH0 encoding, not a synthetic stack operation. -/
def zeroPush : Instr := .push 0 #v[]

/-- The gasless numeric evaluator really accepts an arbitrary number of PUSHes. -/
theorem run_zero_pushes (n : Nat) (tail : Scalar.Stack) :
    Scalar.run (List.replicate n zeroPush) tail =
      some (List.replicate n (0 : Scalar.Word) ++ tail) := by
  induction n generalizing tail with
  | zero => rfl
  | succ n ih =>
    change Scalar.run (List.replicate n zeroPush) (0 :: tail) =
      some (List.replicate (n+1) (0 : Scalar.Word) ++ tail)
    rw [ih, List.replicate_succ', List.append_assoc]
    rfl

/-- Reproduce the confirmed V1 defect; never used as a V2 capacity premise. -/
def legacyOverflow : Solidity.Backend.Selection.FrameCertificate []
    (List.replicate 1025 (0 : Scalar.Word)) where
  code := List.replicate 1025 zeroPush
  frame := run_zero_pushes 1025
  prefixes := by
    intro tail bound before after reached split ran
    apply Scalar.prefix_capacity before after ran
    rw [split]
    exact bound

/-- The same overfull output has no V2 certificate, regardless of peak/code. -/
theorem reject_overflow : ¬ Nonempty
    (FrameCertificate [] (List.replicate 1025 (0 : Scalar.Word))) := by
  apply no_overfull_output
  simp only [List.length_replicate]
  decide

/-- Reject the offending program itself, independently of its declared output. -/
theorem reject_push_program {input output : Scalar.Stack}
    (c : FrameCertificate input output)
    (bad : c.code = List.replicate 1025 zeroPush) : False := by
  have ran : Scalar.run c.code input =
      some (List.replicate 1025 (0 : Scalar.Word) ++ input) := by
    rw [bad]
    exact run_zero_pushes 1025 input
  have bound : (List.replicate 1025 (0 : Scalar.Word) ++ input).length ≤ 1024 :=
    Scalar.run_capacity ran c.capacity_empty
  simp only [List.length_append, List.length_replicate] at bound
  omega

/-- A nonempty protected frame, with a real one-word DUP peak. -/
example : Scalar.run (duplicateHead 7).code ([7] ++ [11,99]) =
    some ([7,7] ++ [11,99]) := (duplicateHead 7).frame [11,99]

example : Scalar.stackBound (duplicateHead 7).code 1023 = true := by decide
example : Scalar.stackBound (duplicateHead 7).code 1024 = false := by decide
example : (identityFrame ([] : Scalar.Stack) (by decide)).peak = 0 := rfl

/-- Explicit nonempty producer control over the existing no-op IR runner.
This is not an instantiation of the unfinished source/compiler theorem. -/
def identityCompiler : CompilerPremise Unit (fun _ => ()) []
    (fun _ initial final => final = initial) where
  inhabited := ⟨0,Evm.Machine.init,Evm.Machine.init,rfl⟩
  preserves := by
    intro _ initial final same
    cases same
    rfl

/-- The runtime witness domain has an actual successful numeric no-op case;
this does not construct a RuntimeConsumer or assume Bridge agreement. -/
theorem runtime_witness_inhabited : ∃ (budget : Nat) (m : Evm.Machine)
    (s t : Scalar.Stack), s.length = 0 ∧ m.stack = irStack s ∧
      { m with stack := irStack t } = m ∧
      Evm.run [] m = .ok { m with stack := irStack t } 0 :=
  ⟨0,Evm.Machine.init,[],[],rfl,rfl,rfl,rfl⟩

/-- The review's incorrect final-stack example cannot be the V2 IR witness. -/
theorem reject_wrong_ir_result : Evm.run [] Evm.Machine.init ≠
    .ok { Evm.Machine.init with stack := irStack [0] } 0 := by
  intro bad
  have lengths : (0 : Nat) = 1 := congrArg
    (fun outcome => match outcome with
      | .ok m _ => m.stack.length
      | _ => 0) bad
  omega

/-- A constantly-false observation relation cannot inhabit the V2 producer. -/
theorem reject_false_compiler (Observation : Type) (source : Nat → Observation)
    (ir : List Evm.Instr) : ¬ Nonempty
      (CompilerPremise Observation source ir (fun _ _ _ => False)) := by
  rintro ⟨c⟩
  obtain ⟨_,_,_,bad⟩ := c.inhabited
  exact bad

/-- The consumer independently rejects an empty relation, even before any
compiler/decoder premise is supplied. No runtime theorem is proved. -/
theorem reject_false_runtime (Observation : Type) (source : Nat → Observation)
    (ir : List Evm.Instr) (b : Block) (input output : Nat)
    (composition : CompositionCertificate ir b input output)
    (bridgeStep : LabelExec.State → Option LabelExec.State)
    (bridgeRun : Nat → LabelExec.State → Option LabelExec.State)
    (reachable : LabelExec.State → Prop) : ¬ Nonempty
      (RuntimeConsumer Observation source ir (fun _ _ _ => False) b input output
        composition bridgeStep bridgeRun reachable) := by
  rintro ⟨c⟩
  obtain ⟨_,_,_,_,_,_,bad,_⟩ := c.inhabited
  exact bad

#print axioms run_zero_pushes
#print axioms reject_overflow
#print axioms reject_push_program
#print axioms reject_false_compiler
#print axioms reject_false_runtime
#print axioms identityCompiler
#print axioms legacyOverflow
#print axioms runtime_witness_inhabited
#print axioms reject_wrong_ir_result

end Solidity.Backend.Selection.V2.Controls
