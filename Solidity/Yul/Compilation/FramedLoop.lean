import Solidity.Yul.Compilation.NormalFramedTransport
import Solidity.Yul.Compilation.WordBlockExecution
/-! Reverse finite-success correspondence for the existing model loop.
An actual successful loop run supplies its own finite horizon, guards and body
traces. No source/native divergence or gas/capacity equivalence follows from
the model's default fault for noncompletion. No loop evaluator is changed. -/
namespace Solidity.Yul.Compilation.FramedLoop
open Backend Scalar Selection MachineAdapter

/-- Every successful actual iteration prefix recovers the original structured
loop trace and exact complete nonstack frame. Count is the existing horizon,
not a new proof budget or a bound on source/native termination. -/
theorem iteration_reflect {c : Backend.Program} {b : Backend.Block} {qc qb : List Evm.Instr}
 (condition : FramedLoweringCertificate qc (.code c)) (body : FramedLoweringCertificate qb b)
 (count : Nat) (input : Stack) (initial final : Evm.Machine) (skip : Nat)
 (represented : initial.stack = irStack input)
 (ran : Evm.loopIterN (Evm.run qc) (Evm.run qb) count initial = .inr (.ok final skip)) :
 ∃ output : Stack, skip = 0 ∧ final = {initial with stack := irStack output} ∧
 StructuredExec (.loop c b) input output := by
 induction count generalizing input initial with
 | zero => cases ran
 | succ count ih =>
   cases actualC : Evm.run qc initial with
   | revert => simp only [Evm.loopIterN,Evm.loopTurn,actualC] at ran; cases ran
   | fault => simp only [Evm.loopIterN,Evm.loopTurn,actualC] at ran; cases ran
   | ok middle pending =>
     cases pending with
     | succ pending => simp only [Evm.loopIterN,Evm.loopTurn,actualC] at ran; cases ran
     | zero =>
       obtain ⟨guarded,_,frame,conditionTrace⟩ := condition.reflect input initial middle 0 represented actualC
       have cRun : Scalar.run c input = some guarded := by
         cases conditionTrace with | code h => exact h
       rw [Evm.loopIterN,Evm.loopTurn,actualC,frame] at ran
       cases guarded with
       | nil => cases ran
       | cons word rest =>
         rw [FramedConditional.irStack_cons] at ran
         change (match (if word.toNat = 0 then
           .inr (.ok {initial with stack := irStack rest} 0)
           else match Evm.run qb {initial with stack := irStack rest} with
           | .ok next 0 => .inl next
           | .ok _ (_+1) => .inr .fault
           | result => .inr result : Evm.Machine ⊕ Evm.Out) with
          | .inl next => Evm.loopIterN (Evm.run qc) (Evm.run qb) count next
          | .inr result => .inr result) = .inr (.ok final skip) at ran
         by_cases zero : word = 0
         · subst word
           change Sum.inr (Evm.Out.ok {initial with stack := irStack rest} 0) = Sum.inr (Evm.Out.ok final skip) at ran
           have parts := Evm.Out.ok.inj (Sum.inr.inj ran)
           exact ⟨rest,parts.2.symm,parts.1.symm,StructuredExec.loopDone cRun⟩
         · have nz : word.toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
           rw [if_neg nz] at ran
           cases actualB : Evm.run qb {initial with stack := irStack rest} with
           | revert => rw [actualB] at ran; cases ran
           | fault => rw [actualB] at ran; cases ran
           | ok next pending =>
             cases pending with
             | succ pending => rw [actualB] at ran; cases ran
             | zero =>
               rw [actualB] at ran
               change Evm.loopIterN (Evm.run qc) (Evm.run qb) count next = .inr (.ok final skip) at ran
               obtain ⟨updated,_,bodyFrame,bodyTrace⟩ := body.reflect rest
                 {initial with stack := irStack rest} next 0 rfl actualB
               obtain ⟨output,done,finalFrame,remaining⟩ := ih updated next
                 (congrArg Evm.Machine.stack bodyFrame) ran
               rw [bodyFrame] at finalFrame
               exact ⟨output,done,finalFrame,StructuredExec.loopMore cRun zero bodyTrace remaining⟩

theorem singleton_run (qc qb : List Evm.Instr) (initial : Evm.Machine) :
 Evm.run [.loop qc qb] initial = Evm.loopRun (Evm.run qc) (Evm.run qb) initial := by
 change (Evm.loopRun (Evm.run qc) (Evm.run qb) initial).bind (fun m k => Evm.exec [] k m) = _
 cases Evm.loopRun (Evm.run qc) (Evm.run qb) initial <;> rfl

/-- Whole successful loop execution derives its finite iteration witness; no
finite-prefix, termination or favourable guard premise is supplied by callers. -/
theorem reflect {c : Backend.Program} {b : Backend.Block} {qc qb : List Evm.Instr}
 (condition : FramedLoweringCertificate qc (.code c)) (body : FramedLoweringCertificate qb b)
 (input : Stack) (initial final : Evm.Machine) (skip : Nat)
 (represented : initial.stack = irStack input)
 (ran : Evm.run [.loop qc qb] initial = .ok final skip) :
 ∃ output : Stack, skip = 0 ∧ final = {initial with stack := irStack output} ∧
 StructuredExec (.loop c b) input output := by
 rw [singleton_run] at ran
 by_cases ends : ∃ result count, Evm.loopIterN (Evm.run qc) (Evm.run qb) count initial = .inr result
 · obtain ⟨result,count,actual⟩ := ends
   have same : result = .ok final skip := (Evm.loopRun_of_iterN actual).symm.trans ran
   exact iteration_reflect condition body count input initial final skip represented
     (actual.trans (congrArg Sum.inr same))
 · simp only [Evm.loopRun,ends,↓reduceDIte] at ran
   cases ran

/-- Existing word selections supply concrete forward execution; reverse success
uses the actual strong body certificate. The later recursive block consumer
discharges that body input constructively. No native/source adequacy is inferred. -/
def loop {c : Backend.Program} {b : Backend.Block} {qc qb : List Evm.Instr}
 (conditionSelection : WordMachine.selectCode c = some qc)
 (bodySelection : WordControl.blockCode b = some qb)
 (body : FramedLoweringCertificate qb b) : FramedLoweringCertificate [.loop qc qb] (.loop c b) where
 reflect := reflect (NormalFramedTransport.word_leaf c qc conditionSelection) body
 success := by
   intro input output initial represented
   constructor
   · intro ran
     obtain ⟨actual,_,frame,trace⟩ := reflect (NormalFramedTransport.word_leaf c qc conditionSelection)
       body input initial _ 0 represented ran
     have same : output = actual := irStack_injective (congrArg Evm.Machine.stack frame)
     simpa only [same] using trace
   · intro trace
     have selected : WordControl.blockCode (.loop c b) = some [.loop qc qb] := by
       change (WordMachine.selectCode c).bind (fun q => (WordControl.blockCode b).map (fun r => [Evm.Instr.loop q r])) = _
       rw [conditionSelection,bodySelection]
       rfl
     have law := WordBlockExecution.execute trace [.loop qc qb] selected initial []
     simp only [List.append_nil] at law
     rw [←NormalFramedTransport.irStack_words input,←NormalFramedTransport.irStack_words output] at law
     have same : {initial with stack := irStack input} = initial := by rw [←represented]
     rw [same] at law
     exact law

/-- info: 'Solidity.Yul.Compilation.FramedLoop.singleton_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms singleton_run
/-- info: 'Solidity.Yul.Compilation.FramedLoop.iteration_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms iteration_reflect
/-- info: 'Solidity.Yul.Compilation.FramedLoop.reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reflect
/-- info: 'Solidity.Yul.Compilation.FramedLoop.loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loop
end Solidity.Yul.Compilation.FramedLoop
