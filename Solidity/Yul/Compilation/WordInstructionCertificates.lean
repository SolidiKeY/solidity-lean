import Solidity.Yul.Compilation.WordClosedExecution
import Solidity.Backend.Selection.Interface
/-! Concrete producers of the EXISTING instruction/lowering contracts used
by P20.InterfaceV1. Closed numeric inputs and exact supplied backend code stay
explicit. This does not define a new P20 interface or supply PendingG24,
Input/Rep, source embedding, physical/native/charged adequacy or capacity. -/
namespace Solidity.Yul.Compilation.WordInstructionCertificates
open Backend Scalar Selection MachineAdapter

private theorem irStack_words (s : Stack) : irStack s = s.map coreWord := by
 apply List.map_congr_left
 intro w _
 apply congrArg Evm.Word.val
 apply Fin.ext
 change w.toNat % Evm.W = w.toNat
 exact Nat.mod_eq_of_lt w.isLt

private theorem singleton_run (i : Evm.Instr) (m : Evm.Machine) : Evm.run [i] m = i.step m := by
 change (i.step m).bind (fun next pending => Evm.exec [] pending next) = _
 cases i.step m <;> rfl

private theorem singleton_selected (i : Backend.Instr) (j : Evm.Instr)
 (selected : WordMachine.selectInstr i = some j) : WordMachine.selectCode [i] = some [j] := by
 change ((WordMachine.selectInstr i).bind (fun k => some [k])) = some [j]
 rw [selected]
 rfl

/-- Both required fields are proved on the actual closed numeric relation.
The certificate code is the supplied instruction, never a canonical replacement. -/
def instruction (i : Backend.Instr) (j : Evm.Instr)
 (selected : WordMachine.selectInstr i = some j) : InstructionCertificate j where
 code := [i]
 success := by
   intro input output m represented
   have law := WordClosedExecution.success_iff [i] [j] (singleton_selected i j selected) input output m
   rw [←irStack_words input,←irStack_words output] at law
   have same : {m with stack := irStack input} = m := by rw [←represented]
   rw [same,singleton_run] at law
   exact law
 refusal := by
   intro input m represented
   have law := WordClosedExecution.failure_iff [i] [j] (singleton_selected i j selected) input m
   rw [←irStack_words input] at law
   have same : {m with stack := irStack input} = m := by rw [←represented]
   rw [same,singleton_run] at law
   exact law

theorem instruction_origin (i : Backend.Instr) (j : Evm.Instr)
 (selected : WordMachine.selectInstr i = some j) : (instruction i j selected).code = [i] := rfl

/-- A real leaf lowering certificate for every actual word selection. This
is model-level iff on the original closed numeric relation, not G24 adequacy. -/
def lowering (p : Backend.Program) (q : List Evm.Instr)
 (selected : WordMachine.selectCode p = some q) : LoweringCertificate q (.code p) where
 success := by
   intro input output m represented
   have law := WordClosedExecution.success_iff p q selected input output m
   rw [←irStack_words input,←irStack_words output] at law
   have same : {m with stack := irStack input} = m := by rw [←represented]
   rw [same] at law
   constructor
   · intro ran
     exact StructuredExec.code (law.mp ran)
   · intro actual
     cases actual with
     | code ran => exact law.mpr ran

/-- info: 'Solidity.Yul.Compilation.WordInstructionCertificates.instruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms instruction
/-- info: 'Solidity.Yul.Compilation.WordInstructionCertificates.instruction_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms instruction_origin
/-- info: 'Solidity.Yul.Compilation.WordInstructionCertificates.lowering' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms lowering
end Solidity.Yul.Compilation.WordInstructionCertificates
