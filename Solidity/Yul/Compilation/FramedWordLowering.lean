import Solidity.Yul.Compilation.SignedInstructionCertificates
import Solidity.Yul.Compilation.ProducerStatements
import Solidity.Backend.Selection.FramedLoweringInterface
/-! Concrete leaf producer for the published framed lowering contract. Every
actual successful selected numeric run is reflected, with exact final machine
and zero pending skip. Closed numeric stacks are essential: arbitrary symbolic
caller words are not represented by this result. No Source/G24, native byte,
gas, capacity, physical view or recursive-control adequacy is supplied. -/
namespace Solidity.Yul.Compilation.FramedWordLowering
open Backend Scalar Selection MachineAdapter

private theorem irStack_words (s : Stack) : irStack s = s.map coreWord := by
 apply List.map_congr_left
 intro w _
 apply congrArg Evm.Word.val
 apply Fin.ext
 change w.toNat % Evm.W = w.toNat
 exact Nat.mod_eq_of_lt w.isLt

/-- Actual producer, not another interface or an assumed reflection law. -/
def lowering (p : Backend.Program) (q : List Evm.Instr)
 (selected : SignedMachine.selectCode p = some q) : FramedLoweringCertificate q (.code p) where
 toLoweringCertificate := SignedInstructionCertificates.lowering p q selected
 reflect := by
   intro input initial final skip represented ran
   have law := SignedClosedExecution.run p q selected input initial
   rw [←irStack_words input] at law
   have same : {initial with stack := irStack input} = initial := by rw [←represented]
   rw [same,ran] at law
   cases actual : Scalar.run p input with
   | none => rw [actual] at law; cases law
   | some output =>
     rw [actual] at law
     simp only [] at law
     rw [←irStack_words output] at law
     have equal := Evm.Out.ok.inj law
     exact ⟨output,equal.2,equal.1,StructuredExec.code actual⟩

/-- A selected original intrinsic expression has no hidden successful result:
its actual compiler update determines the reflected stack and entire frame.
The actual initial numeric representation and successful emission remain real
premises; native validity/capacity is deliberately not inferred. -/
theorem expression_reflect {fuel n depth r : Nat} {expr : Solidity.Yul.Expr [] [] n r}
 (compiled : ProducerExpressions.Compiled fuel expr) (p : Backend.Program) (q : List Evm.Instr)
 (emitted : compiled.lowered.code depth = some p)
 (selected : SignedMachine.selectCode p = some q)
 (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth) (tail : Stack)
 (initial final : Evm.Machine) (skip : Nat)
 (represented : initial.stack = irStack (newer.toList++locals.toList++tail))
 (ran : Evm.run q initial = .ok final skip) :
 skip = 0 ∧ final = {initial with stack := irStack (compiled.value locals::(newer.toList++locals.toList++tail))} := by
 obtain ⟨output,zero,frame,execution⟩ := (lowering p q selected).reflect _ initial final skip represented ran
 have source := compiled.lowered.correct depth p emitted locals newer tail
 cases execution with
 | code actual =>
   have same : output = compiled.value locals::(newer.toList++locals.toList++tail) :=
     Option.some.inj (actual.symm.trans (by simpa only [List.append_assoc] using source))
   exact ⟨zero,frame.trans (congrArg (fun s => {initial with stack := irStack s}) same)⟩

/-- info: 'Solidity.Yul.Compilation.FramedWordLowering.lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowering
/-- info: 'Solidity.Yul.Compilation.FramedWordLowering.expression_reflect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms expression_reflect

/-- Original intrinsic statement compilation determines every successful model
result, including local writes/scopes/sequences in the supplied compiler
certificate. This is neither admission nor Source/G24 simulation. -/
theorem statement_reflect {fuel n depth : Nat} {c : Solidity.Yul.Control}
 {stmt : Solidity.Yul.Stmt [] [] c n}
 (compiled : ProducerStatements.Compiled fuel stmt) (p : Backend.Program) (q : List Evm.Instr)
 (emitted : compiled.lowered.code depth = some p)
 (selected : SignedMachine.selectCode p = some q)
 (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth) (tail : Stack)
 (initial final : Evm.Machine) (skip : Nat)
 (represented : initial.stack = irStack (newer.toList++locals.toList++tail))
 (ran : Evm.run q initial = .ok final skip) :
 skip = 0 ∧ final = {initial with stack := irStack (newer.toList++(compiled.update locals).toList++tail)} := by
 obtain ⟨output,zero,frame,execution⟩ := (lowering p q selected).reflect _ initial final skip represented ran
 have source := compiled.lowered.correct depth p emitted locals newer tail
 cases execution with
 | code actual =>
   have same : output = newer.toList++(compiled.update locals).toList++tail :=
     Option.some.inj (actual.symm.trans (by simpa only [List.append_assoc] using source))
   exact ⟨zero,frame.trans (congrArg (fun s => {initial with stack := irStack s}) same)⟩

/-- info: 'Solidity.Yul.Compilation.FramedWordLowering.statement_reflect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms statement_reflect
end Solidity.Yul.Compilation.FramedWordLowering
