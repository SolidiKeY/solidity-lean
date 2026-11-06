import Solidity.Yul.Compilation.NormalControl
import Solidity.Yul.Compilation.FramedConditional
/-! Framed compiler-model transport for the existing original-AST-indexed
normal-control derivation and unchanged emitted/selected code. Word-selected
leaves are transported to the signed selector before applying
`FramedWordLowering.lowering`; sequence and conditional cases compose those
certificates. Source/G24, physical/native/resource and function/loop/divergence
closure remain open. -/
namespace Solidity.Yul.Compilation.NormalFramedTransport
open Backend Scalar Selection MachineAdapter

/-- The signed adapter conservatively contains every actual word selection. -/
theorem word_instruction (i : Backend.Instr) (j : Evm.Instr)
 (selected : WordMachine.selectInstr i = some j) : SignedMachine.selectInstr i = some j := by
 cases i with
 | push width bytes => exact selected
 | op opcode => cases opcode <;> first | exact selected | cases selected

theorem word_selection (p : Backend.Program) (code : List Evm.Instr)
 (selected : WordMachine.selectCode p = some code) : SignedMachine.selectCode p = some code := by
 induction p generalizing code with
 | nil => cases selected; rfl
 | cons i p ih =>
   obtain ⟨j,hi,rest⟩ := Option.bind_eq_some_iff.mp selected
   obtain ⟨q,hq,same⟩ := Option.map_eq_some_iff.mp rest
   subst code
   change (SignedMachine.selectInstr i).bind (fun k => (SignedMachine.selectCode p).map (fun tail => k::tail)) = _
   rw [word_instruction i j hi,ih q hq]
   rfl

def word_leaf (p : Backend.Program) (code : List Evm.Instr)
 (selected : WordMachine.selectCode p = some code) : FramedLoweringCertificate code (.code p) :=
 FramedWordLowering.lowering p code (word_selection p code selected)

/-- Every successfully emitted/selected existing normal-control derivation has
a framed lowering certificate whose leaves use the signed-selector transport
in `word_leaf`. Recursive cases reuse the same source AST index and actual
component emissions; no component-correctness blanket is an
input parameter and no failure/admission/native coverage is inferred. -/
def certificate {c n fuel} {stmt : Solidity.Yul.Stmt [] [] c n}
 (compiled : NormalControl.Derivation fuel stmt) (depth : Nat)
 (block : Backend.Block) (code : List Evm.Instr)
 (emitted : compiled.emit depth = some block)
 (selected : WordControl.blockCode block = some code) : FramedLoweringCertificate code block := by
 induction compiled generalizing block code with
 | scalar leaf =>
   change (leaf.lowered.code depth).map Backend.Block.code = some block at emitted
   obtain ⟨p,hp,same⟩ := Option.map_eq_some_iff.mp emitted
   subst block
   exact word_leaf p code selected
 | seq first second ihFirst ihSecond =>
   change ((first.emit depth).bind (fun a => (second.emit depth).bind (fun b => some (.seq a b)))) = some block at emitted
   obtain ⟨a,ha,rest⟩ := Option.bind_eq_some_iff.mp emitted
   obtain ⟨b,hb,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   obtain ⟨qa,hqa,rest⟩ := Option.bind_eq_some_iff.mp selected
   obtain ⟨qb,hqb,same⟩ := Option.map_eq_some_iff.mp rest
   subst code
   exact FramedControl.seq (ihFirst a qa ha hqa) (ihSecond b qb hb hqb)
 | branch condition arm ih =>
   change ((condition.lowered.code depth).bind (fun p => (arm.emit depth).bind (fun b => some (.ite p b (.code []))))) = some block at emitted
   obtain ⟨p,hp,rest⟩ := Option.bind_eq_some_iff.mp emitted
   obtain ⟨b,hb,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   obtain ⟨qc,hc,rest⟩ := Option.bind_eq_some_iff.mp selected
   obtain ⟨qa,ha,rest⟩ := Option.bind_eq_some_iff.mp rest
   obtain ⟨qb,hqb,same⟩ := Option.map_eq_some_iff.mp rest
   have empty : qb = [] := (Option.some.inj hqb).symm
   subst qb
   subst code
   exact FramedConditional.conditional (word_leaf p qc hc) (ih b qa hb ha) (word_leaf [] [] rfl)


/-- The existing complete numeric representation agrees with physical words;
no symbolic slots are coerced into this relation. -/
theorem irStack_words (input : Stack) : irStack input = input.map coreWord := by
 induction input with
 | nil => rfl
 | cons word rest ih => rw [FramedConditional.irStack_cons,List.map_cons,ih]

/-- info: 'Solidity.Yul.Compilation.NormalFramedTransport.irStack_words' depends on axioms: [propext] -/
#guard_msgs in
#print axioms irStack_words
/-- info: 'Solidity.Yul.Compilation.NormalFramedTransport.word_instruction' does not depend on any axioms -/
#guard_msgs in
#print axioms word_instruction
/-- info: 'Solidity.Yul.Compilation.NormalFramedTransport.word_selection' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms word_selection
/-- info: 'Solidity.Yul.Compilation.NormalFramedTransport.word_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms word_leaf
/-- info: 'Solidity.Yul.Compilation.NormalFramedTransport.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certificate
end Solidity.Yul.Compilation.NormalFramedTransport
