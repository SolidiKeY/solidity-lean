import Solidity.Yul.Compilation.FramedLoop
/-! Concrete strong certificates for every block selected by the EXISTING word
control adapter. Only existing Block/StructuredExec/selector interfaces are
used. This closes model finite-success correspondence, not source admission,
Source/G24, physical/native resources or source/native divergence adequacy. -/
namespace Solidity.Yul.Compilation.WordBlockFramed
open Backend Scalar Selection

/-- Structural proof consumer over existing target blocks, not a second
compiler/evaluator. Every body/arm certificate is constructed recursively from
actual component selections; no producer callback or simulation law is assumed. -/
def certificate (block : Backend.Block) (code : List Evm.Instr)
 (selected : WordControl.blockCode block = some code) : FramedLoweringCertificate code block := by
 induction block generalizing code with
 | code p => exact NormalFramedTransport.word_leaf p code selected
 | seq a b ihA ihB =>
   obtain ⟨qa,ha,rest⟩ := Option.bind_eq_some_iff.mp selected
   obtain ⟨qb,hb,same⟩ := Option.map_eq_some_iff.mp rest
   subst code
   exact FramedControl.seq (ihA qa ha) (ihB qb hb)
 | ite c a b ihA ihB =>
   obtain ⟨qc,hc,rest⟩ := Option.bind_eq_some_iff.mp selected
   obtain ⟨qa,ha,rest⟩ := Option.bind_eq_some_iff.mp rest
   obtain ⟨qb,hb,same⟩ := Option.map_eq_some_iff.mp rest
   subst code
   exact FramedConditional.conditional (NormalFramedTransport.word_leaf c qc hc) (ihA qa ha) (ihB qb hb)
 | loop c b ih =>
   obtain ⟨qc,hc,rest⟩ := Option.bind_eq_some_iff.mp selected
   obtain ⟨qb,hb,same⟩ := Option.map_eq_some_iff.mp rest
   subst code
   exact FramedLoop.loop hc hb (ih qb hb)

/-- Every successful actual selected run, including loop success, yields the
finite original structured trace and entire numeric machine frame. -/
theorem reflected (block : Backend.Block) (code : List Evm.Instr)
 (selected : WordControl.blockCode block = some code)
 (input : Stack) (initial final : Evm.Machine) (skip : Nat)
 (represented : initial.stack = irStack input)
 (ran : Evm.run code initial = .ok final skip) :
 ∃ output : Stack, skip = 0 ∧ final = {initial with stack := irStack output} ∧
 StructuredExec block input output :=
 (certificate block code selected).reflect input initial final skip represented ran

/-- info: 'Solidity.Yul.Compilation.WordBlockFramed.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certificate
/-- info: 'Solidity.Yul.Compilation.WordBlockFramed.reflected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reflected
end Solidity.Yul.Compilation.WordBlockFramed
