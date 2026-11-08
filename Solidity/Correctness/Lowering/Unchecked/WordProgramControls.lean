import Solidity.Correctness.Lowering.Unchecked.WordProgram
import Solidity.Syntax.Splice

/-!
# Actual-output word-association controls

Guards vacuous association acceptance, checked/wrapping confusion, ignoring an
extra statement, and separate semantic proofs for +=1 and ++ spellings. These
controls run the actual quotation elaborator, then inspect its emitted typed
program. They do not prove arbitrary raw-input/Source association, pipeline
agreement, or the full pass certificate.
-/
namespace Solidity.Correctness.Lowering.Unchecked.WordProgramControls

private def Example : Contract := contract!{}

private def increment := sol[Example]{ uint x = 0; unchecked { x++; }; }
private def compound := sol[Example]{ uint x = 0; unchecked { x += 1; }; }
private def checking := sol[Example]{ uint x = 0; x += 1; }
private def repeated := sol[Example]{ uint x = 0; unchecked { x++; x++; }; }

/-- Select the actual suffix after the example's initial declaration.
Unexpected headers become nil, which the association checker rejects. -/
private def body (program : Prog Example [] [.val .uint]) :
    Prog Example [.val .uint] [.val .uint] :=
  match program with
  | .cons (.declLocal .uint _ _) rest => rest
  | _ => .nil

/-- Both actual producer spellings reach one emitted typed program. -/
theorem compound_increment_same : compound = increment := by
  rfl

/-- The total checker accepts the actual emitted increment body. -/
theorem actual_output_accepted : (checkWordProgram .add (body increment)).isSome = true := by
  rfl

/-- A different requested Source operator cannot certify that output. -/
theorem wrong_operator_rejected : (checkWordProgram .sub (body increment)).isNone = true := by
  rfl

/-- A checked addition is not a wrapping output, even though input zero would
make either run succeed. This is a structural mode check, not a sampled run. -/
theorem checked_output_rejected : (checkWordProgram .add (body checking)).isNone = true := by
  rfl

/-- The checker must not certify only the first statement of a longer output. -/
theorem extra_statement_rejected : (checkWordProgram .add (body repeated)).isNone = true := by
  rfl

#print axioms compound_increment_same
#print axioms actual_output_accepted
#print axioms wrong_operator_rejected
#print axioms checked_output_rejected
#print axioms extra_statement_rejected

end Solidity.Correctness.Lowering.Unchecked.WordProgramControls
