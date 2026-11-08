import Solidity.Correctness.Lowering.Unchecked.WordProgram
import Solidity.Correctness.Lowering.Unchecked.WordOne
import Solidity.Correctness.Lowering.Unchecked.NamedOne
import Solidity.Syntax.Splice

/-!
# Actual-output word-association controls

Guards vacuous association acceptance, checked/wrapping confusion, ignoring an
extra statement, destination/old-value mismatch, the wrong increment amount,
shadowing/type lookup mistakes, and separate semantic proofs for +=1 and ++ spellings. These
controls run the actual quotation elaborator, then inspect its emitted typed
program. They do not prove arbitrary raw-input/Source association, pipeline
agreement, or the full pass certificate.
-/
namespace Solidity.Correctness.Lowering.Unchecked.WordProgramControls

private def Example : Contract := contract!{}

private def increment := sol[Example]{ uint x = 0; unchecked { x++; }; }
private def compound := sol[Example]{ uint x = 0; unchecked { x += 1; }; }
private def checking := sol[Example]{ uint x = 0; x += 1; }
private def byTwo := sol[Example]{ uint x = 0; unchecked { x += 2; }; }
private def redirected := sol[Example]{ uint x = 0; uint z = 0; unchecked { z = x + 1; }; }
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

/-- Select the actual suffix after both declarations in the redirected case. -/
private def bodyTwo (program : Prog Example [] [.val .uint, .val .uint]) :
    Prog Example [.val .uint, .val .uint] [.val .uint, .val .uint] :=
  match program with
  | .cons (.declLocal .uint _ _) (.cons (.declLocal .uint _ _) rest) => rest
  | _ => .nil

/-- The same actual output also passes destination/literal-one refinement. -/
theorem actual_increment_associated : (checkWordOne true (body increment)).isSome = true := by
  rfl

/-- Redirected addition is a general wrapping assignment, so its rejection by
`checkWordOne` below tests the old-value/destination check rather than shape. -/
theorem redirected_general_accepted : (checkWordProgram .add (bodyTwo redirected)).isSome = true := by
  rfl

/-- `z = x +% 1` cannot certify an increment of `z` when the slots differ. -/
theorem redirected_increment_rejected : (checkWordOne true (bodyTwo redirected)).isNone = true := by
  rfl

/-- Increment-by-two remains a general arithmetic assignment. -/
theorem by_two_general_accepted : (checkWordProgram .add (body byTwo)).isSome = true := by
  rfl

/-- The exact literal-one check cannot accept increment-by-two. -/
theorem by_two_increment_rejected : (checkWordOne true (body byTwo)).isNone = true := by
  rfl

/- A finite configurable parser keeps these binding regressions independent
of the standard prefix parser's string-scanner proof obligations. The checker
itself uses the production Var.ofName with its supplied instance unchanged. -/
local instance : FreshNames where
  name b k := s!"{b}{k}"
  parse spelling := if spelling = "ie1" then some ("ie", 1) else none

private def contextX : NCtx := [(.user "x", .val .uint)]
private def rawIncrement : RawStmt := .incDec .postInc (.name "x")
private def rawWrapping : RawStmt := .opAssign .addW (.name "x") (.num 1)

/-- All three supplied objects associate under the actual example context. -/
theorem named_actual_output_accepted :
    (checkNamedOne contextX rawIncrement rawWrapping (body increment)).isSome = true := by
  rfl

/-- A rewritten raw destination cannot silently change its initial name. -/
theorem raw_destination_rejected :
    (checkRawOne rawIncrement (.opAssign .addW (.name "z") (.num 1))).isNone = true := by
  rfl

/-- The raw-output check rejects checked addition independently of the target. -/
theorem raw_checked_operation_rejected :
    (checkRawOne rawIncrement (.opAssign .add (.name "x") (.num 1))).isNone = true := by
  rfl

/-- Every prefix/postfix token uses the same Boolean-indexed raw family. -/
theorem raw_increment_tokens_accepted (token : IncDec) :
    (checkRawOne (.incDec token (.name "x"))
      (.opAssign (if token.isIncrement then .addW else .subW) (.name "x") (.num 1))).isSome = true := by
  cases token <;> rfl

private def oldSlotProgram {Γ : Ctx} (slot : Idx Γ (.val .uint)) : Prog Example Γ Γ :=
  .cons (.assignLocal slot (.binop .addW rfl rfl (.simple (.local slot))
    (.simple (.lit 1 (by decide))))) .nil

private def shadowed : NCtx := [(.user "x", .val .uint), (.user "x", .val .uint)]

/-- The adversarial outer-slot program is otherwise a valid one-update shape. -/
theorem outer_slot_shape_accepted :
    (checkWordOne true (oldSlotProgram (Γ := shadowed.ctx) (.there .here))).isSome = true := by
  rfl

/-- A name at both positions must resolve to its newest slot, not any match. -/
theorem shadowed_outer_slot_rejected :
    (checkNamedOne shadowed rawIncrement rawWrapping
      (oldSlotProgram (Γ := shadowed.ctx) (.there .here))).isNone = true := by
  rfl

private def wrongType : NCtx := [(.user "x", .val .bool), (.user "x", .val .uint)]

/-- A wrong-typed newest binding must not be skipped to an older uint. -/
theorem shadowed_type_rejected :
    (checkNamedOne wrongType rawIncrement rawWrapping
      (oldSlotProgram (Γ := wrongType.ctx) (.there .here))).isNone = true := by
  rfl

section ParsedNames

private def parsedContext : NCtx :=
  [(.user "ie1", .val .uint), (.fresh "ie" 1, .val .uint)]
private def parsedInput : RawStmt := .incDec .postInc (.name "ie1")
private def parsedOutput : RawStmt := .opAssign .addW (.name "ie1") (.num 1)

/-- The configured parser reads ie1 as a fresh variable, even beside a same-spelled user slot. -/
theorem parsed_name_accepted :
    (checkNamedOne parsedContext parsedInput parsedOutput
      (oldSlotProgram (Γ := parsedContext.ctx) (.there .here))).isSome = true := by
  rfl

/-- A same-spelled user slot cannot replace the production fresh-name binding. -/
theorem parsed_user_slot_rejected :
    (checkNamedOne parsedContext parsedInput parsedOutput
      (oldSlotProgram (Γ := parsedContext.ctx) .here)).isNone = true := by
  rfl

local instance : FreshNames where
  name b k := s!"{b}{k}"
  parse spelling := if spelling = "idx1" then some ("ie", 1) else none

private def customContext : NCtx :=
  [(.user "idx1", .val .uint), (.fresh "ie" 1, .val .uint)]
private def customInput : RawStmt := .incDec .postInc (.name "idx1")
private def customOutput : RawStmt := .opAssign .addW (.name "idx1") (.num 1)

/-- The supplied FreshNames instance participates in the production resolver. -/
theorem custom_parsed_name_accepted :
    (checkNamedOne customContext customInput customOutput
      (oldSlotProgram (Γ := customContext.ctx) (.there .here))).isSome = true := by
  rfl

/-- Custom aliases must not bypass fresh-name resolution via the user slot. -/
theorem custom_user_slot_rejected :
    (checkNamedOne customContext customInput customOutput
      (oldSlotProgram (Γ := customContext.ctx) .here)).isNone = true := by
  rfl

end ParsedNames

#print axioms compound_increment_same
#print axioms actual_output_accepted
#print axioms wrong_operator_rejected
#print axioms checked_output_rejected
#print axioms extra_statement_rejected
#print axioms actual_increment_associated
#print axioms redirected_general_accepted
#print axioms redirected_increment_rejected
#print axioms by_two_general_accepted
#print axioms by_two_increment_rejected
#print axioms named_actual_output_accepted
#print axioms raw_destination_rejected
#print axioms raw_checked_operation_rejected
#print axioms raw_increment_tokens_accepted
#print axioms outer_slot_shape_accepted
#print axioms shadowed_outer_slot_rejected
#print axioms shadowed_type_rejected
#print axioms parsed_name_accepted
#print axioms parsed_user_slot_rejected
#print axioms custom_parsed_name_accepted
#print axioms custom_user_slot_rejected

end Solidity.Correctness.Lowering.Unchecked.WordProgramControls
