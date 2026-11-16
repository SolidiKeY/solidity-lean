import Solidity.Syntax.Raw

/-!
# Supplied raw compound-one/increment association

Guards an operation/name mismatch between the initial raw statement and its
supplied rewritten output. These total recognizers inspect both actual trees;
they do not unfold or totalize the partial producer. Certificates contain
syntax facts only. Source typing/bindings, actual final intrinsic elaboration,
errors/effects and the prescribed semantic endpoint remain separate obligations.
-/
namespace Solidity.Correctness.Lowering.Unchecked

/-- Recognized initial spelling, retaining the actual input tree. -/
structure RawOneInput (input : RawStmt) where
  inc : Bool
  name : String
  spelling : input = .opAssign (if inc then .add else .sub) (.name name) (.num 1) ∨
    ∃ token : IncDec, token.isIncrement = inc ∧ input = .incDec token (.name name)

/-- Total recognition of the two compound-one and four increment spellings.
Other inputs remain an explicit coverage gap, not a final source exclusion. -/
def checkRawOneInput : (input : RawStmt) → Option (RawOneInput input)
  | .opAssign .add (.name name) (.num 1) => some ⟨true, name, .inl rfl⟩
  | .opAssign .sub (.name name) (.num 1) => some ⟨false, name, .inl rfl⟩
  | .incDec token (.name name) => some ⟨token.isIncrement, name, .inr ⟨token, rfl, rfl⟩⟩
  | _ => none

/-- Static association to the actual supplied rewritten tree. -/
structure RawOneAssociation (input output : RawStmt) where
  source : RawOneInput input
  rewritten : output = .opAssign (if source.inc then .addW else .subW)
    (.name source.name) (.num 1)

/-- Total validation of this supplied raw-output family. No producer equation
or semantic-correctness proof is an input. The wrapping operation, destination
name and literal-one RHS are all inspected. -/
def checkRawOne (input output : RawStmt) : Option (RawOneAssociation input output) := do
  let source ← checkRawOneInput input
  match output with
  | .opAssign op (.name name) (.num 1) =>
    if operation : op = (if source.inc then .addW else .subW) then
      if binding : name = source.name then
        some ⟨source, by rw [operation, binding]⟩
      else none
    else none
  | _ => none

end Solidity.Correctness.Lowering.Unchecked
