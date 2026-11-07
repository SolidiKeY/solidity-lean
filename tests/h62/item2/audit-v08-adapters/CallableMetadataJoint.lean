import Solidity.Lowering.V08.MetadataControls

/-! Guards metadata hypotheses witnessed in different environments, and treating
arity/types as source argument ordering or executable admission. One existing
abstract source unit supplies function/error declarations, conversions and named
target arguments together. Metadata is NOT independent Source execution, body
selection, canonical admission or ABI/compiler/H68 adequacy. -/
namespace H62.AuditV08Adapters.CallableMetadataJoint
open Solidity Source
open Solidity.Lowering.V08
open CallableMetadata MetadataControls

/-- All facts share the SAME sourceEnv, its actual isBase/mapFree, source
arguments and named target binding. Membership is additional fixture data. -/
def Joint : Prop :=
  declaration ∈ sourceUnit.decls ∧ errorDeclaration ∈ sourceUnit.decls ∧
  declaration.fnSig sourceEnv = some ([.bool,.bool],[.bool]) ∧
  argsFit sourceEnv.isBase sourceEnv.mapFree [.bool,.bool] [.bool,.bool] = true ∧
  errorDeclaration.fitsParams sourceEnv sourceEnv.isBase sourceEnv.mapFree
    [.bool,.rational (Q.ofInt 7)] = true ∧
  errorDeclaration.paramTys sourceEnv = some [.bool,.int IntTy.u8] ∧
  argsFit sourceEnv.isBase sourceEnv.mapFree [.bool,.rational (Q.ofInt 7)] [.bool,.int IntTy.u8] = true ∧
  namesMatch declaration targetArguments = true

theorem joint : Joint :=
  ⟨function_member, error_member, signature, rfl, rfl, rfl, rfl, names⟩

/-- Both identity and heterogeneous implicit-conversion metadata retain their
ORIGINAL source types/order, not merely the selected target parameter types. -/
theorem conversion_origins :
    originTypes (sourceArguments.convert [.bool,.bool] rfl) = [.bool,.bool] ∧
    originTypes (errorArguments.convert [.bool,.int IntTy.u8] rfl) =
      [.bool,.rational (Q.ofInt 7)] :=
  ⟨convert_originTypes sourceArguments _ rfl, convert_originTypes errorArguments _ rfl⟩

/-- Both premises of paramsOf_unique use one actual error declaration. -/
theorem selected_parameters :
    (paramsOf sourceEnv sourceEnv.isBase sourceEnv.mapFree [.bool,.rational (Q.ofInt 7)]
      errorDeclaration rfl).1 = [.bool,.int IntTy.u8] :=
  paramsOf_unique sourceEnv sourceEnv.isBase sourceEnv.mapFree _ errorDeclaration rfl _ rfl

/-- Matching names supplies the original arity conclusion for a genuinely
nonempty target argument frame. -/
theorem named_arity : (parameterNames declaration).length =
    ([.val .bool,.val .bool] : Solidity.Ctx).length :=
  matched_names_length declaration targetArguments names

/-- Same typed arity does not justify reversing two named arguments. -/
theorem same_arity_wrong_names :
    targetArguments.names.length = swappedNames.names.length ∧
    namesMatch declaration targetArguments = true ∧ namesMatch declaration swappedNames = false :=
  ⟨rfl, names, wrong_names⟩

/-- Target binding is actually evaluated in its innermost-first frame order. -/
theorem actual_binding : targetArguments.evalT state = .ok (false,(true,())) := binding_order

theorem wrong_binding_refused : targetArguments.evalT state ≠ .ok (true,(false,())) :=
  wrong_argument_order

/-- Rational/Bool reversal fails the SAME heterogeneous declaration fit test. -/
theorem heterogeneous_order_refused :
    errorDeclaration.fitsParams sourceEnv sourceEnv.isBase sourceEnv.mapFree
      [.rational (Q.ofInt 7),.bool] = false := wrong_error_order

#print axioms joint
#print axioms conversion_origins
#print axioms selected_parameters
#print axioms named_arity
#print axioms same_arity_wrong_names
#print axioms actual_binding
#print axioms wrong_binding_refused
#print axioms heterogeneous_order_refused
end H62.AuditV08Adapters.CallableMetadataJoint
