import Solidity.Lowering.V08.CallableMetadata
import Solidity.Lowering.V08.Controls

/-! Nonempty source declarations, resolved arguments and actual target binding.
These controls do not assert execution of the independent source function. -/
namespace Solidity.Lowering.V08.MetadataControls
open Solidity
open Source
open CallableMetadata

def declaration : Decl :=
  { kind := .function, name := "choose", scope := some "C", top := false,
    node := .function (.ident "choose")
      (.cons (.param (.elem .bool) none (some "left"))
        (.cons (.param (.elem .bool) none (some "right")) .nil))
      (some .external) none .nil false none
      (.cons (.param (.elem .bool) none (some "answer")) .nil) .none }

def errorDeclaration : Decl :=
  { kind := .error, name := "Mismatch", scope := some "C", top := false,
    node := .error "Mismatch" (.cons (.errorParam (.elem .bool) (some "flag"))
      (.cons (.errorParam (.elem (.int false 8 (by decide +kernel))) (some "code")) .nil)) }


/-- Both supplied declarations are members of one actual abstract source unit. -/
def sourceUnit : Syn .unit := .unit (.cons (.contract true "C" .none .nil
  (.cons declaration.node (.cons errorDeclaration.node .nil))) .nil)
def sourceEnv : Source.Env := sourceUnit.env

/-- Membership is separate from name resolution, WellFormed and Typed.toR provenance. -/
theorem function_member : declaration ∈ sourceUnit.decls := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)

theorem error_member : errorDeclaration ∈ sourceUnit.decls := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))

def sourceArguments : RArgs sourceEnv [] [.bool, .bool] :=
  .cons (.bool true) (.cons (.bool false) .nil)
def converted : RConvArgs sourceEnv [] [.bool, .bool] :=
  sourceArguments.convert [.bool, .bool] rfl

def sourceCall : RExpr sourceEnv [] .bool := .call declaration rfl converted

def targetArguments : Args Controls.Cell [] [.val .bool, .val .bool] :=
  .snoc (.snoc .nil .bool (.user "left") (.simple (.bool true)))
    .bool (.user "right") (.simple (.bool false))
def swappedNames : Args Controls.Cell [] [.val .bool, .val .bool] :=
  .snoc (.snoc .nil .bool (.user "right") (.simple (.bool true)))
    .bool (.user "left") (.simple (.bool false))
def state : State Controls.Cell [] :=
  { storage := Storage.init Controls.Cell, H := [], heap := Heap.empty, env := () }

/-- Both parameter and result metadata come from the real source declaration. -/
theorem signature : declaration.fnSig sourceEnv = some ([.bool, .bool], [.bool]) := rfl

/-- Conversion keeps the two distinct expressions in their source order. -/
theorem converted_order : convertedArgs converted =
    .cons (.conv (.bool true) (.inl rfl))
      (.cons (.conv (.bool false) (.inl rfl)) .nil) := rfl

/-- The supplied target parameters use source order despite the reversed frame. -/
theorem names : namesMatch declaration targetArguments = true := rfl

/-- Swapping same-typed named parameters is detected, even though arity agrees. -/
theorem wrong_names : namesMatch declaration swappedNames = false := rfl

/-- Actual target argument evaluation binds the last source argument innermost. -/
theorem binding_order : targetArguments.evalT state = .ok (false, (true, ())) := rfl

/-- Arity and types alone cannot justify the opposite value order. -/
theorem wrong_argument_order : targetArguments.evalT state ≠ .ok (true, (false, ())) := by
  rw [binding_order]
  intro same
  cases same

/-- A different result signature cannot describe this declaration. -/
theorem wrong_signature : declaration.fnSig sourceEnv ≠
    some ([.bool, .bool], [.int IntTy.u8]) := by
  rw [signature]
  intro same
  cases same


def errorArguments : RArgs sourceEnv [] [.bool, .rational (Q.ofInt 7)] :=
  .cons (.bool true) (.cons (.const (Q.ofInt 7)) .nil)

/-- paramsOf selects the heterogeneous declaration's actual parameter list. -/
theorem error_parameters :
    (paramsOf sourceEnv sourceEnv.isBase sourceEnv.mapFree [.bool, .rational (Q.ofInt 7)]
      errorDeclaration rfl).1 = [.bool, .int IntTy.u8] := rfl

/-- The original rational argument is retained, with its implicit conversion. -/
theorem error_argument_origins : originTypes
    (errorArguments.convert [.bool, .int IntTy.u8] rfl) =
      [.bool, .rational (Q.ofInt 7)] := rfl

/-- The heterogeneous reversed argument types fail the existing fit test. -/
theorem wrong_error_order :
    errorDeclaration.fitsParams sourceEnv sourceEnv.isBase sourceEnv.mapFree [.rational (Q.ofInt 7), .bool] = false := rfl

#print axioms function_member
#print axioms error_member
#print axioms signature
#print axioms converted_order
#print axioms names
#print axioms wrong_names
#print axioms binding_order
#print axioms wrong_argument_order
#print axioms wrong_signature
#print axioms error_parameters
#print axioms error_argument_origins
#print axioms wrong_error_order
end Solidity.Lowering.V08.MetadataControls
