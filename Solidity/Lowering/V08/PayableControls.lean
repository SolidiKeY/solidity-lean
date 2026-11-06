import Solidity.Lowering.V08.PayableMetadata
import Solidity.Lowering.V08.Controls
import Solidity.Lowering.V08.MetadataControls

/-! Payment metadata controls only. Source bodies are empty and the target body
is explicitly supplied with writes: these are NOT body-lowering witnesses. -/
namespace Solidity.Lowering.V08.PayableControls
open Solidity
open ContractWorld
open PayableMetadata

def receiving : Source.Decl :=
  { kind := .receive, name := "", scope := some "Header", top := false,
    node := .receive true true .nil false none (.some (.block .nil)) }
def fallbackDecl (payable : Bool) : Source.Decl :=
  { kind := .fallback, name := "", scope := some "Header", top := false,
    node := .fallback .fbNoParams true (if payable then some .payable else none)
      .nil false none (.some (.block .nil)) }
def functionDecl (mutability : Option Source.Mutability) (visibility : Source.Visibility := .external) : Source.Decl :=
  { kind := .function, name := "f", scope := some "Header", top := false,
    node := .function (.ident "f") .nil (some visibility) mutability .nil false none .nil
      (.some (.block .nil)) }
def badReceive : Source.Decl :=
  { kind := .receive, name := "", scope := some "Header", top := false,
    node := .receive false true .nil false none (.some (.block .nil)) }
def constructorDecl : Source.Decl :=
  { kind := .constructor, name := "", scope := some "Header", top := false,
    node := .constructor .nil .nil true none (.block .nil) }

/-- A real source unit contains the receive metadata fixture. Admission and
body lowering remain distinct from this declaration membership witness. -/
def receivingUnit : Source.Syn .unit :=
  .unit (.cons (.contract false "Header" .none .nil (.cons receiving.node .nil)) .nil)
theorem receive_member : receiving ∈ receivingUnit.decls := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)

theorem payable_function : payableOf? (functionDecl (some .payable)) = some true := rfl
theorem receive_flag : payableOf? receiving = some true := rfl
theorem fallback_flags : payableOf? (fallbackDecl false) = some false ∧
    payableOf? (fallbackDecl true) = some true := ⟨rfl, rfl⟩

/-- Permission to read msg.value in an internal function does not accept payment. -/
theorem internal_read_not_payable : Source.readsValue (some .internal) none = true ∧
    payableOf? (functionDecl none .internal) = some false := ⟨rfl, rfl⟩

/-- Existing receiveOK refusal is retained instead of guessing a payment flag. -/
theorem malformed_receive_refused : attach? badReceive Controls.entry = none := rfl

/-- An error declaration is not an ordinary entry. -/
theorem noncallable_refused : attach? MetadataControls.errorDeclaration Controls.entry = none := rfl

/-- Constructors use the creation interface, not ordinary callable entry metadata. -/
theorem constructor_refused : attach? constructorDecl Controls.entry = none := rfl

def runDeclared (declaration : Source.Decl) (context : Context := Controls.paidCtx) :
    Option (TRes (Option (Int × Int × Int × Int))) := do
  let entry ← attach? declaration { Controls.entry with payable := false }
  pure (do
    let before ← Controls.setup
    let (after, _) ← before.call (⟨Controls.self⟩ : Handle ()) entry context
    pure (Controls.observe after))

def resultView (declaration : Source.Decl) (context : Context := Controls.paidCtx) :=
  (runDeclared declaration context).map Except.toOption

def failureView (declaration : Source.Decl) : Option (Option THalt) :=
  (runDeclared declaration).map fun result => match result with | .error halt => some halt | _ => none

/-- Source receive metadata enables actual funded entry and keeps supplied writes. -/
theorem receive_paid : resultView receiving = some (some (some (93, 7, 3, 9))) := by decide +kernel

theorem fallback_paid : resultView (fallbackDecl true) = some (some (some (93, 7, 3, 9))) := by decide +kernel

/-- A nonpayable fallback rejects the nonzero payment with the exact halt. -/
theorem nonpayable_fallback : failureView (fallbackDecl false) = some (some .revert) := by decide +kernel

theorem nonpayable_function : failureView (functionDecl none) = some (some .revert) := by decide +kernel

/-- Zero-payment calls of nonpayable entries retain the actual supplied body. -/
theorem zero_nonpayable : resultView (fallbackDecl false) Controls.ctx =
    some (some (some (100, 0, 3, 9))) := by decide +kernel

/-- Erasing the incoming payment would give the wrong funded receive observation. -/
theorem wrong_payment : resultView receiving ≠ some (some (some (100, 0, 3, 9))) := by
  rw [receive_paid]
  decide +kernel

#print axioms receive_member
#print axioms payable_function
#print axioms receive_flag
#print axioms fallback_flags
#print axioms internal_read_not_payable
#print axioms malformed_receive_refused
#print axioms noncallable_refused
#print axioms constructor_refused
#print axioms receive_paid
#print axioms fallback_paid
#print axioms nonpayable_fallback
#print axioms nonpayable_function
#print axioms zero_nonpayable
#print axioms wrong_payment
end Solidity.Lowering.V08.PayableControls
