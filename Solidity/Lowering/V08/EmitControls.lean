import Solidity.Lowering.V08.Controls
import Solidity.Lowering.V08.CallableMetadata
import Solidity.Lowering.V08.SelectorObservations

/-!
# Erased logs retain actual argument effects and failure order

Published solEmit/RawStmt.eval elaboration and withPanics are exercised directly.
Source fixtures retain the effecting RExpr arguments and their real declaration.
No RStmt execution preservation or source-to-target compiler is postulated.
-/
namespace Solidity.Lowering.V08.EmitControls
open Solidity
open ContractWorld

def u256 : Source.Syn .typeName := .elem (.int false 256 (by decide +kernel))
def savedDeclaration : Source.Decl :=
  { kind := .stateVar, name := "saved", scope := some "C", top := false,
    node := .stateVar u256 none none none false "saved" .none }
def eventDeclaration : Source.Decl :=
  { kind := .event, name := "E", scope := some "C", top := false,
    node := .event "E" (.cons (.eventParam u256 false (some "first"))
      (.cons (.eventParam u256 false (some "second")) .nil)) false }
def scratchDeclaration : Source.Decl :=
  { kind := .stateVar, name := "scratch", scope := some "C", top := false,
    node := .stateVar u256 none none none true "scratch" .none }
def event3Declaration : Source.Decl :=
  { kind := .event, name := "E3", scope := some "C", top := false,
    node := .event "E3" (.cons (.eventParam u256 false (some "first"))
      (.cons (.eventParam u256 false (some "second"))
        (.cons (.eventParam u256 false (some "third")) .nil))) false }
def sourceUnit : Source.Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons savedDeclaration.node (.cons scratchDeclaration.node
    (.cons eventDeclaration.node (.cons event3Declaration.node .nil))))) .nil)
def sourceEnv : Source.Env := sourceUnit.env

def increment : Source.RExpr sourceEnv [] (.int Source.IntTy.u256) :=
  .assign (.state savedDeclaration rfl rfl)
    (.binary .add (.state savedDeclaration rfl) (.conv (.const (Source.Q.ofInt 1)) (.inl rfl)))
def scale : Source.RExpr sourceEnv [] (.int Source.IntTy.u256) :=
  .assign (.state savedDeclaration rfl rfl)
    (.binary .mul (.state savedDeclaration rfl) (.conv (.const (Source.Q.ofInt 10)) (.inl rfl)))
def sourceArguments : Source.RConvArgs sourceEnv [] [.int Source.IntTy.u256, .int Source.IntTy.u256] :=
  .cons increment rfl (.cons scale rfl .nil)
def sourceEmit : Source.RStmt sourceEnv [] false .body [] [] :=
  .emit eventDeclaration rfl sourceArguments

/-- The event identity is an actual declaration of the source unit. -/
theorem event_member : eventDeclaration ∈ sourceUnit.decls := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))

/-- The resolved event arguments retain both assignment expressions in order. -/
theorem source_arguments_retained : CallableMetadata.convertedArgs sourceArguments =
    .cons (.conv increment (.inl rfl)) (.cons (.conv scale (.inl rfl)) .nil) := rfl

def setTwo : Source.RExpr sourceEnv [] (.int Source.IntTy.u256) :=
  .assign (.state savedDeclaration rfl rfl) (.conv (.const (Source.Q.ofInt 2)) (.inl rfl))
def readDivide : Source.RExpr sourceEnv [] (.int Source.IntTy.u256) :=
  .binary .div (.conv (.const (Source.Q.ofInt 10)) (.inl rfl)) (.state savedDeclaration rfl)
def setScratch : Source.RExpr sourceEnv [] (.int Source.IntTy.u256) :=
  .assign (.state scratchDeclaration rfl rfl) (.conv (.const (Source.Q.ofInt 9)) (.inl rfl))
def dependentArguments : Source.RConvArgs sourceEnv []
    [.int Source.IntTy.u256, .int Source.IntTy.u256, .int Source.IntTy.u256] :=
  .cons setTwo rfl (.cons readDivide rfl (.cons setScratch rfl .nil))
def dependentSourceEmit : Source.RStmt sourceEnv [] false .body [] [] :=
  .emit event3Declaration rfl dependentArguments
def reorderedSourceEmit : Source.RStmt sourceEnv [] false .body [] [] :=
  .emit event3Declaration rfl (.cons readDivide rfl (.cons setTwo rfl (.cons setScratch rfl .nil)))

/-- Three-argument probes have their own actual source event declaration. -/
theorem event3_member : event3Declaration ∈ sourceUnit.decls := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_self))))

/-- The matched three-argument resolved fixture retains its assignments/read. -/
theorem dependent_arguments_retained : CallableMetadata.convertedArgs dependentArguments =
    .cons (.conv setTwo (.inl rfl)) (.cons (.conv readDivide (.inl rfl))
      (.cons (.conv setScratch (.inl rfl)) .nil)) := rfl

def effects : Entry Controls.Cell Unit :=
  { locals := [.val .uint, .val .uint], body := (sol[Controls.Cell]{ { emit E((saved = saved + 1), (saved = saved * 10)); } }).withPanics,
    result := fun _ => .ok (), payable := true }
def dependent : Entry Controls.Cell Unit :=
  { locals := [.val .uint], body := (sol[Controls.Cell]{ { emit E3((saved = 2), 10 / saved, (scratch = 9)); } }).withPanics,
    result := fun _ => .ok (), payable := true }
def reordered : Entry Controls.Cell Unit :=
  { locals := [.val .uint], body := (sol[Controls.Cell]{ { emit E3(10 / saved, (saved = 2), (scratch = 9)); } }).withPanics,
    result := fun _ => .ok (), payable := true }

def view (entry : Entry Controls.Cell Unit) : TRes (Option (Int × Int × Int × Int)) := do
  let world ← Controls.setup
  let (next, _) ← world.call (⟨Controls.self⟩ : Handle ()) entry Controls.paidCtx
  pure (Controls.observe next)

/-- Erasing the log retains two noncommuting argument effects and paid settlement. -/
theorem effect_order : (view effects).toOption = some (some (93, 7, 10, 0)) := by decide +kernel

/-- Dropping the argument effects would retain the wrong persistent value. -/
theorem dropped_effects : (view effects).toOption ≠ some (some (93, 7, 0, 0)) := by
  rw [effect_order]
  decide +kernel

/-- Reversing the two noncommuting assignments would yield the wrong value1. -/
theorem reversed_effects : (view effects).toOption ≠ some (some (93, 7, 1, 0)) := by
  rw [effect_order]
  decide +kernel

/-- The first effect is visible to the later divide, before its guard executes. -/
theorem dependent_read : (view dependent).toOption = some (some (93, 7, 2, 9)) := by decide +kernel

def failedView : TRes (Option (Int × Int × Int × Int) × Option THalt) := do
  let world ← Controls.setup
  let (next, result) := atomic world (world.call (⟨Controls.self⟩ : Handle ()) reordered Controls.paidCtx)
  pure (Controls.observe next, match result with | .error halt => some halt | _ => none)

/-- Moving the divide before its effect causes the exact published Panic0x12
and restores the entire paid frame, rather than committing a partial emit. -/
theorem reordered_failure : failedView.toOption =
    some (some (100, 0, 0, 0), some (.revertWith (Semantics.encodePanic 0x12))) := by decide +kernel

/-- A different panic code is not the observed reordered-argument failure. -/
theorem wrong_failure_payload : failedView.toOption ≠
    some (some (100, 0, 0, 0), some (.revertWith (Semantics.encodePanic 0x11))) := by
  rw [reordered_failure]
  decide +kernel

#print axioms event3_member
#print axioms dependent_arguments_retained
#print axioms event_member
#print axioms source_arguments_retained
#print axioms effect_order
#print axioms dropped_effects
#print axioms reversed_effects
#print axioms dependent_read
#print axioms reordered_failure
#print axioms wrong_failure_payload
end Solidity.Lowering.V08.EmitControls
