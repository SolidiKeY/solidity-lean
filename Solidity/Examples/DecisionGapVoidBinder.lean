import Solidity.Examples.DecisionMappingFieldReason

/-!
# Fresh binders of a type with no memory object: both polarities, decided

`Wallet` and `Ledger` have a mapping member. A memory mapping object is
uninhabited, so neither struct has a memory object in any state and
`∀ fresh Wallet w; φ` is valid whatever `φ` is — including bodies that would
be false of a map-free struct (`1 = w.owner`). The three former unknown pins
(`memStructMapping`, `mappingReversed`, `mappingOne`) are proved. The negated
binder is refuted at the given state; it is outside `Fml.inTarget`, so the
target holds no false member of the family. A map-free struct with the same
body is not a member and stays refuted by its own route.
-/
namespace Solidity.Examples.DecisionGapVoidBinder
open Solidity.Decide Solidity.Decide.MappingStruct
open Solidity.Examples.Decision Solidity.Examples.DecisionResidueReasons
open Solidity.Examples.DecisionMappingFieldReason
set_option Elab.async false

/-- A body false of every map-free field: still valid, the binder is vacuous. -/
def ledgerSeven : Fml StandardExample [] := cdl[StandardExample]{ ∀ fresh Ledger l; l.nonce = 7 }

/-- The negated binder: false in every state. -/
def notWallet : Fml StandardExample [] := cdl[StandardExample]{ ¬ (∀ fresh Wallet w; 1 = w.owner) }

example : notWallet = .not mappingOne := rfl

def verdict (φ : Fml StandardExample []) : String :=
  match decideGoal φ with | .proved => "proved" | .refuted _ => "refuted" | .unknown => "unknown"

/--
info: [(true, true, true, "proved"), (true, true, true, "proved"), (true, true, true, "proved"), (true, true, true, "proved"),
  (false, true, true, "refuted"), (true, false, true, "refuted")]
-/
#guard_msgs in
#eval [memStructMapping, mappingReversed, mappingOne, ledgerSeven, notWallet, reversedFive].map
  fun φ => (φ.inTarget {}, φ.freshVoidBinder, φ.Covered, verdict φ)

/-- `memVoid` on mapping-bearing structs, a map-free struct and arrays of mappings. -/
theorem void_types : (RefTy.struct "Wallet").memVoid = true ∧
    (RefTy.struct "Ledger").memVoid = true ∧ (RefTy.struct "Person").memVoid = false ∧
    (RefTy.fixed (.ref (.mapping .uint .uint)) 2).memVoid = true ∧
    (RefTy.array (.ref (.mapping .uint .uint))).memVoid = false := by decide +kernel

/-- The fixtures in the source class; the map-free control is not. -/
theorem members : memStructMapping.freshVoidBinder = true ∧ mappingReversed.freshVoidBinder = true ∧
    mappingOne.freshVoidBinder = true ∧ ledgerSeven.freshVoidBinder = true ∧
    notWallet.freshVoidBinder = true ∧ reversedFive.freshVoidBinder = false := by decide +kernel

/-- The positive members are in the target; the negated binder is not. -/
theorem targets : memStructMapping.inTarget {} = true ∧ mappingReversed.inTarget {} = true ∧
    mappingOne.inTarget {} = true ∧ ledgerSeven.inTarget {} = true ∧
    notWallet.inTarget {} = false := by decide +kernel

/-- The semantic fact, independently of the decider. -/
theorem mappingOne_valid : Fml.Valid mappingOne :=
  fun σ => allocAll_void_holds σ _ _ rfl _

/-- The initial state refutes the negated binder, independently of the decider. -/
theorem notWallet_countermodel : ¬ holds (State.init StandardExample) notWallet :=
  fun h => h (mappingOne_valid _)

/-- The positive members are covered. -/
theorem covered : memStructMapping.Covered = true ∧ mappingReversed.Covered = true ∧
    mappingOne.Covered = true ∧ ledgerSeven.Covered = true := by decide +kernel

/-- `∀ fresh Wallet w; w.owner = w.owner`: proved. -/
theorem memStructMapping_proved : decideGoal memStructMapping = .proved := by rfl
/-- `∀ fresh Wallet w; 0 = w.owner`: proved. -/
theorem mappingReversed_proved : decideGoal mappingReversed = .proved := by rfl
/-- `∀ fresh Wallet w; 1 = w.owner`: proved. -/
theorem mappingOne_proved : decideGoal mappingOne = .proved := by rfl
/-- `∀ fresh Ledger l; l.nonce = 7`: proved. -/
theorem ledgerSeven_proved : decideGoal ledgerSeven = .proved := by rfl

/-- The negated binder's returned state is the initial state, certified. -/
theorem notWallet_refuted : decideGoal notWallet = .refuted (State.init StandardExample) := by rfl

/-- The returned state refutes the negated binder under the hash reading. -/
theorem notWallet_refutesH : ¬ Fml.holdsH (State.init StandardExample) notWallet :=
  decideGoal_refutes notWallet_refuted

/-- info: 'Solidity.Decide.MappingStruct.allocAll_void_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocAll_void_holds
/-- info: 'Solidity.Examples.DecisionGapVoidBinder.mappingOne_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mappingOne_proved

end Solidity.Examples.DecisionGapVoidBinder
