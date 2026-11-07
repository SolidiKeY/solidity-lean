import Solidity.Lowering.P9.DefaultRecognizerCompleteness
import Solidity.Source.Progress.StructParentControls

/-! Positive and insufficient-fuel controls for the unchanged default checker.
A rejected small fuel is deliberately not treated as a type refusal. -/
namespace Solidity.Source.Calls.Recognize.DefaultControls
open Solidity.Source.Progress

def nested : STy := .array .memory (.array .memory .bool (some 2)) (some 3)

theorem bytes_zero (E : Env) : finiteDefaultB E 0 (.bytes .memory) = true := by rfl

theorem nested_zero_refused (E : Env) : finiteDefaultB E 0 nested = false := by rfl

theorem nested_one_refused (E : Env) : finiteDefaultB E 1 nested = false := by rfl

theorem nested_two (E : Env) : finiteDefaultB E 2 nested = true := by rfl

theorem nested_larger (E : Env) (n : Nat) (enough : 2 ≤ n) :
    finiteDefaultB E n nested = true :=
  finiteDefaultB_mono enough (nested_two E)

theorem refused_fuel_not_refutation (E : Env) :
    FiniteDefault E nested ∧ finiteDefaultB E 0 nested = false :=
  ⟨finiteDefaultB_sound 2 (nested_two E),nested_zero_refused E⟩

theorem shared_list_fuel (E : Env) :
    ∃ n, [STy.bytes .memory,nested].all (finiteDefaultB E n) = true :=
  finiteDefaultsB_exists _ (by
    intro τ member
    rcases List.mem_cons.mp member with same | tail
    · subst τ; exact ⟨0,bytes_zero E⟩
    · rcases List.mem_cons.mp tail with same | empty
      · subst τ; exact ⟨2,nested_two E⟩
      · cases empty)


/-- The existing elaborated Pair layout contains two memory-byte fields. -/
theorem struct_zero_refused :
    finiteDefaultB Solidity.Source.Progress.StructParentControls.E 0
      (.struct .memory Solidity.Source.Progress.StructParentControls.dn) = false := by rfl

theorem struct_one :
    finiteDefaultB Solidity.Source.Progress.StructParentControls.E 1
      (.struct .memory Solidity.Source.Progress.StructParentControls.dn) = true := by
  first | rfl | decide

theorem struct_certificate :
    FiniteDefault Solidity.Source.Progress.StructParentControls.E
      (.struct .memory Solidity.Source.Progress.StructParentControls.dn) :=
  finiteDefaultB_sound 1 struct_one

/-- info: 'Solidity.Source.Calls.Recognize.DefaultControls.struct_zero_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms struct_zero_refused
/-- info: 'Solidity.Source.Calls.Recognize.DefaultControls.struct_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms struct_one
/-- info: 'Solidity.Source.Calls.Recognize.DefaultControls.struct_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms struct_certificate
/-- info: 'Solidity.Source.Calls.Recognize.DefaultControls.bytes_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bytes_zero
/-- info: 'Solidity.Source.Calls.Recognize.DefaultControls.nested_zero_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nested_zero_refused
/-- info: 'Solidity.Source.Calls.Recognize.DefaultControls.nested_one_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nested_one_refused
/-- info: 'Solidity.Source.Calls.Recognize.DefaultControls.nested_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nested_two
/-- info: 'Solidity.Source.Calls.Recognize.DefaultControls.nested_larger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nested_larger
/-- info: 'Solidity.Source.Calls.Recognize.DefaultControls.refused_fuel_not_refutation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms refused_fuel_not_refutation
/-- info: 'Solidity.Source.Calls.Recognize.DefaultControls.shared_list_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shared_list_fuel
end Solidity.Source.Calls.Recognize.DefaultControls
