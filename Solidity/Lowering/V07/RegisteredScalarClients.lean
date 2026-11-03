import Solidity.Lowering.V07.UnsignedAddition
import Solidity.Lowering.V07.UnsignedMultiplication
import Solidity.Lowering.V07.AllAliasControls

/-! Closed, inhabited clients for every scalar headline, over published mixed
local/memory/storage fixtures. These are supported operational controls, not
Source admission or a SourceSpec/P8 producer. -/
namespace Solidity.Lowering.V07.RegisteredScalarClients
open Source.SemanticsExamples
abbrev source := MixedAssignmentControls.source
abbrev target := MixedAssignmentControls.target
abbrev si := AllAliasControls.si
abbrev ti := AllAliasControls.ti
abbrev family := AllAliasControls.initial

def addition_source_value :=
  UnsignedAddition.source_add_unchecked (D := MixedAssignmentControls.E.layout) 8 (by decide)
    7 3 (by decide) (by decide)
def addition_word :=
  UnsignedAddition.word_add_eval (integerValue .u8 7 (by decide)) (integerValue .u8 3 (by decide))
def addition_value :=
  UnsignedAddition.add_value_run target 8 (by decide) (.simple (.local .here))
    (.simple (.local (.there .here))) 7 3 (by decide) (by decide) rfl rfl
def addition_source (p : Roadmap.Pipeline) (fuel : Nat) :=
  UnsignedAddition.source_locals_run (MixedAssignmentControls.globals p) F0 fuel source
    8 (by decide) .here (.there .here) 7 3 (by decide) (by decide) rfl rfl
def addition_pair (p : Roadmap.Pipeline) (fuel : Nat) :=
  UnsignedAddition.source_from_pair (MixedAssignmentControls.globals p) F0 (fuel+2) source source
    8 (by decide) (.local .here) (.local (.there .here)) 7 3 (by decide) (by decide)
    (source_local_pair (MixedAssignmentControls.globals p) {F0 with checked := false} fuel
      source .u8 .here (.there .here) 7 3 (by decide) (by decide) rfl rfl)
def addition_locals (p : Roadmap.Pipeline) (fuel : Nat) :=
  UnsignedAddition.locals_transport (MixedAssignmentControls.globals p) F0 fuel source target
    8 (by decide) si ti family (false,false) (true,false) 7 3 (by decide) (by decide) rfl rfl
def addition_assign_source (p : Roadmap.Pipeline) (fuel : Nat) :=
  UnsignedAddition.source_assign_read_run (MixedAssignmentControls.globals p) F0 fuel source
    8 (by decide) (.there .here) .here 7 3 (by decide) (by decide) rfl rfl
def addition_assign_operand (p : Roadmap.Pipeline) :=
  UnsignedAddition.assign_read_operand_run p target 8 (by decide) (.there .here) .here
    7 3 (by decide) (by decide) rfl rfl
def addition_assign_family (p : Roadmap.Pipeline) (fuel : Nat) :=
  UnsignedAddition.assignment_transport (MixedAssignmentControls.globals p) F0 fuel source target
    8 (by decide) si ti family (true,false) (false,false) 7 3 (by decide) (by decide) rfl rfl
def addition_extension (p : Roadmap.Pipeline) :=
  UnsignedAddition.assignment_extension p target 8 (by decide) (.there .here) .here
    7 3 (by decide) (by decide) rfl rfl (Thin.drop (t := .val .bool) .refl) (true,target.env)

def multiplication_source_value :=
  UnsignedMultiplication.source_mul_unchecked (D := MixedAssignmentControls.E.layout) 8 (by decide)
    7 3 (by decide) (by decide)
def multiplication_word :=
  UnsignedMultiplication.word_mul_eval (integerValue .u8 7 (by decide)) (integerValue .u8 3 (by decide))
def multiplication_value :=
  UnsignedMultiplication.mul_value_run target 8 (by decide) (.simple (.local .here))
    (.simple (.local (.there .here))) 7 3 (by decide) (by decide) rfl rfl
def multiplication_source (p : Roadmap.Pipeline) (fuel : Nat) :=
  UnsignedMultiplication.source_locals_run (MixedAssignmentControls.globals p) F0 fuel source
    8 (by decide) .here (.there .here) 7 3 (by decide) (by decide) rfl rfl
def multiplication_pair (p : Roadmap.Pipeline) (fuel : Nat) :=
  UnsignedMultiplication.source_from_pair (MixedAssignmentControls.globals p) F0 (fuel+2) source source
    8 (by decide) (.local .here) (.local (.there .here)) 7 3 (by decide) (by decide)
    (source_local_pair (MixedAssignmentControls.globals p) {F0 with checked := false} fuel
      source .u8 .here (.there .here) 7 3 (by decide) (by decide) rfl rfl)
def multiplication_locals (p : Roadmap.Pipeline) (fuel : Nat) :=
  UnsignedMultiplication.locals_transport (MixedAssignmentControls.globals p) F0 fuel source target
    8 (by decide) si ti family (false,false) (true,false) 7 3 (by decide) (by decide) rfl rfl
def multiplication_assign_source (p : Roadmap.Pipeline) (fuel : Nat) :=
  UnsignedMultiplication.source_assign_read_run (MixedAssignmentControls.globals p) F0 fuel source
    8 (by decide) (.there .here) .here 7 3 (by decide) (by decide) rfl rfl
def multiplication_assign_operand (p : Roadmap.Pipeline) :=
  UnsignedMultiplication.assign_read_operand_run p target 8 (by decide) (.there .here) .here
    7 3 (by decide) (by decide) rfl rfl
def multiplication_assign_family (p : Roadmap.Pipeline) (fuel : Nat) :=
  UnsignedMultiplication.assignment_transport (MixedAssignmentControls.globals p) F0 fuel source target
    8 (by decide) si ti family (true,false) (false,false) 7 3 (by decide) (by decide) rfl rfl
def multiplication_extension (p : Roadmap.Pipeline) :=
  UnsignedMultiplication.assignment_extension p target 8 (by decide) (.there .here) .here
    7 3 (by decide) (by decide) rfl rfl (Thin.drop (t := .val .bool) .refl) (true,target.env)

-- The family clients are executable actual expressions, not supplied desired runs.
example (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := false} (fuel+4)
      (.binary .add (.assign (.local (.there .here)) (.local .here)) (.local (.there .here)))).run source =
      (.ok (.val (.int (if p = .legacy then 10 else 14) (by cases p <;> decide))),
        (source.1.set (.there .here) (.int 7 (by decide)),source.2)) := by
  have h := addition_assign_family p fuel
  cases p <;> exact h.1
example (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := false} (fuel+4)
      (.binary .mul (.assign (.local (.there .here)) (.local .here)) (.local (.there .here)))).run source =
      (.ok (.val (.int (if p = .legacy then 21 else 49) (by cases p <;> decide))),
        (source.1.set (.there .here) (.int 7 (by decide)),source.2)) := by
  have h := multiplication_assign_family p fuel
  cases p <;> exact h.1
-- Concrete wrapping, so the registered clients also reject an in-range-only reading.
example : Source.binVal false .add (.int 255 (by decide) : Source.Val MixedAssignmentControls.E.layout (.int .u8))
    (.int 1 (by decide)) = .ok (.int 0 (by decide)) :=
  UnsignedAddition.source_add_unchecked 8 (by decide) 255 1 (by decide) (by decide)
example : Source.binVal false .mul (.int 255 (by decide) : Source.Val MixedAssignmentControls.E.layout (.int .u8))
    (.int 255 (by decide)) = .ok (.int 1 (by decide)) :=
  UnsignedMultiplication.source_mul_unchecked 8 (by decide) 255 255 (by decide) (by decide)
end Solidity.Lowering.V07.RegisteredScalarClients
