import tests.h62.item2.«audit-language».FullTelescopeWitness
import Solidity.Source.Typing

/-!
Guarded regression: tuple holes and unnamed returns must not lose local types,
and a scope extension must retain the old locals. Whole imported telescopes
include an actual intrinsic statement derivation and all constant-typing guards.
Named frozen headers are checked separately; the production typing module has
been split and dependent definitions evolved. No old/new meaning equivalence,
compiler acceptance, or historical replay is inferred from these witnesses.
-/
set_option autoImplicit false
namespace Solidity.H62.AuditLanguage.SourceTypingWitness
open Solidity.Source

def context : Ctx := { env := ⟨[]⟩, scope := none, locals := [("old", .bool)] }
def locals : List (String × STy) := [("old", .bool)]
def slots : List (Option (String × STy)) :=
  [none, some ("first", .int IntTy.u8), some ("last", .bool)]
def literal : Syn .expr := .lit (.num (.dec 7 0 0))

theorem try_locals_full : hypotheses_of% tryLocals_tys := by
  exact ⟨[some "result", none], [.bool, .int IntTy.u8, .bool], True.intro⟩
#verify_hypotheses try_locals_full for Solidity.Source.tryLocals_tys
#print axioms try_locals_full

theorem catch_locals_full : hypotheses_of% catchLocals_tys := by
  exact ⟨some "reason", locals, True.intro⟩
#verify_hypotheses catch_locals_full for Solidity.Source.catchLocals_tys
#print axioms catch_locals_full

theorem slots_types_full : hypotheses_of% pushSlots_tys := by
  exact ⟨slots, locals, True.intro⟩
#verify_hypotheses slots_types_full for Solidity.Source.pushSlots_tys
#print axioms slots_types_full

theorem slots_suffix_full : hypotheses_of% pushSlots_suffix := by
  exact ⟨slots, locals, True.intro⟩
#verify_hypotheses slots_suffix_full for Solidity.Source.pushSlots_suffix
#print axioms slots_suffix_full

theorem types_suffix_full : hypotheses_of% pushTys_suffix := by
  exact ⟨[none, some .bool, some (.int IntTy.u8)], [.bool], True.intro⟩
#verify_hypotheses types_suffix_full for Solidity.Source.pushTys_suffix
#print axioms types_suffix_full

theorem statement_suffix_full : hypotheses_of% StmtD.locals_suffix := by
  exact ⟨context, ⟨true, false⟩, locals, locals, Syn.breakStmt, StmtD.brk, True.intro⟩
#verify_hypotheses statement_suffix_full for Solidity.Source.StmtD.locals_suffix
#print axioms statement_suffix_full

theorem literal_type_full : hypotheses_of% HasType.of_const := by
  exact ⟨context, literal, (NumLit.dec 7 0 0).value, rfl, rfl, rfl, True.intro⟩
#verify_hypotheses literal_type_full for Solidity.Source.HasType.of_const
#print axioms literal_type_full

/-- No tuple-declaration slot list can delete an existing local context. -/
theorem existing_locals_preserved (ss : List (Option (String × STy)))
    (old : List (String × STy)) (nonempty : old ≠ []) : pushSlots ss old ≠ [] := by
  intro empty
  obtain ⟨addedLocals, extension⟩ := pushSlots_suffix ss old
  have lengths := congrArg List.length extension
  rw [empty] at lengths
  simp only [List.length_nil, List.length_append] at lengths
  have zero : old.length = 0 := by omega
  exact nonempty (List.length_eq_zero.mp zero)

example : pushSlots slots locals = [("last", .bool), ("first", .int IntTy.u8), ("old", .bool)] := rfl
example : tryLocals [some "result", none] [.bool, .int IntTy.u8, .bool] =
    [("result", .bool), ("", .int IntTy.u8), ("", .bool)] := rfl
example : HasType context literal (.rational (NumLit.dec 7 0 0).value) :=
  HasType.of_const rfl rfl rfl

#print axioms existing_locals_preserved
end Solidity.H62.AuditLanguage.SourceTypingWitness
