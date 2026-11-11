import tests.h62.item2.«audit-language».FullTelescopeWitness
import Solidity.Source.Resolved

/-!
Guarded regression: resolved field positions and local types must follow actual
lookup and typing evidence, not independently inhabited assumptions. Certificates
cover only the seven unchanged named headers; five mapFree-changed conversion
headers remain outside original-header credit. Dependent-definition meaning
agreement is not established. The closed zero-index schema earns no input tuple.
These are local resolution/progress clients, not compiler acceptance or totality.
-/
set_option autoImplicit false
namespace Solidity.H62.AuditLanguage.SourceResolvedWitness
open Solidity.Source

def unitSyntax : Syn .unit := .unit (.cons (.topPart
  (.struct "S" (.structMember (.elem .bool) "first")
    (.cons (.structMember (.elem .bool) "flag") .nil))) .nil)
def environment : Env := unitSyntax.env
def structName : DeclName := ⟨none, "S"⟩
def locals : List (String × STy) := [("old", .bool)]
def context : Ctx := { env := environment, scope := none, locals := locals }
def literal : Syn .expr := .lit (.num (.dec 7 0 0))
def blockItems : Syn (.list (.item ⟨true, false⟩)) := .cons (.stmtItem .breakStmt) .nil

theorem mobile_fits_full : hypotheses_of% Q.mobileInt?_fits := by
  exact ⟨Q.ofInt 7, IntTy.u8, by decide, True.intro⟩
#verify_hypotheses mobile_fits_full for Solidity.Source.Q.mobileInt?_fits
#print axioms mobile_fits_full

theorem field_position_full : hypotheses_of% Env.fieldTy?_of_fieldAt := by
  exact ⟨environment, structName, .memory, "flag", 1, .bool, rfl, True.intro⟩
#verify_hypotheses field_position_full for Solidity.Source.Env.fieldTy?_of_fieldAt
#print axioms field_position_full

theorem index_closed_schema : hypotheses_of% zero_isIndex := by
  exact True.intro
#verify_hypotheses index_closed_schema for Solidity.Source.zero_isIndex
#print axioms index_closed_schema

theorem singleton_filter_full : hypotheses_of% mem_of_filter_eq := by
  exact ⟨Bool, (fun b => b), [false, true], true, rfl, True.intro⟩
#verify_hypotheses singleton_filter_full for Solidity.Source.mem_of_filter_eq
#print axioms singleton_filter_full

theorem try_types_full : hypotheses_of% tryOk_tys := by
  exact ⟨[some "result", none], [.bool, .int IntTy.u8], locals, True.intro⟩
#verify_hypotheses try_types_full for Solidity.Source.tryOk_tys
#print axioms try_types_full

theorem resolved_literal_full : hypotheses_of% HasType.resolved := by
  exact ⟨context, literal, .rational (NumLit.dec 7 0 0).value, HasType.of_const rfl rfl rfl, True.intro⟩
#verify_hypotheses resolved_literal_full for Solidity.Source.HasType.resolved
#print axioms resolved_literal_full

theorem resolved_block_full : hypotheses_of% ItemsOK.resolved := by
  exact ⟨context, ⟨true, false⟩, locals, locals, blockItems, ⟨ItemsD.stmt StmtD.brk ItemsD.nil⟩, True.intro⟩
#verify_hypotheses resolved_block_full for Solidity.Source.ItemsOK.resolved
#print axioms resolved_block_full

-- Retain the actual closed index fact separately from its empty schema.
example : STy.isIndex (.rational (Q.ofInt 0)) = true := zero_isIndex

/-- The original three constant guards suffice to produce a resolved value. -/
theorem constant_has_resolved_form (Γ : Ctx) (e : Syn .expr) (q : Q)
    (value : e.const = some q) (notAddress : e.isAddressLit = false)
    (notHex : e.hexLen? = none) : Nonempty (RExpr Γ.env Γ.tys (.rational q)) :=
  HasType.resolved (HasType.of_const value notAddress notHex)

example : environment.fieldTy? structName .memory 1 = some .bool :=
  Env.fieldTy?_of_fieldAt (x := "flag") rfl
example : Nonempty (RItems context.env context.rets context.inModifier
    ⟨true, false⟩ (tysOf locals) (tysOf locals)) :=
  ItemsOK.resolved (C := context) (b := blockItems) ⟨ItemsD.stmt StmtD.brk ItemsD.nil⟩

#print axioms constant_has_resolved_form
end Solidity.H62.AuditLanguage.SourceResolvedWitness
