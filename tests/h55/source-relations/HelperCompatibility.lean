import Solidity.Source.Infer
import Solidity.Frontend.Static.InferComplete

/-!
H70 typed owner compatibility inventory against unchanged H55 producers.
This standalone interface does not extract helpers or migrate inferencers.
All lvalue/typing witnesses, refusal tests, eligibility, conversion tests and
result types remain explicit. No H62 candidate or Lean 4.35 acceptance follows.
-/
namespace H55.HelperCompatibility
open Solidity.Source
open Solidity.Frontend.Static (Res prefixOne infer delete_res payable_mem convElem_mem)

theorem source_mapping_guard (τ : STy) :
    τ.isMapping = false ↔ (τ matches .mapping _ _) = false := Iff.rfl

theorem static_mapping_guard (τ : STy) :
    Solidity.Frontend.Static.isMappingTy τ = false ↔
      (τ matches .mapping _ _) = false := Iff.rfl

theorem source_payable_guard (σ : STy) :
    σ.isPayableArg = true ↔
      (match σ with | .address _ => true | .contract _ => true | _ => false) = true := Iff.rfl

theorem static_payable_guard (σ : STy) :
    Solidity.Frontend.Static.payableArg σ = true ↔
      (match σ with | .address _ => true | .contract _ => true | _ => false) = true := Iff.rfl

theorem source_location_guard (σ τ : STy) (el : Elem) :
    τ = el.ty σ.convLoc ↔
      τ = el.ty (match σ with | .bytes l => l | .string l => l | _ => .memory) := Iff.rfl

theorem static_location_guard (σ τ : STy) (el : Elem) :
    τ = el.ty (Solidity.Frontend.Static.convLoc σ) ↔
      τ = el.ty (match σ with | .bytes l => l | .string l => l | _ => .memory) := Iff.rfl

/-- Both delete guards; these predicates alone do not assert an lvalue. -/
def sourceDeleteGuards (Γ : Ctx) (τ : STy) (e : Syn .expr) : Prop :=
  τ.isMapping = false ∧ Γ.deleteRefused τ e = false

def staticDeleteGuards (Γ : Ctx) (τ : STy) (e : Syn .expr) : Prop :=
  Solidity.Frontend.Static.isMappingTy τ = false ∧ Γ.deleteRefused τ e = false

theorem delete_guards_exact (Γ : Ctx) (τ : STy) (e : Syn .expr) :
    sourceDeleteGuards Γ τ e ↔ staticDeleteGuards Γ τ e := Iff.rfl

/-- Arbitrary result type and explicit test. Eligibility and dx remain separate
parameters of the typed adapters below, as in the original constructor. -/
def sourceConversionGuards (Γ : Ctx) (σ τ : STy) (el : Elem) : Prop :=
  τ = el.ty σ.convLoc ∧ σ.explicit Γ.isBase τ = true

def staticConversionGuards (Γ : Ctx) (σ τ : STy) (el : Elem) : Prop :=
  τ = el.ty (Solidity.Frontend.Static.convLoc σ) ∧ σ.explicit Γ.isBase τ = true

theorem conversion_guards_exact (Γ : Ctx) (σ τ : STy) (el : Elem) :
    sourceConversionGuards Γ σ τ el ↔ staticConversionGuards Γ σ τ el := Iff.rfl

section TypedInterfaces
variable {Γ : Ctx} {e x : Syn .expr} {τ σ : STy}

def sourceDelete (d : LVal Γ e τ) (mapping : τ.isMapping = false)
    (refusal : Γ.deleteRefused τ e = false) :
    Typed Γ (.unaryPrefix .delete e) (.tuple []) := .delete d mapping refusal

def staticDelete (d : LVal Γ e τ) (mapping : Solidity.Frontend.Static.isMappingTy τ = false)
    (refusal : Γ.deleteRefused τ e = false) :
    Typed Γ (.unaryPrefix .delete e) (.tuple []) := .delete d mapping refusal

theorem delete_constructor_exact (d : LVal Γ e τ) (mapping : τ.isMapping = false)
    (refusal : Γ.deleteRefused τ e = false) :
    sourceDelete d mapping refusal = staticDelete d mapping refusal := rfl

def sourcePayable (d : Typed Γ x σ) (payable : σ.isPayableArg = true) :
    Typed Γ (.payableConv (.positional (.cons x .nil))) (.address true) := .payable d payable

def staticPayable (d : Typed Γ x σ) (payable : Solidity.Frontend.Static.payableArg σ = true) :
    Typed Γ (.payableConv (.positional (.cons x .nil))) (.address true) := .payable d payable

theorem payable_constructor_exact (d : Typed Γ x σ) (payable : σ.isPayableArg = true) :
    sourcePayable d payable = staticPayable d payable := rfl

variable {el : Elem} {eligible : el ≠ .addressPayable}

def sourceConvert (d : Typed Γ x σ) (location : τ = el.ty σ.convLoc)
    (conversion : σ.explicit Γ.isBase τ = true) :
    Typed Γ (.call (.elemType el eligible) (.positional (.cons x .nil))) τ :=
  .convElem d location conversion

def staticConvert (d : Typed Γ x σ) (location : τ = el.ty (Solidity.Frontend.Static.convLoc σ))
    (conversion : σ.explicit Γ.isBase τ = true) :
    Typed Γ (.call (.elemType el eligible) (.positional (.cons x .nil))) τ :=
  .convElem d location conversion

theorem conversion_constructor_exact (d : Typed Γ x σ) (location : τ = el.ty σ.convLoc)
    (conversion : σ.explicit Γ.isBase τ = true) :
    sourceConvert (eligible := eligible) d location conversion =
      staticConvert (eligible := eligible) d location conversion := rfl

/-- Exact existing Res membership, not only type-membership completeness. -/
theorem delete_consumer (d : LVal Γ e τ) (mapping : τ.isMapping = false)
    (refusal : Γ.deleteRefused τ e = false) :
    Res.expr (sourceDelete d mapping refusal) ∈ prefixOne Γ .delete (.lval d) :=
  delete_res d mapping refusal

theorem payable_consumer (d : Typed Γ x σ) (input : Res.expr d ∈ infer Γ x)
    (payable : σ.isPayableArg = true) :
    Res.expr (sourcePayable d payable) ∈ infer Γ
      (.payableConv (.positional (.cons x .nil))) := payable_mem input payable

theorem conversion_consumer (d : Typed Γ x σ) (input : Res.expr d ∈ infer Γ x)
    (location : τ = el.ty σ.convLoc) (conversion : σ.explicit Γ.isBase τ = true) :
    Res.expr (sourceConvert (eligible := eligible) d location conversion) ∈ infer Γ
      (.call (.elemType el eligible) (.positional (.cons x .nil))) := by
  subst τ
  exact convElem_mem input conversion
end TypedInterfaces

/-- A top-level test, not a claim that the array may be deleted. -/
theorem array_of_mapping_control (location : DataLoc) (key value : STy) (length : Option Nat) :
    STy.isMapping (.array location (.mapping key value) length) = false := rfl

theorem mapping_refusal_control (Γ : Ctx) (key value : STy) (e : Syn .expr) :
    ¬ sourceDeleteGuards Γ (.mapping key value) e := by
  intro guards
  have impossible : true = false := guards.1
  cases impossible

/-- A concrete non-mapping type for which the second delete guard refuses. -/
theorem calldata_second_guard_control (Γ : Ctx) (e : Syn .expr) :
    STy.isMapping (.bytes .calldata) = false ∧
      Γ.deleteRefused (.bytes .calldata) e = true := ⟨rfl, rfl⟩

theorem calldata_refusal_control (Γ : Ctx) (e : Syn .expr) :
    ¬ sourceDeleteGuards Γ (.bytes .calldata) e := by
  intro guards
  have impossible : true = false := guards.2
  cases impossible

theorem address_payable_control (flag : Bool) : STy.isPayableArg (.address flag) = true := rfl

theorem contract_payable_control (name : DeclName) : STy.isPayableArg (.contract name) = true := rfl

theorem boolean_payable_refusal : STy.isPayableArg .bool = false := rfl

theorem bytes_location_control (location : DataLoc) : STy.convLoc (.bytes location) = location := rfl

theorem string_location_control (location : DataLoc) : STy.convLoc (.string location) = location := rfl

theorem default_location_control : STy.convLoc .bool = .memory := rfl

theorem explicit_conversion_refusal (Γ : Ctx) (σ τ : STy) (el : Elem)
    (refused : σ.explicit Γ.isBase τ = false) :
    ¬ sourceConversionGuards Γ σ τ el := by
  intro guards
  have impossible : false = true := refused.symm.trans guards.2
  cases impossible

#check sourceDelete
#check staticDelete
#check sourcePayable
#check staticPayable
#check sourceConvert
#check staticConvert
#print axioms source_mapping_guard
#print axioms static_mapping_guard
#print axioms source_payable_guard
#print axioms static_payable_guard
#print axioms source_location_guard
#print axioms static_location_guard
#print axioms delete_guards_exact
#print axioms conversion_guards_exact
#print axioms delete_constructor_exact
#print axioms payable_constructor_exact
#print axioms conversion_constructor_exact
#print axioms delete_consumer
#print axioms payable_consumer
#print axioms conversion_consumer
#print axioms array_of_mapping_control
#print axioms mapping_refusal_control
#print axioms calldata_second_guard_control
#print axioms calldata_refusal_control
#print axioms address_payable_control
#print axioms contract_payable_control
#print axioms boolean_payable_refusal
#print axioms bytes_location_control
#print axioms string_location_control
#print axioms default_location_control
#print axioms explicit_conversion_refusal
end H55.HelperCompatibility
