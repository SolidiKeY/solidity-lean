import Solidity.Yul.ScalarLocals
set_option Elab.async false

namespace Solidity.Yul.Checks.ScalarLocals
open Solidity.Source

def ctx : Ctx :=
  {env := ⟨[]⟩, scope := none,
   locals := [("small",.int .u8),("flag",.bool),("other",.int .u8)]}
def smallData := (checkClassifiedSourceLocal ctx "small").get (by decide)
def flagData := (checkClassifiedSourceLocal ctx "flag").get (by decide)
def otherData := (checkClassifiedSourceLocal ctx "other").get (by decide)
def small : SourceScalarCell ctx := .ofClassified smallData (.unsigned 0) (by decide)
def flag : SourceScalarCell ctx := .ofClassified flagData .boolean (by decide)
def other : SourceScalarCell ctx := .ofClassified otherData (.unsigned 0) (by decide)

example : small.position = 0 := by decide
example : flag.position = 1 := by decide
example : other.position = 2 := by decide
example : ctx.resolve "small" = some (.loc small.position) :=
  SourceScalarCell.ofClassified_resolves smallData _ _
example : ctx.resolve "flag" = some (.loc flag.position) :=
  SourceScalarCell.ofClassified_resolves flagData _ _
example : ctx.resolve "other" = some (.loc other.position) :=
  SourceScalarCell.ofClassified_resolves otherData _ _

/-- Yul occurrence order differs from Source order; it is not a stack layout. -/
def types : List ExternalType :=
  [.value .boolean,.value (.unsigned 0),.value (.unsigned 0),
   .constant (word 9),.storage false false]
def smallBinding : ScalarBinding types ctx := ⟨small,.there .here⟩
def flagBinding : ScalarBinding types ctx := ⟨flag,.here⟩
def otherBinding : ScalarBinding types ctx := ⟨other,.there (.there .here)⟩
def bindings := [smallBinding,flagBinding,otherBinding]
def source : SourceScalarView ctx := fun cell => word (100+cell.position)
def yul : ScalarView types := fun ref =>
  if ref.position=0 then word 101 else if ref.position=1 then word 100 else word 102

theorem coherent : ScalarBindingsCoherent bindings := by
  intro first member second member'
  simp only [bindings,List.mem_cons,List.not_mem_nil,or_false] at member member'
  rcases member with rfl|rfl|rfl <;> rcases member' with rfl|rfl|rfl <;> decide
theorem agree : ScalarViewsAgree bindings yul source := by
  intro binding member
  simp only [bindings,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl <;> decide

example : smallBinding.ref.position = 1 := by decide
example : flagBinding.ref.position = 0 := by decide
example : otherBinding.ref.position = 2 := by decide
example : smallBinding.source.position ≠ smallBinding.ref.position := by decide
example : ScalarViewsAgree bindings (yul.write smallBinding.ref (word 257))
    (source.write small (word 257)) :=
  agree.write coherent smallBinding (List.mem_cons_self) (word 257)
example : ScalarViewsAgree bindings (yul.write flagBinding.ref (word 2))
    (source.write flag (word 2)) :=
  agree.write coherent flagBinding (List.mem_cons_of_mem _ List.mem_cons_self) (word 2)

example : ((source.write small (word 257)) small).val = 257 := by decide
example : ((source.write small (word (2^256-1))) small).val = 2^256-1 := by decide
example : ((source.write flag (word 2)) flag).val = 2 := by decide
example : ((source.write small (word 257)) flag).val = 101 := by decide
example : ((source.write small (word 257)) other).val = 102 := by decide
example : small.encoding = .unsigned 0 := rfl
example : flag.encoding = .boolean := rfl
example : ((yul.write smallBinding.ref (word 257)) smallBinding.ref).val = 257 := by decide
example : ((yul.write flagBinding.ref (word 2)) flagBinding.ref).val = 2 := by decide

/-- Raw snapshot values above narrow/bool ranges are retained by the view.
These are NOT a proof of initialization from clean Source.Val or solc pipelines. -/
example : ((source.write small (word 257)) small).val ≠ 1 := by decide
example : ((source.write flag (word 2)) flag).val ≠ 1 := by decide

example (first second : ScalarRef types) (same : first.position = second.position) :
    first = second := ScalarRef.position_injective first second same
example (first second : SourceScalarCell ctx) (same : first.position = second.position) :
    first = second := SourceScalarCell.position_injective first second same
example (ref : ScalarRef (globals types)) : False := ref.not_globals
example : globals types = [.constant (word 9),.storage false false] := by decide
example (one two : ScalarView (globals types)) : one = two := ScalarView.function_unique one two

/-- Intrinsic type-correct bindings may still alias different source slots.
Full root-table construction must prove alias preservation, not assume it. -/
def badOne : ScalarBinding types ctx := ⟨small,.there .here⟩
def badTwo : ScalarBinding types ctx := ⟨other,.there .here⟩
def bad := [badOne,badTwo]
example : ¬ ScalarBindingsCoherent bad := by
  intro h
  have equal := (h badOne (List.mem_cons_self) badTwo (List.mem_cons_of_mem _ List.mem_cons_self)).mp rfl
  have wrong : (0:Nat) = 2 := equal
  cases wrong
example (view : ScalarView types) : ¬ ScalarViewsAgree bad view source := by
  intro h
  have one := h badOne (List.mem_cons_self)
  have two := h badTwo (List.mem_cons_of_mem _ List.mem_cons_self)
  have wrong : word 100 = word 102 := one.symm.trans two
  exact (by decide : word 100 ≠ word 102) wrong
example : badOne.ref.position = badTwo.ref.position := rfl
example : badOne.source.position ≠ badTwo.source.position := by decide

/-- A canonical checked source occurrence remains the same actual handle. -/
example : sourceRefFromPayload ctx (sourceRefPayload ctx small.ref) = small.ref :=
  sourceRefPayload_inverse ctx small.ref
example : (sourceIndexMember flag.ref.index).position = flag.ref.index.toNat :=
  sourceIndexMember_position flag.ref.index


/-- Reverse incoherence: initially equal views split two Yul occurrences that
refer to ONE Source cell. A write exposes the missing reverse implication. -/
def reverseOne : ScalarBinding types ctx := ⟨small,.there .here⟩
def reverseTwo : ScalarBinding types ctx := ⟨small,.there (.there .here)⟩
def reverseBindings := [reverseOne,reverseTwo]
def reverseYul : ScalarView types := fun _ => word 100
theorem reverseAgree : ScalarViewsAgree reverseBindings reverseYul source := by
  intro binding member
  simp only [reverseBindings,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl <;> rfl
example : ¬ ScalarBindingsCoherent reverseBindings := by
  intro h
  have equal := (h reverseOne List.mem_cons_self reverseTwo
    (List.mem_cons_of_mem _ List.mem_cons_self)).mpr rfl
  have wrong : (1:Nat) = 2 := equal
  cases wrong
example : reverseOne.source.position = reverseTwo.source.position := rfl
example : reverseOne.ref.position ≠ reverseTwo.ref.position := by decide
example : ¬ ScalarViewsAgree reverseBindings (reverseYul.write reverseOne.ref (word 257))
    (source.write reverseOne.source (word 257)) := by
  intro h
  have other := h reverseTwo (List.mem_cons_of_mem _ List.mem_cons_self)
  have wrong : word 100 = word 257 := other
  exact (by decide : word 100 ≠ word 257) wrong

end Solidity.Yul.Checks.ScalarLocals
