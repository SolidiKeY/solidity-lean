import Solidity.Yul.LocalProjection
import Solidity.Yul.Checks.SourceContext
set_option Elab.async false

namespace Solidity.Yul.Checks.LocalProjection

def small := SourceContext.targetSmall.ref
def flagBinding : ScalarBinding (localExternalTypes SourceContext.ctx) SourceContext.ctx :=
  (localScalarBindings SourceContext.ctx)[2]'(by decide)
def otherBinding : ScalarBinding (localExternalTypes SourceContext.ctx) SourceContext.ctx :=
  (localScalarBindings SourceContext.ctx)[3]'(by decide)
def source : SourceScalarView SourceContext.ctx := fun cell => word (100+cell.position)
def projected := projectLocalScalars SourceContext.ctx source

example : small.position = 1 := by decide
example : (sourceScalarAt SourceContext.ctx small).position = 2 := by decide
example : (sourceScalarAt SourceContext.ctx small).encoding = .unsigned 0 := rfl
example : (sourceScalarAt SourceContext.ctx flagBinding.ref).position = 3 := by decide
example : (sourceScalarAt SourceContext.ctx flagBinding.ref).encoding = .boolean := rfl
example : (sourceScalarAt SourceContext.ctx otherBinding.ref).position = 4 := by decide
example : (projected small).val = 102 := by decide
example : (projected flagBinding.ref).val = 103 := by decide
example : (projected otherBinding.ref).val = 104 := by decide
example : ScalarViewsAgree (localScalarBindings SourceContext.ctx) projected source :=
  projectLocalScalars_agree SourceContext.ctx source

example : (sourceEntryAt SourceContext.ctx small.index).val.ref.index.toNat = 2 := by decide
example : (sourceEntryAt SourceContext.ctx small.index).val.kind = .value (.unsigned 0) :=
  (sourceEntryAt SourceContext.ctx small.index).property
example : sourceScalarAt SourceContext.ctx small = SourceContext.targetSmall.source :=
  sourceScalarAt_binding SourceContext.ctx SourceContext.targetSmall SourceContext.targetPresent
example : ∃ ref, sourceScalarAt SourceContext.ctx ref = SourceContext.targetSmall.source :=
  sourceScalarAt_surjective SourceContext.ctx SourceContext.targetSmall.source

example (one two : ScalarRef (localExternalTypes SourceContext.ctx))
    (same : sourceScalarAt SourceContext.ctx one = sourceScalarAt SourceContext.ctx two) : one = two :=
  sourceScalarAt_injective SourceContext.ctx one two same
example (cell : SourceScalarCell SourceContext.ctx) : ∃ ref, sourceScalarAt SourceContext.ctx ref = cell :=
  sourceScalarAt_surjective SourceContext.ctx cell

example : projectLocalScalars SourceContext.ctx (source.write SourceContext.targetSmall.source (word 257)) =
    projected.write small (word 257) :=
  projectLocalScalars_binding_write SourceContext.ctx source SourceContext.targetSmall SourceContext.targetPresent (word 257)
example : projectLocalScalars SourceContext.ctx
    (source.write (sourceScalarAt SourceContext.ctx flagBinding.ref) (word 2)) =
    projected.write flagBinding.ref (word 2) :=
  projectLocalScalars_write SourceContext.ctx source flagBinding.ref (word 2)
example : ((projected.write small (word 257)) small).val = 257 := by decide
example : ((projected.write small (word 257)) flagBinding.ref).val = 103 := by decide
example : ((projected.write small (word 257)) otherBinding.ref).val = 104 := by decide
example : ((projected.write flagBinding.ref (word 2)) flagBinding.ref).val = 2 := by decide
example : ((projected.write small (word (2^256-1))) small).val = 2^256-1 := by decide
example : ((projected.write small (word (2^256-1))) otherBinding.ref).val = 104 := by decide
example : ((projectLocalScalars SourceContext.ctx
    (source.write SourceContext.targetSmall.source (word 257))) small).val = 257 := by decide
example : ((projectLocalScalars SourceContext.ctx
    (source.write SourceContext.targetSmall.source (word 257))) flagBinding.ref).val = 103 := by decide

/-- Non-scalar references never receive a fabricated scalar/default word. -/
example (ref : ScalarRef (localExternalTypes SourceContext.ctx)) (same : ref.position = 4) : False := by
  let memoryIndex : Member (localExternalTypes SourceContext.ctx) .memory :=
    .there (.there (.there (.there .here)))
  have equal := Member.payload_position (localExternalTypes SourceContext.ctx)
    ⟨.value ref.encoding,ref.index⟩ ⟨.memory,memoryIndex⟩ same
  have kinds := congrArg Sigma.fst equal
  cases kinds
example (ref : ScalarRef (localExternalTypes SourceContext.empty)) : False := by cases ref.index
example (ref : ScalarRef (localExternalTypes SourceContext.unsupported)) : False := by cases ref.index
example : small.position ≠ (sourceScalarAt SourceContext.ctx small).position := by decide
example : ((projected.write small (word 257)) small).val ≠ 1 := by decide
example : ((projected.write flagBinding.ref (word 2)) flagBinding.ref).val ≠ 1 := by decide

end Solidity.Yul.Checks.LocalProjection
