import Solidity.Yul.SourceContext

/-! Total reverse projection for the concrete local context. This projects a
SOURCE RAW scalar snapshot; it does not initialize dirty words from clean
Source.Val or claim a source/pipeline execution refinement. -/
namespace Solidity.Yul

theorem Member.getElem {α : Type} {types : List α} {ty : α}
    (index : Member types ty) : types[index.position]'index.position_lt = ty := by
  induction index with
  | here => rfl
  | there previous ih => exact ih

/-- Reverse lookup uses the actual generated occurrence number, never names or
a default value. Its selected type is proved equal to the intrinsic index type. -/
def sourceEntryAt (ctx : Solidity.Source.Ctx) {kind : ExternalType}
    (index : Member (localExternalTypes ctx) kind) :
    {entry : SourceLocalEntry ctx // entry.kind = kind} :=
  let bound : index.position < (sourceLocalEntries ctx).length := by
    have h := index.position_lt
    simpa only [localExternalTypes,List.length_map] using h
  let entry := (sourceLocalEntries ctx)[index.position]'bound
  ⟨entry, by
    have h := index.getElem
    change ((sourceLocalEntries ctx).map SourceLocalEntry.kind)[index.position]'index.position_lt = kind at h
    simpa only [List.getElem_map] using h⟩

theorem sourceEntryAt_mapped (ctx : Solidity.Source.Ctx)
    (mapped : MappedLocal ctx (localExternalTypes ctx))
    (present : mapped ∈ localExternalMap ctx) :
    (sourceEntryAt ctx mapped.index).val = mapped.source := by
  have atIndex := mappedLocals_at ctx (sourceLocalEntries ctx) mapped present
  have bound : mapped.index.position < (sourceLocalEntries ctx).length := by
    have h := mapped.index.position_lt
    simpa only [localExternalTypes,List.length_map] using h
  rw [List.getElem?_eq_getElem bound] at atIndex
  exact Option.some.inj atIndex

def sourceScalarAt (ctx : Solidity.Source.Ctx)
    (ref : ScalarRef (localExternalTypes ctx)) : SourceScalarCell ctx :=
  let entry := sourceEntryAt ctx ref.index
  ⟨entry.val.ref,ref.encoding,Eq.mp (congrArg (fun kind => DeclaredSourceTypeD ctx.env entry.val.ref.ty kind) entry.property) entry.val.shape⟩

theorem sourceEntryAt_same_position (ctx : Solidity.Source.Ctx) {one two}
    (first : Member (localExternalTypes ctx) one) (second : Member (localExternalTypes ctx) two)
    (same : first.position = second.position) :
    (sourceEntryAt ctx first).val = (sourceEntryAt ctx second).val := by
  unfold sourceEntryAt
  simp only
  exact getElem_congr_idx same

theorem sourceScalarAt_binding (ctx : Solidity.Source.Ctx)
    (binding : ScalarBinding (localExternalTypes ctx) ctx)
    (present : binding ∈ localScalarBindings ctx) :
    sourceScalarAt ctx binding.ref = binding.source := by
  rcases List.mem_filterMap.mp present with ⟨mapped,member,scalar⟩
  obtain ⟨yulPosition,sourcePosition⟩ := mapped.scalar_positions binding scalar
  have sameEntries := sourceEntryAt_same_position ctx binding.ref.index mapped.index yulPosition
  have atIndex := sourceEntryAt_mapped ctx mapped member
  apply SourceScalarCell.position_injective
  change (sourceEntryAt ctx binding.ref.index).val.position = binding.source.position
  rw [sameEntries,atIndex]
  exact sourcePosition.symm

def projectLocalScalars (ctx : Solidity.Source.Ctx) (source : SourceScalarView ctx) :
    ScalarView (localExternalTypes ctx) :=
  fun ref => source (sourceScalarAt ctx ref)

theorem projectLocalScalars_agree (ctx : Solidity.Source.Ctx) (source : SourceScalarView ctx) :
    ScalarViewsAgree (localScalarBindings ctx) (projectLocalScalars ctx source) source := by
  intro binding present
  unfold projectLocalScalars
  rw [sourceScalarAt_binding ctx binding present]


theorem sourceEntryAt_position_key (ctx : Solidity.Source.Ctx) {kind}
    (index : Member (localExternalTypes ctx) kind) :
    ((sourceLocalEntries ctx).map SourceLocalEntry.position)[index.position]? =
      some (sourceEntryAt ctx index).val.position := by
  have bound : index.position < (sourceLocalEntries ctx).length := by
    have h := index.position_lt
    simpa only [localExternalTypes,List.length_map] using h
  rw [List.getElem?_map,List.getElem?_eq_getElem bound]
  rfl

theorem sourceScalarAt_position_iff (ctx : Solidity.Source.Ctx)
    (first second : ScalarRef (localExternalTypes ctx)) :
    (sourceScalarAt ctx first).position = (sourceScalarAt ctx second).position ↔
      first.position = second.position := by
  constructor
  · intro same
    have one := sourceEntryAt_position_key ctx first.index
    have two := sourceEntryAt_position_key ctx second.index
    have bound : first.position < ((sourceLocalEntries ctx).map SourceLocalEntry.position).length := by
      have h := first.index.position_lt
      simpa only [localExternalTypes,List.length_map] using h
    exact List.getElem?_inj bound (sourceLocalEntries_distinct ctx)
      (one.trans ((congrArg some same).trans two.symm))
  · intro same
    have entries := sourceEntryAt_same_position ctx first.index second.index same
    exact congrArg SourceLocalEntry.position entries

theorem sourceScalarAt_injective (ctx : Solidity.Source.Ctx)
    (first second : ScalarRef (localExternalTypes ctx))
    (same : sourceScalarAt ctx first = sourceScalarAt ctx second) : first = second :=
  ScalarRef.position_injective first second
    ((sourceScalarAt_position_iff ctx first second).mp (congrArg SourceScalarCell.position same))

theorem sourceScalarAt_surjective (ctx : Solidity.Source.Ctx) (cell : SourceScalarCell ctx) :
    ∃ ref, sourceScalarAt ctx ref = cell := by
  rcases localScalarBindings_complete ctx cell with ⟨binding,present,same⟩
  exact ⟨binding.ref,(sourceScalarAt_binding ctx binding present).trans same⟩

/-- Exact commutation for the CONSTRUCTED raw projection, with no caller-supplied
agreement/coherence/completion premise. This is not clean Source.Val writeback. -/
theorem projectLocalScalars_write (ctx : Solidity.Source.Ctx) (source : SourceScalarView ctx)
    (target : ScalarRef (localExternalTypes ctx)) (value : Word) :
    projectLocalScalars ctx (source.write (sourceScalarAt ctx target) value) =
      (projectLocalScalars ctx source).write target value := by
  funext ref
  unfold projectLocalScalars SourceScalarView.write ScalarView.write
  simp only [sourceScalarAt_position_iff ctx ref target]

theorem projectLocalScalars_binding_write (ctx : Solidity.Source.Ctx)
    (source : SourceScalarView ctx) (binding : ScalarBinding (localExternalTypes ctx) ctx)
    (present : binding ∈ localScalarBindings ctx) (value : Word) :
    projectLocalScalars ctx (source.write binding.source value) =
      (projectLocalScalars ctx source).write binding.ref value := by
  have h := projectLocalScalars_write ctx source binding.ref value
  rw [sourceScalarAt_binding ctx binding present] at h
  exact h

end Solidity.Yul
