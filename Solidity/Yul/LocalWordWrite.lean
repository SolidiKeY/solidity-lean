import Solidity.Yul.LocalWordView

/-! Actual typed Source local updates and occurrence separation. These are
logical LOCAL positions, never physical slots. Different-cell preservation
uses original intrinsic indices and actual declaration uniqueness. -/
namespace Solidity.Yul

theorem LocalValues.get_set_other {env ctx ty otherTy}
    (locals : LocalValues env ctx) (target : Solidity.Source.Idx ctx ty)
    (other : Solidity.Source.Idx ctx otherTy) (value : LocalValue env ty)
    (different : target.toNat ≠ other.toNat) :
    (locals.set target value).get other = locals.get other := by
  induction target generalizing otherTy with
  | here =>
      cases other with
      | here => exact False.elim (different rfl)
      | there previous => rfl
  | there target ih =>
      cases other with
      | here => rfl
      | there other =>
          exact ih locals.2 other value (by
            change target.toNat + 1 ≠ other.toNat + 1 at different
            omega)

def SourceFunctionCell.position {ctx} (cell : SourceFunctionCell ctx) : Nat :=
  cell.ref.index.toNat

theorem SourceFunctionCell.position_injective {ctx}
    (first second : SourceFunctionCell ctx) (same : first.position = second.position) :
    first = second := by
  rcases first with ⟨one,da⟩
  rcases second with ⟨two,db⟩
  have refs := SourceLocalRef.position_injective one two same
  cases refs
  have certificates := Option.some.inj (da.complete.symm.trans db.complete)
  cases certificates
  rfl

theorem SourceScalarCell.position_ne_function {ctx}
    (scalar : SourceScalarCell ctx) (function : SourceFunctionCell ctx) :
    scalar.position ≠ function.position := by
  intro same
  rcases scalar with ⟨one,encoding,da⟩
  rcases function with ⟨two,db⟩
  have refs := SourceLocalRef.position_injective one two same
  cases refs
  have impossible := DeclaredSourceTypeD.unique da db
  cases impossible

theorem sourceEntryAt_position_iff (ctx : Solidity.Source.Ctx) {one two}
    (first : Member (localExternalTypes ctx) one)
    (second : Member (localExternalTypes ctx) two) :
    (sourceEntryAt ctx first).val.position = (sourceEntryAt ctx second).val.position ↔
      first.position = second.position := by
  constructor
  · intro same
    have a := sourceEntryAt_position_key ctx first
    have b := sourceEntryAt_position_key ctx second
    have bound : first.position < ((sourceLocalEntries ctx).map SourceLocalEntry.position).length := by
      have h := first.position_lt
      simpa only [localExternalTypes,List.length_map] using h
    exact List.getElem?_inj bound (sourceLocalEntries_distinct ctx)
      (a.trans ((congrArg some same).trans b.symm))
  · intro same
    exact congrArg SourceLocalEntry.position (sourceEntryAt_same_position ctx first second same)

theorem sourceFunctionAt_position_iff (ctx : Solidity.Source.Ctx)
    (first second : Member (localExternalTypes ctx) .externalFunction) :
    (sourceFunctionAt ctx first).position = (sourceFunctionAt ctx second).position ↔
      first.position = second.position :=
  sourceEntryAt_position_iff ctx first second

theorem SourceScalarCell.wordRead_congr {ctx} (cell : SourceScalarCell ctx)
    (first second : LocalValues ctx.env ctx.tys)
    (same : first.get cell.ref.index = second.get cell.ref.index) :
    cell.wordRead first = cell.wordRead second := by
  apply Option.some.inj
  exact (Option.some_get (cell.localWordRead_total first)).trans
    ((congrArg (fun value => value.readScalar cell.shape) same).trans
      (Option.some_get (cell.localWordRead_total second)).symm)

theorem SourceFunctionCell.fields_congr {ctx} (cell : SourceFunctionCell ctx)
    (first second : LocalValues ctx.env ctx.tys)
    (same : first.get cell.ref.index = second.get cell.ref.index) :
    cell.fields first = cell.fields second := by
  apply Option.some.inj
  exact (Option.some_get (cell.localFields_total first)).trans
    ((congrArg (fun value => value.readFunctionFields cell.shape) same).trans
      (Option.some_get (cell.localFields_total second)).symm)

theorem SourceScalarCell.wordRead_scalar_write_other {ctx}
    (target other : SourceScalarCell ctx) (locals : LocalValues ctx.env ctx.tys) (raw : Word)
    (different : target.position ≠ other.position) :
    other.wordRead (target.localWrite locals raw) = other.wordRead locals := by
  apply other.wordRead_congr
  exact LocalValues.get_set_other locals target.ref.index other.ref.index
    (.scalar target.shape raw) different

theorem SourceFunctionCell.fields_scalar_write {ctx}
    (target : SourceScalarCell ctx) (other : SourceFunctionCell ctx)
    (locals : LocalValues ctx.env ctx.tys) (raw : Word) :
    other.fields (target.localWrite locals raw) = other.fields locals := by
  apply other.fields_congr
  exact LocalValues.get_set_other locals target.ref.index other.ref.index
    (.scalar target.shape raw) (target.position_ne_function other)

theorem SourceScalarCell.wordRead_function_write {ctx}
    (target : SourceFunctionCell ctx) (other : SourceScalarCell ctx)
    (locals : LocalValues ctx.env ctx.tys) (address selector : Word) :
    other.wordRead (target.writeFields locals address selector) = other.wordRead locals := by
  apply other.wordRead_congr
  exact LocalValues.get_set_other locals target.ref.index other.ref.index
    ((LocalValue.rawFunction target.ref.ty address selector).get
      (LocalValue.rawFunction_total target.shape address selector))
    (Ne.symm (other.position_ne_function target))

theorem SourceFunctionCell.fields_function_write_other {ctx}
    (target other : SourceFunctionCell ctx) (locals : LocalValues ctx.env ctx.tys)
    (address selector : Word) (different : target.position ≠ other.position) :
    other.fields (target.writeFields locals address selector) = other.fields locals := by
  apply other.fields_congr
  exact LocalValues.get_set_other locals target.ref.index other.ref.index
    ((LocalValue.rawFunction target.ref.ty address selector).get
      (LocalValue.rawFunction_total target.shape address selector)) different

/-- One actual pure WordCell update in the actual typed Source local domain. -/
def writeLocalWord (ctx : Solidity.Source.Ctx) (locals : LocalValues ctx.env ctx.tys)
    (raw : Word) : WordCell (localExternalTypes ctx) → LocalValues ctx.env ctx.tys
  | .scalar ref => (sourceScalarAt ctx ref).localWrite locals raw
  | .address index => (sourceFunctionAt ctx index).writeAddress locals raw
  | .selector index => (sourceFunctionAt ctx index).writeSelector locals raw

theorem functionIndex_position_injective {X : List ExternalType}
    (first second : Member X .externalFunction) (same : first.position = second.position) :
    first = second :=
  WordCell.address.inj (WordCell.key_injective (.address first) (.address second)
    (congrArg (fun position => (position,Attribute.address)) same))

theorem sourceFunctionAt_different (ctx : Solidity.Source.Ctx)
    (first second : Member (localExternalTypes ctx) .externalFunction) (different : first ≠ second) :
    (sourceFunctionAt ctx first).position ≠ (sourceFunctionAt ctx second).position := by
  intro same
  exact different (functionIndex_position_injective first second
    ((sourceFunctionAt_position_iff ctx first second).mp same))

theorem sourceScalarAt_different (ctx : Solidity.Source.Ctx)
    (first second : ScalarRef (localExternalTypes ctx)) (different : first ≠ second) :
    (sourceScalarAt ctx first).position ≠ (sourceScalarAt ctx second).position := by
  intro same
  exact different (ScalarRef.position_injective first second
    ((sourceScalarAt_position_iff ctx first second).mp same))

theorem localWordCells_write_same (ctx : Solidity.Source.Ctx)
    (locals : LocalValues ctx.env ctx.tys) (target : WordCell (localExternalTypes ctx))
    (raw : Word) : localWordCells ctx (writeLocalWord ctx locals raw target) target = raw := by
  cases target with
  | scalar ref => exact localWordCells_scalar_write ctx locals ref raw
  | address index => exact localWordCells_address_write ctx locals index raw
  | selector index => exact localWordCells_selector_write ctx locals index raw

theorem localWordCells_write_other (ctx : Solidity.Source.Ctx)
    (locals : LocalValues ctx.env ctx.tys) (target other : WordCell (localExternalTypes ctx))
    (raw : Word) (different : other ≠ target) :
    localWordCells ctx (writeLocalWord ctx locals raw target) other = localWordCells ctx locals other := by
  cases target with
  | scalar target =>
      cases other with
      | scalar other =>
          exact (sourceScalarAt ctx target).wordRead_scalar_write_other
            (sourceScalarAt ctx other) locals raw (sourceScalarAt_different ctx target other
              (fun same => different (congrArg WordCell.scalar same.symm)))
      | address other =>
          exact congrArg Prod.fst ((sourceFunctionAt ctx other).fields_scalar_write
            (sourceScalarAt ctx target) locals raw)
      | selector other =>
          exact congrArg Prod.snd ((sourceFunctionAt ctx other).fields_scalar_write
            (sourceScalarAt ctx target) locals raw)
  | address target =>
      cases other with
      | scalar other =>
          exact (sourceScalarAt ctx other).wordRead_function_write
            (sourceFunctionAt ctx target) locals raw ((sourceFunctionAt ctx target).fields locals).2
      | address other =>
          exact congrArg Prod.fst ((sourceFunctionAt ctx target).fields_function_write_other
            (sourceFunctionAt ctx other) locals raw ((sourceFunctionAt ctx target).fields locals).2
              (sourceFunctionAt_different ctx target other
                (fun same => different (congrArg WordCell.address same.symm))))
      | selector other =>
          by_cases same : other = target
          · subst other
            exact localWordCells_selector_after_address ctx locals target raw
          · exact congrArg Prod.snd ((sourceFunctionAt ctx target).fields_function_write_other
              (sourceFunctionAt ctx other) locals raw ((sourceFunctionAt ctx target).fields locals).2
                (sourceFunctionAt_different ctx target other (Ne.symm same)))
  | selector target =>
      cases other with
      | scalar other =>
          exact (sourceScalarAt ctx other).wordRead_function_write
            (sourceFunctionAt ctx target) locals ((sourceFunctionAt ctx target).fields locals).1 raw
      | selector other =>
          exact congrArg Prod.snd ((sourceFunctionAt ctx target).fields_function_write_other
            (sourceFunctionAt ctx other) locals ((sourceFunctionAt ctx target).fields locals).1 raw
              (sourceFunctionAt_different ctx target other
                (fun same => different (congrArg WordCell.selector same.symm))))
      | address other =>
          by_cases same : other = target
          · subst other
            exact localWordCells_address_after_selector ctx locals target raw
          · exact congrArg Prod.fst ((sourceFunctionAt ctx target).fields_function_write_other
              (sourceFunctionAt ctx other) locals ((sourceFunctionAt ctx target).fields locals).1 raw
                (sourceFunctionAt_different ctx target other (Ne.symm same)))

/-- Concrete whole-view update equation, including EVERY other cell. -/
theorem localWordCells_write (ctx : Solidity.Source.Ctx)
    (locals : LocalValues ctx.env ctx.tys) (target : WordCell (localExternalTypes ctx))
    (raw : Word) :
    localWordCells ctx (writeLocalWord ctx locals raw target) =
      (localWordCells ctx locals).write target raw := by
  funext other
  by_cases same : other = target
  · subst other
    rw [localWordCells_write_same,WordCells.write_same]
  · rw [localWordCells_write_other ctx locals target other raw same,
      WordCells.write_other _ _ _ _ same]

theorem SourceLocalRef.position_different_kinds {ctx}
    (first second : SourceLocalRef ctx) {one two}
    (firstShape : DeclaredSourceTypeD ctx.env first.ty one)
    (secondShape : DeclaredSourceTypeD ctx.env second.ty two) (different : one ≠ two) :
    first.index.toNat ≠ second.index.toNat := by
  intro same
  have refs := SourceLocalRef.position_injective first second same
  cases refs
  exact different (DeclaredSourceTypeD.unique firstShape secondShape)

/-- A zero-width PURE-view category (e.g. memory/internal function) is not
modified. Zero here says nothing about its physical representation. -/
theorem get_writeLocalWord_zero (ctx : Solidity.Source.Ctx)
    (locals : LocalValues ctx.env ctx.tys) (ref : SourceLocalRef ctx) {kind}
    (shape : DeclaredSourceTypeD ctx.env ref.ty kind) (zero : wordCellWidth kind = 0)
    (target : WordCell (localExternalTypes ctx)) (raw : Word) :
    (writeLocalWord ctx locals raw target).get ref.index = locals.get ref.index := by
  cases target with
  | scalar target =>
      let cell := sourceScalarAt ctx target
      apply LocalValues.get_set_other
      apply SourceLocalRef.position_different_kinds cell.ref ref cell.shape shape
      intro same
      have widths := congrArg wordCellWidth same
      rw [zero] at widths
      cases widths
  | address target =>
      let cell := sourceFunctionAt ctx target
      apply LocalValues.get_set_other
      apply SourceLocalRef.position_different_kinds cell.ref ref cell.shape shape
      intro same
      have widths := congrArg wordCellWidth same
      rw [zero] at widths
      cases widths
  | selector target =>
      let cell := sourceFunctionAt ctx target
      apply LocalValues.get_set_other
      apply SourceLocalRef.position_different_kinds cell.ref ref cell.shape shape
      intro same
      have widths := congrArg wordCellWidth same
      rw [zero] at widths
      cases widths

end Solidity.Yul
