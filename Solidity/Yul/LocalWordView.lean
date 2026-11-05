import Solidity.Yul.CleanFunctions
import Solidity.Yul.WordLocals

/-! Total logical word projection of actual extended Source LOCAL values.
It includes scalar locals and separate external-function fields, never physical
reference pointers. Clean initialization is derived, not an assumed snapshot. -/
namespace Solidity.Yul

theorem LocalValue.readScalar_total {env ty encoding} (value : LocalValue env ty)
    (shape : DeclaredSourceTypeD env ty (.value encoding)) :
    (value.readScalar shape).isSome = true := by
  cases value with
  | clean value => exact shape.word_isSome value
  | scalar written raw => rfl
  | externalFunction params rets mutability address selector =>
      have impossible := DeclaredSourceTypeD.unique shape
        (.basic (.reference (.externalFunction params rets mutability)))
      cases impossible

namespace SourceScalarCell
theorem localWordRead_total {ctx} (cell : SourceScalarCell ctx)
    (locals : LocalValues ctx.env ctx.tys) : (cell.localWordRead? locals).isSome = true :=
  LocalValue.readScalar_total (locals.get cell.ref.index) cell.shape

def wordRead {ctx} (cell : SourceScalarCell ctx)
    (locals : LocalValues ctx.env ctx.tys) : Word :=
  (cell.localWordRead? locals).get (cell.localWordRead_total locals)

theorem wordRead_write {ctx} (cell : SourceScalarCell ctx)
    (locals : LocalValues ctx.env ctx.tys) (raw : Word) :
    cell.wordRead (cell.localWrite locals raw) = raw := by
  apply Option.some.inj
  exact (Option.some_get (cell.localWordRead_total _)).trans (cell.localWordRead_write locals raw)

theorem wordRead_ofClean {ctx} (cell : SourceScalarCell ctx)
    (locals : Solidity.Source.Locals ctx.env.layout ctx.tys) :
    cell.wordRead (LocalValues.ofClean locals) = cell.cleanWord locals := by
  apply Option.some.inj
  exact (Option.some_get (cell.localWordRead_total _)).trans
    ((cell.localWordRead_ofClean locals).trans (Option.some_get (cell.shape.word_isSome _)).symm)
end SourceScalarCell

structure SourceFunctionCell (ctx : Solidity.Source.Ctx) where
  ref : SourceLocalRef ctx
  shape : DeclaredSourceTypeD ctx.env ref.ty .externalFunction

namespace SourceFunctionCell

def localFields? {ctx} (cell : SourceFunctionCell ctx)
    (locals : LocalValues ctx.env ctx.tys) : Option (Word × Word) :=
  (locals.get cell.ref.index).readFunctionFields cell.shape

theorem localFields_total {ctx} (cell : SourceFunctionCell ctx)
    (locals : LocalValues ctx.env ctx.tys) : (cell.localFields? locals).isSome = true :=
  LocalValue.readFunctionFields_total (locals.get cell.ref.index) cell.shape

def fields {ctx} (cell : SourceFunctionCell ctx)
    (locals : LocalValues ctx.env ctx.tys) : Word × Word :=
  (cell.localFields? locals).get (cell.localFields_total locals)

theorem fields_ofClean {ctx} (cell : SourceFunctionCell ctx)
    (locals : Solidity.Source.Locals ctx.env.layout ctx.tys) :
    some (cell.fields (LocalValues.ofClean locals)) =
      cleanFunctionFields (locals.get cell.ref.index) := by
  calc
    _ = cell.localFields? (LocalValues.ofClean locals) := Option.some_get _
    _ = _ := by
      unfold localFields?
      rw [LocalValues.get_ofClean]
      rfl

def writeFields {ctx} (cell : SourceFunctionCell ctx)
    (locals : LocalValues ctx.env ctx.tys) (address selector : Word) :
    LocalValues ctx.env ctx.tys :=
  locals.set cell.ref.index ((LocalValue.rawFunction cell.ref.ty address selector).get
    (LocalValue.rawFunction_total cell.shape address selector))

theorem fields_writeFields {ctx} (cell : SourceFunctionCell ctx)
    (locals : LocalValues ctx.env ctx.tys) (address selector : Word) :
    cell.fields (cell.writeFields locals address selector) = (address,selector) := by
  apply Option.some.inj
  calc
    _ = cell.localFields? (cell.writeFields locals address selector) := Option.some_get _
    _ = _ := by
      unfold localFields? writeFields
      rw [LocalValues.get_set]
      exact LocalValue.rawFunction_read cell.shape address selector

def writeAddress {ctx} (cell : SourceFunctionCell ctx)
    (locals : LocalValues ctx.env ctx.tys) (address : Word) : LocalValues ctx.env ctx.tys :=
  cell.writeFields locals address (cell.fields locals).2

def writeSelector {ctx} (cell : SourceFunctionCell ctx)
    (locals : LocalValues ctx.env ctx.tys) (selector : Word) : LocalValues ctx.env ctx.tys :=
  cell.writeFields locals (cell.fields locals).1 selector

theorem fields_writeAddress {ctx} (cell : SourceFunctionCell ctx)
    (locals : LocalValues ctx.env ctx.tys) (address : Word) :
    cell.fields (cell.writeAddress locals address) = (address,(cell.fields locals).2) :=
  cell.fields_writeFields locals address (cell.fields locals).2

theorem fields_writeSelector {ctx} (cell : SourceFunctionCell ctx)
    (locals : LocalValues ctx.env ctx.tys) (selector : Word) :
    cell.fields (cell.writeSelector locals selector) = ((cell.fields locals).1,selector) :=
  cell.fields_writeFields locals (cell.fields locals).1 selector

end SourceFunctionCell

def sourceFunctionAt (ctx : Solidity.Source.Ctx)
    (index : Member (localExternalTypes ctx) .externalFunction) : SourceFunctionCell ctx :=
  let entry := sourceEntryAt ctx index
  ⟨entry.val.ref,Eq.mp
    (congrArg (fun kind => DeclaredSourceTypeD ctx.env entry.val.ref.ty kind) entry.property)
    entry.val.shape⟩

def localWordCells (ctx : Solidity.Source.Ctx) (locals : LocalValues ctx.env ctx.tys) :
    WordCells (localExternalTypes ctx)
  | .scalar ref => (sourceScalarAt ctx ref).wordRead locals
  | .address index => ((sourceFunctionAt ctx index).fields locals).1
  | .selector index => ((sourceFunctionAt ctx index).fields locals).2

theorem localWordCells_scalar (ctx : Solidity.Source.Ctx)
    (locals : LocalValues ctx.env ctx.tys) (ref : ScalarRef (localExternalTypes ctx)) :
    localWordCells ctx locals (.scalar ref) = (sourceScalarAt ctx ref).wordRead locals := rfl

theorem localWordCells_clean_scalar (ctx : Solidity.Source.Ctx)
    (locals : Solidity.Source.Locals ctx.env.layout ctx.tys)
    (ref : ScalarRef (localExternalTypes ctx)) :
    localWordCells ctx (LocalValues.ofClean locals) (.scalar ref) =
      cleanLocalScalars ctx locals ref := (sourceScalarAt ctx ref).wordRead_ofClean locals

theorem localWordCells_scalar_write (ctx : Solidity.Source.Ctx)
    (locals : LocalValues ctx.env ctx.tys) (ref : ScalarRef (localExternalTypes ctx)) (raw : Word) :
    localWordCells ctx ((sourceScalarAt ctx ref).localWrite locals raw) (.scalar ref) = raw :=
  (sourceScalarAt ctx ref).wordRead_write locals raw

theorem localWordCells_address_write (ctx : Solidity.Source.Ctx)
    (locals : LocalValues ctx.env ctx.tys) (index : Member (localExternalTypes ctx) .externalFunction)
    (raw : Word) :
    localWordCells ctx ((sourceFunctionAt ctx index).writeAddress locals raw) (.address index) = raw :=
  congrArg Prod.fst ((sourceFunctionAt ctx index).fields_writeAddress locals raw)

theorem localWordCells_selector_write (ctx : Solidity.Source.Ctx)
    (locals : LocalValues ctx.env ctx.tys) (index : Member (localExternalTypes ctx) .externalFunction)
    (raw : Word) :
    localWordCells ctx ((sourceFunctionAt ctx index).writeSelector locals raw) (.selector index) = raw :=
  congrArg Prod.snd ((sourceFunctionAt ctx index).fields_writeSelector locals raw)

theorem localWordCells_selector_after_address (ctx : Solidity.Source.Ctx)
    (locals : LocalValues ctx.env ctx.tys) (index : Member (localExternalTypes ctx) .externalFunction)
    (raw : Word) :
    localWordCells ctx ((sourceFunctionAt ctx index).writeAddress locals raw) (.selector index) =
      localWordCells ctx locals (.selector index) := by
  change ((sourceFunctionAt ctx index).fields
    ((sourceFunctionAt ctx index).writeAddress locals raw)).2 =
      ((sourceFunctionAt ctx index).fields locals).2
  rw [SourceFunctionCell.fields_writeAddress]

theorem localWordCells_address_after_selector (ctx : Solidity.Source.Ctx)
    (locals : LocalValues ctx.env ctx.tys) (index : Member (localExternalTypes ctx) .externalFunction)
    (raw : Word) :
    localWordCells ctx ((sourceFunctionAt ctx index).writeSelector locals raw) (.address index) =
      localWordCells ctx locals (.address index) := by
  change ((sourceFunctionAt ctx index).fields
    ((sourceFunctionAt ctx index).writeSelector locals raw)).1 =
      ((sourceFunctionAt ctx index).fields locals).1
  rw [SourceFunctionCell.fields_writeSelector]

def initialLocalWordState (ctx : Solidity.Source.Ctx)
    (locals : Solidity.Source.Locals ctx.env.layout ctx.tys) :
    WordState (localExternalTypes ctx) 0 :=
  ⟨Fin.elim0,localWordCells ctx (LocalValues.ofClean locals)⟩

end Solidity.Yul
