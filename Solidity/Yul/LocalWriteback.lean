import Solidity.Yul.LocalWordWrite

/-! Concrete finite writeback of every pure LOCAL word cell. Enumeration uses
the existing logical cell-slot bijection, not a physical allocation/layout.
All writes execute the actual typed Source updates proved in LocalWordWrite. -/
namespace Solidity.Yul

def WordCells.overwriteList {X} (initial values : WordCells X) (cells : List (WordCell X)) :
    WordCells X :=
  cells.foldl (fun view cell => view.write cell (values cell)) initial

theorem WordCells.overwriteList_correct {X} (initial values : WordCells X)
    (cells : List (WordCell X)) (query : WordCell X) (correct : initial query = values query) :
    overwriteList initial values cells query = values query := by
  induction cells generalizing initial with
  | nil => exact correct
  | cons cell rest ih =>
      apply ih (initial.write cell (values cell))
      by_cases same : query.key = cell.key
      · have equal := WordCell.key_injective query cell same
        subst query
        exact WordCells.write_same initial cell (values cell)
      · change (if query.key = cell.key then values cell else initial query) = _
        rw [if_neg same]
        exact correct

theorem WordCells.overwriteList_mem {X} (initial values : WordCells X)
    (cells : List (WordCell X)) (query : WordCell X) (member : query ∈ cells) :
    overwriteList initial values cells query = values query := by
  induction cells generalizing initial with
  | nil => cases member
  | cons cell rest ih =>
      rcases List.mem_cons.mp member with same | later
      · subst query
        exact overwriteList_correct (initial.write cell (values cell)) values rest cell
          (WordCells.write_same initial cell (values cell))
      · exact ih (initial.write cell (values cell)) later

def allWordCells (X : List ExternalType) : List (WordCell X) :=
  List.ofFn (wordCellAt X)

theorem allWordCells_complete {X} (cell : WordCell X) : cell ∈ allWordCells X :=
  List.mem_ofFn.mpr ⟨cell.slot,wordCellAt_slot cell⟩

def writeLocalWords (ctx : Solidity.Source.Ctx) (locals : LocalValues ctx.env ctx.tys)
    (values : WordCells (localExternalTypes ctx))
    (cells : List (WordCell (localExternalTypes ctx))) : LocalValues ctx.env ctx.tys :=
  cells.foldl (fun state cell => writeLocalWord ctx state (values cell) cell) locals

theorem writeLocalWords_view (ctx : Solidity.Source.Ctx)
    (locals : LocalValues ctx.env ctx.tys) (values : WordCells (localExternalTypes ctx))
    (cells : List (WordCell (localExternalTypes ctx))) :
    localWordCells ctx (writeLocalWords ctx locals values cells) =
      WordCells.overwriteList (localWordCells ctx locals) values cells := by
  induction cells generalizing locals with
  | nil => rfl
  | cons cell rest ih =>
      change localWordCells ctx
        (writeLocalWords ctx (writeLocalWord ctx locals (values cell) cell) values rest) = _
      rw [ih,localWordCells_write]
      rfl

def writebackLocalWords (ctx : Solidity.Source.Ctx) (locals : LocalValues ctx.env ctx.tys)
    (values : WordCells (localExternalTypes ctx)) : LocalValues ctx.env ctx.tys :=
  writeLocalWords ctx locals values (allWordCells (localExternalTypes ctx))

/-- Exact full projection after concrete writeback, for EVERY initial typed
Source local environment and EVERY final raw cell view. No agreement oracle. -/
theorem writebackLocalWords_view (ctx : Solidity.Source.Ctx)
    (locals : LocalValues ctx.env ctx.tys) (values : WordCells (localExternalTypes ctx)) :
    localWordCells ctx (writebackLocalWords ctx locals values) = values := by
  rw [writebackLocalWords,writeLocalWords_view]
  funext query
  exact WordCells.overwriteList_mem _ _ _ _ (allWordCells_complete query)

theorem writeLocalWords_zero (ctx : Solidity.Source.Ctx)
    (locals : LocalValues ctx.env ctx.tys) (values : WordCells (localExternalTypes ctx))
    (cells : List (WordCell (localExternalTypes ctx))) (ref : SourceLocalRef ctx) {kind}
    (shape : DeclaredSourceTypeD ctx.env ref.ty kind) (zero : wordCellWidth kind = 0) :
    (writeLocalWords ctx locals values cells).get ref.index = locals.get ref.index := by
  induction cells generalizing locals with
  | nil => rfl
  | cons cell rest ih =>
      change (writeLocalWords ctx (writeLocalWord ctx locals (values cell) cell) values rest).get
        ref.index = _
      rw [ih,get_writeLocalWord_zero ctx locals ref shape zero cell (values cell)]

theorem writebackLocalWords_zero (ctx : Solidity.Source.Ctx)
    (locals : LocalValues ctx.env ctx.tys) (values : WordCells (localExternalTypes ctx))
    (ref : SourceLocalRef ctx) {kind} (shape : DeclaredSourceTypeD ctx.env ref.ty kind)
    (zero : wordCellWidth kind = 0) :
    (writebackLocalWords ctx locals values).get ref.index = locals.get ref.index :=
  writeLocalWords_zero ctx locals values _ ref shape zero

end Solidity.Yul
