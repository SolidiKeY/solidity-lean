import Solidity.Yul.WordLocals
set_option Elab.async false

namespace Solidity.Yul.Checks.WordLocals
def X : List ExternalType :=
  [.memory,.value (.unsigned 0),.externalFunction,.constant (word 11),
   .value .boolean,.externalFunction,.storage false true,.calldataDynamic]
def small : WordCell X := .scalar ⟨.unsigned 0,.there .here⟩
def flag : WordCell X := .scalar ⟨.boolean,.there (.there (.there (.there .here)))⟩
def first : Member X .externalFunction := .there (.there .here)
def second : Member X .externalFunction := .there (.there (.there (.there (.there .here))))
def cells : WordCells X := fun cell =>
  if cell.key = small.key then word 257 else
  if cell.key = flag.key then word 2 else
  if cell.key = (WordCell.selector first).key then word 0x100000001 else
  if cell.key = (WordCell.address second).key then word (2^256-1) else word 0

example : wordCellCount X = 6 := rfl
example : small.slot.val = 0 := rfl
example : (WordCell.address first).slot.val = 1 := rfl
example : (WordCell.selector first).slot.val = 2 := rfl
example : flag.slot.val = 3 := rfl
example : (WordCell.address second).slot.val = 4 := rfl
example : (WordCell.selector second).slot.val = 5 := rfl
example : WordCells.pack X cells ⟨0,by decide⟩ = word 257 := by decide
example : WordCells.pack X cells ⟨1,by decide⟩ = word 0 := by decide
example : WordCells.pack X cells ⟨2,by decide⟩ = word 0x100000001 := by decide
example : WordCells.pack X cells ⟨3,by decide⟩ = word 2 := by decide
example : WordCells.pack X cells ⟨4,by decide⟩ = word (2^256-1) := by decide
example : WordCells.pack X cells ⟨5,by decide⟩ = word 0 := by decide
example : wordCellAt X ⟨0,by decide⟩ = small := rfl
example : wordCellAt X ⟨1,by decide⟩ = .address first := rfl
example : wordCellAt X ⟨2,by decide⟩ = .selector first := rfl
example : wordCellAt X ⟨3,by decide⟩ = flag := rfl
example : wordCellAt X ⟨4,by decide⟩ = .address second := rfl
example : wordCellAt X ⟨5,by decide⟩ = .selector second := rfl

-- Physical, internal and immutable declarations contribute no mutable cells.
example : wordCellCount [.memory,.calldataStatic,.calldataDynamic,
    .storage true false,.storage false true,.internalFunction,.library,
    .constant (word 9)] = 0 := rfl
example (cell : WordCell [.memory,.constant (word 9)]) : False := by
  have slot := cell.slot
  exact Fin.elim0 slot
example : wordCellCount (globals X) = 0 := wordCellCount_globals X
example : globals X = [.constant (word 11),.storage false true] := rfl

def values : Fin 6 → Word := fun i => word (300+i.val)
example : WordCells.unpack (WordCells.pack X cells) = cells := WordCells.unpack_pack cells
example : WordCells.pack X (WordCells.unpack (X := X) values) = values :=
  WordCells.pack_unpack (X := X) values
example : (WordCells.unpack (X := X) values) small = word 300 := by decide
example : (WordCells.unpack (X := X) values) (.selector first) = word 302 := by decide
example : (WordCells.unpack (X := X) values) (.address second) = word 304 := by decide
example : WordCells.pack X (cells.write (.selector first) (word 67)) ⟨2,by decide⟩ =
    word 67 := by decide
example : WordCells.pack X (cells.write (.selector first) (word 67)) ⟨4,by decide⟩ =
    word (2^256-1) := by decide

def state : WordState X 2 :=
  ⟨Fin.cases (word 99) (fun _ => word 100),cells⟩
example : state.pack ⟨0,by decide⟩ = word 99 := by decide
example : state.pack ⟨1,by decide⟩ = word 100 := by decide
example : state.pack ⟨2,by decide⟩ = word 257 := by decide
example : state.pack ⟨4,by decide⟩ = word 0x100000001 := by decide
example : state.pack ⟨6,by decide⟩ = word (2^256-1) := by decide
example : WordState.unpack state.pack = state := WordState.unpack_pack state
example : (WordState.unpack (X := X) (n := 2) (fun i => word i.val)).pack =
    (fun i => word i.val) := WordState.pack_unpack _
example (first second : WordCell X) (h : first.slot = second.slot) :
    first = second := WordCell.slot_injective first second h

def witness : Nonempty (WordState X 2) := ⟨state⟩
def dirtyWitness : ∃ packed : Fin (wordCellCount X) → Word,
    packed small.slot = word 257 ∧ packed flag.slot = word 2 ∧
    packed (WordCell.selector first).slot = word 0x100000001 :=
  ⟨WordCells.pack X cells,by decide,by decide,by decide⟩

end Solidity.Yul.Checks.WordLocals
