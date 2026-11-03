import Solidity.Yul.WordCells
namespace Solidity.Yul.Checks.WordCells
def context : List ExternalType :=
  [.value (.unsigned 0),.externalFunction,.value .boolean,.externalFunction,
   .memory,.calldataDynamic,.storage true false,.internalFunction,.constant (word 9)]
def small : WordCell context := .scalar ⟨.unsigned 0,.here⟩
def flag : WordCell context := .scalar ⟨.boolean,.there (.there .here)⟩
def first : Member context .externalFunction := .there .here
def second : Member context .externalFunction := .there (.there (.there .here))
def initial : WordCells context := fun _ => word 0
def dirty : WordCells context :=
  ((initial.write small (word 257)).write flag (word 2)).write (.selector first) (word 0x100000001)

example : small.key = (0,.plain) := rfl
example : flag.key = (2,.plain) := rfl
example : (WordCell.address first).key = (1,.address) := rfl
example : (WordCell.selector first).key = (1,.selector) := rfl
example : (WordCell.address second).key = (3,.address) := rfl
example : dirty small = word 257 := by decide
example : dirty flag = word 2 := by decide
example : dirty (.selector first) = word 0x100000001 := by decide
example : dirty (.address first) = word 0 := by decide
example : dirty (.selector second) = word 0 := by decide
example : (dirty.write (.address first) (word (2^256-1))) (.address first) =
    word (2^256-1) := by decide
example : (dirty.write (.address first) (word (2^256-1))) (.selector first) =
    word 0x100000001 := by decide
example : (dirty.write (.selector first) (word 66)) (.address first) = word 0 := by decide
example : (dirty.write (.selector first) (word 66)) (.selector second) = word 0 := by decide
example : (dirty.write (.selector first) (word 66)) small = word 257 := by decide
example : (dirty.write small (word 258)).scalars ⟨.unsigned 0,.here⟩ = word 258 := by decide
example : (dirty.write (.selector first) (word 66)).write (.selector first) (word 67) =
    dirty.write (.selector first) (word 67) := dirty.write_shadow _ _ _
example : (dirty.write (.selector first) (word 66)).write (.address first) (word 67) =
    (dirty.write (.address first) (word 67)).write (.selector first) (word 66) := by
  apply dirty.write_commute
  intro same
  cases same
example : small.readRef.wordCell = some small := small.read_inverse
example : small.writeRef.wordCell = some small := small.write_inverse
example : (WordCell.address first).readRef.wordCell = some (.address first) := rfl
example : (WordCell.address first).writeRef.wordCell = some (.address first) := rfl
example : (WordCell.selector first).readRef.wordCell = some (.selector first) := rfl
example : (WordCell.selector first).writeRef.wordCell = some (.selector first) := rfl

-- Well-typed physical/internal/constant references are not raw mutable cells.
def memory : ExternalRef [.memory] false := ⟨.here,.plain,.memoryRead⟩
def calldata : ExternalRef [.calldataDynamic] true := ⟨.here,.length,.lengthWrite⟩
def storage : ExternalRef [.storage true false] true := ⟨.here,.slot,.slotWrite⟩
def internalFn : ExternalRef [.internalFunction] false := ⟨.here,.plain,.internalRead⟩
def constant : ExternalRef [.constant (word 9)] false := ⟨.here,.plain,.constantRead⟩
example : memory.wordCell = none := rfl
example : calldata.wordCell = none := rfl
example : storage.wordCell = none := rfl
example : internalFn.wordCell = none := rfl
example : constant.wordCell = none := rfl

-- A real function-global projection contains constants/storage but no cells.
def mixed : List ExternalType :=
  [.value (.unsigned 0),.externalFunction,.constant (word 9),.storage false false]
example : globals mixed = [.constant (word 9),.storage false false] := rfl
example (cell : WordCell (globals mixed)) : False := cell.not_globals
example (one two : WordCells (globals mixed)) : one = two := WordCells.function_unique one two

def inhabited : Nonempty (WordCell context) := ⟨small⟩
def dirtyWitness : ∃ view : WordCells context,
    view small = word 257 ∧ view flag = word 2 ∧
    view (.selector first) = word 0x100000001 :=
  ⟨dirty,by decide,by decide,by decide⟩
end Solidity.Yul.Checks.WordCells
