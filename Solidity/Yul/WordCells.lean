import Solidity.Yul.ScalarLocals

/-! Logical raw-word cells for Solidity value locals and the two fields of local
external-function values. These are context occurrences, not physical slots.
Widths describe declarations; writes never clean. Constants and physical views
are not mutable cells. No Source.Val, pipeline refinement or interpreter is
supplied here. -/
namespace Solidity.Yul

inductive WordCell (X : List ExternalType) where
  | scalar : ScalarRef X → WordCell X
  | address : Member X .externalFunction → WordCell X
  | selector : Member X .externalFunction → WordCell X

def WordCell.key {X} : WordCell X → Nat × Attribute
  | .scalar ref => (ref.position,.plain)
  | .address index => (index.position,.address)
  | .selector index => (index.position,.selector)

theorem WordCell.key_injective {X} (first second : WordCell X)
    (same : first.key = second.key) : first = second := by
  cases first with
  | scalar one =>
    cases second with
    | scalar two =>
      have positions := congrArg Prod.fst same
      exact congrArg WordCell.scalar (ScalarRef.position_injective one two positions)
    | address two => cases congrArg Prod.snd same
    | selector two => cases congrArg Prod.snd same
  | address one =>
    cases second with
    | scalar two => cases congrArg Prod.snd same
    | address two =>
      have positions := congrArg Prod.fst same
      have pair := Member.payload_position X ⟨.externalFunction,one⟩
        ⟨.externalFunction,two⟩ positions
      cases pair
      rfl
    | selector two => cases congrArg Prod.snd same
  | selector one =>
    cases second with
    | scalar two => cases congrArg Prod.snd same
    | address two => cases congrArg Prod.snd same
    | selector two =>
      have positions := congrArg Prod.fst same
      have pair := Member.payload_position X ⟨.externalFunction,one⟩
        ⟨.externalFunction,two⟩ positions
      cases pair
      rfl

def WordCell.readRef {X} : WordCell X → ExternalRef X false
  | .scalar ref => ⟨ref.index,.plain,.valueRead⟩
  | .address index => ⟨index,.address,.addressRead⟩
  | .selector index => ⟨index,.selector,.selectorRead⟩

def WordCell.writeRef {X} : WordCell X → ExternalRef X true
  | .scalar ref => ⟨ref.index,.plain,.valueWrite⟩
  | .address index => ⟨index,.address,.addressWrite⟩
  | .selector index => ⟨index,.selector,.selectorWrite⟩

theorem WordCell.not_globals {X} (cell : WordCell (globals X)) : False := by
  cases cell with
  | scalar ref => exact ref.not_globals
  | address index | selector index =>
    have member := index.mem
    change ExternalType.externalFunction ∈ X.filter ExternalType.isGlobal at member
    have global := (List.mem_filter.mp member).2
    cases global

abbrev WordCells (X : List ExternalType) := WordCell X → Word

def WordCells.write {X} (view : WordCells X) (target : WordCell X) (value : Word) :
    WordCells X :=
  fun cell => if cell.key = target.key then value else view cell

theorem WordCells.write_same {X} (view : WordCells X) (target : WordCell X)
    (value : Word) : (view.write target value) target = value := if_pos rfl

theorem WordCells.write_other {X} (view : WordCells X) (target other : WordCell X)
    (value : Word) (different : other ≠ target) :
    (view.write target value) other = view other := by
  apply if_neg
  intro same
  exact different (WordCell.key_injective other target same)

theorem WordCells.write_shadow {X} (view : WordCells X) (target : WordCell X)
    (first second : Word) :
    (view.write target first).write target second = view.write target second := by
  funext cell
  by_cases same : cell.key = target.key
  · simp only [WordCells.write,same,↓reduceIte]
  · simp only [WordCells.write,same,↓reduceIte]

theorem WordCells.write_commute {X} (view : WordCells X) (first second : WordCell X)
    (a b : Word) (different : first ≠ second) :
    (view.write first a).write second b = (view.write second b).write first a := by
  have keys : first.key ≠ second.key :=
    fun same => different (WordCell.key_injective first second same)
  funext cell
  by_cases one : cell.key = first.key
  · simp only [WordCells.write,one,keys,↓reduceIte]
  · by_cases two : cell.key = second.key
    · simp only [WordCells.write,two,Ne.symm keys,↓reduceIte]
    · simp only [WordCells.write,one,two,↓reduceIte]

/-- Raw scalar projection agrees with the existing occurrence-indexed view. -/
def WordCells.scalars {X} (view : WordCells X) : ScalarView X :=
  fun ref => view (.scalar ref)

theorem WordCells.scalar_write {X} (view : WordCells X) (target : ScalarRef X)
    (value : Word) :
    (view.write (.scalar target) value).scalars = view.scalars.write target value := by
  funext ref
  change (if (ref.position,Attribute.plain) = (target.position,Attribute.plain)
    then value else view (.scalar ref)) =
    (if ref.position = target.position then value else view (.scalar ref))
  simp only [Prod.mk.injEq,and_true]

def WordCells.functionEmpty (X : List ExternalType) : WordCells (globals X) :=
  fun cell => False.elim cell.not_globals

theorem WordCells.function_unique {X} (first second : WordCells (globals X)) :
    first = second := by
  funext cell
  exact False.elim cell.not_globals

/-- Recognize only these logical mutable fields, without treating a physical
reference, constant, library or internal-function value as a word cell. -/
def ExternalRef.wordCell {X write} (ref : ExternalRef X write) : Option (WordCell X) :=
  (Access.casesOn
    (motive := fun ty _ _ _ => Member X ty → Option (WordCell X)) ref.access
    (valueRead := fun {e} index => some (.scalar ⟨e,index⟩))
    (valueWrite := fun {e} index => some (.scalar ⟨e,index⟩))
    (memoryRead := fun _ => none) (memoryWrite := fun _ => none)
    (staticRead := fun _ => none) (staticWrite := fun _ => none)
    (offsetRead := fun _ => none) (offsetWrite := fun _ => none)
    (lengthRead := fun _ => none) (lengthWrite := fun _ => none)
    (slotRead := fun {_ _} _ => none) (slotWrite := fun {_} _ => none)
    (storageOffset := fun {_ _} _ => none)
    (selectorRead := fun index => some (.selector index))
    (selectorWrite := fun index => some (.selector index))
    (addressRead := fun index => some (.address index))
    (addressWrite := fun index => some (.address index))
    (constantRead := fun {_} _ => none) (libraryRead := fun _ => none)
    (internalRead := fun _ => none) (internalWrite := fun _ => none)) ref.index

theorem WordCell.read_inverse {X} (cell : WordCell X) :
    cell.readRef.wordCell = some cell := by
  cases cell <;> rfl

theorem WordCell.write_inverse {X} (cell : WordCell X) :
    cell.writeRef.wordCell = some cell := by
  cases cell <;> rfl

theorem WordCells.address_selector {X} (view : WordCells X)
    (index : Member X .externalFunction) (value : Word) :
    (view.write (.address index) value) (.selector index) = view (.selector index) := by
  apply view.write_other
  intro same
  cases same

theorem WordCells.selector_address {X} (view : WordCells X)
    (index : Member X .externalFunction) (value : Word) :
    (view.write (.selector index) value) (.address index) = view (.address index) := by
  apply view.write_other
  intro same
  cases same

/-- Recognition preserves the exact intrinsic occurrence, attribute and access,
rather than only retaining a key or returning a compatible field. -/
theorem ExternalRef.wordCell_read_sound {X} (ref : ExternalRef X false)
    (cell : WordCell X) (found : ref.wordCell = some cell) : ref = cell.readRef := by
  cases ref with
  | mk index attr permit =>
    cases permit <;> cases found <;> rfl

theorem ExternalRef.wordCell_write_sound {X} (ref : ExternalRef X true)
    (cell : WordCell X) (found : ref.wordCell = some cell) : ref = cell.writeRef := by
  cases ref with
  | mk index attr permit =>
    cases permit <;> cases found <;> rfl

end Solidity.Yul
