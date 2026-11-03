import Solidity.Yul.WordLocals
import Solidity.Yul.TierPolicy

/-! Concrete tier-A external operands. Each admitted read is a typed raw cell
or the actual declared constant word, and each admitted write is a real cell.
No physical, internal-function or resource fallback is supplied. -/
namespace Solidity.Yul

inductive WordRead (X : List ExternalType) where
  | cell : WordCell X → WordRead X
  | literal : Word → WordRead X

def WordAccessResult (X : List ExternalType) : Bool → Type
  | false => WordRead X
  | true => WordCell X

def wordAccess {X ty attr write} (cap : Access ty attr write) (index : Member X ty)
    (allowed : Policy.ExternalP .A ty) : WordAccessResult X write :=
  (Access.casesOn
    (motive := fun ty _ write _ =>
      Member X ty → Policy.ExternalP .A ty → WordAccessResult X write) cap
    (valueRead := fun {e} index _ => WordRead.cell (.scalar ⟨e,index⟩))
    (valueWrite := fun {e} index _ => WordCell.scalar ⟨e,index⟩)
    (memoryRead := fun _ policy => False.elim (by cases policy))
    (memoryWrite := fun _ policy => False.elim (by cases policy))
    (staticRead := fun _ policy => False.elim (by cases policy))
    (staticWrite := fun _ policy => False.elim (by cases policy))
    (offsetRead := fun _ policy => False.elim (by cases policy))
    (offsetWrite := fun _ policy => False.elim (by cases policy))
    (lengthRead := fun _ policy => False.elim (by cases policy))
    (lengthWrite := fun _ policy => False.elim (by cases policy))
    (slotRead := fun {_ _} _ policy => False.elim (by cases policy))
    (slotWrite := fun {_} _ policy => False.elim (by cases policy))
    (storageOffset := fun {_ _} _ policy => False.elim (by cases policy))
    (selectorRead := fun index _ => WordRead.cell (.selector index))
    (selectorWrite := fun index _ => WordCell.selector index)
    (addressRead := fun index _ => WordRead.cell (.address index))
    (addressWrite := fun index _ => WordCell.address index)
    (constantRead := fun {value} _ _ => WordRead.literal value)
    (libraryRead := fun _ policy => False.elim (by cases policy))
    (internalRead := fun _ policy => False.elim policy)
    (internalWrite := fun _ policy => False.elim policy)) index allowed

def ExternalRef.wordRead {X} (ref : ExternalRef X false)
    (allowed : Policy.ExternalP .A ref.ty) : WordRead X :=
  wordAccess ref.access ref.index allowed

def ExternalRef.wordWrite {X} (ref : ExternalRef X true)
    (allowed : Policy.ExternalP .A ref.ty) : WordCell X :=
  wordAccess ref.access ref.index allowed

theorem WordCell.read_word {X} (cell : WordCell X)
    (allowed : Policy.ExternalP .A cell.readRef.ty) :
    cell.readRef.wordRead allowed = WordRead.cell cell := by
  cases cell <;> rfl

theorem WordCell.write_word {X} (cell : WordCell X)
    (allowed : Policy.ExternalP .A cell.writeRef.ty) :
    cell.writeRef.wordWrite allowed = cell := by
  cases cell <;> rfl

theorem ExternalRef.wordWrite_ref {X} (ref : ExternalRef X true)
    (allowed : Policy.ExternalP .A ref.ty) :
    (ref.wordWrite allowed).writeRef = ref := by
  cases ref with
  | mk index attr cap => cases cap <;> first | rfl | cases allowed

theorem ExternalRef.wordRead_cell_ref {X} (ref : ExternalRef X false)
    (allowed : Policy.ExternalP .A ref.ty) (cell : WordCell X)
    (found : ref.wordRead allowed = .cell cell) : cell.readRef = ref := by
  cases ref with
  | mk index attr cap =>
    cases cap <;> first | (cases found; rfl) | (cases allowed; done) | (cases found; done)

theorem ExternalRef.wordRead_literal_type {X} (ref : ExternalRef X false)
    (allowed : Policy.ExternalP .A ref.ty) (value : Word)
    (found : ref.wordRead allowed = .literal value) : ref.ty = .constant value := by
  cases ref with
  | mk index attr cap =>
    cases cap <;> first | (cases found; rfl) | (cases allowed; done) | (cases found; done)

def WordRead.expression {F X n} (operand : WordRead X) (cells : WordCell X → Fin n) :
    Expr F [] n 1 :=
  match operand with
  | .cell ref => .local (cells ref)
  | .literal value => .literal value

end Solidity.Yul
