import Solidity.Yul.WordCells
import Init.Data.Fin.Lemmas

/-! Concrete logical packing of raw cells into an intrinsic word-local context.
The coordinates are an adapter to the existing interpreter's Fin locals, NOT
solc stack slots, physical memory, Source.Val or compiler refinement. -/
namespace Solidity.Yul

def wordCellWidth : ExternalType → Nat
  | .value _ => 1
  | .externalFunction => 2
  | _ => 0

def wordCellCount : List ExternalType → Nat
  | [] => 0
  | ty :: rest => wordCellWidth ty + wordCellCount rest

def Member.wordSlot {X ty} (index : Member X ty) :
    Fin (wordCellWidth ty) → Fin (wordCellCount X) := by
  apply Member.casesOn (motive := fun X ty _ =>
    Fin (wordCellWidth ty) → Fin (wordCellCount X)) index
  case here => intro ty rest; exact Fin.castAdd (wordCellCount rest)
  case there =>
    intro ty head rest previous
    exact fun field => Fin.natAdd (wordCellWidth head) (previous.wordSlot field)
termination_by structural index

def WordCell.lift {X} (head : ExternalType) : WordCell X → WordCell (head :: X)
  | .scalar ref => .scalar ⟨ref.encoding,.there ref.index⟩
  | .address index => .address (.there index)
  | .selector index => .selector (.there index)

def WordCell.ofMember {X ty} (index : Member X ty)
    (field : Fin (wordCellWidth ty)) : WordCell X := by
  cases ty with
  | value encoding => exact .scalar ⟨encoding,index⟩
  | externalFunction =>
    exact if field.val = 0 then .address index else .selector index
  | memory | calldataStatic | calldataDynamic | storage | internalFunction
  | constant | library => exact Fin.elim0 field

theorem WordCell.ofMember_lift {X ty} (head : ExternalType) (index : Member X ty)
    (field : Fin (wordCellWidth ty)) :
    ofMember (.there (b := head) index) field = (ofMember index field).lift head := by
  cases ty with
  | value encoding => rfl
  | externalFunction =>
    by_cases zero : field.val = 0
    · simp only [ofMember,zero,↓reduceIte,lift]
    · simp only [ofMember,zero,↓reduceIte,lift]
  | memory | calldataStatic | calldataDynamic | storage | internalFunction
  | constant | library => exact Fin.elim0 field

def WordCell.slot {X} : WordCell X → Fin (wordCellCount X)
  | .scalar ref => ref.index.wordSlot ⟨0,by change 0 < 1; decide⟩
  | .address index => index.wordSlot ⟨0,by decide⟩
  | .selector index => index.wordSlot ⟨1,by decide⟩

def WordCells.pack : (X : List ExternalType) → WordCells X → Fin (wordCellCount X) → Word
  | [], _ => Fin.elim0
  | ty :: rest, view => Fin.addCases (motive := fun _ => Word)
      (fun field => view (WordCell.ofMember .here field))
      (pack rest (fun cell => view (cell.lift ty)))

theorem WordCells.pack_member {X ty} (index : Member X ty)
    (view : WordCells X) (field : Fin (wordCellWidth ty)) :
    pack X view (index.wordSlot field) = view (WordCell.ofMember index field) := by
  revert view field
  induction index with
  | @here ty rest =>
    intro view field
    change Fin.addCases (motive := fun _ => Word)
      (fun field => view (WordCell.ofMember (.here : Member (ty :: rest) ty) field))
      (pack rest (fun cell => view (cell.lift ty))) (Fin.castAdd (wordCellCount rest) field) = _
    exact Fin.addCases_left field
  | @there ty head rest previous ih =>
    intro view field
    change Fin.addCases (motive := fun _ => Word)
      (fun field => view (WordCell.ofMember (.here : Member (head :: rest) head) field))
      (pack rest (fun cell => view (cell.lift head)))
      (Fin.natAdd (wordCellWidth head) (previous.wordSlot field)) = _
    rw [Fin.addCases_right,ih]
    exact congrArg view (WordCell.ofMember_lift head previous field).symm

theorem WordCells.pack_cell {X} (view : WordCells X) (cell : WordCell X) :
    pack X view cell.slot = view cell := by
  cases cell with
  | scalar ref => exact pack_member ref.index view ⟨0,by change 0 < 1; decide⟩
  | address index => exact pack_member index view ⟨0,by decide⟩
  | selector index => exact pack_member index view ⟨1,by decide⟩

def WordCells.unpack {X} (values : Fin (wordCellCount X) → Word) : WordCells X :=
  fun cell => values cell.slot

theorem WordCells.unpack_pack {X} (view : WordCells X) :
    unpack (pack X view) = view := by
  funext cell
  exact pack_cell view cell

theorem WordCell.ofMember_slot {X ty} (index : Member X ty)
    (field : Fin (wordCellWidth ty)) :
    (ofMember index field).slot = index.wordSlot field := by
  cases ty with
  | value encoding =>
    change index.wordSlot _ = index.wordSlot field
    apply congrArg index.wordSlot
    apply Fin.ext
    change 0 = field.val
    have bound := field.isLt
    change field.val < 1 at bound
    omega
  | externalFunction =>
    change (if field.val = 0 then WordCell.address index else .selector index).slot = _
    split
    · next zero =>
      apply congrArg index.wordSlot
      apply Fin.ext
      change 0 = field.val
      exact zero.symm
    · next nonzero =>
      apply congrArg index.wordSlot
      apply Fin.ext
      change 1 = field.val
      have bound := field.isLt
      change field.val < 2 at bound
      omega
  | memory | calldataStatic | calldataDynamic | storage | internalFunction
  | constant | library => exact Fin.elim0 field

theorem WordCell.lift_slot {X} (head : ExternalType) (cell : WordCell X) :
    (cell.lift head).slot = Fin.natAdd (wordCellWidth head) cell.slot := by
  cases cell <;> rfl

def wordCellAt : (X : List ExternalType) → Fin (wordCellCount X) → WordCell X
  | [], position => Fin.elim0 position
  | ty :: rest, position => Fin.addCases (motive := fun _ => WordCell (ty :: rest))
      (fun field => WordCell.ofMember .here field)
      (fun i => (wordCellAt rest i).lift ty) position

theorem wordCellAt_member {X ty} (index : Member X ty)
    (field : Fin (wordCellWidth ty)) :
    wordCellAt X (index.wordSlot field) = WordCell.ofMember index field := by
  revert field
  induction index with
  | @here ty rest =>
    intro field
    exact Fin.addCases_left field
  | @there ty head rest previous ih =>
    intro field
    change Fin.addCases (motive := fun _ => WordCell (head :: rest))
      (fun field => WordCell.ofMember (.here : Member (head :: rest) head) field)
      (fun i => (wordCellAt rest i).lift head)
      (Fin.natAdd (wordCellWidth head) (previous.wordSlot field)) = _
    rw [Fin.addCases_right,ih]
    exact (WordCell.ofMember_lift head previous field).symm

theorem wordCellAt_slot {X} (cell : WordCell X) :
    wordCellAt X cell.slot = cell := by
  cases cell with
  | scalar ref => exact wordCellAt_member ref.index ⟨0,by change 0 < 1; decide⟩
  | address index => exact wordCellAt_member index ⟨0,by decide⟩
  | selector index => exact wordCellAt_member index ⟨1,by decide⟩

theorem wordCellAt_slot_inverse (X : List ExternalType)
    (position : Fin (wordCellCount X)) : (wordCellAt X position).slot = position := by
  induction X with
  | nil => exact Fin.elim0 position
  | cons ty rest ih =>
    refine Fin.addCases (motive := fun i => (wordCellAt (ty :: rest) i).slot = i)
      ?_ ?_ position
    · intro field
      change (Fin.addCases (motive := fun _ => WordCell (ty :: rest))
        (fun field => WordCell.ofMember (.here : Member (ty :: rest) ty) field)
        (fun i => (wordCellAt rest i).lift ty) (Fin.castAdd (wordCellCount rest) field)).slot = _
      rw [Fin.addCases_left,WordCell.ofMember_slot]
      rfl
    · intro i
      change (Fin.addCases (motive := fun _ => WordCell (ty :: rest))
        (fun field => WordCell.ofMember (.here : Member (ty :: rest) ty) field)
        (fun i => (wordCellAt rest i).lift ty) (Fin.natAdd (wordCellWidth ty) i)).slot = _
      rw [Fin.addCases_right,WordCell.lift_slot,ih]

theorem WordCell.slot_injective {X} (first second : WordCell X)
    (same : first.slot = second.slot) : first = second := by
  have equal := congrArg (wordCellAt X) same
  rw [wordCellAt_slot,wordCellAt_slot] at equal
  exact equal

theorem wordCellCount_globals (X : List ExternalType) : wordCellCount (globals X) = 0 := by
  by_cases zero : wordCellCount (globals X) = 0
  · exact zero
  · have positive : 0 < wordCellCount (globals X) := Nat.pos_of_ne_zero zero
    exact False.elim (wordCellAt (globals X) ⟨0,positive⟩).not_globals

theorem WordCells.pack_unpack {X} (values : Fin (wordCellCount X) → Word) :
    pack X (unpack values) = values := by
  funext position
  have inverse := wordCellAt_slot_inverse X position
  rw [← inverse,pack_cell]
  rfl


/-- Actual raw-cell updates become the existing interpreter's local-word
update; no caller-supplied agreement or bijection premise is needed. -/
theorem WordCells.pack_write {X} (view : WordCells X) (target : WordCell X)
    (value : Word) :
    pack X (view.write target value) =
      (fun position => if position = target.slot then value else pack X view position) := by
  funext position
  have inverse := wordCellAt_slot_inverse X position
  rw [← inverse,pack_cell,pack_cell]
  by_cases same : wordCellAt X position = target
  · rw [same,write_same,if_pos rfl]
  · have different : (wordCellAt X position).slot ≠ target.slot :=
      fun equal => same (WordCell.slot_injective _ _ equal)
    rw [write_other _ _ _ _ same,if_neg different]

/-- Intrinsic word state: every Solidity cell and Yul local remains in its real
context. This is NOT the clean S02 Source state or a physical view. -/
structure WordState (X : List ExternalType) (n : Nat) where
  locals : Fin n → Word
  cells : WordCells X

def WordState.pack {X n} (state : WordState X n) :
    Fin (n + wordCellCount X) → Word :=
  Fin.addCases (motive := fun _ => Word) state.locals (WordCells.pack X state.cells)

def WordState.unpack {X n} (values : Fin (n + wordCellCount X) → Word) : WordState X n :=
  ⟨fun index => values (Fin.castAdd (wordCellCount X) index),
   fun cell => values (Fin.natAdd n cell.slot)⟩

theorem WordState.pack_local {X n} (state : WordState X n) (index : Fin n) :
    state.pack (Fin.castAdd (wordCellCount X) index) = state.locals index :=
  Fin.addCases_left index

theorem WordState.pack_cell {X n} (state : WordState X n) (cell : WordCell X) :
    state.pack (Fin.natAdd n cell.slot) = state.cells cell := by
  rw [pack,Fin.addCases_right,WordCells.pack_cell]

theorem WordState.unpack_pack {X n} (state : WordState X n) :
    unpack state.pack = state := by
  cases state with
  | mk locals cells =>
    have localEqual : (unpack (WordState.pack ⟨locals,cells⟩)).locals = locals := by
      funext index
      exact pack_local ⟨locals,cells⟩ index
    have cellEqual : (unpack (WordState.pack ⟨locals,cells⟩)).cells = cells := by
      funext cell
      exact pack_cell ⟨locals,cells⟩ cell
    have pairEqual :
        ((unpack (WordState.pack ⟨locals,cells⟩)).locals,
         (unpack (WordState.pack ⟨locals,cells⟩)).cells) = (locals,cells) :=
      Prod.ext localEqual cellEqual
    exact congrArg (fun pair : (Fin n → Word) × WordCells X =>
      (WordState.mk pair.1 pair.2)) pairEqual

theorem WordState.pack_unpack {X n} (values : Fin (n + wordCellCount X) → Word) :
    (unpack values).pack = values := by
  funext position
  refine Fin.addCases (motive := fun i => (unpack values).pack i = values i) ?_ ?_ position
  · intro index
    rw [pack_local]
    rfl
  · intro index
    have inverse := wordCellAt_slot_inverse X index
    rw [← inverse,pack_cell]
    rfl


end Solidity.Yul
