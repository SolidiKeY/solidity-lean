import Solidity.Yul.DirectWords

/-! Typed logical coordinates of the existing raw local/cell banks. This is
not a compiler stack, physical memory or new source state. Both inverse laws
are real fields; concrete canonical/prepend constructions discharge them. -/
namespace Solidity.Yul

structure Coordinates (X : List ExternalType) (n m : Nat) where
  locals : Fin n → Fin m
  cells : WordCell X → Fin m
  origin : Fin m → Sum (Fin n) (WordCell X)
  origin_local : ∀ i, origin (locals i) = .inl i
  origin_cell : ∀ cell, origin (cells cell) = .inr cell
  location_origin : ∀ i, Sum.elim locals cells (origin i) = i

namespace Coordinates
def location {X n m} (coordinates : Coordinates X n m) : Sum (Fin n) (WordCell X) → Fin m :=
  Sum.elim coordinates.locals coordinates.cells

def pack {X n m} (coordinates : Coordinates X n m) (state : WordState X n) : Closed.Values m :=
  fun i => match coordinates.origin i with
    | .inl index => state.locals index
    | .inr cell => state.cells cell

theorem pack_local {X n m} (coordinates : Coordinates X n m) (state : WordState X n) (i : Fin n) :
    coordinates.pack state (coordinates.locals i) = state.locals i := by
  simp only [pack,coordinates.origin_local]

theorem pack_cell {X n m} (coordinates : Coordinates X n m) (state : WordState X n) (cell : WordCell X) :
    coordinates.pack state (coordinates.cells cell) = state.cells cell := by
  simp only [pack,coordinates.origin_cell]

theorem origin_injective {X n m} (coordinates : Coordinates X n m)
    (one two : Fin m) (same : coordinates.origin one = coordinates.origin two) : one = two := by
  have located := congrArg coordinates.location same
  exact (coordinates.location_origin one).symm.trans (located.trans (coordinates.location_origin two))

theorem local_injective {X n m} (coordinates : Coordinates X n m)
    (one two : Fin n) (same : coordinates.locals one = coordinates.locals two) : one = two := by
  have origins := congrArg coordinates.origin same
  rw [coordinates.origin_local,coordinates.origin_local] at origins
  exact Sum.inl.inj origins

theorem cell_injective {X n m} (coordinates : Coordinates X n m)
    (one two : WordCell X) (same : coordinates.cells one = coordinates.cells two) : one = two := by
  have origins := congrArg coordinates.origin same
  rw [coordinates.origin_cell,coordinates.origin_cell] at origins
  exact Sum.inr.inj origins

theorem disjoint {X n m} (coordinates : Coordinates X n m) (i : Fin n) (cell : WordCell X) :
    coordinates.locals i ≠ coordinates.cells cell := by
  intro same
  have origins := congrArg coordinates.origin same
  rw [coordinates.origin_local,coordinates.origin_cell] at origins
  cases origins

def canonical (X : List ExternalType) (n : Nat) : Coordinates X n (n+wordCellCount X) where
  locals := Fin.castAdd (wordCellCount X)
  cells := fun cell => Fin.natAdd n cell.slot
  origin := Fin.addCases .inl (fun i => .inr (wordCellAt X i))
  origin_local := fun i => Fin.addCases_left i
  origin_cell := fun cell => by
    rw [Fin.addCases_right,wordCellAt_slot]
  location_origin := fun i => by
    refine Fin.addCases (motive := fun i =>
      Sum.elim (Fin.castAdd (wordCellCount X)) (fun cell => Fin.natAdd n cell.slot)
        (Fin.addCases Sum.inl (fun j => Sum.inr (wordCellAt X j)) i) = i) ?_ ?_ i
    · intro j
      rw [Fin.addCases_left]
      rfl
    · intro j
      rw [Fin.addCases_right]
      exact congrArg (Fin.natAdd n) (wordCellAt_slot_inverse X j)

theorem canonical_pack {X n} (state : WordState X n) :
    (canonical X n).pack state = state.pack := by
  funext i
  refine Fin.addCases (motive := fun i => (canonical X n).pack state i = state.pack i) ?_ ?_ i
  · intro j
    exact (pack_local (canonical X n) state j).trans (state.pack_local j).symm
  · intro j
    have position : Fin.natAdd n j = Fin.natAdd n (wordCellAt X j).slot :=
      congrArg (Fin.natAdd n) (wordCellAt_slot_inverse X j).symm
    rw [position]
    exact (pack_cell (canonical X n) state (wordCellAt X j)).trans
      (state.pack_cell (wordCellAt X j)).symm

def prepend {X n m} (r : Nat) (coordinates : Coordinates X n m) :
    Coordinates X (r+n) (r+m) where
  locals := WordAdapter.bindLocals r coordinates.locals
  cells := fun cell => Fin.natAdd r (coordinates.cells cell)
  origin := Fin.addCases (fun i => .inl (Fin.castAdd n i)) (fun i =>
    match coordinates.origin i with
    | .inl index => .inl (Fin.natAdd r index)
    | .inr cell => .inr cell)
  origin_local := fun i => by
    refine Fin.addCases (motive := fun i =>
      (Fin.addCases (motive := fun _ => Sum (Fin (r+n)) (WordCell X)) (fun j => Sum.inl (Fin.castAdd n j)) (fun j =>
        match coordinates.origin j with
        | .inl index => .inl (Fin.natAdd r index)
        | .inr cell => .inr cell)) (WordAdapter.bindLocals r coordinates.locals i) = Sum.inl i) ?_ ?_ i
    · intro j
      simp only [WordAdapter.bindLocals,Fin.addCases_left]
    · intro j
      simp only [WordAdapter.bindLocals,Fin.addCases_right,coordinates.origin_local]
  origin_cell := fun cell => by
    simp only [Fin.addCases_right,coordinates.origin_cell]
  location_origin := fun i => by
    refine Fin.addCases (motive := fun i =>
      Sum.elim (WordAdapter.bindLocals r coordinates.locals)
        (fun cell => Fin.natAdd r (coordinates.cells cell))
        (Fin.addCases (motive := fun _ => Sum (Fin (r+n)) (WordCell X)) (fun j => Sum.inl (Fin.castAdd n j)) (fun j =>
          match coordinates.origin j with
          | .inl index => .inl (Fin.natAdd r index)
          | .inr cell => .inr cell) i) = i) ?_ ?_ i
    · intro j
      simp only [Fin.addCases_left,Sum.elim_inl,WordAdapter.bindLocals]
    · intro j
      rw [Fin.addCases_right]
      have located := coordinates.location_origin j
      cases source : coordinates.origin j with
      | inl index =>
        rw [source] at located
        change coordinates.locals index = j at located
        change WordAdapter.bindLocals r coordinates.locals (Fin.natAdd r index) = Fin.natAdd r j
        rw [WordAdapter.bindLocals,Fin.addCases_right,located]
      | inr cell =>
        rw [source] at located
        change coordinates.cells cell = j at located
        exact congrArg (Fin.natAdd r) located

end Coordinates

def WordState.extend {X n r} (front : Closed.Values r) (state : WordState X n) :
    WordState X (r+n) := ⟨Closed.extendValues front state.locals,state.cells⟩

def WordState.drop {X n} (r : Nat) (state : WordState X (r+n)) : WordState X n :=
  ⟨Closed.dropValues r state.locals,state.cells⟩

namespace Coordinates
theorem pack_prefix {X n m r} (coordinates : Coordinates X n m)
    (front : Closed.Values r) (state : WordState X n) :
    (coordinates.prepend r).pack (state.extend front) = Closed.extendValues front (coordinates.pack state) := by
  funext i
  refine Fin.addCases (motive := fun i =>
    (coordinates.prepend r).pack (state.extend front) i =
      Closed.extendValues front (coordinates.pack state) i) ?_ ?_ i
  · intro j
    simp only [pack,prepend,Fin.addCases_left,WordState.extend,Closed.extendValues]
  · intro j
    simp only [pack,prepend,Fin.addCases_right,WordState.extend,Closed.extendValues]
    cases source : coordinates.origin j with
    | inl index => exact Fin.addCases_right index
    | inr cell => rfl

theorem pack_drop {X n m r} (coordinates : Coordinates X n m) (state : WordState X (r+n)) :
    coordinates.pack (state.drop r) = Closed.dropValues r ((coordinates.prepend r).pack state) := by
  funext i
  simp only [pack,WordState.drop,Closed.dropValues,prepend,Fin.addCases_right]
  cases coordinates.origin i <;> rfl

theorem expression_agrees (fuel : Nat) {X n m r} (coordinates : Coordinates X n m)
    (code : Expr [] X n r) (policy : Policy.ExprP .A code) (state : WordState X n) :
    DirectWords.eval fuel code policy state =
      Closed.evalExpr fuel .nil True.intro
        (WordAdapter.expression code policy coordinates.locals coordinates.cells).code
        (WordAdapter.expression code policy coordinates.locals coordinates.cells).words
        (coordinates.pack state) :=
  DirectWords.agrees fuel code policy state coordinates.locals coordinates.cells
    (coordinates.pack state) (coordinates.pack_local state) (coordinates.pack_cell state)

end Coordinates
end Solidity.Yul
