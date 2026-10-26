import Solidity.Semantics.RecursiveStorage.Defaults

namespace Solidity.TypeGraph

inductive Step {n : Nat} (G : Schema n) : Ty n → Ty n → Type where
  | field {i : Fin n} {T : Ty n} (position : Field (G.fields i) T) :
      Step G (.node i) T
  | index {E : Ty n} (index : Index) : Step G (.array E) E
  | fixed {E : Ty n} {m : FixedSize} (index : Index) : Step G (.fixed E m) E
  | key {K : PrimTy} {V : Ty n} (key : K.Denote) : Step G (.mapping K V) V

def Step.get {n : Nat} {G : Schema n}
    (defaults : (T : Ty n) → Value G T) :
    {A B : Ty n} → Step G A B → Value G A → Option (Value G B)
  | _, _, .field p, .node fs => some (Fields.get fs p)
  | _, _, .index i, .array extent _ _ slots =>
    if hi : i.val < extent.val then
      some ((slots ⟨i.val, hi⟩).getD (defaults _))
    else none
  | _, _, .fixed i, @Value.fixed _ _ E m slots =>
    if hi : i.val < m.val then
      some ((slots ⟨i.val, hi⟩).getD (defaults E))
    else none
  | _, _, .key k, .mapping slots => some ((slots k).getD (defaults _))

def Step.put {n : Nat} {G : Schema n} :
    {A B : Ty n} → Step G A B → Value G A → Value G B → Option (Value G A)
  | _, _, .field p, .node fs, v => some (.node (Fields.set fs p v))
  | _, _, .index i, .array extent length h slots, v =>
    if hi : i.val < extent.val then
      some (.array extent length h (Slots.write slots ⟨i.val, hi⟩ v))
    else none
  | _, _, .fixed i, @Value.fixed _ _ E m slots, v =>
    if hi : i.val < m.val then
      some (.fixed (Slots.write slots ⟨i.val, hi⟩ v))
    else none
  | _, _, .key k, .mapping slots, v => some (.mapping (Slots.write slots k v))

inductive Path {n : Nat} (G : Schema n) : Ty n → Ty n → Type where
  | nil {T : Ty n} : Path G T T
  | cons {A B C : Ty n} (step : Step G A B) (rest : Path G B C) : Path G A C

def Path.read {n : Nat} {G : Schema n}
    (defaults : (T : Ty n) → Value G T) :
    {A B : Ty n} → Path G A B → Value G A → Option (Value G B)
  | _, _, .nil, v => some v
  | _, _, .cons s p, v => (s.get defaults v).bind (p.read defaults)

def Path.save {n : Nat} {G : Schema n}
    (defaults : (T : Ty n) → Value G T) :
    {A B : Ty n} → Path G A B → Value G A → Value G B → Option (Value G A)
  | _, _, .nil, _, v => some v
  | _, _, .cons s p, root, v => do
    let old ← s.get defaults root
    let value ← p.save defaults old v
    s.put root value

def Path.append {n : Nat} {G : Schema n} :
    {A B C : Ty n} → Path G A B → Path G B C → Path G A C
  | _, _, _, .nil, q => q
  | _, _, _, .cons s p, q => .cons s (p.append q)

def Step.toStr {n : Nat} {G : Schema n} : {A B : Ty n} → Step G A B → String
  | _, _, .field p => "." ++ p.name
  | _, _, .index i => s!"[{i.val}]"
  | _, _, .fixed i => s!"[{i.val}]"
  | _, _, .key k => s!"[{PrimTy.key k}]"

def Path.toStr {n : Nat} {G : Schema n} : {A B : Ty n} → Path G A B → String
  | _, _, .nil => ""
  | _, _, .cons s p => s.toStr ++ p.toStr

theorem Step.get_put {n : Nat} {G : Schema n}
    (defaults : (T : Ty n) → Value G T) {A B : Ty n}
    (s : Step G A B) (root result : Value G A) (v : Value G B)
    (h : s.put root v = some result) : s.get defaults result = some v := by
  cases s with
  | field p =>
    cases root with
    | node fs =>
      cases h
      exact congrArg some (Fields.get_set fs p v)
  | index i =>
    cases root with
    | array extent length le slots =>
      simp only [Step.put] at h
      split at h
      next hi =>
        cases h
        simp only [Step.get, dif_pos hi, Slots.write_self, Slot.getD]
      next hi => cases h
  | fixed i =>
    cases root with
    | fixed slots =>
      simp only [Step.put] at h
      split at h
      next hi =>
        cases h
        simp only [Step.get, dif_pos hi, Slots.write_self, Slot.getD]
      next hi => cases h
  | key k =>
    cases root with
    | mapping slots =>
      cases h
      simp only [Step.get, Slots.write_self, Slot.getD]

theorem Path.read_save {n : Nat} {G : Schema n}
    (defaults : (T : Ty n) → Value G T) {A B : Ty n}
    (p : Path G A B) (root result : Value G A) (v : Value G B)
    (h : p.save defaults root v = some result) :
    p.read defaults result = some v := by
  induction p with
  | nil => cases h; rfl
  | cons s p ih =>
    simp only [Path.save, Option.bind_eq_bind] at h
    cases hg : s.get defaults root with
    | none => simp only [hg, Option.bind_none] at h; cases h
    | some old =>
      cases hs : p.save defaults old v with
      | none => simp only [hg, hs, Option.bind_some, Option.bind_none] at h; cases h
      | some value =>
        simp only [hg, hs, Option.bind_some] at h
        have hr : s.get defaults result = some value := s.get_put defaults root result value h
        simp only [Path.read, hr, Option.bind_some]
        exact ih old value v hs

theorem Path.read_append {n : Nat} {G : Schema n}
    (defaults : (T : Ty n) → Value G T) {A B C : Ty n}
    (p : Path G A B) (q : Path G B C) (root : Value G A) :
    (p.append q).read defaults root =
      (p.read defaults root).bind (q.read defaults) := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    simp only [Path.append, Path.read]
    cases hg : s.get defaults root with
    | none => rfl
    | some v => exact ih q v

end Solidity.TypeGraph
