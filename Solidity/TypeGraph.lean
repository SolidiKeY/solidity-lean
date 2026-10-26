import Solidity.AST

/-!
A finite declaration graph for recursive Solidity structs. Node positions
retain declaration identity within a compilation unit. The inline-layout
certificate follows struct and fixed-array edges and stops at mappings and
dynamic arrays. Runtime observations may follow either kind of guarded edge
for any finite number of steps.

This module does not change the existing Ty or structDef representation.
The graph storage and its compatibility boundaries are documented separately.
-/

namespace Solidity.TypeGraph

abbrev Index := Fin (2 ^ 256)

abbrev FixedSize := { m : Nat // 0 < m ∧ m < 2 ^ 256 }

inductive Ty (n : Nat) where
  | prim (p : PrimTy)
  | node (id : Fin n)
  | array (elem : Ty n)
  | fixed (elem : Ty n) (size : FixedSize)
  | mapping (key : PrimTy) (value : Ty n)
  deriving DecidableEq, Repr

def Ty.inlineRank {n : Nat} (rank : Fin n → Nat) : Ty n → Nat
  | .prim _ => 0
  | .node i => rank i
  | .array _ => 0
  | .fixed E _ => E.inlineRank rank + 1
  | .mapping _ _ => 0

def Ty.isPrimitive {n : Nat} : Ty n → Bool
  | .prim _ => true
  | _ => false

def Ty.toStr {n : Nat} (names : Fin n → Name) : Ty n → String
  | .prim p => p.toStr
  | .node i => names i
  | .array E => s!"{E.toStr names}[]"
  | .fixed E m => s!"{E.toStr names}[{m.val}]"
  | .mapping K V => s!"mapping({K.toStr}=>{V.toStr names})"

/-- The rank is a layout certificate, not a bound on path depth or on
stored recursive data. Mapping-freedom requires graph reachability instead. -/
structure Schema (n : Nat) where
  origin : Name
  declId : Fin n → Nat
  declId_injective : ∀ i j, declId i = declId j → i = j
  name : Fin n → Name
  fields : Fin n → List (Name × Ty n)
  rank : Fin n → Nat
  nonempty : ∀ i, (fields i).isEmpty = false
  distinct : ∀ i, Semantics.nodupKeysB (fields i) = true
  guarded : ∀ i (f : Name × Ty n), f ∈ fields i →
    f.2.inlineRank rank < rank i

/-- A typed member position. Names remain metadata of the ordered schema. -/
inductive Field {n : Nat} : List (Name × Ty n) → Ty n → Type where
  | here {f : Name} {T : Ty n} {fs : List (Name × Ty n)} :
      Field ((f, T) :: fs) T
  | there {f : Name} {S T : Ty n} {fs : List (Name × Ty n)} (p : Field fs T) :
      Field ((f, S) :: fs) T

def Field.toNat {n : Nat} {fs : List (Name × Ty n)} {T : Ty n} :
    Field fs T → Nat
  | .here => 0
  | .there p => p.toNat + 1

theorem Field.toNat_lt {n : Nat} {fs : List (Name × Ty n)} {T : Ty n}
    (p : Field fs T) : p.toNat < fs.length := by
  induction p with
  | here => exact Nat.succ_pos _
  | there p ih => exact Nat.succ_lt_succ ih

def Field.name {n : Nat} {fs : List (Name × Ty n)} {T : Ty n}
    (p : Field fs T) : Name := (fs[p.toNat]'p.toNat_lt).1

theorem Field.type_eq {n : Nat} :
    {fs : List (Name × Ty n)} → {T U : Ty n} →
    (p : Field fs T) → (q : Field fs U) → p.toNat = q.toNat → T = U
  | _, _, _, .here, .here, _ => rfl
  | _, _, _, .here, .there _, h => Nat.noConfusion h
  | _, _, _, .there _, .here, h => Nat.noConfusion h
  | _, _, _, .there p, .there q, h => Field.type_eq p q (Nat.succ.inj h)

theorem Field.eq_of_toNat_eq {n : Nat} :
    {fs : List (Name × Ty n)} → {T : Ty n} →
    (p q : Field fs T) → p.toNat = q.toNat → p = q
  | _, _, .here, .here, _ => rfl
  | _, _, .here, .there _, h => Nat.noConfusion h
  | _, _, .there _, .here, h => Nat.noConfusion h
  | _, _, .there p, .there q, h =>
      congrArg Field.there (Field.eq_of_toNat_eq p q (Nat.succ.inj h))

theorem Field.mem {n : Nat} : {fs : List (Name × Ty n)} → {T : Ty n} →
    (p : Field fs T) → ∃ f : Name, (f, T) ∈ fs
  | _, _, .here => ⟨_, .head _⟩
  | _, _, .there p => by
    obtain ⟨f, h⟩ := p.mem
    exact ⟨f, .tail _ h⟩

theorem Field.rank_lt {n : Nat} {fs : List (Name × Ty n)} {T : Ty n}
    {rank : Fin n → Nat} {k : Nat} (p : Field fs T)
    (h : ∀ f ∈ fs, f.2.inlineRank rank < k) : T.inlineRank rank < k := by
  obtain ⟨f, hf⟩ := p.mem
  exact h (f, T) hf

/-- A node reached without crossing a mapping or dynamic-array boundary. -/
inductive Inline {n : Nat} : Ty n → Fin n → Prop where
  | node {i : Fin n} : Inline (.node i) i
  | fixed {E : Ty n} {m : FixedSize} {i : Fin n} (h : Inline E i) :
      Inline (.fixed E m) i

theorem Inline.rank_le {n : Nat} (rank : Fin n → Nat) :
    {T : Ty n} → {i : Fin n} → Inline T i → rank i ≤ T.inlineRank rank
  | _, _, .node => Nat.le_refl _
  | _, _, .fixed h =>
    Nat.le_trans (Inline.rank_le rank h) (Nat.le_succ _)

theorem Schema.no_inline_self {n : Nat} (G : Schema n)
    {i : Fin n} {f : Name} {T : Ty n} (hf : (f, T) ∈ G.fields i) :
    ¬ Inline T i :=
  fun h => Nat.lt_irrefl (G.rank i)
    (Nat.lt_of_le_of_lt (Inline.rank_le G.rank h) (G.guarded i (f, T) hf))

/-- One or more inline declaration edges; guarded edges are absent. -/
inductive InlinePath {n : Nat} (G : Schema n) : Fin n → Fin n → Prop where
  | field {i j : Fin n} {f : Name} {T : Ty n}
      (hf : (f, T) ∈ G.fields i) (h : Inline T j) : InlinePath G i j
  | trans {i j k : Fin n} (a : InlinePath G i j) (b : InlinePath G j k) :
      InlinePath G i k

theorem InlinePath.decreases {n : Nat} {G : Schema n} :
    {i j : Fin n} → InlinePath G i j → G.rank j < G.rank i
  | _, _, .field hf h =>
    Nat.lt_of_le_of_lt (Inline.rank_le G.rank h) (G.guarded _ _ hf)
  | _, _, .trans a b =>
    Nat.lt_trans (InlinePath.decreases b) (InlinePath.decreases a)

theorem Schema.no_inline_cycle {n : Nat} (G : Schema n) (i : Fin n) :
    ¬ InlinePath G i i :=
  fun h => Nat.lt_irrefl (G.rank i) (InlinePath.decreases h)

end Solidity.TypeGraph
