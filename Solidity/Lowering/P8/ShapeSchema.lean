import Solidity.Lowering.P8.ScalarSchema

/-! Partial executable Source type/schema extraction using existing graph
constructors. Node/recursive and all unsupported source cases remain OPEN.
No runtime/value preservation or full frontend admission follows. -/
namespace Solidity.Lowering.P8
open V07

structure ShapeCode (D : Source.Layout) {n : Nat} (names : Fin n → Source.DeclName)
    (τ : Source.STy) where
  target : TypeGraph.Ty n
  related : GraphTypeRel D names τ target
  height : Nat
  inline_eq : ∀ rank, target.inlineRank rank = height

def scalarShape {D : Source.Layout} {n : Nat} {names : Fin n → Source.DeclName}
    {τ : Source.STy} (c : ScalarCode D names τ) : ShapeCode D names τ :=
  ⟨.prim c.prim, c.related, 0, fun _ => rfl⟩

/-- Structural recursion consumes actual source type children. UDVT underlyings
are checked by the scalar producer, never recursively assumed well-founded. -/
def encodeShape (D : Source.Layout) {n : Nat} (names : Fin n → Source.DeclName) :
    (τ : Source.STy) → Option (ShapeCode D names τ)
  | .array loc elem len => do
    let e ← encodeShape D names elem
    match len with
    | none => return ⟨.array e.target, .array loc e.related, 0, fun _ => rfl⟩
    | some m =>
      if h : 0 < m ∧ m < 2^256 then
        return ⟨.fixed e.target ⟨m, h⟩, .fixed loc ⟨m, h⟩ e.related, e.height + 1, by
          intro rank
          change e.target.inlineRank rank + 1 = e.height + 1
          rw [e.inline_eq]⟩
      else none
  | .mapping key value => do
    let k ← encodeScalar D names key
    let v ← encodeShape D names value
    return ⟨.mapping k.prim v.target, .mapping k.related v.related, 0, fun _ => rfl⟩
  | .udvt d => do
    let u ← encodeScalar D names (D.underlying d)
    return ⟨.prim u.prim, .udvt u.related, 0, fun _ => rfl⟩
  | τ => (encodeScalar D names τ).map scalarShape

structure ShapeFields (D : Source.Layout) {n : Nat} (names : Fin n → Source.DeclName)
    (source : List (String × Source.STy)) where
  target : List (Name × TypeGraph.Ty n)
  related : GraphFieldsRel D names source target
  bound : Nat
  guarded : ∀ rank f, f ∈ target → f.2.inlineRank rank < bound

def encodeShapeFields (D : Source.Layout) {n : Nat} (names : Fin n → Source.DeclName) :
    (source : List (String × Source.STy)) → Option (ShapeFields D names source)
  | [] => some ⟨[], .nil, 1, by intro rank f hf; cases hf⟩
  | (name, τ) :: rest => do
    let head ← encodeShape D names τ
    let tail ← encodeShapeFields D names rest
    return ⟨(name, head.target) :: tail.target, .cons rfl head.related tail.related,
      head.height + tail.bound + 1, by
        intro rank f hf
        rcases List.mem_cons.mp hf with he | ht
        · subst f
          change head.target.inlineRank rank < head.height + tail.bound + 1
          rw [head.inline_eq]
          omega
        · have hh := tail.guarded rank f ht
          omega⟩

/-- Actual resolved singleton producer. Every schema/rank/field certificate
is computed here; no target graph or desired execution is an input. -/
def shapeStruct (d : Source.Decl) (hd : d.kind = .struct) (loc : Source.DataLoc) :
    Option (Σ G : TypeGraph.Schema 1, DeclarationGraph (singletonEnv d) loc G) :=
  match hf : (singletonEnv d).structFields (sourceName d) loc with
  | none => none
  | some fs => do
    let code ← encodeShapeFields (singletonEnv d).layout (fun _ : Fin 1 => sourceName d) fs
    if hn : code.target.isEmpty = false then
      if hdup : Semantics.nodupKeysB code.target = true then
        let G : TypeGraph.Schema 1 := {
          origin := d.name
          declId := fun _ => 0
          declId_injective := by intro i j _; apply Fin.ext; omega
          name := fun _ => d.name
          fields := fun _ => code.target
          rank := fun _ => code.bound
          nonempty := fun _ => hn
          distinct := fun _ => hdup
          guarded := by intro i f h; exact code.guarded (fun _ => code.bound) f h }
        return ⟨G, {
          sourceName := fun _ => sourceName d
          sourceName_injective := by intro i j _; apply Fin.ext; omega
          sourceIndex := fun _ => ⟨0, by change 0 < 1; decide⟩
          identity := fun _ => rfl
          source_kind := fun _ => hd
          source_scope := fun _ => rfl
          source_name := fun _ => rfl
          source_resolves := by
            intro i
            simp only [Source.Env.declOf, singletonEnv, sourceName, List.find?_cons,
              hd, beq_self_eq_true, Bool.true_and]
            rfl
          target_name := fun _ => rfl
          sourceFields := fun _ => fs
          fields_resolve := fun _ => hf
          fields_relate := fun _ => code.related
          complete := by
            intro j _
            have hj : j = ⟨0, by change 0 < 1; decide⟩ := by apply Fin.ext; change j.val = 0; have hb := j.isLt; change j.val < 1 at hb; omega
            exact ⟨⟨0, by change 0 < 1; decide⟩, hj.symm⟩ }⟩
      else none
    else none


#print axioms encodeShape
#print axioms shapeStruct
end Solidity.Lowering.P8
