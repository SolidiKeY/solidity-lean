import Solidity.Lowering.P8.ShapeSchema

/-! Guarded recursive singleton extraction over existing
Source/TypeGraph definitions. Not admitted profile/heap execution preservation. -/
namespace Solidity.Lowering.P8
open V07

structure GraphCode (D : Source.Layout) {n : Nat} (names : Fin n → Source.DeclName)
    (τ : Source.STy) where
  target : TypeGraph.Ty n
  related : GraphTypeRel D names τ target

def findNode {n : Nat} (names : Fin n → Source.DeclName) (d : Source.DeclName) :
    Option {i : Fin n // names i = d} :=
  match h : (List.finRange n).find? (fun i => decide (names i = d)) with
  | none => none
  | some i => some ⟨i, of_decide_eq_true (List.find?_some (p := fun j => decide (names j = d)) h)⟩

def encodeGraph (D : Source.Layout) {n : Nat} (names : Fin n → Source.DeclName) :
    (τ : Source.STy) → Option (GraphCode D names τ)
  | .struct loc d => do
    let i ← findNode names d
    return ⟨.node i.val, Eq.mp (congrArg
      (fun d' => GraphTypeRel D names (.struct loc d') (.node i.val))
      i.property) (.node loc i.val)⟩
  | .array loc elem len => do
    let e ← encodeGraph D names elem
    match len with
    | none => return ⟨.array e.target, .array loc e.related⟩
    | some m =>
      if h : 0 < m ∧ m < 2^256 then
        return ⟨.fixed e.target ⟨m, h⟩, .fixed loc ⟨m, h⟩ e.related⟩
      else none
  | .mapping key value => do
    let k ← encodeGraph D names key
    let v ← encodeGraph D names value
    match hk : k.target with
    | .prim p => return ⟨.mapping p v.target, .mapping (hk ▸ k.related) v.related⟩
    | _ => none
  | τ => (encodeShape D names τ).map (fun c => ⟨c.target, c.related⟩)

structure GraphFields (D : Source.Layout) {n : Nat} (names : Fin n → Source.DeclName)
    (source : List (String × Source.STy)) where
  target : List (Name × TypeGraph.Ty n)
  related : GraphFieldsRel D names source target

def encodeGraphFields (D : Source.Layout) {n : Nat} (names : Fin n → Source.DeclName) :
    (source : List (String × Source.STy)) → Option (GraphFields D names source)
  | [] => some ⟨[], .nil⟩
  | (name, τ) :: rest => do
    let head ← encodeGraph D names τ
    let tail ← encodeGraphFields D names rest
    return ⟨(name, head.target) :: tail.target, .cons rfl head.related tail.related⟩

def schemaRank {n : Nat} (fs : List (Name × TypeGraph.Ty n)) : Nat :=
  fs.foldl (fun h f => max h (f.2.inlineRank (fun _ => 0))) 0 + 1

/-- Guardedness is actually checked at the computed rank, never assumed.
Uniform singleton ranks intentionally do not establish multi-node extraction. -/
def graphStruct (d : Source.Decl) (hd : d.kind = .struct) (loc : Source.DataLoc) :
    Option (Σ G : TypeGraph.Schema 1, DeclarationGraph (singletonEnv d) loc G) :=
  match hf : (singletonEnv d).structFields (sourceName d) loc with
  | none => none
  | some fs => do
    let code ← encodeGraphFields (singletonEnv d).layout (fun _ : Fin 1 => sourceName d) fs
    if hn : code.target.isEmpty = false then
      if hdup : Semantics.nodupKeysB code.target = true then
        if hg : code.target.all (fun f => decide (f.2.inlineRank (fun _ => schemaRank code.target) < schemaRank code.target)) = true then
          let G : TypeGraph.Schema 1 := {
            origin := d.name
            declId := fun _ => 0
            declId_injective := by intro i j _; apply Fin.ext; omega
            name := fun _ => d.name
            fields := fun _ => code.target
            rank := fun _ => schemaRank code.target
            nonempty := fun _ => hn
            distinct := fun _ => hdup
            guarded := by
              intro i f hf
              exact of_decide_eq_true ((List.all_eq_true.mp hg) f hf) }
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
    else none


#print axioms graphStruct
end Solidity.Lowering.P8
