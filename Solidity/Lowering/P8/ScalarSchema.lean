import Solidity.Lowering.V07.DeclarationGraph
import Solidity.Source.WellFormed

/-! P8 executable scalar-field schema producer. This constructs real Schema and
DeclarationGraph evidence from actual Source field resolution for a singleton
struct environment. It is NOT full G15 admission: unsupported legal fields and
multi-struct/recursive extraction remain open, never profile exclusions. -/
namespace Solidity.Lowering.P8
open V07

structure ScalarCode (D : Source.Layout) {n : Nat} (names : Fin n → Source.DeclName)
    (τ : Source.STy) where
  prim : PrimTy
  related : GraphTypeRel D names τ (.prim prim)

def encodeScalar (D : Source.Layout) {n : Nat} (names : Fin n → Source.DeclName) :
    (τ : Source.STy) → Option (ScalarCode D names τ)
  | .int t => some ⟨integerPrim t, .int t⟩
  | .bool => some ⟨.bool, .bool⟩
  | .address payable => some ⟨.uint, .address payable⟩
  | .enum d => if h : D.enumSize d ≤ 2^256 then some ⟨.uint, .enum d h⟩ else none
  | _ => none

structure ScalarFields (D : Source.Layout) {n : Nat} (names : Fin n → Source.DeclName)
    (source : List (String × Source.STy)) where
  target : List (Name × TypeGraph.Ty n)
  related : GraphFieldsRel D names source target
  inline_zero : ∀ f ∈ target, f.2.inlineRank (fun _ => 1) = 0

def encodeFields (D : Source.Layout) {n : Nat} (names : Fin n → Source.DeclName) :
    (source : List (String × Source.STy)) → Option (ScalarFields D names source)
  | [] => some ⟨[], .nil, by intro f hf; cases hf⟩
  | (name, τ) :: rest => do
    let head ← encodeScalar D names τ
    let tail ← encodeFields D names rest
    return ⟨(name, .prim head.prim) :: tail.target, .cons rfl head.related tail.related, by
      intro f hf
      rcases List.mem_cons.mp hf with he | ht
      · subst f; rfl
      · exact tail.inline_zero f ht⟩

def singletonEnv (d : Source.Decl) : Source.Env := ⟨[d]⟩
def sourceName (d : Source.Decl) : Source.DeclName := ⟨d.scope, d.name⟩

/-- No target certificate is an input: actual field resolution, scalar lowering,
nonempty and duplicate-name checks construct every output proof. The kind proof
is a source declaration fact, not a desired semantic preservation premise. -/
def scalarStruct (d : Source.Decl) (hd : d.kind = .struct) (loc : Source.DataLoc) :
    Option (Σ G : TypeGraph.Schema 1, DeclarationGraph (singletonEnv d) loc G) :=
  match hf : (singletonEnv d).structFields (sourceName d) loc with
  | none => none
  | some fs => do
    let code ← encodeFields (singletonEnv d).layout (fun _ : Fin 1 => sourceName d) fs
    if hn : code.target.isEmpty = false then
      if hdup : Semantics.nodupKeysB code.target = true then
        let G : TypeGraph.Schema 1 := {
          origin := d.name
          declId := fun _ => 0
          declId_injective := by intro i j _; apply Fin.ext; omega
          name := fun _ => d.name
          fields := fun _ => code.target
          rank := fun _ => 1
          nonempty := fun _ => hn
          distinct := fun _ => hdup
          guarded := by intro i f h; rw [code.inline_zero f h]; exact Nat.zero_lt_succ 0 }
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

#print axioms scalarStruct
end Solidity.Lowering.P8
