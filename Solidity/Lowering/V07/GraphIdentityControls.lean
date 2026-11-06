import Solidity.Lowering.V07.GraphControls

namespace Solidity.Lowering.V07.GraphIdentityControls

def declaration (name : String) : Source.Decl :=
  ⟨.struct,name,none,true,
    .struct name (.structMember (.elem (.int false 8 (by decide))) "value") .nil⟩
def env : Source.Env := ⟨[declaration "Left",declaration "Right"]⟩
def name (i : Fin 2) : Source.DeclName := ⟨none,if i.val = 0 then "Left" else "Right"⟩

theorem two_cases (i : Fin 2) : i = ⟨0,by decide⟩ ∨ i = ⟨1,by decide⟩ := by
  by_cases h : i.val = 0
  · left; apply Fin.ext; exact h
  · right; apply Fin.ext; change i.val = 1; have := i.isLt; omega

def schema : TypeGraph.Schema 2 where
  origin := "v07-distinct-declarations-equal-fields"
  declId := fun i => i.val
  declId_injective := fun _ _ h => Fin.ext h
  name := fun i => (name i).name
  fields := fun _ => [("value",.prim .uint)]
  rank := fun _ => 1
  nonempty := fun _ => rfl
  distinct := fun _ => rfl
  guarded := by
    intro i f h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    cases h
    exact Nat.zero_lt_succ 0

def certificate (loc : Source.DataLoc) : DeclarationGraph env loc schema where
  sourceName := name
  sourceName_injective := by
    intro i j h
    rcases two_cases i with rfl | rfl <;> rcases two_cases j with rfl | rfl
    · rfl
    · exact ((by decide : name ⟨0,by decide⟩ ≠ name ⟨1,by decide⟩) h).elim
    · exact ((by decide : name ⟨1,by decide⟩ ≠ name ⟨0,by decide⟩) h).elim
    · rfl
  sourceIndex := fun i => ⟨i.val,i.isLt⟩
  identity := fun _ => rfl
  source_kind := by intro i; rcases two_cases i with rfl | rfl <;> rfl
  source_scope := by intro i; rcases two_cases i with rfl | rfl <;> rfl
  source_name := by intro i; rcases two_cases i with rfl | rfl <;> rfl
  source_resolves := by intro i; rcases two_cases i with rfl | rfl <;> rfl
  target_name := fun _ => rfl
  sourceFields := fun _ => [("value",.int .u8)]
  fields_resolve := by intro i; rcases two_cases i with rfl | rfl <;> rfl
  fields_relate := fun _ => .cons rfl (.int .u8) .nil
  complete := by
    intro j _
    exact ⟨⟨j.val,j.isLt⟩,rfl⟩

theorem equal_fields : schema.fields ⟨0,by decide⟩ = schema.fields ⟨1,by decide⟩ := rfl

theorem distinct_source_identity (loc : Source.DataLoc) :
    (certificate loc).sourceIndex ⟨0,by decide⟩ ≠ (certificate loc).sourceIndex ⟨1,by decide⟩ := by
  intro h
  have e := congrArg Fin.val h
  change (0 : Nat) = 1 at e
  omega

theorem collapsed_map_rejected (loc : Source.DataLoc) :
    ¬ (∀ i, (certificate loc).sourceIndex i = (certificate loc).sourceIndex ⟨0,by decide⟩) := by
  intro h
  exact distinct_source_identity loc (h ⟨1,by decide⟩).symm

theorem field_type_mismatch :
    ¬ GraphTypeRel env.layout name (.int .u8) (.prim .bool) := by
  intro h
  cases h

end Solidity.Lowering.V07.GraphIdentityControls
