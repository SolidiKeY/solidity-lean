import Solidity.Lowering.V07.DeclarationGraph

namespace Solidity.Lowering.V07.GraphControls

def cellName : Source.DeclName := ⟨none,"Cell"⟩
def cellDecl : Source.Decl :=
  ⟨.struct,"Cell",none,true,
    .struct "Cell" (.structMember (.elem (.int false 8 (by decide))) "value") .nil⟩
def env : Source.Env := ⟨[cellDecl]⟩
def schema : TypeGraph.Schema 1 where
  origin := "v07-declaration-control"
  declId := fun _ => 0
  declId_injective := by intro i j _; apply Fin.ext; omega
  name := fun _ => "Cell"
  fields := fun _ => [("value", .prim .uint)]
  rank := fun _ => 1
  nonempty := fun _ => rfl
  distinct := fun _ => rfl
  guarded := by
    intro i f h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    cases h
    exact Nat.zero_lt_succ 0

/-- A real resolved source struct, at either of its valid field locations. -/
def certificate (loc : Source.DataLoc) : DeclarationGraph env loc schema where
  sourceName := fun _ => cellName
  sourceName_injective := by intro i j _; apply Fin.ext; omega
  sourceIndex := fun _ => ⟨0,by decide⟩
  identity := fun _ => rfl
  source_kind := fun _ => rfl
  source_scope := fun _ => rfl
  source_name := fun _ => rfl
  source_resolves := fun _ => rfl
  target_name := fun _ => rfl
  sourceFields := fun _ => [("value", .int .u8)]
  fields_resolve := fun _ => rfl
  fields_relate := fun _ => .cons rfl (.int .u8) .nil
  complete := by
    intro j _
    have hj : j = ⟨0,by decide⟩ := by
      apply Fin.ext
      change j.val = 0
      have h := j.isLt
      change j.val < 1 at h
      omega
    exact ⟨⟨0,by decide⟩,hj.symm⟩

theorem inhabited_storage : Nonempty (DeclarationGraph env .storage schema) := ⟨certificate .storage⟩
theorem inhabited_memory : Nonempty (DeclarationGraph env .memory schema) := ⟨certificate .memory⟩
theorem actual_memory_layout : env.layout.fields cellName = [.int .u8] :=
  (certificate .memory).memory_layout ⟨0,by decide⟩
theorem wrong_field_name : schema.fields ⟨0,by decide⟩ ≠ [("wrong", .prim .uint)] := by decide

end Solidity.Lowering.V07.GraphControls
