import Solidity.Yul.Views.PackedDynamicRegions

namespace Solidity.Yul.Views

theorem scalarFamily_dynamic_header_cell {E : Source.Env} {root : Source.DeclName} {t : DynamicScalarKind}
    (declared : E.rootTy root = some (.array .storage (t.ty) none)) :
    E.cellTy ⟨root,[]⟩ = .int .u256 := by
  simp only [Source.Env.cellTy,Source.Env.pathTy,List.foldl_nil,declared,Option.map_some,
    Source.STy.cell,Option.getD_some]

/-- Typed actual declaration and actual checked header cursor, NOT assumed
physical/source agreement. Bool/address/fixedBytes component; existing integer APIs remain separate. -/
structure ScalarDynamicHeader (E : Source.Env) (root : Source.DeclName) (t : DynamicScalarKind) (cursor : Nat) where
  declared : E.rootTy root = some (.array .storage (t.ty) none)
  bounded : ((dynamicHeaderSeed E).position (roundSlot cursor)).start / 32 < 2^256

def ScalarDynamicHeader.registration {E root t cursor} (h : ScalarDynamicHeader E root t cursor)
    (a : Roadmap.Address) : ScalarPath E.layout (E.lay a) :=
  ((dynamicHeaderSeed E).position (roundSlot cursor)).registration ⟨root,[]⟩ (scalarFamily_dynamic_header_cell h.declared) a h.bounded

/-- Header packing is the SAME existing uint256 cell operation. Its enclosing
root declaration has already been checked at its actual array element type. -/
theorem ScalarDynamicHeader.header_packed {E root t cursor} (h : ScalarDynamicHeader E root t cursor) (a : Roadmap.Address) :
    (StorageDeclaration.uintArray (E := E)).pack ⟨root,[]⟩ a cursor = .ok ([h.registration a],roundSlot cursor+32) := by
  have typed := scalarFamily_dynamic_header_cell h.declared
  change ((packDeclarationPaths E (fun _ => ⟨root,[]⟩) a 0 [("",.int .u256)] (roundSlot cursor)).map
    (fun out => (out.1,roundSlot out.2))) = _
  have scalar : declarationScalar? E.layout (.int .u256) = some (dynamicHeaderSeed E) := Option.get_mem (by rfl)
  simp only [packDeclarationPaths,scalar,dif_pos typed,dif_pos h.bounded,Except.map]
  have endEq : ((dynamicHeaderSeed E).position (roundSlot cursor)).start +
      ((dynamicHeaderSeed E).position (roundSlot cursor)).field.width = roundSlot cursor+32 := by
    rw [dynamic_header_start]
    rfl
  apply congrArg Except.ok
  apply Prod.ext
  · rfl
  · change roundSlot (((dynamicHeaderSeed E).position (roundSlot cursor)).start+
        ((dynamicHeaderSeed E).position (roundSlot cursor)).field.width) = roundSlot cursor+32
    rw [endEq]
    exact roundSlot_aligned _ (by have := (roundSlot_spec cursor).2.2; omega)

theorem scalarFamily_header_of_packed {E : Source.Env} {root t cursor a cs stop}
    (declared : E.rootTy root = some (.array .storage (t.ty) none))
    (success : (StorageDeclaration.uintArray (E := E)).pack ⟨root,[]⟩ a cursor = .ok (cs,stop)) :
    ∃ h : ScalarDynamicHeader E root t cursor, cs = [h.registration a] ∧ stop = roundSlot cursor+32 := by
  by_cases bound : ((dynamicHeaderSeed E).position (roundSlot cursor)).start/32 < 2^256
  · let h : ScalarDynamicHeader E root t cursor := ⟨declared,bound⟩
    have same := Except.ok.inj ((h.header_packed a).symm.trans success)
    exact ⟨h,(congrArg Prod.fst same).symm,(congrArg Prod.snd same).symm⟩
  · have typed := scalarFamily_dynamic_header_cell declared
    have scalar : declarationScalar? E.layout (.int .u256) = some (dynamicHeaderSeed E) := Option.get_mem (by rfl)
    change ((packDeclarationPaths E (fun _ => ⟨root,[]⟩) a 0 [("",.int .u256)] (roundSlot cursor)).map
      (fun out => (out.1,roundSlot out.2))) = _ at success
    simp only [packDeclarationPaths,scalar,dif_pos typed,dif_neg bound,Except.map] at success
    cases success

end Solidity.Yul.Views
