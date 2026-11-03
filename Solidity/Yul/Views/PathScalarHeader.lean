import Solidity.Yul.Views.PrimitiveOwnershipResidual
import Solidity.Source.ExprProgress

namespace Solidity.Yul.Views

theorem path_scalar_header_cell {E : Source.Env} {root : Source.SPath} {t : DynamicScalarKind}
    (declared : E.pathTy root = some (.array .storage (t.ty) none)) :
    E.cellTy root = .int .u256 := by
  simp only [Source.Env.cellTy,declared,Option.map_some,
    Source.STy.cell,Option.getD_some]

/-- Typed actual declaration and actual checked header cursor, NOT assumed
physical/source agreement. Bool/address/fixedBytes component; existing integer APIs remain separate. -/
structure PathScalarHeader (E : Source.Env) (root : Source.SPath) (t : DynamicScalarKind) (cursor : Nat) where
  declared : E.pathTy root = some (.array .storage (t.ty) none)
  bounded : ((dynamicHeaderSeed E).position (roundSlot cursor)).start / 32 < 2^256

def PathScalarHeader.registration {E root t cursor} (h : PathScalarHeader E root t cursor)
    (a : Roadmap.Address) : ScalarPath E.layout (E.lay a) :=
  ((dynamicHeaderSeed E).position (roundSlot cursor)).registration root (path_scalar_header_cell h.declared) a h.bounded

/-- Header packing is the SAME existing uint256 cell operation. Its enclosing
root declaration has already been checked at its actual array element type. -/
theorem PathScalarHeader.header_packed {E root t cursor} (h : PathScalarHeader E root t cursor) (a : Roadmap.Address) :
    (StorageDeclaration.uintArray (E := E)).pack root a cursor = .ok ([h.registration a],roundSlot cursor+32) := by
  have typed := path_scalar_header_cell h.declared
  change ((packDeclarationPaths E (fun _ => root) a 0 [("",.int .u256)] (roundSlot cursor)).map
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

theorem path_scalar_header_of_packed {E : Source.Env} {root t cursor a cs stop}
    (declared : E.pathTy root = some (.array .storage (t.ty) none))
    (success : (StorageDeclaration.uintArray (E := E)).pack root a cursor = .ok (cs,stop)) :
    ∃ h : PathScalarHeader E root t cursor, cs = [h.registration a] ∧ stop = roundSlot cursor+32 := by
  by_cases bound : ((dynamicHeaderSeed E).position (roundSlot cursor)).start/32 < 2^256
  · let h : PathScalarHeader E root t cursor := ⟨declared,bound⟩
    have same := Except.ok.inj ((h.header_packed a).symm.trans success)
    exact ⟨h,(congrArg Prod.fst same).symm,(congrArg Prod.snd same).symm⟩
  · have typed := path_scalar_header_cell declared
    have scalar : declarationScalar? E.layout (.int .u256) = some (dynamicHeaderSeed E) := Option.get_mem (by rfl)
    change ((packDeclarationPaths E (fun _ => root) a 0 [("",.int .u256)] (roundSlot cursor)).map
      (fun out => (out.1,roundSlot out.2))) = _ at success
    simp only [packDeclarationPaths,scalar,dif_pos typed,dif_neg bound,Except.map] at success
    cases success

end Solidity.Yul.Views
