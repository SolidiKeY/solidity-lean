import Solidity.Yul.Views.StorageDeclarationHead

namespace Solidity.Yul.Views

def dynamicHeaderSeed (E : Source.Env) : DeclScalar E.layout (.int .u256) :=
  (declarationScalar? E.layout (.int .u256)).get (by rfl)

/-- Checked ACTUAL declaration and the existing planner's real offset bound.
No location/read/inverse/coverage law is a field. Cursor is provided by the
computed ordered declaration traversal, not an arbitrary final slot. -/
structure DynamicHeader (E : Source.Env) (root : Source.DeclName) (cursor : Nat) where
  declared : E.rootTy root = some (.array .storage (.int .u256) none)
  bounded : ((dynamicHeaderSeed E).position (roundSlot cursor)).start / 32 < 2^256

def DynamicHeader.registration {E root cursor} (h : DynamicHeader E root cursor) (a : Roadmap.Address) : ScalarPath E.layout (E.lay a) :=
  ((dynamicHeaderSeed E).position (roundSlot cursor)).registration ⟨root,[]⟩ (dynamic_header_cell h.declared) a h.bounded

theorem dynamic_header_start (E : Source.Env) (cursor : Nat) :
    ((dynamicHeaderSeed E).position (roundSlot cursor)).start = roundSlot cursor := by
  change packedStart (roundSlot cursor) 32 = roundSlot cursor
  rw [packedStart,(roundSlot_spec cursor).2.2]
  rfl

theorem DynamicHeader.slot {E root cursor} (h : DynamicHeader E root cursor) (a : Roadmap.Address) :
    (h.registration a).slot.val = roundSlot cursor/32 := by
  change ((dynamicHeaderSeed E).position (roundSlot cursor)).start/32 = _
  rw [dynamic_header_start]

theorem DynamicHeader.reservation {E root cursor} (h : DynamicHeader E root cursor) (a : Roadmap.Address) :
    declarationStart (h.registration a) = roundSlot cursor ∧
    declarationEnd (h.registration a) = roundSlot cursor+32 := by
  have start := DeclPosition.registration_start ((dynamicHeaderSeed E).position (roundSlot cursor))
    ⟨root,[]⟩ (dynamic_header_cell h.declared) a h.bounded
  rw [dynamic_header_start] at start
  change declarationStart (h.registration a) = roundSlot cursor at start
  exact ⟨start,by unfold declarationEnd; rw [start]; rfl⟩

theorem DynamicHeader.packed {E root cursor} (h : DynamicHeader E root cursor) (a : Roadmap.Address) :
    (StorageDeclaration.uintArray (E := E)).pack ⟨root,[]⟩ a cursor = .ok ([h.registration a],roundSlot cursor+32) := by
  have typed := dynamic_header_cell h.declared
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

end Solidity.Yul.Views

namespace Solidity.Yul.Views

theorem dynamic_header_of_packed {E : Source.Env} {root cursor a cs stop}
    (declared : E.rootTy root = some (.array .storage (.int .u256) none))
    (success : (StorageDeclaration.uintArray (E := E)).pack ⟨root,[]⟩ a cursor = .ok (cs,stop)) :
    ∃ h : DynamicHeader E root cursor, cs = [h.registration a] ∧ stop = roundSlot cursor+32 := by
  by_cases bound : ((dynamicHeaderSeed E).position (roundSlot cursor)).start/32 < 2^256
  · let h : DynamicHeader E root cursor := ⟨declared,bound⟩
    have same := Except.ok.inj ((h.packed a).symm.trans success)
    exact ⟨h,(congrArg Prod.fst same).symm,(congrArg Prod.snd same).symm⟩
  · have typed := dynamic_header_cell declared
    have scalar : declarationScalar? E.layout (.int .u256) = some (dynamicHeaderSeed E) := Option.get_mem (by rfl)
    change ((packDeclarationPaths E (fun _ => ⟨root,[]⟩) a 0 [("",.int .u256)] (roundSlot cursor)).map
      (fun out => (out.1,roundSlot out.2))) = _ at success
    simp only [packDeclarationPaths,scalar,dif_pos typed,dif_neg bound,Except.map] at success
    cases success

end Solidity.Yul.Views
