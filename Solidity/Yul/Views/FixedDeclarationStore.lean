import Solidity.Yul.Views.FixedDeclarationState

namespace Solidity.Yul.Views.Controls

def recursiveSnapshot (q : Roadmap.Word) : Roadmap.Word :=
  if q = 8 then recursiveRaw8 else if q = 9 then recursiveRaw9 else if q = 10 then recursiveRaw10 else if q = 11 then recursiveRaw11 else if q = 12 then recursiveRaw12 else if q = 13 then recursiveRaw13 else recursiveInitialRaw q
def recursiveEmptyStore : Source.Storage recursiveDeclEnv.layout (recursiveDeclEnv.lay account) := Source.Storage.empty

theorem recursive_store_ready : (recursiveChecked.storeWriteback recursiveSnapshot recursiveEmptyStore).isSome := by decide

def recursiveStore := (recursiveChecked.storeWriteback recursiveSnapshot recursiveEmptyStore).get recursive_store_ready

theorem recursive_store_full_reencode :
    finiteEncode recursiveChecked.registrations recursiveStore.1 recursiveStore.2 = some recursiveSnapshot :=
  recursiveChecked.store_reencode _ _ _ _ (Option.get_mem recursive_store_ready)

theorem recursive_store_unchanged : recursiveChecked.storeWriteback recursiveSnapshot recursiveStore.1 = some (recursiveStore.1,recursiveStore.2) := by
  have view := recursiveChecked.store_view _ _ _ _ (Option.get_mem recursive_store_ready)
  exact recursiveChecked.store_unchanged _ _ view

theorem recursive_empty_identity : finiteWriteback recursiveChecked.registrations (fun _ => 0) recursiveEmptyStore = some recursiveEmptyStore := by
  apply recursiveChecked.unchanged
  exact (finiteViewBool_iff _ _ _).mp (by decide)

theorem recursive_written_default_identity :
    let s := recursiveEmptyStore.write (recursiveGridPath 0 0 0) (.bool false)
    finiteWriteback recursiveChecked.registrations (fun _ => 0) s = some s := by
  apply recursiveChecked.unchanged
  exact (finiteViewBool_iff _ _ _).mp (by decide)

theorem recursive_nonzero_padding :
    List.ofFn (fun i : Fin 32 => packedOwnsByte recursiveChecked.registrations 8 i) = List.replicate 3 true ++ List.replicate 29 false ∧
    List.ofFn (fun i : Fin 32 => packedOwnsByte recursiveChecked.registrations 12 i) = List.replicate 32 true ∧
    List.ofFn (fun i : Fin 32 => packedOwnsByte recursiveChecked.registrations 13 i) = List.replicate 16 true ++ List.replicate 16 false := by decide

theorem recursive_dirty_owned_preparation : (preparePackedFrame (ps := recursiveRegistry) (ts := recursiveRegistry) packedStepFrame false 8 2).isNone := by decide

end Solidity.Yul.Views.Controls
