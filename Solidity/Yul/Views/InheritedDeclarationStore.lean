import Solidity.Yul.Views.InheritedDeclarationState

namespace Solidity.Yul.Views.Controls

def diamondSnapshot (q : Roadmap.Word) : Roadmap.Word :=
  if q = 0 then diamondRaw0 else if q = 1 then diamondRaw1 else if q = 2 then diamondRaw2 else if q = 3 then diamondRaw3 else if q = 4 then diamondRaw4 else if q = 5 then diamondRaw5 else if q = 6 then diamondRaw6 else diamondInitialRaw q
def diamondEmptyStore : Source.Storage diamondEnv.layout (diamondEnv.lay account) := Source.Storage.empty

theorem diamond_store_ready : (diamondChecked.storeWriteback diamondSnapshot diamondInitialStore).isSome := by decide

def diamondStore := (diamondChecked.storeWriteback diamondSnapshot diamondInitialStore).get diamond_store_ready

theorem diamond_store_full_reencode : finiteEncode diamondChecked.registrations diamondStore.1 diamondStore.2 = some diamondSnapshot :=
  diamondChecked.store_reencode _ _ _ _ (Option.get_mem diamond_store_ready)

theorem diamond_store_unchanged : diamondChecked.storeWriteback diamondSnapshot diamondStore.1 = some (diamondStore.1,diamondStore.2) :=
  diamondChecked.store_unchanged _ _ (diamondChecked.store_view _ _ _ _ (Option.get_mem diamond_store_ready))

theorem diamond_empty_administrative_identity : finiteWriteback diamondChecked.registrations (fun _ => 0) diamondEmptyStore = some diamondEmptyStore := by
  apply diamondChecked.unchanged
  exact (finiteViewBool_iff _ _ _).mp (by decide)

theorem diamond_written_default_identity :
    let s := diamondEmptyStore.write (diamondPath "c") (.bool false)
    finiteWriteback diamondChecked.registrations (fun _ => 0) s = some s := by
  apply diamondChecked.unchanged
  exact (finiteViewBool_iff _ _ _).mp (by decide)

theorem diamond_exact_padding_masks :
    List.ofFn (fun i : Fin 32 => packedOwnsByte diamondChecked.registrations 0 i) = List.replicate 32 true ∧
    List.ofFn (fun i : Fin 32 => packedOwnsByte diamondChecked.registrations 1 i) = true::List.replicate 31 false ∧
    List.ofFn (fun i : Fin 32 => packedOwnsByte diamondChecked.registrations 2 i) = List.replicate 3 true ++ List.replicate 29 false ∧
    List.ofFn (fun i : Fin 32 => packedOwnsByte diamondChecked.registrations 4 i) = List.replicate 31 true ++ [false] ∧
    List.ofFn (fun i : Fin 32 => packedOwnsByte diamondChecked.registrations 5 i) = List.replicate 2 true ++ List.replicate 30 false := by decide

theorem diamond_dirty_owned_preparation : (preparePackedFrame (ps := diamondRegistry) (ts := diamondTempRegistry) packedStepFrame false 1 2).isNone := by decide

end Solidity.Yul.Views.Controls
