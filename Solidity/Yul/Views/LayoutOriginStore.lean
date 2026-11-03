import Solidity.Yul.Views.LayoutOriginState

namespace Solidity.Yul.Views.Controls

def originSnapshot (q : Roadmap.Word) : Roadmap.Word :=
  if q = 42 then originRaw0 else if q = 43 then originRaw1 else if q = 44 then originRaw2 else if q = 45 then originRaw3 else if q = 46 then originRaw4 else if q = 47 then originRaw5 else if q = 48 then originRaw6 else originInitialRaw q
def originEmptyStore : Source.Storage originEnv.layout (originEnv.lay account) := Source.Storage.empty

theorem origin_store_ready : (originChecked.storeWriteback originSnapshot originInitialStore).isSome := by decide

def originStore := (originChecked.storeWriteback originSnapshot originInitialStore).get origin_store_ready

theorem origin_store_full_reencode : finiteEncode originChecked.registrations originStore.1 originStore.2 = some originSnapshot :=
  originChecked.store_reencode _ _ _ _ (Option.get_mem origin_store_ready)

theorem origin_store_unchanged : originChecked.storeWriteback originSnapshot originStore.1 = some (originStore.1,originStore.2) :=
  originChecked.store_unchanged _ _ (originChecked.store_view _ _ _ _ (Option.get_mem origin_store_ready))

theorem origin_empty_administrative_identity : finiteWriteback originChecked.registrations (fun _ => 0) originEmptyStore = some originEmptyStore := by
  apply originChecked.unchanged
  exact (finiteViewBool_iff _ _ _).mp (by decide)

theorem origin_written_default_identity :
    let s := originEmptyStore.write (originPath "c") (.bool false)
    finiteWriteback originChecked.registrations (fun _ => 0) s = some s := by
  apply originChecked.unchanged
  exact (finiteViewBool_iff _ _ _).mp (by decide)

theorem origin_exact_padding_masks :
    List.ofFn (fun i : Fin 32 => packedOwnsByte originChecked.registrations 42 i) = List.replicate 32 true ∧
    List.ofFn (fun i : Fin 32 => packedOwnsByte originChecked.registrations 43 i) = true::List.replicate 31 false ∧
    List.ofFn (fun i : Fin 32 => packedOwnsByte originChecked.registrations 44 i) = List.replicate 3 true ++ List.replicate 29 false ∧
    List.ofFn (fun i : Fin 32 => packedOwnsByte originChecked.registrations 46 i) = List.replicate 31 true ++ [false] ∧
    List.ofFn (fun i : Fin 32 => packedOwnsByte originChecked.registrations 47 i) = List.replicate 2 true ++ List.replicate 30 false := by decide

theorem origin_dirty_owned_preparation : (preparePackedFrame (ps := originRegistry) (ts := originTempRegistry) packedStepFrame false 43 2).isNone := by decide

end Solidity.Yul.Views.Controls
