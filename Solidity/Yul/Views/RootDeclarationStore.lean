import Solidity.Yul.Views.RootDeclarationState

namespace Solidity.Yul.Views.Controls

def rootSnapshot (q : Roadmap.Word) : Roadmap.Word :=
  if q = 0 then rootRaw0 else if q = 1 then rootRaw1 else if q = 2 then rootRaw2 else if q = 3 then rootRaw3 else if q = 4 then rootRaw4 else if q = 5 then rootRaw5 else if q = 6 then rootRaw6 else rootInitialRaw q
def rootEmptyStore : Source.Storage rootEnv.layout (rootEnv.lay account) := Source.Storage.empty

theorem root_store_ready : (rootChecked.storeWriteback rootSnapshot rootInitialStore).isSome := by decide

def rootStore := (rootChecked.storeWriteback rootSnapshot rootInitialStore).get root_store_ready

theorem root_store_full_reencode : finiteEncode rootChecked.registrations rootStore.1 rootStore.2 = some rootSnapshot :=
  rootChecked.store_reencode _ _ _ _ (Option.get_mem root_store_ready)

theorem root_store_unchanged : rootChecked.storeWriteback rootSnapshot rootStore.1 = some (rootStore.1,rootStore.2) :=
  rootChecked.store_unchanged _ _ (rootChecked.store_view _ _ _ _ (Option.get_mem root_store_ready))

theorem root_empty_administrative_identity : finiteWriteback rootChecked.registrations (fun _ => 0) rootEmptyStore = some rootEmptyStore := by
  apply rootChecked.unchanged
  exact (finiteViewBool_iff _ _ _).mp (by decide)

theorem root_written_default_identity :
    let s := rootEmptyStore.write (rootPath "c") (.bool false)
    finiteWriteback rootChecked.registrations (fun _ => 0) s = some s := by
  apply rootChecked.unchanged
  exact (finiteViewBool_iff _ _ _).mp (by decide)

theorem root_exact_padding_masks :
    List.ofFn (fun i : Fin 32 => packedOwnsByte rootChecked.registrations 0 i) = List.replicate 32 true ∧
    List.ofFn (fun i : Fin 32 => packedOwnsByte rootChecked.registrations 1 i) = true::List.replicate 31 false ∧
    List.ofFn (fun i : Fin 32 => packedOwnsByte rootChecked.registrations 2 i) = List.replicate 3 true ++ List.replicate 29 false ∧
    List.ofFn (fun i : Fin 32 => packedOwnsByte rootChecked.registrations 4 i) = List.replicate 31 true ++ [false] ∧
    List.ofFn (fun i : Fin 32 => packedOwnsByte rootChecked.registrations 5 i) = List.replicate 2 true ++ List.replicate 30 false := by decide

theorem root_dirty_owned_preparation : (preparePackedFrame (ps := rootRegistry) (ts := rootTempRegistry) packedStepFrame false 1 2).isNone := by decide

end Solidity.Yul.Views.Controls
