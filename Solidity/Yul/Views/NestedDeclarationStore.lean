import Solidity.Yul.Views.NestedDeclarationJournal

namespace Solidity.Yul.Views.Controls

def nestedSnapshot (q : Roadmap.Word) : Roadmap.Word :=
  if q = 4 then nestedRaw4 else if q = 5 then nestedRaw5 else if q = 6 then nestedRaw6 else nestedInitialRaw q

def nestedEmptyStore : Source.Storage declBoundaryEnv.layout (declBoundaryEnv.lay account) := Source.Storage.empty

theorem nested_store_ready : (nestedDeclCert.storeWriteback nestedSnapshot nestedEmptyStore).isSome := by decide

def nestedStore := (nestedDeclCert.storeWriteback nestedSnapshot nestedEmptyStore).get nested_store_ready

theorem nested_store_full_map_reencoding :
    finiteEncode nestedDeclCert.registrations nestedStore.1 nestedStore.2 = some nestedSnapshot :=
  nestedDeclCert.store_reencode _ _ _ _ (Option.get_mem nested_store_ready)

theorem nested_store_selected_reads :
    nestedStore.1.read (nestedArrayPath declBoundaryRoot 0) = some (.int 1 (by decide)) ∧
    nestedStore.1.read (nestedArrayPath declBoundaryRoot 11) = some (.int 12 (by decide)) ∧
    nestedStore.1.read (nestedStructPath declBoundaryRoot 0) = some (.bool true) ∧
    nestedStore.1.read (nestedStructPath declBoundaryRoot 2) = some (.fixedBytes [0x12,0x34,0x56] rfl) := ⟨rfl,rfl,rfl,rfl⟩

theorem nested_store_whole_unchanged :
    nestedDeclCert.storeWriteback nestedSnapshot nestedStore.1 = some (nestedStore.1,nestedStore.2) := by
  have view := nestedDeclCert.store_view _ _ _ _ (Option.get_mem nested_store_ready)
  have residual : nestedStore.2 = packedMask nestedDeclCert.registrations nestedSnapshot := rfl
  rw [residual]
  exact nestedDeclCert.store_unchanged _ _ view

theorem nested_empty_administrative_identity : finiteWriteback nestedDeclCert.registrations (fun _ => 0) nestedEmptyStore = some nestedEmptyStore := by
  apply nestedDeclCert.unchanged
  exact (finiteViewBool_iff _ _ _).mp (by decide)

theorem nested_written_default_administrative_identity :
    let s := nestedEmptyStore.write (nestedStructPath declBoundaryRoot 0) (.bool false)
    finiteWriteback nestedDeclCert.registrations (fun _ => 0) s = some s := by
  apply nestedDeclCert.unchanged
  exact (finiteViewBool_iff _ _ _).mp (by decide)

theorem nested_exact_byte_ownership :
    List.ofFn (fun i : Fin 32 => packedOwnsByte nestedDeclCert.registrations 4 i) = List.replicate 30 true ++ List.replicate 2 false ∧
    List.ofFn (fun i : Fin 32 => packedOwnsByte nestedDeclCert.registrations 5 i) = List.replicate 6 true ++ List.replicate 26 false ∧
    List.ofFn (fun i : Fin 32 => packedOwnsByte nestedDeclCert.registrations 6 i) = List.replicate 26 true ++ List.replicate 6 false := by decide

theorem nested_dirty_owned_preparation : (preparePackedFrame (ps := nestedDeclRegistry) (ts := nestedDeclRegistry)
    packedStepFrame false 6 2).isNone := by decide

theorem nested_wrong_path_preparation :
    packDeclarationPaths declBoundaryEnv (fun i => ⟨declBoundaryRoot,[.field 9,.index i]⟩) account 0 [("",.int unsigned24)] (4*32) = .error .cellMismatch := by rfl

theorem nested_no_out_of_range_registration : nestedArrayPath declBoundaryRoot 12 ∉ nestedDeclCert.registrations.map ScalarPath.path := by decide

def nestedOverflowBoundary := (prepareDeclaredArrayStruct declBoundaryEnv declBoundaryRoot ⟨2^256-1,by decide⟩).get (by decide)

theorem nested_real_slot_overflow : (prepareNestedDeclaration nestedOverflowBoundary account).toOption = none := by
  apply Option.eq_none_of_isNone
  decide

end Solidity.Yul.Views.Controls
