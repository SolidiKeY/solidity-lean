import Solidity.Yul.Views.DeclarationDefaults
import Solidity.Yul.Views.TransientCellUpdateControls
import Solidity.Yul.Views.DeclarationControls

/-! The computed mixed declaration codecs derive zero defaults through actual
packing. The actual scalar transient root resets all raw slots; the supported
function codec retains its genuine unavailable Source-default boundary. -/
namespace Solidity.Yul.Views.Controls

theorem dd_mixed_payload : ∀ c ∈ declPackingRegistry account,
    (Source.Val.default declPackingEnv.layout (declPackingEnv.lay account c.path)).map (fun value => (c.codec.encode value).val)=
      (Source.Val.default declPackingEnv.layout (declPackingEnv.lay account c.path)).map (fun _ => 0) :=
  DeclarationDefaults.packed (declarationFieldPath declPackingRoot) account (declPackingCert account).fields 0 0 _ _
    (declPackingCert account).packed

theorem dd_mixed_check : scalarZeroDefaultCheck (declPackingRegistry account)=true := by
  change scalarZeroDefaultCheck (declPackingCert account).registrations=true
  rw [DeclarationDefaults.packed_check (declarationFieldPath declPackingRoot) account (declPackingCert account).fields 0 0 _ _
    (declPackingCert account).packed]
  decide

theorem dd_temp_packed : packDeclarationPaths rootEnv (fun _ => rootPath "temp") account 0 [("",.int unsigned16)] 0=
    .ok (rootTempRegistry account,2) := rfl

theorem dd_temp_available : (rootTempRegistry account).all
    (fun c => (Source.Val.default rootEnv.layout (rootEnv.lay account c.path)).isSome)=true := by decide

theorem dd_temp_defaults : ∀ c ∈ rootTempRegistry account, ∃ value,
    Source.Val.default rootEnv.layout (rootEnv.lay account c.path)=some value ∧ (c.codec.encode value).val=0 :=
  DeclarationDefaults.packed_available (fun _ => rootPath "temp") account [("",.int unsigned16)] 0 0 _ 2 dd_temp_packed
    (List.all_eq_true.mp dd_temp_available)

/-- This uses the real ordinary transient declaration, not a persistent struct
relabelled as a supported transient aggregate. -/
theorem dd_temp_reset (slot : Roadmap.Word) :
    reencodeTransientSlot rootTempRegistry (companionEndTx TransientSlotControls.childCore) account slot=some 0 :=
  packedEndTx_transient _ _ _ _ (fun c member => dd_temp_defaults c ((selectedSlotPaths_mem _ _ _).mp member).1)

theorem dd_function_selected : (declarationScalar? rootEnv.layout (.fn true [] [] none)).isSome=true := rfl

theorem dd_function_no_default : Source.Val.default rootEnv.layout (.fn true [] [] none)=none := rfl
end Solidity.Yul.Views.Controls
