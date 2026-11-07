import Solidity.Yul.Views.MemberDynamicInitial

-- Serialize concrete proof elaboration to bound pending computed-state memory.
set_option Elab.async false

namespace Solidity.Yul.Views.Controls
theorem md_x_decoded : (finiteAccountWrite? (T := mdEnv.lay) account
    (mdLayout.snapshot mdFixed (saveSlot mdRaw 1 17)) (saveSlot mdRaw 1 17)).isSome := by decide
theorem md_x_separated : packedSeparationCheck (mdLayout.snapshot mdFixed (saveSlot mdRaw 1 17)) = true := by decide
def mdXOp : Source.Op mdEnv.layout mdEnv.lay mdEnv.lay :=
  (finiteAccountWrite? account (mdLayout.snapshot mdFixed (saveSlot mdRaw 1 17)) (saveSlot mdRaw 1 17)).get md_x_decoded
@[irreducible]
def mdGrow : MemberOwnershipPlan packedStepFrame mdLayout mdFixed 1 17 mdState mdResidual :=
  ⟨mdLayout.snapshot mdFixed mdRaw,mdLayout.sourceInventory_view packedStepFrame mdFixed mdState mdRaw md_initial_view,
   mdRaw,md_initial_encoding,(by rw [md_empty_inventory]; exact (packedSeparationCheck_iff _).mpr mdLayout.separated),
   md_x_separated,mdXOp,Option.get_mem md_x_decoded⟩
def mdGrowRaw := saveSlot mdRaw 1 17
theorem md_grow_raw : mdGrow.raw = mdRaw := by unfold mdGrow; rfl
theorem md_grow_next : mdGrow.nextRaw = mdGrowRaw := congrArg (fun m => saveSlot m 1 17) md_grow_raw
theorem md_grow_map : finiteEncode mdGrow.next (mdGrow.step.1.2.2.ex.world.accounts account).storage
    (fun q => mdGrow.step.2.cells (complementKey false account q)) = some mdGrowRaw :=
  (mdGrow.reencode rfl).trans (congrArg some md_grow_next)

end Solidity.Yul.Views.Controls
