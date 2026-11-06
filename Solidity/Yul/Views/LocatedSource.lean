import Solidity.Yul.Views.LocatedControls
import Solidity.Yul.Views.LocatedInventory

namespace Solidity.Yul.Views.Controls

def locatedEntries (fixed : Roadmap.Evm.Fixed) : List (LocatedEntry locatedEnv fixed locatedRoot locatedTree) :=
  [⟨locatedMapping,locatedMapCert fixed⟩,⟨locatedNested,locatedNestedCert fixed⟩]

theorem located_entries_checked (fixed : Roadmap.Evm.Fixed) : locatedInventoryCheck (locatedEntries fixed) = true := by rfl

def locatedAccount : Roadmap.Address := ⟨1,by decide⟩
def locatedRegistry (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) := [(locatedMapCert fixed).registration a]
def locatedRequest (fixed : Roadmap.Evm.Fixed) (tr : Bool) : PackedSlotRequest :=
  ⟨tr,locatedAccount,((locatedMapCert fixed).registration locatedAccount).slot,777⟩

theorem located_registry_separated (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) :
    finiteSeparated (locatedRegistry fixed a) := List.pairwise_singleton _ _

theorem located_decode777 (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) :
    canonicalScalarDecode ((locatedMapCert fixed).registration a).codec
      (((locatedMapCert fixed).registration a).field.findWord 777) = some (.int 777 (by decide)) := by
  change canonicalScalarDecode (intCodec locatedEnv.layout .u256 0 (by decide))
    ((intField .u256 0 (by decide)).findWord 777) = _
  have payload : (intField .u256 0 (by decide)).findWord 777 =
      (intCodec locatedEnv.layout .u256 0 (by decide)).encode (.int 777 (by decide)) := by
    apply Fin.ext
    decide
  rw [payload,canonicalScalarDecode_encode]

theorem located_plan_ready (fixed : Roadmap.Evm.Fixed) (tr : Bool) :
    (preparePackedSlot (locatedRegistry fixed) (locatedRegistry fixed) (locatedRequest fixed tr)).isSome = true := by
  cases tr <;>
    simp only [preparePackedSlot,packedRequestOp?,locatedRequest,locatedRegistry,
      Bool.false_eq_true,if_false,if_true,selectedSlotPaths,List.filter_cons,beq_self_eq_true,
      List.filter_nil,Option.isSome_pmap,finiteAccountWrite?,finiteTransientWrite?,finitePrepare,located_decode777,Option.bind_some,Option.map_some] <;> rfl

def locatedPlan (fixed : Roadmap.Evm.Fixed) (tr : Bool) :=
  (preparePackedSlot (locatedRegistry fixed) (locatedRegistry fixed) (locatedRequest fixed tr)).get (located_plan_ready fixed tr)

def locatedInitial (fixed : Roadmap.Evm.Fixed) : ResidualCompanion locatedEnv.layout locatedEnv.lay locatedEnv.lay complementCarrierOwnership :=
  ⟨⟨⟨fun _ => Source.Account.empty (D := locatedEnv.layout) (locatedEnv.lay locatedAccount)⟩,.empty,[]⟩,
    initialPackedComplement (locatedRegistry fixed) (locatedRegistry fixed) (fun _ => 42)⟩

theorem located_raw_readback (fixed : Roadmap.Evm.Fixed) :
    reencodePersistentSlot (locatedRegistry fixed) (applyPackedSlot (locatedInitial fixed) (locatedPlan fixed false))
      (locatedPlan fixed false).request.address (locatedPlan fixed false).request.slot = some (locatedPlan fixed false).request.raw :=
  packedPersistent_reencode _ _ (by
    have h := preparePackedSlot_request (locatedRequest fixed false) (locatedPlan fixed false)
      (Option.get_mem (located_plan_ready fixed false))
    exact congrArg PackedSlotRequest.transient h) (located_registry_separated fixed _)

theorem located_source_value (fixed : Roadmap.Evm.Fixed) :
    (((applyPackedSlot (locatedInitial fixed) (locatedPlan fixed false)).source.world.accounts locatedAccount).storage).cell
      (locatedMapCert fixed).path = some (.int 777 (by decide)) := by
  simp only [applyPackedSlot,locatedPlan,preparePackedSlot,packedRequestOp?,locatedRequest,
    locatedRegistry,Bool.false_eq_true,if_false,selectedSlotPaths,List.filter_cons,
    beq_self_eq_true,List.filter_nil,if_true,finiteAccountWrite?,finitePrepare,located_decode777,Option.bind_some,Option.map_some]
  rfl

theorem located_child_rollback (fixed : Roadmap.Evm.Fixed) :
    let caller := runPackedSlots (locatedInitial fixed) [locatedPlan fixed false]
    companionRollback (companionEnter caller locatedAccount locatedAccount 0 [] false)
      (runPackedSlots caller [locatedPlan fixed true]) = caller :=
  packed_frame_child_rollback _ _ _ _ _ _ _ _

theorem located_outer_rollback (fixed : Roadmap.Evm.Fixed) :
    let initial := locatedInitial fixed
    let caller := runPackedSlots initial [locatedPlan fixed false]
    companionRollback (companionEnter initial locatedAccount locatedAccount 0 [] false)
      (companionCommit (companionEnter caller locatedAccount locatedAccount 0 [] false)
        (runPackedSlots caller [locatedPlan fixed true])) = initial :=
  packed_frame_outer_commit _ _ _ _ _ _ _ _

theorem located_reset (fixed : Roadmap.Evm.Fixed) :
    let after := runPackedSlots (locatedInitial fixed) [locatedPlan fixed false,locatedPlan fixed true]
    (companionEndTx after).source.world = after.source.world ∧
    ((companionEndTx after).source.transient.cells locatedAccount).read (locatedMapCert fixed).path =
      Source.Val.default locatedEnv.layout (locatedEnv.lay locatedAccount (locatedMapCert fixed).path) ∧
    (companionEndTx after).residual.cells (complementKey true locatedAccount ((locatedMapCert fixed).registration locatedAccount).slot) = 0 := by
  dsimp only
  have reset := companionEndTx_transient
    (runPackedSlots (locatedInitial fixed) [locatedPlan fixed false,locatedPlan fixed true])
    (complementKey true locatedAccount ((locatedMapCert fixed).registration locatedAccount).slot)
    rfl locatedAccount (locatedMapCert fixed).path
  exact ⟨rfl,reset.1,reset.2.1⟩

theorem located_source_key_provenance (F : Source.Fr) (horizon : Nat)
    (s : Source.EMState locatedEnv []) :
    (Source.keyStep F horizon (.val (uintValueOfWord locatedEnv.layout 7))).run s =
      (.ok (.key (Source.wordBytes 7)),s) := located_keyStep F horizon 7 s

end Solidity.Yul.Views.Controls
