import Solidity.Yul.Views.DynamicAccess

namespace Solidity.Yul.Views.Controls

def dynName (name : String) : Source.DeclName := ⟨some (if name = "a" then "Base" else "DS"),name⟩
def dynPath (name : String) : Source.SPath := ⟨dynName name,[]⟩
def dynU : Source.Syn .typeName := .elem (.int false 256 (by decide))
def dynArray : Source.STy := .array .storage (.int .u256) none

def dynEnv : Source.Env := ⟨[
  ⟨.contract,"Base",none,true,.contract false "Base" .none .nil .nil⟩,
  ⟨.stateVar,"a",some "Base",false,.stateVar (.elem (.int false 8 (by decide))) (some .priv) none none false "a" .none⟩,
  ⟨.contract,"DS",none,true,.contract false "DS" (.some (.lit (.num (.dec 42 0 0)))) (.cons (.inherit ⟨"Base",[]⟩ .none) .nil) .nil⟩,
  ⟨.stateVar,"n",some "DS",false,.stateVar (.elem (.int false 248 (by decide))) none none none false "n" .none⟩,
  ⟨.stateVar,"xs",some "DS",false,.stateVar (.array dynU .none) none none none false "xs" .none⟩,
  ⟨.stateVar,"mid",some "DS",false,.stateVar (.elem (.int false 16 (by decide))) none none none false "mid" .none⟩,
  ⟨.stateVar,"ys",some "DS",false,.stateVar (.array dynU .none) none none none false "ys" .none⟩,
  ⟨.stateVar,"marker",some "DS",false,.stateVar dynU none none none false "marker" .none⟩,
  ⟨.stateVar,"temp",some "DS",false,.stateVar (.elem (.int false 16 (by decide))) none none none true "temp" .none⟩]⟩

def dynTypes : List (Source.DeclName × Source.STy) :=
  [(dynName "a",.int originU8),(dynName "n",.int originU248),(dynName "xs",dynArray),
   (dynName "mid",.int unsigned16),(dynName "ys",dynArray),(dynName "marker",.int .u256)]

def dynDeclarations : StorageDeclarations dynEnv dynTypes :=
  .cons (.fixed (.scalar (.int originU8) (by decide)))
  (.cons (.fixed (.scalar (.int originU248) (by decide)))
  (.cons .uintArray (.cons (.fixed (.scalar (.int unsigned16) (by decide)))
  (.cons .uintArray (.cons (.fixed (.scalar (.int .u256) (by decide))) .nil)))))

theorem dyn_ready : (prepareComputedStorage dynDeclarations "DS" account).toOption.isSome := by decide

def dynComputed := (prepareComputedStorage dynDeclarations "DS" account).toOption.get dyn_ready

theorem dyn_origin : dynComputed.origin.persistent = 42 := rfl

theorem dyn_coordinates : dynComputed.registrations.map (fun c => (c.slot.val,c.field.offset,c.field.width)) =
    [(42,0,1),(42,1,31),(43,0,32),(44,0,2),(45,0,32),(46,0,32)] := rfl

theorem dyn_end : dynComputed.endByte = 1504 := rfl

theorem dyn_header_trace : dynComputed.headerTrace = [(dynName "xs",1376),(dynName "ys",1410)] := rfl

theorem dyn_x_ready : (dynComputed.header? (dynName "xs")).isSome := by decide
theorem dyn_y_ready : (dynComputed.header? (dynName "ys")).isSome := by decide
def dynXSelection := (dynComputed.header? (dynName "xs")).get dyn_x_ready
def dynYSelection := (dynComputed.header? (dynName "ys")).get dyn_y_ready
def dynX : DynamicHeader dynEnv (dynName "xs") 1376 := dynXSelection.property
def dynY : DynamicHeader dynEnv (dynName "ys") 1410 := dynYSelection.property

theorem dyn_x_slot : (dynX.registration account).slot = 43 := rfl
theorem dyn_y_slot : (dynY.registration account).slot = 45 := rfl

theorem dyn_header_member : dynX.registration account ∈ dynComputed.registrations ∧
    dynY.registration account ∈ dynComputed.registrations :=
  ⟨(dynComputed.header_selected (dynName "xs") 1376 dynX (Option.get_mem dyn_x_ready)).2,
   (dynComputed.header_selected (dynName "ys") 1410 dynY (Option.get_mem dyn_y_ready)).2⟩

/-- Inhabits the finite region algebra ONLY. Real-keccak provenance is a
separate theorem below; this executable test function is not real keccak. -/
def dynTestFixed : Roadmap.Evm.Fixed where
  keccak b := if b = layoutPreimageBytes (.data 43) then 1000 else 2000
  keccak_lt _ := by split <;> decide
  precompile _ _ := none
  precompileGas _ _ := 0

def dynRoots := [42,43,44,45,46]
def dynPreimages : List Storage.Pre := [.data 43,.data 45]

theorem dyn_test_regions : Hash.RegionsDisjoint (2^256) 8 (fixedLayoutHash dynTestFixed) dynRoots dynPreimages := by decide

theorem dyn_test_slots : (dynX.element dynTestFixed account 0).slot = 1000 ∧
    (dynX.element dynTestFixed account 1).slot = 1001 ∧ (dynY.element dynTestFixed account 0).slot = 2000 := by decide

theorem dyn_real_keccak_input (i : Nat) : (dynX.element Roadmap.Evm.withKeccak account i).slot.val =
    (Roadmap.Evm.withKeccak.keccak (layoutPreimageBytes (.data (dynX.registration account).slot.val))+i)%(2^256) :=
  dynX.element_word Roadmap.Evm.withKeccak account i

theorem dyn_real_header_preimage : layoutPreimageBytes (.data (dynX.registration account).slot.val) =
    layoutPreimageBytes (.data 43) := by
  rw [dyn_x_slot]
  change layoutPreimageBytes (.data (43 % (2^256))) = _
  rw [Nat.mod_eq_of_lt (by decide : 43 < 2^256)]

theorem dyn_exact_input_bytes : layoutPreimageBytes (.data 43) = List.replicate 31 0 ++ [43] := rfl

end Solidity.Yul.Views.Controls
