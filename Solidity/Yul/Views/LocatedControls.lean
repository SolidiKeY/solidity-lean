import Solidity.Yul.Views.LocatedSeparation
import Solidity.Yul.Views.PackedResidualFrame

namespace Solidity.Yul.Views.Controls

def locatedU : Source.Syn .typeName := .elem (.int false 256 (by decide))
def locatedK : Source.MapKey := .elem (.int false 256 (by decide)) (by decide)
def locatedRoot : Source.DeclName := ⟨none,"state"⟩
def locatedEnv : Source.Env := ⟨[
  ⟨.struct,"Root",none,true,.struct "Root" (.structMember locatedU "plain")
    (.cons (.structMember (.mapping locatedK none locatedU none) "table")
    (.cons (.structMember (.array locatedU .none) "items")
    (.cons (.structMember (.mapping locatedK none (.array locatedU .none) none) "nested") .nil)))⟩,
  ⟨.stateVar,"state",none,true,.stateVar (.userType ⟨"Root",[]⟩) none none none false "state" .none⟩]⟩
def locatedTree : Storage.STy := .strct [.word,.map .word,.darr .word,.map (.darr .word)]
def locatedMapping := [Storage.Step.field 1,.key 7]
def locatedArray := [Storage.Step.field 2,.index 3]
def locatedNested := [Storage.Step.field 3,.key 9,.index 2]
def locatedPlain := [Storage.Step.field 0]

theorem located_mapping_prepared (fixed : Roadmap.Evm.Fixed) :
    (prepareLocatedWord locatedEnv fixed locatedRoot locatedTree locatedMapping).isOk = true := by rfl

theorem located_array_prepared (fixed : Roadmap.Evm.Fixed) :
    (prepareLocatedWord locatedEnv fixed locatedRoot locatedTree locatedArray).isOk = true := by rfl

theorem located_nested_prepared (fixed : Roadmap.Evm.Fixed) :
    (prepareLocatedWord locatedEnv fixed locatedRoot locatedTree locatedNested).isOk = true := by rfl

def locatedMapCert (fixed : Roadmap.Evm.Fixed) :=
  (prepareLocatedWord locatedEnv fixed locatedRoot locatedTree locatedMapping).toOption.get (by
    rfl)

def locatedNestedCert (fixed : Roadmap.Evm.Fixed) :=
  (prepareLocatedWord locatedEnv fixed locatedRoot locatedTree locatedNested).toOption.get (by rfl)

theorem located_nested_term (fixed : Roadmap.Evm.Fixed) :
    (locatedNestedCert fixed).location = .data (.hash 9 (.root 3) 0) 2 := rfl

theorem located_nested_inputs (fixed : Roadmap.Evm.Fixed) :
    (locatedNestedCert fixed).location.pres (2^256) (fixedLayoutHash fixed) =
      [.entry 9 3,.data (fixed.keccak (layoutPreimageBytes (.entry 9 3)))] := by
  change [Storage.Pre.entry 9 3,Storage.Pre.data ((fixed.keccak (layoutPreimageBytes (.entry 9 3)) + 0) % (2^256))] = _
  rw [Nat.add_zero,Nat.mod_eq_of_lt (fixed.keccak_lt _)]

theorem located_nested_inputs_words (fixed : Roadmap.Evm.Fixed) :
    ∀ p ∈ (locatedNestedCert fixed).location.pres (2^256) (fixedLayoutHash fixed), p.Words := by
  rw [located_nested_inputs]
  intro p member
  rcases List.mem_cons.mp member with equal | member
  · subst p; exact ⟨by decide,by decide⟩
  · have equal := List.mem_singleton.mp member
    subst p
    exact fixed.keccak_lt _

theorem located_mapping_term (fixed : Roadmap.Evm.Fixed) : (locatedMapCert fixed).location = .hash 7 (.root 1) 0 := rfl

theorem located_mapping_input (fixed : Roadmap.Evm.Fixed) :
    (locatedMapCert fixed).location.pres (2^256) (fixedLayoutHash fixed) = [.entry 7 1] := rfl

theorem located_mapping_slot (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) :
    ((locatedMapCert fixed).registration a).slot.val = fixed.keccak (layoutPreimageBytes (.entry 7 1)) := by
  change (fixed.keccak (layoutPreimageBytes (.entry 7 1)) + 0) % (2^256) = _
  rw [Nat.add_zero,Nat.mod_eq_of_lt (fixed.keccak_lt _)]

theorem located_bad_index (fixed : Roadmap.Evm.Fixed) :
    (prepareLocatedWord locatedEnv fixed locatedRoot locatedTree [.field 2,.index Storage.lmax]).toOption = none := by rfl

theorem located_bad_key (fixed : Roadmap.Evm.Fixed) :
    (prepareLocatedWord locatedEnv fixed locatedRoot locatedTree [.field 1,.key (2^256)]).toOption = none := by rfl

theorem located_wrong_path (fixed : Roadmap.Evm.Fixed) :
    (prepareLocatedWord locatedEnv fixed locatedRoot locatedTree [.field 0,.key 1]).toOption = none := by rfl

theorem located_nonvalue (fixed : Roadmap.Evm.Fixed) :
    (prepareLocatedWord locatedEnv fixed locatedRoot locatedTree [.field 1]).toOption = none := by rfl

theorem located_missing_root (fixed : Roadmap.Evm.Fixed) :
    (prepareLocatedWord locatedEnv fixed ⟨none,"missing"⟩ locatedTree []).toOption = none := by rfl

theorem located_alias_detected (fixed : Roadmap.Evm.Fixed) : locatedAliasCheck (locatedMapCert fixed) (locatedMapCert fixed) = true := by
  simp only [locatedAliasCheck,beq_self_eq_true,Bool.true_or]

end Solidity.Yul.Views.Controls
