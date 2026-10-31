import Solidity.Backend.Environment.Observations
import SolidityBridge.RoadmapV15.ReferenceEncoding
import SolidityBridge.ExternalEvm.Environment
import SolidityBridge.ExternalEvm.Memory

/-! G46.04 consumers connecting intrinsic backend environment selection to the
actual reference account/context projections. The supplied-opcode consequence
uses positive fuel and zero charged gas. It is not X/driver adequacy, Osaka fork
agreement, source execution, or account/transaction/trace correspondence.
BALANCE and other metadata instructions remain separate open obligations. -/
namespace SolidityBridge.RoadmapV15
open Solidity Solidity.Backend

def environmentReferenceWord (w : EvmYul.UInt256) : Solidity.Backend.Environment.Word :=
  lenU w.toNat w.val.isLt

def environmentReferenceAddress (a : EvmYul.AccountAddress) : Solidity.Backend.Environment.Address :=
  ⟨lenU a.val (Nat.lt_trans a.isLt (by decide)), by
    change (a.val : Int) < (2 : Int) ^ 160
    exact_mod_cast a.isLt⟩

theorem environment_address_word (a : EvmYul.AccountAddress) :
    (environmentReferenceAddress a).1 =
      environmentReferenceWord (EvmYul.UInt256.ofNat a.val) := by
  apply Subtype.ext
  change (a.val : Int) = (a.val % EvmYul.UInt256.size : Nat)
  rw [Nat.mod_eq_of_lt (Nat.lt_trans a.isLt (by decide))]

theorem environment_address_roundtrip (a : EvmYul.AccountAddress) :
    EvmYul.AccountAddress.ofNat (environmentReferenceAddress a).1.1.toNat = a := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt a.isLt

/-- Canonical frame from the actual reference account map, including absent
accounts. This constructs an observation frame, not an execution witness. -/
def environmentReferenceFrame (s : EvmYul.EVM.State) : Solidity.Backend.Environment.Frame where
  self := environmentReferenceAddress s.executionEnv.codeOwner
  sender := environmentReferenceAddress s.executionEnv.source
  value := environmentReferenceWord s.executionEnv.weiValue
  time := environmentReferenceWord (EvmYul.State.timeStamp s.toState)
  funds := fun a => environmentReferenceWord ((s.accountMap.find?
    (EvmYul.AccountAddress.ofNat a.1.1.toNat)).elim (EvmYul.UInt256.ofNat 0) (·.balance))

/-- Routing existing reference projections; no environment semantics is added. -/
def environmentReferenceValue (s : EvmYul.EVM.State) : EnvKey → EvmYul.UInt256
  | .msgSender => EvmYul.UInt256.ofNat s.executionEnv.source.val
  | .msgValue => s.executionEnv.weiValue
  | .timestamp => EvmYul.State.timeStamp s.toState
  | .selfBalance => EvmYul.State.selfbalance s.toState
  | .selfAddress => EvmYul.UInt256.ofNat s.executionEnv.codeOwner.val

theorem environment_word_encode (w : EvmYul.UInt256) :
    Solidity.Evm.External.encode (Scalar.encodeValue .uint
      (environmentReferenceWord w)).toFin = w := by
  have hn := Scalar.encode_uint_toNat (environmentReferenceWord w)
  have hf : (Scalar.encodeValue .uint (environmentReferenceWord w)).toFin =
      Solidity.Evm.External.decode w := Fin.ext hn
  rw [hf, Solidity.Evm.External.encode_decode]

theorem environment_observe_reference (s : EvmYul.EVM.State) (k : EnvKey) :
    Solidity.Backend.Environment.observe (environmentReferenceFrame s) k =
      environmentReferenceWord (environmentReferenceValue s k) := by
  cases k
  · exact environment_address_word _
  · rfl
  · rfl
  · change environmentReferenceWord ((s.accountMap.find?
      (EvmYul.AccountAddress.ofNat (environmentReferenceAddress
        s.executionEnv.codeOwner).1.1.toNat)).elim _ _) = _
    rw [environment_address_roundtrip]
    rfl
  · exact environment_address_word _

theorem environment_selected_backend (s : EvmYul.EVM.State) (k : EnvKey)
    (tail : List Solidity.Backend.Environment.Word) :
    Solidity.Backend.Environment.step (environmentReferenceFrame s) (Solidity.Backend.Environment.select k) tail =
      some (environmentReferenceWord (environmentReferenceValue s k) :: tail) := by
  rw [Solidity.Backend.Environment.select_correct, environment_observe_reference]

def environmentReferenceOp : EnvKey → EvmYul.Operation .EVM
  | .msgSender => .CALLER
  | .msgValue => .CALLVALUE
  | .timestamp => .TIMESTAMP
  | .selfBalance => .SELFBALANCE
  | .selfAddress => .ADDRESS

/-- Actual supplied-opcode dispatch: the whole resulting state and stack tail
are retained. Gas/stack/X admissibility and fetched code are not established. -/
theorem environment_selected_reference (s : EvmYul.EVM.State) (k : EnvKey)
    (tail : List EvmYul.UInt256) (fuel : Nat) :
    EvmYul.EVM.step (fuel + 1) 0 (some (environmentReferenceOp k, none))
      {s with stack := tail} = .ok
        ((Solidity.Evm.External.Memory.prepare {s with stack := tail}).replaceStackAndIncrPC
          (Solidity.Evm.External.encode (Scalar.encodeValue .uint
            (Solidity.Backend.Environment.observe (environmentReferenceFrame s) k)).toFin :: tail)) := by
  rw [environment_observe_reference, environment_word_encode]
  cases k <;> rfl

/-- Full ordered 32-byte observation of the selected value. -/
theorem environment_reference_bytes (s : EvmYul.EVM.State) (k : EnvKey) :
    (Solidity.Evm.External.Memory.encoding (environmentReferenceValue s k)).toList =
      (toBytesBE 32 (Scalar.encodeValue .uint
        (Solidity.Backend.Environment.observe (environmentReferenceFrame s) k)).toNat).toList := by
  rw [← environment_word_encode (environmentReferenceValue s k)]
  rw [reference_encoding_scalar, environment_observe_reference]

/-- Source observation transport with the published representation relation
explicit. This does not assert preservation or construction of a source run. -/
theorem environment_source_observation {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (s : EvmYul.EVM.State)
    (h : Solidity.Backend.Environment.Represents (environmentReferenceFrame s) σ)
    (k : EnvKey) :
    Solidity.Evm.External.encode (Scalar.encodeValue .uint (σ.envVal k)).toFin =
      environmentReferenceValue s k := by
  rw [h.denote, environment_observe_reference, environment_word_encode]

end SolidityBridge.RoadmapV15
