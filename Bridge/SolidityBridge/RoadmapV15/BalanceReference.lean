import SolidityBridge.RoadmapV15.EnvironmentReference

/-! G46.04 operandful BALANCE consumers. Account truncation, ledger lookup and
access-list update are the actual published definitions. The reference step is
supplied, positive-fuel and zero-charge; warm/cold gas/X, fetched driver, Osaka,
compiler reachability and transaction/world execution remain unproved. -/
namespace SolidityBridge.RoadmapV15
open Solidity Solidity.Backend

/-- Unrestricted256bit operand: backend low160bit addressing observes exactly
the actual reference account lookup, including absent-account zero. -/
theorem environment_balance_value (s : EvmYul.EVM.State) (w : EvmYul.UInt256) :
    (environmentReferenceFrame s).funds
      (Solidity.Backend.Environment.account (environmentReferenceWord w)) =
      environmentReferenceWord (EvmYul.State.balance s.toState w).2 := by
  rfl

/-- Backend consumes the address operand and preserves the complete tail. -/
theorem environment_balance_backend (s : EvmYul.EVM.State) (w : EvmYul.UInt256)
    (tail : List Solidity.Backend.Environment.Word) :
    Solidity.Backend.Environment.step (environmentReferenceFrame s) (.op .BALANCE)
      (environmentReferenceWord w :: tail) =
        some (environmentReferenceWord (EvmYul.State.balance s.toState w).2 :: tail) := by
  rw [Solidity.Backend.Environment.balance_correct, environment_balance_value]

/-- Full actual result state, including the reference's accessed-account update;
no local journal or Boolean replaces it. Backend value is the real pushed word. -/
theorem environment_balance_reference (s : EvmYul.EVM.State) (w : EvmYul.UInt256)
    (tail : List EvmYul.UInt256) (fuel : Nat) :
    let p := Solidity.Evm.External.Memory.prepare {s with stack := w :: tail}
    let pair := EvmYul.State.balance p.toState w
    EvmYul.EVM.step (fuel + 1) 0 (some (.BALANCE, none)) {s with stack := w :: tail} =
      .ok ({p with toState := pair.1}.replaceStackAndIncrPC
        (Solidity.Evm.External.encode (Scalar.encodeValue .uint
          ((environmentReferenceFrame p).funds
            (Solidity.Backend.Environment.account (environmentReferenceWord w)))).toFin :: tail)) := by
  dsimp only []
  rw [environment_balance_value, environment_word_encode]
  rfl

end SolidityBridge.RoadmapV15
