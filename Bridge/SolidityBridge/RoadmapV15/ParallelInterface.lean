import SolidityBridge.ExternalEvm.Assembly.Driver
import Solidity.Roadmap.Evm

/-! Concrete handoff over the actual pinned reference state/driver. The G06
Osaka pin and its approved resource predicate are exported separately: this
module does not identify the Cancun reference with a complete Osaka machine.
No new transition system or assumed execution/simulation is introduced. -/
namespace SolidityBridge.RoadmapV15
open EvmYul Solidity.Evm.External

abbrev ReferenceObservation := Assembly.StateView
abbrev referenceObservation := Assembly.observeState

/-- The producer's full retained observation, never just a payment bit/stack. -/
def ReferenceRelated (s t : EVM.State) : Prop :=
  referenceObservation s = referenceObservation t

/-- Resource abstraction remains the existing G06 predicate, not a fabricated
local gas oracle. It does not by itself discharge any opcode gate. -/
abbrev ApprovedResource :=
  {r : Solidity.Roadmap.Evm.GasRes // r.Admissible Solidity.Roadmap.Evm.pinned}

/-- No information is lost when the two explicitly omitted resource fields
are restored: the relation determines the entire actual reference state. -/
theorem reference_related_exact {s t : EVM.State} (h : ReferenceRelated s t)
    (gas : s.gasAvailable = t.gasAvailable) (count : s.execLength = t.execLength) : s = t := by
  cases s with
  | mk ss spc sstack scount =>
    cases t with
    | mk ts tpc tstack tcount =>
      cases ss with
      | mk sw smachine =>
        cases ts with
        | mk tw tmachine =>
          cases smachine with
          | mk sg sa sm sr sh =>
            cases tmachine with
            | mk tg ta tm tr th =>
              cases h
              cases gas
              cases count
              rfl

/-- Concrete decoder and original gas/stack/static/destination checks. There
is no desired step/outcome field; opcode correspondence remains a real proof. -/
structure OpcodeReady (valid : Array UInt256) (s : EVM.State) (packet : Assembly.Packet) where
  charged : EVM.State
  cost : Nat
  decoded : EVM.decode s.executionEnv.code s.pc = some packet
  gate : Assembly.driverGate valid s packet.1 = .ok (charged, cost)

/-- A client must prove its real charged step; the original X continuation is
then available with unchanged fuel and exceptional-halting obligations. -/
theorem OpcodeReady.continue {valid : Array UInt256} {s : EVM.State} {packet : Assembly.Packet}
    (ready : OpcodeReady valid s packet) (fuel : Nat) (next : EVM.State)
    (step : EVM.step (fuel + 1) ready.cost (some packet) ready.charged = .ok next)
    (nonhalting : Assembly.NonhaltingOpcode packet.1) :
    EVM.X (fuel + 2) valid s = EVM.X (fuel + 1) valid next :=
  Assembly.X_continue fuel valid s ready.charged next packet ready.cost
    ready.decoded ready.gate step nonhalting
end SolidityBridge.RoadmapV15
