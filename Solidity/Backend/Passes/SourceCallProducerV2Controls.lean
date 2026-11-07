import Solidity.Backend.Passes.SourceCallProducerV2
import Solidity.Backend.Passes.SourceCallProducerControls

/-! Controls for the MachineV2 G42.02 producer on the actual payment
invocation `WorldCalls.PaymentControl.origin` (`ping()`, value 0, source
outcome `success []`). Positive: the agreeing oracle leaves the source payload
in the buffer and journals the `ping()` selector bytes. Negative: a lying
oracle is observed, and the pinned relation refuses a wrong buffer. -/
namespace Solidity.Backend.Passes.SourceCallProducerV2Controls
open Solidity.Source Solidity.Source.SemanticsExamples Solidity.Evm
open Solidity.Backend.WorldCalls
open Solidity.Backend.Passes.SourceCallProducerV2

abbrev origin := PaymentControl.origin

theorem small : (input origin).length < W := by decide

theorem source_payload : SourceCallProducerV2.payload (SourceCallProducer.raw origin) = some (true, []) := by
  rw [SourceCallProducerControls.produced_raw.1]
  rfl

def cell : Fin W := ⟨64, by decide⟩
def machine : MachineV2 := MachineV2.ofBase PaymentControl.initial

theorem transported_control :
    ∃ m', runV2 (code origin cell) (oracle origin machine true []) = .ok m' 0 ∧ m'.returndata = [] ∧
      m'.base.stack = [] ∧ m'.calls = [⟨receiver origin, amount origin, input origin, true, []⟩] :=
  transported origin cell machine small true [] source_payload

/-- The journaled call input is the captured `ping()` selector. -/
theorem journaled_input :
    ∃ m', runV2 (code origin cell) (oracle origin machine true []) = .ok m' 0 ∧
      m'.calls.map (·.input) = [selOf "ping()"] := by
  obtain ⟨m', run, _, _, calls⟩ := transported_control
  exact ⟨m', run, by rw [calls]; rfl⟩

/-- A lying oracle: funded and accepting, but answering `[1]`. -/
def liar : MachineV2 := {oracle origin machine true [] with reply := fun _ _ _ => [1]}

theorem liar_disagrees : ¬ OracleAgrees origin liar true [] := by
  intro h
  have r := h.reply
  cases r

theorem liar_observed :
    ∃ m', runV2 (code origin cell) liar = .ok m' 0 ∧ m'.returndata = [1] := by
  obtain ⟨m', run, _, _, _, cases⟩ := call_run origin cell liar small
  rcases cases with ⟨_, buffer, _⟩ | ⟨poor, _, _⟩
  · exact ⟨m', run, buffer⟩
  · exact absurd poor (Nat.not_lt_of_le (Nat.le_of_lt (amount origin).isLt))

/-- `Returndata` is not identically true in the target outcome: an outcome
with another buffer (hand-built, not a run) is refused under agreeing oracles. -/
theorem wrong_buffer_refused :
    ¬ Returndata origin (oracle origin machine true [])
      (.ok {oracle origin machine true [] with returndata := [1]} 0) (SourceCallProducer.raw origin) := by
  intro h
  obtain ⟨m', same, buffer, _⟩ := h true [] source_payload (oracle_agrees origin machine true [])
  cases same
  cases buffer

/-- Multi-cell transport, computed by the kernel independently of
`readBytes_stores` (on explicit cells, since `chunks` is well-founded and does
not reduce in the kernel): a 40-byte input spans two cells and reads back. -/
def forty : List UInt8 := (List.range 40).map UInt8.ofNat

/-- The two padded cells of `forty`, written out. -/
def fortyCells : List (List UInt8) :=
  [(List.range 32).map UInt8.ofNat,
    (List.range' 32 8).map UInt8.ofNat ++ List.replicate 24 0]

theorem two_cells_read :
    readBytes (SourceCallBytes.storeMem (fun _ => w[0]) 3 fortyCells) 3 40 = some forty := by
  decide +kernel

end Solidity.Backend.Passes.SourceCallProducerV2Controls

/-- info: 'Solidity.Backend.Passes.SourceCallProducerV2Controls.small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducerV2Controls.small
/-- info: 'Solidity.Backend.Passes.SourceCallProducerV2Controls.source_payload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducerV2Controls.source_payload
/-- info: 'Solidity.Backend.Passes.SourceCallProducerV2Controls.transported_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducerV2Controls.transported_control
/-- info: 'Solidity.Backend.Passes.SourceCallProducerV2Controls.journaled_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducerV2Controls.journaled_input
/-- info: 'Solidity.Backend.Passes.SourceCallProducerV2Controls.liar_disagrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducerV2Controls.liar_disagrees
/-- info: 'Solidity.Backend.Passes.SourceCallProducerV2Controls.liar_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducerV2Controls.liar_observed
/-- info: 'Solidity.Backend.Passes.SourceCallProducerV2Controls.wrong_buffer_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducerV2Controls.wrong_buffer_refused

/-- info: 'Solidity.Backend.Passes.SourceCallProducerV2Controls.two_cells_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducerV2Controls.two_cells_read
