import Solidity.Lowering.V08.HelperPackets.ConstructorTransport.MachineRelV1

/-! H57 exact-Nat constructor relation and bounded, lossless V1/V2 bridges.
The Nat relation has no intrinsic Fits field; bounds below are proved for this
actual constructor fixture, not claimed for arbitrary reachable Source states. -/
namespace Solidity.Lowering.V08.HelperPackets.ConstructorTransport
open Solidity
open Solidity.Lowering.V07

structure MachineRelNat (bytes : Roadmap.Bytes) (s : Source.St E) (t : State Cell []) : Prop where
  saved : SlotRel savedDecl (SRef.ofRoot "saved" rfl) s t
  captured : SlotRel capturedDecl (SRef.ofRoot "captured" rfl) s t
  sourceHeap : s.heap = (initial bytes).heap
  sourceEvents : s.events = (initial bytes).events
  sourceLogs : s.logs = (initial bytes).logs
  sourceLocals : s.fnLocals = (initial bytes).fnLocals
  targetHeap : t.H = entered.H
  heap : HEq t.heap entered.heap
  balance : (s.ex.world.accounts frame.this).balance = t.selfBalance.1.toNat
  net : t.net = entered.net
  tx : t.tx = entered.tx

theorem word_relation_to_nat (bytes : Roadmap.Bytes) (s : Source.St E) (t : State Cell [])
    (w : Roadmap.Word) (balance_eq : w.val = (s.ex.world.accounts frame.this).balance)
    (old : MachineRelV1 bytes s t w) : MachineRelNat bytes s t := by
  refine ⟨old.saved, old.captured, old.sourceHeap, old.sourceEvents, old.sourceLogs,
    old.sourceLocals, old.targetHeap, old.heap, ?_, old.net, old.tx⟩
  rw [← balance_eq]
  exact old.balance

theorem nat_relation_to_word (bytes : Roadmap.Bytes) (s : Source.St E) (t : State Cell [])
    (w : Roadmap.Word) (balance_eq : w.val = (s.ex.world.accounts frame.this).balance)
    (exactMoney : MachineRelNat bytes s t) : MachineRelV1 bytes s t w := by
  refine ⟨exactMoney.saved, exactMoney.captured, exactMoney.sourceHeap, exactMoney.sourceEvents,
    exactMoney.sourceLogs, exactMoney.sourceLocals, exactMoney.targetHeap, exactMoney.heap,
    ?_, exactMoney.net, exactMoney.tx⟩
  rw [balance_eq]
  exact exactMoney.balance

theorem relations_iff_of_word (bytes : Roadmap.Bytes) (s : Source.St E) (t : State Cell [])
    (w : Roadmap.Word) (balance_eq : w.val = (s.ex.world.accounts frame.this).balance) :
    MachineRelV1 bytes s t w ↔ MachineRelNat bytes s t :=
  ⟨word_relation_to_nat bytes s t w balance_eq, nat_relation_to_word bytes s t w balance_eq⟩

/-- The legacy Word view is lossless only under this explicit bound. -/
theorem relations_iff_of_fits (bytes : Roadmap.Bytes) (s : Source.St E) (t : State Cell [])
    (fits : Source.Monetary.Fits (s.ex.world.accounts frame.this).balance) :
    MachineRelV1 bytes s t (Source.Monetary.wordView (s.ex.world.accounts frame.this).balance) ↔
      MachineRelNat bytes s t :=
  relations_iff_of_word bytes s t _ (Source.Monetary.wordView_exact _ fits)

theorem initial_balance_fits (bytes : Roadmap.Bytes) :
    Source.Monetary.Fits ((initial bytes).ex.world.accounts frame.this).balance := by
  change (5 : Nat) < Source.Monetary.wordLimit
  decide

theorem reached_balance_fits (bytes : Roadmap.Bytes) (n : Int) (h : range n) :
    Source.Monetary.Fits ((reached bytes n h).ex.world.accounts frame.this).balance := by
  change (5 : Nat) < Source.Monetary.wordLimit
  decide

end Solidity.Lowering.V08.HelperPackets.ConstructorTransport
