import Solidity.Lowering.V08.HelperPackets.ConstructorTransport.Target

/-! H57 frozen Word-balance relation. Current Source.St carries exact Nat money,
so the former Word balance is an explicit legacy view; its .val condition and
all nonmonetary observations are retained. No equality to exact money is assumed
by this record: the bridge must establish that equality. The original full
declaration and statements are preserved verbatim in the frozen text snapshot. -/
namespace Solidity.Lowering.V08.HelperPackets.ConstructorTransport
open Solidity
open Solidity.Lowering.V07

def SlotRel (d : Source.Decl) (r : SRef Cell (.prim .uint))
    (s : Source.St E) (t : State Cell [])
    (hd : E.lay frame.this d.path = uint := by rfl) : Prop :=
  ∃ (v : Int) (hv : range v),
    (s.ex.world.accounts frame.this).storage.read d.path = some (hd.symm ▸ (Source.Val.int v hv : Source.Val E.layout uint)) ∧
    t.storage.find r = some (.prim (integerValue Source.IntTy.u256 v hv))

structure MachineRelV1 (bytes : Roadmap.Bytes) (s : Source.St E) (t : State Cell [])
    (sourceBalance : Roadmap.Word) : Prop where
  saved : SlotRel savedDecl (SRef.ofRoot "saved" rfl) s t
  captured : SlotRel capturedDecl (SRef.ofRoot "captured" rfl) s t
  sourceHeap : s.heap = (initial bytes).heap
  sourceEvents : s.events = (initial bytes).events
  sourceLogs : s.logs = (initial bytes).logs
  sourceLocals : s.fnLocals = (initial bytes).fnLocals
  targetHeap : t.H = entered.H
  heap : HEq t.heap entered.heap
  balance : sourceBalance.val = t.selfBalance.1.toNat
  net : t.net = entered.net
  tx : t.tx = entered.tx


end Solidity.Lowering.V08.HelperPackets.ConstructorTransport
