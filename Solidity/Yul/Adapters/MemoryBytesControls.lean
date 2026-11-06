import Solidity.Yul.Adapters.MemoryBytes

/-! Finite controls for snapshot overlap and byte preservation. These test
existing mathematical byte APIs, not compiler/EVM execution or heap adequacy. -/
namespace Solidity.Yul.Adapters.MemoryBytes.Controls
open Solidity.Backend

def seed : Views.ByteView := fun i => UInt8.ofNat (i+1)
def forward : Views.ByteView := Environment.writeBytes seed 2 (Environment.readMemory seed 0 4)
def backward : Views.ByteView := Views.mcopy seed 0 2 4

/-- info: [1, 2, 1, 2, 3, 4, 7] -/
#guard_msgs in #eval (Views.readBytes forward 0 7).map UInt8.toNat
/-- info: [3, 4, 5, 6, 5, 6, 7] -/
#guard_msgs in #eval (Environment.readMemory backward 0 7).map UInt8.toNat

/- Reading a newly overwritten source byte discriminates in-place sequencing
from the old-snapshot semantics; this is an explicit bad update, no interpreter. -/
def overwritten : Views.ByteView := Environment.writeByte seed 2 (seed 0)
def wrong : Views.ByteView := Environment.writeByte overwritten 4 (overwritten 2)
/-- info: false -/
#guard_msgs in #eval decide (wrong 4=forward 4)
/-- info: true -/
#guard_msgs in #eval decide (forward 6=seed 6 ∧ backward 6=seed 6)
/-- info: true -/
#guard_msgs in #eval decide
  (Environment.readMemory (Environment.writeBytes seed 64 [255,2,0,170]) 64 4=[255,2,0,170])

end Solidity.Yul.Adapters.MemoryBytes.Controls
