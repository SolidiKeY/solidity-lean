import Solidity.Yul.Composition.LocalPhysical
import Solidity.Yul.Composition.PhysicalMemory

/-! Concrete observation consumers AFTER actual raw local execution. No raw
Source operator, allocator, physical-world journal carrier or log conversion. -/
namespace Solidity.Yul.Composition
open Solidity.Yul.Views
open Solidity.Roadmap (Address)

/-- The actual physical full word survives the actual local block, including
owned dirty bytes and padding. Request/account/static/separation remain real. -/
theorem local_persistent_word (ctx : Source.Ctx)
    (ps ts : (a : Address) → List (ScalarPath ctx.env.layout (ctx.env.lay a)))
    (q : PackedSlotRequest) (before : BoolEncodingJournal) (F : Source.Fr)
    (p : RepresentedSlotPlan ps ts q before) (s : Source.EMState ctx.env ctx.tys)
    (r : ResidualJournal complementCarrierOwnership) {control}
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (fuel : Nat) {result}
    (done : (representedThenLocal ctx ps ts q before F p s r code policy fuel).2 = .ok (some result))
    (owner : q.address = F.this) (static : F.static = false) (bank : q.transient = false)
    (separated : finiteSeparated (ps q.address)) :
    reencodePersistentSlot (representedBanks ps false (representedSourceStep ps ts q before F p s r).2)
      ⟨result.state.2.ex,(representedSourceStep ps ts q before F p s r).1.2⟩ F.this q.slot = some q.raw := by
  rw [represented_local_source ctx ps ts q before F p s r code policy fuel done,← owner]
  exact represented_step_persistent_at_request F p s r static bank separated

/-- A typed heap byte object remains present in the complete Source.St after
raw writeback, so the real image/window/target copy theorem still applies.
Placement/reserved/window/bounds are explicit; this is not G01 refinement. -/
theorem local_heap_window_target (ctx : Source.Ctx)
    (ps ts : (a : Address) → List (ScalarPath ctx.env.layout (ctx.env.lay a)))
    (q : PackedSlotRequest) (before : BoolEncodingJournal) (F : Source.Fr)
    (p : RepresentedSlotPlan ps ts q before) (s : Source.EMState ctx.env ctx.tys)
    (r : ResidualJournal complementCarrierOwnership) {control}
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (fuel : Nat) {result}
    (done : (representedThenLocal ctx ps ts q before F p s r code policy fuel).2 = .ok (some result))
    (placement : Placement (representedSourceStep ps ts q before F p s r).1.1.2.2.heap)
    (id : Nat) (bytes : List UInt8) (bound : bytes.length < 2^256)
    (found : (representedSourceStep ps ts q before F p s r).1.1.2.2.heap.get id =
      some ⟨.bytes .memory,.bytes bytes⟩)
    (memory : ByteView) (reserved : ReservedOK memory placement.free)
    (offset size destination : Nat) (selected : List UInt8)
    (window : Solidity.Yul.World.returnWindow bytes offset size = some selected)
    (caller : Solidity.Backend.Environment.Slice) (fits : destination + selected.length ≤ 2^256) :
    result.state.2.heap.get id = some ⟨.bytes .memory,.bytes bytes⟩ ∧
    let image : MemoryImage placement (Source.Data.bytes (l := .memory) bytes) := .bytes bytes bound
    let physical := image.encode memory (placement.address id)
    ReservedOK physical placement.free ∧
    Solidity.Backend.Environment.runData (Solidity.Backend.Environment.materialize destination selected) caller =
      some {caller with memory := copyBytes caller.memory physical destination (placement.address id+32+offset) size} ∧
    ValidRange (placement.address id+32+offset) size := by
  constructor
  · rw [represented_local_source ctx ps ts q before F p s r code policy fuel done]
    exact found
  · exact allocated_bytes_window_target placement id bytes bound found memory reserved
      offset size destination selected window caller fits

#print axioms local_persistent_word
#print axioms local_heap_window_target
end Solidity.Yul.Composition
