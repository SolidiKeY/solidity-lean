import Solidity.Yul.World.LoadV2Producer
/-! Guard full-word versus low-byte decoding using a genuinely written initial
image, a nonempty preserved tail, address/capacity boundaries and underflow.
These are point-load kernel controls, not compiler, gas or Y04 adequacy. -/
namespace Solidity.Yul.World.LoadV2Producer.Controls
open Solidity.Backend Solidity.Backend.Environment

def image (memory : Memory) (cell value : Roadmap.Word) : Memory :=
  writeBytes memory (32*cell.val) (Semantics.wordBytes value.val)

theorem populated_image (memory : Memory) (cell value : Roadmap.Word) :
    readMemory (image memory cell value) (32*cell.val) 32 = Semantics.wordBytes value.val := by
  have length : (Semantics.wordBytes value.val).length = 32 := by
    simp only [Semantics.wordBytes,List.length_map,List.length_range]
  have written := read_written (Semantics.wordBytes value.val) (32*cell.val) memory
  rw [length] at written
  exact written

theorem load_written (frame : Frame) (memory : Memory) (cell value : Roadmap.Word)
    (tail : List Word) (fits : 32*cell.val+32 ≤ 2^256) (room : tail.length+1 ≤ 1024) :
    LoadV2.run frame (LoadV2Port.code cell.val) ⟨tail,image memory cell value⟩ =
      some ⟨lenU value.val value.isLt::tail,image memory cell value⟩ :=
  concrete_producer.load frame (image memory cell value) cell value tail fits room
    (populated_image memory cell value)

def dirty : Roadmap.Word := ⟨2^200+257,by decide⟩
def cell : Roadmap.Word := ⟨3,by decide⟩
def tail : List Word := [uintOfNat 7,uintOfNat 511]
def frame : Frame :=
  ⟨account (uintOfNat 0),account (uintOfNat 0),uintOfNat 0,uintOfNat 0,fun _ => uintOfNat 0⟩
def initial : Slice := ⟨tail,image (fun _ => 0) cell dirty⟩

theorem actual_dirty :
    LoadV2.run frame (LoadV2Port.code cell.val) initial =
      some ⟨lenU dirty.val dirty.isLt::tail,initial.memory⟩ :=
  load_written frame (fun _ => 0) cell dirty tail (by decide) (by decide)

theorem wrong_low_byte_refused :
    LoadV2.run frame (LoadV2Port.code cell.val) initial ≠
      some ⟨lenU 1 (by decide)::tail,initial.memory⟩ := by
  intro wrong
  have same := List.cons.inj (congrArg Slice.stack (Option.some.inj (actual_dirty.symm.trans wrong)))
  have values := congrArg (fun word : Word => word.1.toNat) same.1
  change dirty.val = 1 at values
  exact (by decide : dirty.val ≠ 1) values

/-- A concrete singleton word footprint agrees with the same written image.
No correspondence outside that selected cell is asserted. -/
def numeric : Evm.Machine :=
  {Evm.Machine.init (fun _ => 0) ⟨0,by decide⟩ with mem := fun _ => .val dirty}
def live : Nat → Prop := fun n => n = cell.val

theorem numeric_frame : MemoryOps.Physical.WordFrame numeric initial.memory live := by
  constructor
  · intro n hn
    change n = cell.val at hn
    subst n
    decide
  · intro n hn
    change n = cell.val at hn
    subst n
    exact ⟨dirty,rfl,populated_image (fun _ => 0) cell dirty⟩

theorem coherent_point_load :
    ∃ value : Fin Evm.W, numeric.mem cell.val = .val value ∧
      Evm.run [.mloadAt] (numeric.push (.val cell)) = .ok (numeric.push (.val value)) 0 ∧
      LoadV2.run frame (LoadV2Port.code cell.val) ⟨tail,initial.memory⟩ =
        some ⟨lenU value.val value.isLt::tail,initial.memory⟩ ∧
      MemoryOps.Physical.WordFrame (numeric.push (.val value)) initial.memory live :=
  MemoryOps.Physical.ByteWorldV2.Producer.load_at concrete_producer frame numeric
    initial.memory live numeric_frame cell rfl tail (by decide)

theorem empty_stack_refused (f : Frame) (memory : Memory) :
    LoadV2.step f (.op .MLOAD) ⟨[],memory⟩ = none := LoadV2.load_underflow f memory

#guard dirty.val % 256 = 1
#guard dirty.val ≠ 1
#guard tail.length+1 ≤ 1024
#guard ¬ (32*(2^256-1)+32 ≤ 2^256)
#guard (List.replicate 1024 (uintOfNat 0)).length+1 > 1024

/-- info: 'Solidity.Yul.World.LoadV2Producer.Controls.load_written' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms load_written
/-- info: 'Solidity.Yul.World.LoadV2Producer.Controls.actual_dirty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_dirty
/-- info: 'Solidity.Yul.World.LoadV2Producer.Controls.wrong_low_byte_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_low_byte_refused
/-- info: 'Solidity.Yul.World.LoadV2Producer.Controls.coherent_point_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms coherent_point_load
end Solidity.Yul.World.LoadV2Producer.Controls
