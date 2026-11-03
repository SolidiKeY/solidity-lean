import Solidity.Backend.MemoryCopies.InterfaceV2Laws
import Solidity.Evm.MemoryObjectArrayExamples

/-! Inhabited V2 controls reuse master's populated, separated allocator input.
The oversized/empty-code controls refute certificate construction, not runtime
Panic 0x41, revert or out-of-gas behavior. -/
namespace Solidity.Backend.MemoryCopies.V2.Controls
open Solidity.Evm Solidity.Evm.Memory

private def witness : AllocatorWitness 1 :=
  ⟨_, _, _, 8, ⟨40, by decide⟩, _, ObjectArrayExamples.initial_allocator, by decide⟩

private def default : DefaultCertificate (.array (.prim .uint)) rfl 1 :=
  ⟨Objects.DefaultBuilder.empty (.prim .uint) rfl, witness⟩

private def value : SVal (.ref (.array (.prim .uint))) := .array .nil .nil W_pos

private theorem contents {H : HTy} (hp : Heap H) :
    MVal.copyMToSt (value.copyStToM hp rfl).heap (value.copyStToM hp rfl).val = value.strip := by
  change MVal.copyMToSt ((SVal.array SVec.nil SList.nil W_pos).copyStToM hp rfl).heap
    ((SVal.array SVec.nil SList.nil W_pos).copyStToM hp rfl).val = value.strip
  rw [SVal.copyStToM_array, SVec.copyStToM_nil]
  change MVal.copyMToSt (T := .ref (.array (.prim .uint))) (hp.alloc (Objects.emptyArray (.prim .uint))).1
    (hp.alloc (Objects.emptyArray (.prim .uint))).2 = value.strip
  unfold MVal.copyMToSt
  rw [MVal.copyBelow, MVal.copyAt, MVal.copyRefAt]
  simpa only [MVal.copyAt, MObj.wk, Objects.emptyArray, List.map_nil, value,
    SVal.strip_array, SVec.strip_nil, SVec.ofList] using
    (congrArg (fun object : {l : List PrimTy.uint.Denote // l.length < 2 ^ 256} =>
      SVal.array (SVec.ofList (object.val.map fun x => SVal.prim (p := .uint) x)) SList.nil
        (by simpa only [List.length_map] using object.property))
      (Heap.get_alloc hp (Objects.emptyArray (.prim .uint))))

private def word : StorageWordCertificate value rfl 1 where
  code := default.builder.code
  heap := ⟨contents⟩
  positive := by decide
  feasible := witness
  correct := by
    intro H hp base frame cursor machine represented fits
    obtain ⟨base', machine', execution, allocator, root, extension, shape, preserved, gaps⟩ :=
      default.builder.correct hp base frame cursor machine represented fits
    have selected : base' (value.copyStToM hp rfl).val.id = cursor := by
      simpa only [Heap.allocDefault, SVal.dflt_array, value] using root
    refine ⟨base', machine', ?_, allocator, extension, shape, preserved, selected, ?_⟩
    · rw [selected]
      exact execution
    · intro lo hi gap below
      intro R reference
      exact gaps lo hi gap below reference

theorem default_inhabited : Nonempty (DefaultCertificate (.array (.prim .uint)) rfl 1) :=
  ⟨default⟩

theorem word_inhabited : Nonempty (StorageWordCertificate value rfl 1) := ⟨word⟩

theorem default_empty_rejected : default.builder.code ≠ [] := default.code_ne_nil

theorem word_empty_rejected : word.code ≠ [] := word.code_ne_nil

theorem default_cost_W_rejected :
    ¬ Nonempty (DefaultCertificate (.array (.prim .uint)) rfl W) := default_cost_W_impossible rfl

theorem word_cost_W_rejected : ¬ Nonempty (StorageWordCertificate value rfl W) :=
  word_cost_W_impossible value rfl

private def observe : Evm.Out → Option (Nat × Nat × Nat)
  | .ok machine _ => match machine.stack, machine.mem 0, machine.mem 40 with
    | .val root :: _, .val cursor, .val length => some (root.val, cursor.val, length.val)
    | _, _, _ => none
  | _ => none

/-- Actual emitted default/copy code advances the populated allocator from 40
to 41 and initializes the new empty array's live length. -/
theorem actual_word_observation : observe (run word.code witness.machine) = some (40, 41, 0) := by
  decide +kernel

/-- The actual represented reserved frame is a nonempty object gap; the
strengthened word certificate preserves it and returns the old cursor. -/
theorem actual_reserved_gap :
    let g := value.copyStToM witness.heap rfl
    ∃ (base' : Nat → Fin W) (machine' : Machine), run word.code witness.machine =
      .ok (machine'.push (.val witness.cursor)) 0 ∧
      Objects.Gap g.heap base' 0 witness.frame := by
  have gap : Objects.Gap witness.heap witness.base 0 witness.frame := by
    intro R reference
    exact .inr (witness.represented.heap.owner.above reference)
  obtain ⟨base', machine', execution, _, _, _, _, root, gaps⟩ :=
    word.correct witness.heap witness.base witness.frame witness.cursor witness.machine
      witness.represented witness.fits
  rw [root] at execution
  exact ⟨base', machine', execution, gaps 0 witness.frame gap witness.represented.free.above⟩

#print axioms default_inhabited
#print axioms word_inhabited
#print axioms default_cost_W_rejected
#print axioms word_cost_W_rejected
#print axioms actual_word_observation
#print axioms actual_reserved_gap
end Solidity.Backend.MemoryCopies.V2.Controls
