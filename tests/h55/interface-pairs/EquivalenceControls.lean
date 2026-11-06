import Solidity.Backend.MemoryCopies.ControlsV2
import Solidity.Backend.Passes.MappedSequence
import Solidity.Backend.MemoryCopies.FixedPathCopyInterface
import Solidity.Backend.MemoryCopies.MemoryPathCopyInterface
import Solidity.Backend.Selection.InterfaceV2Controls
import Solidity.Backend.MemoryCopies.Interface
import Solidity.Backend.MemoryCopies.InterfaceV2Laws

/-! Standalone migration controls. No production API is changed or retired. -/
namespace H55.InterfacePairs
open Solidity Solidity.Backend

namespace SelectionControls

def forgetFrame {input output : Scalar.Stack}
    (c : Selection.V2.FrameCertificate input output) :
    Selection.FrameCertificate input output where
  code := c.code
  frame := c.frame
  prefixes := by
    intro tail bound before after reached split ran
    apply Scalar.prefix_capacity before after ran
    rw [split]
    exact bound

def restoreFrame {input output : Scalar.Stack}
    (c : Selection.FrameCertificate input output) (peak : Nat)
    (room : input.length + peak ≤ 1024)
    (capacity : ∀ tail : Scalar.Stack, (input ++ tail).length + peak ≤ 1024 →
      Scalar.stackBound c.code ((input ++ tail).length : Int) = true) :
    Selection.V2.FrameCertificate input output where
  code := c.code
  peak := peak
  inputRoom := room
  frame := c.frame
  capacity := capacity

theorem frame_roundtrip {input output : Scalar.Stack}
    (c : Selection.V2.FrameCertificate input output) :
    restoreFrame (forgetFrame c) c.peak c.inputRoom c.capacity = c := by
  cases c
  rfl

theorem legacy_frame_roundtrip {input output : Scalar.Stack}
    (c : Selection.FrameCertificate input output) (peak : Nat)
    (room : input.length + peak ≤ 1024)
    (capacity : ∀ tail : Scalar.Stack, (input ++ tail).length + peak ≤ 1024 →
      Scalar.stackBound c.code ((input ++ tail).length : Int) = true) :
    forgetFrame (restoreFrame c peak room capacity) = c := by
  cases c
  rfl

variable {Observation : Type} {source : Nat → Observation}
  {ir : List Evm.Instr} {relation : Observation → Evm.Machine → Evm.Machine → Prop}

def forgetCompiler (c : Selection.V2.CompilerPremise Observation source ir relation) :
    Selection.CompilerPremise Observation source ir relation := ⟨c.preserves⟩

def restoreCompiler (c : Selection.CompilerPremise Observation source ir relation)
    (witness : ∃ budget initial final, relation (source budget) initial final) :
    Selection.V2.CompilerPremise Observation source ir relation :=
  ⟨witness, c.preserves⟩

theorem compiler_exact :
    Selection.V2.CompilerPremise Observation source ir relation ↔
      Selection.CompilerPremise Observation source ir relation ∧
        ∃ budget initial final, relation (source budget) initial final :=
  ⟨fun c => ⟨forgetCompiler c, c.inhabited⟩,
    fun ⟨c, witness⟩ => restoreCompiler c witness⟩

variable {b : Block} {input output : Nat}
  {composition : Selection.CompositionCertificate ir b input output}
  {bridgeStep : LabelExec.State → Option LabelExec.State}
  {bridgeRun : Nat → LabelExec.State → Option LabelExec.State}
  {reachable : LabelExec.State → Prop}

def RuntimeWitness : Prop :=
  ∃ (budget : Nat) (m : Evm.Machine) (s t : Scalar.Stack),
    s.length = input ∧ m.stack = Selection.irStack s ∧
      relation (source budget) m {m with stack := Selection.irStack t} ∧
      Evm.run ir m = .ok {m with stack := Selection.irStack t} 0

def forgetRuntime
    (c : Selection.V2.RuntimeConsumer Observation source ir relation b input output
      composition bridgeStep bridgeRun reachable) :
    Selection.RuntimeConsumer Observation source ir relation b input output
      composition bridgeStep bridgeRun reachable where
  consume := by
    intro compiler decoder budget m s t height stack related
    obtain ⟨budget', m', s', t', _, _, related', _⟩ := c.inhabited
    exact c.consume (restoreCompiler compiler ⟨budget', m', _, related'⟩)
      decoder budget m s t height stack related

def restoreRuntime
    (c : Selection.RuntimeConsumer Observation source ir relation b input output
      composition bridgeStep bridgeRun reachable)
    (witness : RuntimeWitness (source := source) (ir := ir)
      (relation := relation) (input := input)) :
    Selection.V2.RuntimeConsumer Observation source ir relation b input output
      composition bridgeStep bridgeRun reachable where
  inhabited := witness
  consume := fun compiler => c.consume (forgetCompiler compiler)

theorem runtime_exact :
    Selection.V2.RuntimeConsumer Observation source ir relation b input output
      composition bridgeStep bridgeRun reachable ↔
    Selection.RuntimeConsumer Observation source ir relation b input output
      composition bridgeStep bridgeRun reachable ∧
      RuntimeWitness (source := source) (ir := ir) (relation := relation) (input := input) :=
  ⟨fun c => ⟨forgetRuntime c, c.inhabited⟩,
    fun ⟨c, witness⟩ => restoreRuntime c witness⟩

end SelectionControls

namespace MemoryControls
open Evm Evm.Memory
variable {R : RefTy} {value : SVal (.ref R)}
  {hm : (Ty.ref R).mapFree = true} {cost : Nat}

def forgetHeap (c : MemoryCopies.V2.StorageHeapCertificate value hm) :
    MemoryCopies.StorageHeapCertificate value hm where
  keeps := fun hp => SVal.keeps_copyStToM value hm hp
  fresh := fun hp => SVal.copyStToM_id_ge hp value hm
  contents := c.contents

def restoreHeap (c : MemoryCopies.StorageHeapCertificate value hm) :
    MemoryCopies.V2.StorageHeapCertificate value hm := ⟨c.contents⟩

theorem heap_exact :
    MemoryCopies.StorageHeapCertificate value hm ↔
      MemoryCopies.V2.StorageHeapCertificate value hm :=
  ⟨restoreHeap, forgetHeap⟩

def forgetWord (c : MemoryCopies.V2.StorageWordCertificate value hm cost) :
    MemoryCopies.StorageWordCertificate value hm cost where
  code := c.code
  heap := forgetHeap c.heap
  positive := c.positive
  correct := c.correct

def restoreWord (c : MemoryCopies.StorageWordCertificate value hm cost)
    (feasible : MemoryCopies.V2.AllocatorWitness cost) :
    MemoryCopies.V2.StorageWordCertificate value hm cost where
  code := c.code
  heap := restoreHeap c.heap
  positive := c.positive
  feasible := feasible
  correct := c.correct

theorem word_roundtrip (c : MemoryCopies.V2.StorageWordCertificate value hm cost) :
    restoreWord (forgetWord c) c.feasible = c := by
  cases c
  rfl

theorem word_exact :
    Nonempty (MemoryCopies.V2.StorageWordCertificate value hm cost) ↔
      Nonempty (MemoryCopies.StorageWordCertificate value hm cost) ∧
        Nonempty (MemoryCopies.V2.AllocatorWitness cost) := by
  constructor
  · rintro ⟨c⟩
    exact ⟨⟨forgetWord c⟩, ⟨c.feasible⟩⟩
  · rintro ⟨⟨c⟩, ⟨feasible⟩⟩
    exact ⟨restoreWord c feasible⟩

theorem legacy_word_roundtrip (c : MemoryCopies.StorageWordCertificate value hm cost)
    (feasible : MemoryCopies.V2.AllocatorWitness cost) :
    forgetWord (restoreWord c feasible) = c := by
  cases c
  rfl

theorem inhabited_word_roundtrip :
    ∃ (R : RefTy) (value : SVal (.ref R)) (hm : (Ty.ref R).mapFree = true)
      (cost : Nat) (c : MemoryCopies.V2.StorageWordCertificate value hm cost),
      restoreWord (forgetWord c) c.feasible = c := by
  obtain ⟨c⟩ := MemoryCopies.V2.Controls.word_inhabited
  exact ⟨_, _, _, _, c, word_roundtrip c⟩

/-- Root/gap obligations are transported only across an exact roundtrip;
they are not consequences manufactured from a basic word certificate. -/
theorem roots_roundtrip (c : MemoryCopies.V2.StorageWordCertificate value hm cost) :
    MemoryCopies.V2.StorageWordRootCertificate (restoreWord (forgetWord c) c.feasible) ↔
      MemoryCopies.V2.StorageWordRootCertificate c := by
  rw [word_roundtrip]

end MemoryControls

/-! Prototype for the shared room/guard law. Height admission is necessary:
natural subtraction alone accepts height 1025 at peak zero. -/
def StackRoom (height peak : Nat) : Prop := height + peak ≤ 1024

def capacityGuard (height peak : Nat) : Bool := decide (height + peak ≤ 1024)

theorem capacityGuard_exact (height peak : Nat) :
    capacityGuard height peak = true ↔ StackRoom height peak := by
  simp only [capacityGuard, StackRoom, decide_eq_true_eq]

/-- Exact correspondence with the existing scalar primitive capacity guard.
This is not a whole-program stackBound theorem. -/
theorem scalar_guard_exact (height peak : Nat) :
    Scalar.safeHeight ((height + peak : Nat) : Int) = true ↔ StackRoom height peak := by
  simp only [Scalar.safeHeight, decide_eq_true_eq, StackRoom]
  omega

theorem room_remaining_exact (height peak : Nat) :
    StackRoom height peak ↔ height ≤ 1024 ∧ peak ≤ 1024 - height := by
  unfold StackRoom
  omega

theorem frame_room_exact {α : Type} (input tail : List α) (peak : Nat) :
    StackRoom (input ++ tail).length peak ↔
      input.length + peak + tail.length ≤ 1024 := by
  simp only [StackRoom, List.length_append]
  omega

example : capacityGuard 1024 0 = true := rfl
example : capacityGuard 1024 1 = false := rfl
example : capacityGuard 1025 0 = false := rfl
example : (0 : Nat) ≤ 1024 - 1025 := by decide

/-! The shared path schema must preserve unsuccessful-resolution vacuity and
different per-reference costs. It does not identify fixed and dynamic layouts. -/
def ResolvedRoom {Reference : Type} (resolved : Reference → Prop)
    (cursor : Nat) (cost : Reference → Nat) : Prop :=
  ∀ reference, resolved reference → cursor + cost reference < 2^256

theorem unresolved_room {Reference : Type} (cursor : Nat) (cost : Reference → Nat) :
    ResolvedRoom (fun _ => False) cursor cost := fun _ bad => False.elim bad

theorem selected_map_counterexample :
    (∃ map : Nat, map = 1) ∧ ¬ (∀ map : Nat, map = 1 → map = 0) := by
  constructor
  · exact ⟨1, rfl⟩
  · intro bad
    have impossible : (1 : Nat) = 0 := bad 1 rfl
    cases impossible

example : max 1 (0 : Nat) = 1 := rfl
example : max 1 (1 : Nat) ≠ 1 + 1 := by decide

#print axioms SelectionControls.frame_roundtrip
#print axioms SelectionControls.legacy_frame_roundtrip
#print axioms SelectionControls.compiler_exact
#print axioms SelectionControls.runtime_exact
#print axioms MemoryControls.heap_exact
#print axioms MemoryControls.word_roundtrip
#print axioms MemoryControls.inhabited_word_roundtrip
#print axioms MemoryControls.roots_roundtrip
#print axioms MemoryControls.word_exact
#print axioms MemoryControls.legacy_word_roundtrip
#print axioms capacityGuard_exact
#print axioms scalar_guard_exact
#print axioms room_remaining_exact
#print axioms frame_room_exact
#print axioms unresolved_room
#print axioms selected_map_counterexample

namespace BoundaryControls
open Evm Evm.Compiler Passes
variable {C : Contract} {b L frame : Nat} {Γ Δ Ξ : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ}

/-- A proof-only map policy over the existing mapped output, with all success
and representation hypotheses retained. It does not select a new runtime map. -/
def Transport (left : Compilation b F P) (right : Compilation b left.frag Q)
    (L frame : Nat) (base : Nat → Fin W) (σ : State C Γ) (m : Machine)
    (select : (Nat → Fin W) → (Nat → Fin W)) : Prop :=
  ∀ (o : Solidity.Out C σ.H Δ) (m' : Machine) (midBase : Nat → Fin W),
    P.run σ = .ok o → run left.code m = .ok m' 0 →
    MappedOutput left (L + Evm.Prog.pushes P) frame base σ m o.st m' midBase →
    right.Input (L + Evm.Prog.pushes P) frame (select midBase) o.st m'

theorem fixed_exact (left : Compilation b F P) (right : Compilation b left.frag Q)
    (base nextBase : Nat → Fin W) (σ : State C Γ) (m : Machine) :
    BoundaryLink left right L frame base nextBase σ m ↔
      Transport left right L frame base σ m (fun _ => nextBase) := by
  constructor
  · intro link o m' midBase source target mapped
    exact link o m' source target
      ((mapped_output_iff left (L + Evm.Prog.pushes P) frame base σ m o.st m').mpr
        ⟨midBase, mapped⟩)
  · intro link o m' source target represented
    obtain ⟨midBase, mapped⟩ :=
      (mapped_output_iff left (L + Evm.Prog.pushes P) frame base σ m o.st m').mp represented
    exact link o m' midBase source target mapped

theorem mapped_exact (left : Compilation b F P) (right : Compilation b left.frag Q)
    (base : Nat → Fin W) (σ : State C Γ) (m : Machine) :
    MappedBoundaryLink left right L frame base σ m ↔
      Transport left right L frame base σ m (fun midBase => midBase) := Iff.rfl

/-- Conversion is valid only on an explicitly fixed selected-map domain. -/
theorem fixed_to_mapped (left : Compilation b F P) (right : Compilation b left.frag Q)
    (base nextBase : Nat → Fin W) (σ : State C Γ) (m : Machine)
    (same : ∀ (o : Solidity.Out C σ.H Δ) (m' : Machine) (midBase : Nat → Fin W),
      P.run σ = .ok o → run left.code m = .ok m' 0 →
      MappedOutput left (L + Evm.Prog.pushes P) frame base σ m o.st m' midBase →
      midBase = nextBase)
    (link : BoundaryLink left right L frame base nextBase σ m) :
    MappedBoundaryLink left right L frame base σ m := by
  intro o m' midBase source target mapped
  rw [same o m' midBase source target mapped]
  exact (fixed_exact left right base nextBase σ m).mp link o m' midBase source target mapped

theorem mapped_to_fixed (left : Compilation b F P) (right : Compilation b left.frag Q)
    (base nextBase : Nat → Fin W) (σ : State C Γ) (m : Machine)
    (same : ∀ (o : Solidity.Out C σ.H Δ) (m' : Machine) (midBase : Nat → Fin W),
      P.run σ = .ok o → run left.code m = .ok m' 0 →
      MappedOutput left (L + Evm.Prog.pushes P) frame base σ m o.st m' midBase →
      midBase = nextBase)
    (link : MappedBoundaryLink left right L frame base σ m) :
    BoundaryLink left right L frame base nextBase σ m := by
  intro o m' source target represented
  obtain ⟨midBase, mapped⟩ :=
    (mapped_output_iff left (L + Evm.Prog.pushes P) frame base σ m o.st m').mp represented
  rw [← same o m' midBase source target mapped]
  exact link o m' midBase source target mapped

end BoundaryControls

namespace PathControls
open Evm Evm.Memory MemoryCopies
variable {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat}

/-- The fixed schema retains the actual indexed path and its headerless cost. -/
theorem fixed_exact (state : State C Γ) (cursor : Fin W)
    (path : MPath C Γ (.ref (.fixed (.prim primitive) count))) :
    FixedPathRoom state cursor path ↔
      ResolvedRoom (fun reference => path.mvalT state = .ok reference)
        cursor.val (fun _ => max 1 count) := Iff.rfl

/-- Dynamic cost observes the live parent header through the same typed reference. -/
theorem dynamic_exact (state : State C Γ) (cursor : Fin W)
    (path : MPath C Γ (.ref (.array (.prim primitive)))) :
    MemoryPathRoom state cursor path ↔
      ResolvedRoom (fun reference => path.mvalT state = .ok reference)
        cursor.val (fun reference => state.heap.len reference .dyn + 1) := Iff.rfl

end PathControls

#print axioms BoundaryControls.fixed_exact
#print axioms BoundaryControls.mapped_exact
#print axioms BoundaryControls.fixed_to_mapped
#print axioms BoundaryControls.mapped_to_fixed
#print axioms PathControls.fixed_exact
#print axioms PathControls.dynamic_exact
end H55.InterfacePairs
