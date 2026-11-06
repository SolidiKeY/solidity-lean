import Solidity.Backend.Passes.EffectfulReferencePair
import Solidity.Evm.MemoryCompileExamples
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.Passes.EffectfulReferencePair.Controls
open Evm Evm.Memory Evm.Compiler Solidity.Lowering.V07
open Source.SemanticsExamples (E0 G0 F0 s0)
open CompileExamples
abbrev srcΓ : Source.RCtx := [.bytes .memory,.bytes .memory]
def sourceHeap : Source.Heap E0.layout :=
  (((Source.Heap.empty : Source.Heap E0.layout).alloc ⟨.bytes .memory,.bytes [7,9]⟩).1.alloc
    ⟨.bytes .memory,.bytes [4]⟩).1
def source : Source.EMState E0 srcΓ :=
  (.cons (.memRef rfl 1) (.cons (.memRef rfl 0) .nil),{s0 with heap := sourceHeap})
abbrev oldIndex : Idx Γ (.mem bytesR) := .there .here
abbrev newIndex : Idx Γ (.mem bytesR) := .there (.there (.there .here))
def program (p : Roadmap.Pipeline) : Prog C Γ (.mem bytesR :: .mem bytesR :: Γ) :=
  memoryAssignReadPrefix p oldIndex newIndex rfl
def selected (p : Roadmap.Pipeline) : Memory.CompiledProg 0 (Frag.init Γ) (program p) :=
  (Memory.compileProg 0 (Frag.init Γ) (program p)).get (by cases p <;> decide +kernel)
def compiled (p : Roadmap.Pipeline) : Compilation 0 (Frag.init Γ) (program p) := .memory (selected p)

theorem input (p : Roadmap.Pipeline) : (compiled p).Input 1 6 base σ machine := by
  refine ⟨fixture_six_cells,?_,?_⟩
  · cases p <;> decide +kernel
  · apply Or.inl
    cases p <;> rfl

theorem identities : (0 : Nat) = 1 ↔ r0 = r1 := by
  constructor
  · intro impossible; omega
  · intro same
    have number := congrArg HRef.id same
    change (0 : Nat) = 1 at number
    omega

def application (p : Roadmap.Pipeline) (fuel : Nat) :=
  execution (G0 p) F0 fuel source σ (.there .here) .here oldIndex newIndex
    0 1 r0 r1 rfl rfl rfl rfl (fun address ref => address = ref.id)
    rfl rfl identities (compiled p) (input p)

theorem source_heap_live : source.2.heap.get 0 = some ⟨.bytes .memory,.bytes [7,9]⟩ ∧
    source.2.heap.get 1 = some ⟨.bytes .memory,.bytes [4]⟩ := ⟨rfl,rfl⟩

private def okMachine : Evm.Out → Option Machine
  | .ok m 0 => some m | _ => none
private theorem extracted {out : Evm.Out} (h : (okMachine out).isSome) :
    out = .ok ((okMachine out).get h) 0 := by
  cases out with
  | ok m skip => cases skip with
    | zero => rfl
    | succ n => cases h
  | revert => cases h
  | fault => cases h
@[irreducible] def executed (p : Roadmap.Pipeline) : Machine :=
  (okMachine (run (compiled p).code machine)).get (by cases p <;> decide +kernel)
def observed (p : Roadmap.Pipeline) (tail : List Word) : Machine := {executed p with stack := tail}

theorem actual_target (p : Roadmap.Pipeline) :
    run (compiled p).code machine = .ok (executed p) 0 := by unfold executed; exact extracted _

theorem target_tail (p : Roadmap.Pipeline) (tail : List Word) :
    run (compiled p).code {machine with stack := tail} = .ok (observed p tail) 0 := by
  have canonical := compilation_tail_exact (compiled p) (input p) (payment_free p oldIndex newIndex) []
  change run (compiled p).code machine = _ at canonical
  rw [actual_target] at canonical
  have target := compilation_tail_exact (compiled p) (input p) (payment_free p oldIndex newIndex) tail
  cases outcome : run (compiled p).code {machine with stack := []} with
  | ok final skip =>
    rw [outcome] at canonical target
    have skipZero : skip = 0 := (Evm.Out.ok.inj canonical).2.symm
    subst skip
    have projected := congrArg (fun m : Machine => {m with stack := tail}) (Evm.Out.ok.inj canonical).1
    simpa only [replaceOutStack,observed] using target.trans
      (congrArg (fun m => Evm.Out.ok m 0) projected.symm)
  | revert => rw [outcome] at canonical; cases canonical
  | fault => rw [outcome] at canonical; cases canonical

def cells : List Nat := [0,1,2,3,4,5,16,17,18,19,20,21,22]
theorem initial_observations : (cells.map machine.mem,machine.stack) =
    ([w[20],w[16],w[16],w[0],w[0],w[0],w[2],w[7],w[9],w[0],w[1],w[4],w[0]],[]) := by decide +kernel

theorem complete_observations (p : Roadmap.Pipeline) (tail : List Word) :
    (cells.map (observed p tail).mem,(observed p tail).stack) =
      ([w[20],w[16],w[20],w[0],(if p = .legacy then w[16] else w[20]),w[20],
        w[2],w[7],w[9],w[0],w[1],w[4],w[0]],tail) := by
  apply Prod.ext
  · change cells.map (executed p).mem =
      [w[20],w[16],w[20],w[0],(if p = .legacy then w[16] else w[20]),w[20],
        w[2],w[7],w[9],w[0],w[1],w[4],w[0]]
    unfold executed
    cases p <;> decide +kernel
  · rfl

/-- Actual via-IR code cannot substitute for legacy capture timing. -/
theorem wrong_pipeline_capture : (observed .legacy []).mem 4 ≠ (observed .viaIR []).mem 4 := by
  unfold observed executed
  decide +kernel
/-- The other old alias survives the local rebind, rather than following it. -/
theorem wrong_alias : (observed .legacy []).mem 1 ≠ (observed .legacy []).mem 2 := by
  unfold observed executed
  decide +kernel

theorem saved_tail_wrong (p : Roadmap.Pipeline) (tail : List Word) :
    (observed p (w[77] :: tail)).stack ≠ w[78] :: tail := by
  intro same
  exact (by decide : (w[77] : Word) ≠ w[78]) (List.cons.inj same).1

theorem insufficient_frame (p : Roadmap.Pipeline) : ¬ (compiled p).Input 1 5 base σ machine := by
  intro h
  have room := h.2.1
  cases p <;> change 6 ≤ 5 at room <;> omega

end Solidity.Backend.Passes.EffectfulReferencePair.Controls
