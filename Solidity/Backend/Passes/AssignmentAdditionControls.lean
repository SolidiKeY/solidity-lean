import Solidity.Backend.Passes.AssignmentAdditionPass
import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerRefArrayControls
import Solidity.Backend.InternalFlow.RuntimeFrameRestoredRepresentation
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.Passes.AssignmentAdditionPass.Controls
open Evm Evm.Memory Evm.Compiler Solidity.Lowering.V07
open Solidity.Backend.InternalFlow.RuntimeFrame
open Solidity.Lowering.V07.UnsignedNarrowing
open Source.SemanticsExamples
abbrev C := V3CallProducerRef.ArrayControls.C
abbrev A := V3CallProducerRef.ArrayControls.A
abbrev Γ : Ctx := [.val .uint,.val .uint,.mem A]
def F : Frag Γ := V3CallProducerRef.ArrayControls.F.push (.val .uint) .ok
def target : State C Γ := (V3CallProducerRef.ArrayControls.caller (wmod 1)).push
  (t := .val .uint) (integerValue .u8 255 (by decide))
abbrev bases := V3CallProducerRef.ArrayControls.bases
def machine := writeMachine (V3CallProducerRef.ArrayControls.machine (wmod 1)) 3 w[255]
abbrev i : Idx Γ (.val .uint) := .there .here
abbrev a : Idx Γ (.val .uint) := .here

def source : Source.EMState E0 [.int .u8,.int .u8] :=
  (.cons (.int 255 (by decide)) (.cons (.int 1 (by decide)) .nil),s0)

theorem initial : StateRepr 1 1 64 F target bases machine :=
  (V3CallProducerRef.ArrayControls.initial (wmod 1)).1.consVal
    (integerValue .u8 255 (by decide)) w[255] (ReprV.uint_of rfl) (by decide)
def compiled (p : Roadmap.Pipeline) : Memory.CompiledProg 1 F (assignReadPrefix (C := C) p i a) :=
  (Memory.compileProg 1 F (assignReadPrefix p i a)).get (by cases p <;> decide +kernel)
def operand (p : Roadmap.Pipeline) : CompiledVal 1 (compiled p).frag (value (C := C) (Γ := Γ) p 8) :=
  (compileVal 1 (compiled p).frag (value p 8)).get (by cases p <;> decide +kernel)
theorem input (p : Roadmap.Pipeline) : (Compilation.memory (compiled p)).Input 1 64 bases target machine :=
  ⟨initial,by cases p <;> decide +kernel,Or.inl (by cases p <;> rfl)⟩

def si (k : Bool) : Source.Idx [.int .u8,.int .u8] (.int .u8) := if k then .there .here else .here
def ti (k : Bool) : Idx Γ (.val .uint) := if k then i else a
theorem family : IntegerLocalFamily (ty 8 (by decide)) si ti source.1 target.env := by
  constructor
  · intro k; cases k <;> rfl
  · intro k l; cases k <;> cases l <;> decide

def application (p : Roadmap.Pipeline) (fuel : Nat) := execution
  (G0 p) F0 fuel source target 8 (by decide) si ti family true false
  255 1 (by decide) (by decide) rfl rfl (compiled p) (operand p) (input p)

private def successMachine : Evm.Out → Option Machine
  | .ok m 0 => some m | _ => none
@[irreducible] def after (p : Roadmap.Pipeline) : Machine :=
  (successMachine (run (compiled p).code {machine with stack := []})).get (by cases p <;> decide +kernel)
theorem prefix_run (p : Roadmap.Pipeline) :
    run (compiled p).code {machine with stack := []} = .ok (after p) 0 := by
  have h : some (after p) = successMachine (run (compiled p).code {machine with stack := []}) := by
    unfold after
    exact Option.some_get _
  generalize run (compiled p).code {machine with stack := []} = result at h ⊢
  cases result with
  | ok m skip => cases skip with
    | zero => exact congrArg (fun m => Evm.Out.ok m 0) (Option.some.inj h).symm
    | succ n => cases h
  | revert => cases h
  | fault => cases h

def resultWord (p : Roadmap.Pipeline) : Word := if p = .legacy then w[0] else w[254]
def code (p : Roadmap.Pipeline) := (compiled p).code ++ (operand p).code

theorem emitted (p : Roadmap.Pipeline) (tail : List Word) :
    run (code p) {machine with stack := tail} = .ok ({after p with stack := tail}.push (resultWord p)) 0 := by
  obtain ⟨_,_,_,canonical,addresses,word,repr,empty,runs⟩ := application p 0
  have ce : {canonical with stack := []} = canonical := by cases canonical;cases empty;rfl
  have same : canonical = after p := by
    have h := (Evm.Out.ok.inj ((runs []).1.symm.trans (prefix_run p))).1
    exact ce.symm.trans h
  subst canonical
  have correct : word = resultWord p := by
    cases p <;> exact Restored.value_unique repr (ReprV.uint_of rfl)
  subst word
  exact (runs tail).2.2.2

theorem source_execution (p : Roadmap.Pipeline) (fuel : Nat)  :
    (Source.evalE (G0 p) {F0 with checked := false} (fuel+4)
      (.binary .add (.assign (.local (.there .here)) (.local .here)) (.local (.there .here)))).run source =
      (.ok (.val (.int (if p = .legacy then 0 else 254) (by cases p <;> decide))),
        (source.1.set (.there .here) (.int 255 (by decide)),source.2)) := by
  cases p <;> exact (application _ fuel).1

def cells : List Nat := [0,1,2,3,4,5,16,63,128,129,130]
theorem complete_observations (p : Roadmap.Pipeline) (tail : List Word) :
    (cells.map (after p).mem,({after p with stack := w[77] :: tail}.push (resultWord p)).stack) =
      ([w[130],w[128],w[255],w[255],(if p = .legacy then w[1] else w[255]),w[255],w[20],w[99],w[1],w[0],w[0]],
        resultWord p :: w[77] :: tail) := by
  apply Prod.ext
  · change cells.map (after p).mem =
      [w[130],w[128],w[255],w[255],(if p = .legacy then w[1] else w[255]),w[255],w[20],w[99],w[1],w[0],w[0]]
    cases p <;> unfold cells after <;> decide +kernel
  · rfl

theorem different_pipelines : resultWord .legacy ≠ resultWord .viaIR := by decide
theorem stale_rhs_refused (tail : List Word) :
    run (code .viaIR) {machine with stack := tail} ≠ .ok ({after .viaIR with stack := tail}.push w[0]) 0 := by
  intro h
  rw [emitted] at h
  have stack := congrArg Machine.stack (Evm.Out.ok.inj h).1
  have wrong : w[254] = w[0] := (List.cons.inj stack).1
  exact (by decide : w[254] ≠ w[0]) wrong

theorem short_frame_refused (p : Roadmap.Pipeline) :
    ¬ (Compilation.memory (compiled p)).Input 1 5 bases target machine := by
  intro h
  have bound := h.2.1
  cases p <;> change 6 ≤ 5 at bound <;> omega

theorem corrupted_saved_tail (tail : List Word) :
    run (code .legacy) {machine with stack := w[77] :: tail} ≠
      .ok ({after .legacy with stack := w[88] :: tail}.push w[0]) 0 := by
  intro h
  rw [emitted] at h
  have stack := congrArg Machine.stack (Evm.Out.ok.inj h).1
  have wrong : w[77] = w[88] := (List.cons.inj (List.cons.inj stack).2).1
  exact (by decide : w[77] ≠ w[88]) wrong

end Solidity.Backend.Passes.AssignmentAdditionPass.Controls
