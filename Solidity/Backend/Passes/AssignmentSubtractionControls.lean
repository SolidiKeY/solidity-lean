import Solidity.Backend.Passes.AssignmentSubtractionPass
import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerRefArrayControls
import Solidity.Backend.InternalFlow.RuntimeFrameRestoredRepresentation
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.Passes.AssignmentSubtractionPass.Controls
open Evm Evm.Memory Evm.Compiler Solidity.Lowering.V07
open Solidity.Backend.InternalFlow.RuntimeFrame
open Source.SemanticsExamples
abbrev C := V3CallProducerRef.ArrayControls.C
abbrev A := V3CallProducerRef.ArrayControls.A
abbrev Γ : Ctx := [.val .uint,.val .uint,.mem A]
def F : Frag Γ := V3CallProducerRef.ArrayControls.F.push (.val .uint) .ok
def target : State C Γ := (V3CallProducerRef.ArrayControls.caller (wmod 7)).push
  (t := .val .uint) (integerValue .u8 9 (by decide))
abbrev bases := V3CallProducerRef.ArrayControls.bases
def machine := writeMachine (V3CallProducerRef.ArrayControls.machine (wmod 7)) 3 w[9]
abbrev i : Idx Γ (.val .uint) := .there .here
abbrev a : Idx Γ (.val .uint) := .here

def source : Source.EMState E0 [.int .u8,.int .u8] :=
  (.cons (.int 9 (by decide)) (.cons (.int 7 (by decide)) .nil),s0)

theorem initial : StateRepr 1 1 64 F target bases machine :=
  (V3CallProducerRef.ArrayControls.initial (wmod 7)).1.consVal
    (integerValue .u8 9 (by decide)) w[9] (ReprV.uint_of rfl) (by decide)
def compiled (p : Roadmap.Pipeline) : Memory.CompiledProg 1 F (assignReadPrefix (C := C) p i a) :=
  (Memory.compileProg 1 F (assignReadPrefix p i a)).get (by cases p <;> decide +kernel)
def operand (p : Roadmap.Pipeline) : CompiledVal 1 (compiled p).frag (value (C := C) (Γ := Γ) p .u8) :=
  (compileVal 1 (compiled p).frag (value p .u8)).get (by cases p <;> decide +kernel)
theorem input (p : Roadmap.Pipeline) : (Compilation.memory (compiled p)).Input 1 64 bases target machine :=
  ⟨initial,by cases p <;> decide +kernel,Or.inl (by cases p <;> rfl)⟩

def application (p : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) := execution
  (G0 p) {F0 with checked := checked} fuel source target .u8 (.there .here) .here i a
  9 7 (by decide) (by decide) rfl rfl rfl rfl (by cases p <;> decide)
  (compiled p) (operand p) (input p)

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

def resultWord (p : Roadmap.Pipeline) : Word := if p = .legacy then w[2] else w[0]
def code (p : Roadmap.Pipeline) := (compiled p).code ++ (operand p).code

theorem emitted (p : Roadmap.Pipeline) (tail : List Word) :
    run (code p) {machine with stack := tail} = .ok ({after p with stack := tail}.push (resultWord p)) 0 := by
  obtain ⟨_,_,canonical,addresses,word,repr,empty,runs⟩ := application p 0 false
  have ce : {canonical with stack := []} = canonical := by cases canonical;cases empty;rfl
  have same : canonical = after p := by
    have h := (Evm.Out.ok.inj ((runs []).1.symm.trans (prefix_run p))).1
    exact ce.symm.trans h
  subst canonical
  have correct : word = resultWord p := by
    cases p <;> exact Restored.value_unique repr (ReprV.uint_of rfl)
  subst word
  exact (runs tail).2.2.2

theorem source_execution (p : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) :
    (Source.evalE (G0 p) {F0 with checked := checked} (fuel+4)
      (.binary .sub (.assign (.local (.there .here)) (.local .here)) (.local (.there .here)))).run source =
      (.ok (.val (.int (if p = .legacy then 2 else 0) (by cases p <;> decide))),
        (source.1.set (.there .here) (.int 9 (by decide)),source.2)) := by
  cases p <;> exact (application _ fuel checked).1

def cells : List Nat := [0,1,2,3,4,5,16,63,128,129,130]
theorem complete_observations (p : Roadmap.Pipeline) (tail : List Word) :
    (cells.map (after p).mem,({after p with stack := w[77] :: tail}.push (resultWord p)).stack) =
      ([w[130],w[128],w[9],w[9],(if p = .legacy then w[7] else w[9]),w[9],w[20],w[99],w[1],w[0],w[0]],
        resultWord p :: w[77] :: tail) := by
  apply Prod.ext
  · change cells.map (after p).mem =
      [w[130],w[128],w[9],w[9],(if p = .legacy then w[7] else w[9]),w[9],w[20],w[99],w[1],w[0],w[0]]
    cases p <;> unfold cells after <;> decide +kernel
  · rfl

theorem different_pipelines : resultWord .legacy ≠ resultWord .viaIR := by decide
theorem stale_rhs_refused (tail : List Word) :
    run (code .viaIR) {machine with stack := tail} ≠ .ok ({after .viaIR with stack := tail}.push w[2]) 0 := by
  intro h
  rw [emitted] at h
  have stack := congrArg Machine.stack (Evm.Out.ok.inj h).1
  have wrong : w[0] = w[2] := (List.cons.inj stack).1
  exact (by decide : w[0] ≠ w[2]) wrong

theorem short_frame_refused (p : Roadmap.Pipeline) :
    ¬ (Compilation.memory (compiled p)).Input 1 5 bases target machine := by
  intro h
  have bound := h.2.1
  cases p <;> change 6 ≤ 5 at bound <;> omega

def reversed : CompiledVal 1 (compiled .legacy).frag (value (C := C) (Γ := Γ) .viaIR .u8) :=
  (compileVal 1 (compiled .legacy).frag (value .viaIR .u8)).get (by decide +kernel)
theorem reversed_source :
    (value (C := C) (Γ := Γ) .viaIR .u8).evalT
      (reached .legacy target .u8 i 9 7 (by decide) (by decide)) = .error .revert := by
  with_unfolding_all rfl

theorem wrong_order_reverts (tail : List Word) :
    run ((compiled .legacy).code ++ reversed.code) {machine with stack := tail} = .revert := by
  obtain ⟨_,_,canonical,addresses,word,repr,empty,runs⟩ := application .legacy 0 false
  have failed := (value_revert_iff reversed (runs []).2.1.1 tail).mpr reversed_source
  exact (run_append_ok (c₂ := reversed.code) (runs tail).1).trans failed

theorem corrupted_saved_tail (tail : List Word) :
    run (code .legacy) {machine with stack := w[77] :: tail} ≠
      .ok ({after .legacy with stack := w[88] :: tail}.push w[2]) 0 := by
  intro h
  rw [emitted] at h
  have stack := congrArg Machine.stack (Evm.Out.ok.inj h).1
  have wrong : w[77] = w[88] := (List.cons.inj (List.cons.inj stack).2).1
  exact (by decide : w[77] ≠ w[88]) wrong

end Solidity.Backend.Passes.AssignmentSubtractionPass.Controls
