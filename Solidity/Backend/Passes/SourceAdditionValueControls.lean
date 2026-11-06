import Solidity.Backend.Passes.SourceAdditionValue
import Solidity.Backend.Passes.PositiveAllocationFailure
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.Passes.SourceAdditionValue.Controls
open Evm Evm.Memory Solidity.Lowering.V07 Solidity.Lowering.V07.UnsignedNarrowing
open Solidity.Lowering.V07.UnsignedAddition
open Source.SemanticsExamples (E0 G0 F0 s0)
abbrev C := PositiveAllocationFailure.C
abbrev T : Source.IntTy := ty 8 (by decide)
abbrev Γ : Ctx := [.val .uint,.val .uint,.val .uint]
abbrev srcΓ : Source.RCtx := [.int T,.int T]
abbrev F := Frag.init Γ
def source : Source.EMState E0 srcΓ :=
  (.cons (.int 255 (by decide)) (.cons (.int 1 (by decide)) .nil),s0)
def target : State C Γ :=
  (PositiveAllocationFailure.before.push (t := .val .uint) (CompileExamples.uint 1 (by decide))).push
    (t := .val .uint) (CompileExamples.uint 255 (by decide))
def si (k : Bool) : Source.Idx srcΓ (.int T) := if k then .there .here else .here
def ti (k : Bool) : Idx Γ (.val .uint) := if k then .there .here else .here

theorem family : IntegerLocalFamily T si ti source.1 target.env := by
  constructor
  · intro k; cases k <;> rfl
  · intro k l; cases k <;> cases l <;> decide

def expression : Val C Γ .uint := addValue 8 (.simple (.local .here)) (.simple (.local (.there .here)))
def compiled : CompiledVal 1 F expression :=
  (Memory.compileVal 1 F expression).get (by decide +kernel)
def machine : Machine := writeMachine (writeMachine
  (PositiveAllocationFailure.machine (wmod 64)) 2 w[1]) 3 w[255]

theorem represented : StateRepr 1 1 16 F target PositiveAllocationFailure.base machine := by
  have h := (PositiveAllocationFailure.initial (wmod 64) (by decide)).1
  exact (h.consVal (CompileExamples.uint 1 (by decide)) w[1] (ReprV.uint_of rfl) (by decide)).consVal
    (CompileExamples.uint 255 (by decide)) w[255] (ReprV.uint_of rfl) (by decide)

def application (p : Roadmap.Pipeline) (fuel : Nat) :=
  execution (G0 p) F0 fuel source target 8 (by decide) si ti family false true
    255 1 (by decide) (by decide) rfl rfl compiled represented

theorem actual_target (tail : List Word) :
    run compiled.code {machine with stack := tail} = .ok ({machine with stack := tail}.push w[0]) 0 := by
  obtain ⟨_,_,_,word,repr,runs⟩ := application .legacy 0
  have same : word = w[0] := Backend.InternalFlow.RuntimeFrame.Restored.value_unique repr (ReprV.uint_of rfl)
  subst word
  exact runs tail

def cells : List Nat := [0,1,2,3,8,9]
theorem complete_observations (tail : List Word) :
    (cells.map ({machine with stack := tail}.push w[0]).mem,
      ({machine with stack := tail}.push w[0]).stack) =
      ([w[64],w[0],w[1],w[255],w[10],w[99]],w[0] :: tail) := rfl

theorem unmasked_wrong : (w[0] : Word) ≠ w[256] := by decide

theorem saved_tail_wrong (tail : List Word) :
    ({machine with stack := w[77] :: tail}.push w[0]).stack ≠ w[0] :: w[78] :: tail := by
  intro same
  have wrong := (List.cons.inj (List.cons.inj same).2).1
  exact (by decide : (w[77] : Word) ≠ w[78]) wrong

def unmasked : Val C Γ .uint := .binop .addW rfl rfl
  (.simple (.local .here)) (.simple (.local (.there .here)))
def unmaskedCode : CompiledVal 1 F unmasked :=
  (Memory.compileVal 1 F unmasked).get (by decide +kernel)

theorem actual_unmasked (tail : List Word) :
    run unmaskedCode.code {machine with stack := tail} =
      .ok ({machine with stack := tail}.push w[256]) 0 := by
  obtain ⟨word,repr,runs⟩ := value_success_tail unmaskedCode represented
    (value := CompileExamples.uint 256 (by decide)) (by rfl) tail
  have same : word = w[256] := Backend.InternalFlow.RuntimeFrame.Restored.value_unique repr (ReprV.uint_of rfl)
  subst word
  exact runs

def nonzeroTarget : State C Γ :=
  (PositiveAllocationFailure.before.push (t := .val .uint) (CompileExamples.uint 1 (by decide))).push
    (t := .val .uint) (CompileExamples.uint 1 (by decide))
def nonzeroMachine : Machine := writeMachine (writeMachine
  (PositiveAllocationFailure.machine (wmod 64)) 2 w[1]) 3 w[1]
theorem nonzeroRepresented : StateRepr 1 1 16 F nonzeroTarget PositiveAllocationFailure.base nonzeroMachine := by
  have h := (PositiveAllocationFailure.initial (wmod 64) (by decide)).1
  exact (h.consVal (CompileExamples.uint 1 (by decide)) w[1] (ReprV.uint_of rfl) (by decide)).consVal
    (CompileExamples.uint 1 (by decide)) w[1] (ReprV.uint_of rfl) (by decide)
theorem actual_nonzero (tail : List Word) :
    run compiled.code {nonzeroMachine with stack := tail} =
      .ok ({nonzeroMachine with stack := tail}.push w[2]) 0 := by
  obtain ⟨word,repr,runs⟩ := value_success_tail compiled nonzeroRepresented
    (value := CompileExamples.uint 2 (by decide)) (by rfl) tail
  have same : word = w[2] := Backend.InternalFlow.RuntimeFrame.Restored.value_unique repr (ReprV.uint_of rfl)
  subst word
  exact runs

end Solidity.Backend.Passes.SourceAdditionValue.Controls
