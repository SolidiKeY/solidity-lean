import Solidity.Backend.Passes.SourceNarrowingValue
import Solidity.Backend.Passes.PositiveAllocationFailure
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.Passes.SourceNarrowingValue.Controls
open Evm Evm.Memory Solidity.Lowering.V07 Solidity.Lowering.V07.UnsignedNarrowing
open Source.SemanticsExamples (E0 G0 F0 s0)
abbrev C := PositiveAllocationFailure.C
abbrev T : Source.IntTy := ty 8 (by decide)
abbrev Γ : Ctx := [.val .uint,.val .uint,.val .uint]
abbrev srcΓ : Source.RCtx := [.int T,.int T]
abbrev F := Frag.init Γ
def source : Source.EMState E0 srcΓ :=
  (.cons (.int 0 (by decide)) (.cons (.int 1 (by decide)) .nil),s0)
def target : State C Γ :=
  (PositiveAllocationFailure.before.push (t := .val .uint) (CompileExamples.uint 1 (by decide))).push
    (t := .val .uint) (CompileExamples.uint 0 (by decide))
def si (k : Bool) : Source.Idx srcΓ (.int T) := if k then .there .here else .here
def ti (k : Bool) : Idx Γ (.val .uint) := if k then .there .here else .here

theorem family : IntegerLocalFamily T si ti source.1 target.env := by
  constructor
  · intro k; cases k <;> rfl
  · intro k l; cases k <;> cases l <;> decide

def expression : Val C Γ .uint := subValue 8 (.simple (.local .here)) (.simple (.local (.there .here)))
def compiled : CompiledVal 1 F expression :=
  (Memory.compileVal 1 F expression).get (by decide +kernel)
def machine : Machine := writeMachine (writeMachine
  (PositiveAllocationFailure.machine (wmod 64)) 2 w[1]) 3 w[0]

theorem represented : StateRepr 1 1 16 F target PositiveAllocationFailure.base machine := by
  have h := (PositiveAllocationFailure.initial (wmod 64) (by decide)).1
  exact (h.consVal (CompileExamples.uint 1 (by decide)) w[1] (ReprV.uint_of rfl) (by decide)).consVal
    (CompileExamples.uint 0 (by decide)) w[0] (ReprV.uint_of rfl) (by decide)

def application (p : Roadmap.Pipeline) (fuel : Nat) :=
  execution (G0 p) F0 fuel source target 8 (by decide) si ti family false true
    0 1 (by decide) (by decide) rfl rfl compiled represented

theorem actual_target (tail : List Word) :
    run compiled.code {machine with stack := tail} = .ok ({machine with stack := tail}.push w[255]) 0 := by
  obtain ⟨_,_,_,word,repr,runs⟩ := application .legacy 0
  have same : word = w[255] := Backend.InternalFlow.RuntimeFrame.Restored.value_unique repr (ReprV.uint_of rfl)
  subst word
  exact runs tail

def checked : Val C Γ .uint := .binop .sub rfl rfl (.simple (.local .here)) (.simple (.local (.there .here)))
def checkedCode : CompiledVal 1 F checked := (Memory.compileVal 1 F checked).get (by decide +kernel)
theorem checked_guard (tail : List Word) : run checkedCode.code {machine with stack := tail} = .revert :=
  (value_revert_iff checkedCode represented tail).mpr rfl

def cells : List Nat := [0,1,2,3,8,9]
theorem complete_observations (tail : List Word) :
    (cells.map ({machine with stack := tail}.push w[255]).mem,
      ({machine with stack := tail}.push w[255]).stack) =
      ([w[64],w[0],w[1],w[0],w[10],w[99]],w[255] :: tail) := rfl

theorem wrong_width : (w[255] : Word) ≠ w[256] := by decide
theorem unmasked_word_wrong : (w[255] : Word) ≠ .val (wmod (W-1)) := by decide +kernel

theorem wrong_operand_order :
    (subValue 8 (.simple (.local (.there .here))) (.simple (.local .here)) : Val C Γ .uint).evalT target =
      .ok (CompileExamples.uint 1 (by decide)) :=
  sub_value_run target 8 (by decide) _ _ 1 0 (by decide) (by decide) rfl rfl

theorem saved_tail_wrong (tail : List Word) :
    ({machine with stack := w[77] :: tail}.push w[255]).stack ≠ w[255] :: w[78] :: tail := by
  intro same
  have wrong := (List.cons.inj (List.cons.inj same).2).1
  exact (by decide : (w[77] : Word) ≠ w[78]) wrong

end Solidity.Backend.Passes.SourceNarrowingValue.Controls
