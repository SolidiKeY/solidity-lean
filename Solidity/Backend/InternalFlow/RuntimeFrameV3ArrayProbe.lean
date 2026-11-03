import Solidity.Backend.InternalFlow.RuntimeFrameV3ParentStop

/-! Checked bounds-probe leaf for a recursive-failure consumer. It reuses the
published value compiler and its exact ValOutT semantics. No recursive-family
simulation, failed state, rollback or byte/world correspondence is asserted. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ArrayProbe
open Evm Evm.Memory RecursiveSource RecursiveActivation
abbrev A : RefTy := .array (.prim .uint)

def value {C : Contract} : Val C (Parameters A) .uint :=
 .readMem (.index .dyn (.var (.there .here) rfl) decrement)

def selected {C : Contract} (b : Nat) (F : Frag (Parameters A)) : CompiledVal b F (value (C:=C)) :=
 ⟨_,.read (.there .here) rfl decrement _ (compiled (C:=C) b F).cert⟩

theorem public_selection {C : Contract} (b : Nat) (F : Frag (Parameters A)) :
 Evm.Memory.compileVal b F (value (C:=C))=some (selected b F) := by rfl

def code {C : Contract} (b : Nat) (F : Frag (Parameters A)) : List Instr :=
 (selected (C:=C) b F).code ++ [.pop]

/-- The value before discarding the probe is the actual represented source
word, not an arbitrary push that would disappear under the final pop. -/
theorem read_success {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 {σ : State C (Parameters A)} {base : Nat → Fin W} {machine : Machine}
 (repr : StateRepr L b frame F σ base machine) (v : PrimTy.uint.Denote) (word : Word)
 (evaluated : value.evalT σ=.ok v) (prescribed : ReprV .uint v word) :
 run (selected (C:=C) b F).code machine=.ok (machine.push word) 0 := by
 have actual := (selected (C:=C) b F).cert.correct repr
 rcases actual with ⟨got,result,source,represented,executed⟩ | ⟨source,executed⟩
 · have same : got=v := Except.ok.inj (source.symm.trans evaluated)
   subst got
   rw [Restore.uint_unique represented prescribed] at executed
   exact executed
 · rw [evaluated] at source
   cases source

/-- Successful checked evaluation pushes one represented word; consuming that
word yields the EXACT original machine, not only a projected memory frame. -/
theorem success {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 {σ : State C (Parameters A)} {base : Nat → Fin W} {machine : Machine}
 (repr : StateRepr L b frame F σ base machine) (v : PrimTy.uint.Denote)
 (evaluated : value.evalT σ=.ok v) : run (code (C:=C) b F) machine=.ok machine 0 := by
 have actual := (selected (C:=C) b F).cert.correct repr
 rcases actual with ⟨got,word,source,represented,executed⟩ | ⟨source,executed⟩
 · exact (run_append_ok executed).trans (show run [.pop] (machine.push word)=.ok machine 0 from rfl)
 · rw [evaluated] at source
   cases source

/-- Actual bare source failure yields bare target REVERT, absorbing the real
pop and any continuation. Error-valued execution supplies no final State. -/
theorem failure_suffix {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 {σ : State C (Parameters A)} {base : Nat → Fin W} {machine : Machine}
 (repr : StateRepr L b frame F σ base machine)
 (evaluated : value.evalT σ=.error .revert) (suffix : List Instr) :
 run (code (C:=C) b F ++ suffix) machine=.revert := by
 have actual := (selected (C:=C) b F).cert.correct repr
 rcases actual with ⟨got,word,source,represented,executed⟩ | ⟨source,executed⟩
 · rw [evaluated] at source
   cases source
 · simpa only [code,List.append_assoc] using
     run_append_revert (c₂ := [.pop] ++ suffix) executed

namespace Checks
open CountdownWitness
abbrev F := CountdownWitness.F
abbrev input := AllocatorReturn.Checks.input
def bad := CountdownWitness.callee.setLocal .here (countValue 3 (by decide))
def badMachine := writeMachine input 3 w[3]

theorem bad_repr : StateRepr 1 2 16 F bad P.base badMachine :=
 AllocatorReturn.Checks.represented.setVal .here (countValue 3 (by decide)) w[3] (ReprV.uint_of rfl)
theorem bad_ownership : StructAllocatorRepr bad.heap P.base 16 ⟨22,by decide⟩ badMachine :=
 AllocatorReturn.Checks.ownership.localWrite 3 (by decide) (by decide) w[3]

theorem good_evaluated : value.evalT CountdownWitness.callee=.ok (P.uint 9 (by decide)) := by with_unfolding_all rfl
theorem bad_evaluated : value.evalT bad=.error .revert := by with_unfolding_all rfl

theorem good_read : run (selected (C:=P.C) 2 F).code input=.ok (input.push w[9]) 0 :=
 read_success AllocatorReturn.Checks.represented _ _ good_evaluated (ReprV.uint_of rfl)

theorem wrong_read : run (selected (C:=P.C) 2 F).code input≠.ok (input.push w[7]) 0 := by
 rw [good_read]
 intro bad
 have stacks := congrArg Machine.stack (Out.ok.inj bad).1
 have top : w[9]=w[7] := (List.cons.inj stacks).1
 have different : w[9]≠w[7] := by decide
 exact different top

theorem bad_not_exhausted : value.evalT bad≠.error .exhausted := by
 rw [bad_evaluated];intro mismatch;cases mismatch

theorem good_target : run (code (C:=P.C) 2 F) input=.ok input 0 :=
 success AllocatorReturn.Checks.represented _ good_evaluated

theorem bad_target (suffix : List Instr) : run (code (C:=P.C) 2 F ++ suffix) badMachine=.revert :=
 failure_suffix bad_repr bad_evaluated suffix

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.ArrayProbe

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ArrayProbe.failure_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ArrayProbe.failure_suffix
