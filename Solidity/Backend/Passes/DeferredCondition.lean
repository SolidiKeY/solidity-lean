import Solidity.Backend.Passes.MappedTail
import Solidity.Backend.Passes.CapturedValueStability

/-! Compile an existing deferred Boolean operand without reading its value
again after its private context is dropped. No alternate operand IR is added. -/
namespace Solidity.Backend.Passes.DeferredCondition
open Evm Evm.Memory Evm.Compiler
variable {C : Contract} {Γ : Ctx}

def expression (operand : DeferredSource.Operand C Γ (.prim .bool)) :
    Val C operand.tailCtx .bool :=
  match operand.value with | .val value => value

theorem expression_source (operand : DeferredSource.Operand C Γ (.prim .bool)) :
    operand.value = .val (expression operand) := by
  cases operand with
  | mk tail code value => cases value; rfl

/-- The Boolean was read in the actual reached private context, before dropping it. -/
theorem unpack (operand : DeferredSource.Operand C Γ (.prim .bool))
    (state : State C Γ) (out : Out C state.H Γ) (choice : Bool)
    (success : operand.run state = .ok (out,.prim choice)) :
    ∃ reached : Out C state.H operand.tailCtx,
      operand.code.run state = .ok reached ∧
      (expression operand).evalT reached.st = .ok choice ∧
      reached.st.drop operand.code.ext = out.st := by
  unfold DeferredSource.Operand.run at success
  rw [expression_source operand] at success
  simp only [Src.valueT] at success
  cases hc : operand.code.run state with
  | error err =>
    simp only [hc,bind,Except.bind] at success
    cases success
  | ok reached =>
    simp only [hc,bind,Except.bind] at success
    cases hv : (expression operand).evalT reached.st with
    | error err =>
      simp only [hv] at success
      cases success
    | ok value =>
      simp only [hv,pure,Except.pure] at success
      have fields := Except.ok.inj success
      have eqBool : value = choice := SVal.prim.inj (congrArg Prod.snd fields)
      have eqState : reached.st.drop operand.code.ext = out.st :=
        congrArg (fun o : Out C state.H Γ => o.st) (congrArg Prod.fst fields)
      exact ⟨reached,rfl,by rw [hv,eqBool],eqState⟩

/-- Compile the existing prefix and read its final Boolean before dropping
private locals. One actual map and machine are shared by every saved tail. -/
theorem shared {b L frame : Nat} {F : Frag Γ}
    (operand : DeferredSource.Operand C Γ (.prim .bool))
    (code : CompiledProg b F operand.code)
    (reader : CompiledVal b code.frag (expression operand))
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (input : (Compilation.memory code).Input L frame base state machine)
    (free : Evm.Prog.pays operand.code = false)
    (out : Out C state.H Γ) (choice : Bool)
    (success : operand.run state = .ok (out,.prim choice)) :
    ∃ (reached : Out C state.H operand.tailCtx) (canonical : Machine)
      (selected : Nat → Fin W) (word : Word),
      operand.code.run state = .ok reached ∧
      (expression operand).evalT reached.st = .ok choice ∧
      reached.st.drop operand.code.ext = out.st ∧
      canonical.stack = [] ∧ ReprV .bool choice word ∧ ∀ tail,
      (Compilation.memory code).Input L frame base state {machine with stack := tail} ∧
      run code.code {machine with stack := tail} = .ok {canonical with stack := tail} 0 ∧
      MappedOutput (.memory code) L frame base state {machine with stack := tail}
        reached.st {canonical with stack := tail} selected ∧
      StateRepr L b frame (code.frag.restrict Γ) out.st selected {canonical with stack := tail} ∧
      run reader.code {canonical with stack := tail} =
        .ok ({canonical with stack := tail}.push word) 0 ∧
      run (code.code ++ reader.code) {machine with stack := tail} =
        .ok ({canonical with stack := tail}.push word) 0 := by
  obtain ⟨reached,source,evaluated,dropped⟩ := unpack operand state out choice success
  obtain ⟨canonical,selected,_,empty,runs⟩ :=
    compilation_success_shared_mapped (.memory code) input free source
  have mapped := (runs []).2
  rw [code.cert.pushes_zero,Nat.add_zero] at mapped
  obtain ⟨word,repr,reads⟩ := CapturedValueStability.value_shared
    (expression operand) reader mapped.1 choice evaluated
  refine ⟨reached,canonical,selected,word,source,evaluated,dropped,empty,repr,?_⟩
  intro tail
  have full := (runs tail).2
  rw [code.cert.pushes_zero,Nat.add_zero] at full
  have caller := full.1.drop operand.code.ext
  rw [dropped] at caller
  refine ⟨compilation_input_stack (.memory code) input tail,(runs tail).1,full,caller,?_,?_⟩
  · exact reads tail
  · have executed : run code.code {machine with stack := tail} =
        .ok {canonical with stack := tail} 0 := (runs tail).1
    rw [run_append_ok executed]
    exact reads tail

end Solidity.Backend.Passes.DeferredCondition

/-- info: 'Solidity.Backend.Passes.DeferredCondition.expression_source' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredCondition.expression_source

/-- info: 'Solidity.Backend.Passes.DeferredCondition.unpack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredCondition.unpack

/-- info: 'Solidity.Backend.Passes.DeferredCondition.shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredCondition.shared
