import Solidity.Backend.Passes.ReferenceCallReadback
import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerRefTupleControls

/-! One accepted tuple call: a runtime argument may fail before the return
initializer/body, while another runtime input actually returns. No post-revert heap or public failure bytes are claimed. -/
namespace Solidity.Backend.Passes.ReferenceCallArgumentFailure
open Evm Evm.Memory Evm.Compiler
open Solidity.Backend.InternalFlow.RuntimeFrame
open V3CallProducerRef.Tuple.Controls (C A Γ F rs binders body)
abbrev caller := V3CallProducerRef.ArrayControls.caller (wmod 2)
abbrev base := V3CallProducerRef.ArrayControls.bases
abbrev machine := V3CallProducerRef.ArrayControls.machine (wmod 2)

def argumentRead : Val C Γ .uint := .readMem
  (.index .dyn (.var (.there .here) rfl) (.simple (.local .here)))
def args : Args C Γ [.mem A,.val .uint] :=
  .snocMemory (.snoc .nil .uint (.user "index") argumentRead)
    A (.user "input") (.var (.there .here) rfl)
def call : Stmt C Γ (rs ++ Γ) := .call "argumentFails" args (.rets binders) body

def expanded : Composition.Program 1 F (V3CallProducerRef.Tuple.expand args binders body) :=
  (Composition.compileProgram 1 F (V3CallProducerRef.Tuple.expand args binders body)).get (by decide +kernel)
def statement : Composition.Statement 1 F call :=
  V3CallProducerRef.Tuple.emit "argumentFails" args binders body expanded
def selected : Composition.Program 1 F (.cons call .nil) :=
  Composition.cons statement (Composition.nil 1 statement.checked.frag)

theorem argument_revert : argumentRead.evalT caller = .error .revert := by
  first
  | (solve | simp only)
  | (solve | decide)
  | (solve | omega)
  | (solve | rfl)
  | with_unfolding_all rfl

theorem source_revert : call.run caller = .error .revert := by
  first
  | (solve | simp only)
  | (solve | decide)
  | (solve | omega)
  | (solve | rfl)
  | with_unfolding_all rfl

theorem capacity : AllocationInput 1 64 (selected.checked.cost caller) caller base machine :=
  .inr ⟨by decide,wmod 130,(V3CallProducerRef.ArrayControls.initial (wmod 2)).2,by decide +kernel⟩
theorem member : V3CallProducerRef.admitted selected 16 16 1 64 caller base machine 20 :=
  ⟨(V3CallProducerRef.ArrayControls.initial (wmod 2)).1,by decide +kernel,by decide,by decide,
    by decide,by decide,by decide,by decide,rfl,capacity⟩
theorem entered : InterfaceV1.Entry (V3CallProducerRef.plan selected 16 16) 1 1 64 F caller base machine 20 :=
  V3CallProducerRef.coverage selected 16 16 1 64 caller base machine 20 member

theorem target_revert (suffix : List Instr) (tail : List Word) :
    run ((V3CallProducerRef.plan selected 16 16).code ++ suffix) (appendTail machine tail) = .revert :=
  ReferenceCallReadback.call_revert (body := body) (f := "argumentFails")
    (args := args) (ret := .rets binders) selected 16 16 entered source_revert suffix tail

theorem reached_cost : selected.checked.cost caller = 0 := by decide +kernel
theorem static_allocates : selected.checked.allocates = true := by decide +kernel
theorem wrong_positive_cost : selected.checked.cost caller ≠ 1 := by rw [reached_cost]; decide

theorem declaration_revert : (Stmt.declLocal .uint (.user "index") (some argumentRead)).run caller = .error .revert := by
  change TRun.declLocal .uint (some argumentRead) caller = _
  simp only [TRun.declLocal,argument_revert,bind,Except.bind]

def first : CompiledVal 1 F argumentRead := (compileVal 1 F argumentRead).get (by decide +kernel)
theorem emitted_first : ∃ rest : List Instr,
    selected.checked.code = (first.code ++ [.mstore 3]) ++ rest := by
  first
  | (solve | simp only)
  | (solve | decide)
  | (solve | omega)
  | (solve | rfl)
  | with_unfolding_all exact ⟨_,rfl⟩

abbrev goodCaller := V3CallProducerRef.ArrayControls.caller (wmod 0)
abbrev goodMachine := V3CallProducerRef.ArrayControls.machine (wmod 0)
private def successOut : TRes (Solidity.Out C goodCaller.H (rs ++ Γ)) → Option (Solidity.Out C goodCaller.H (rs ++ Γ))
  | .ok out => some out | _ => none
@[irreducible] def goodOutput : Solidity.Out C goodCaller.H (rs ++ Γ) :=
  (successOut (call.run goodCaller)).get (by decide +kernel)
theorem source_success : call.run goodCaller = .ok goodOutput := by
  have h : some goodOutput = successOut (call.run goodCaller) := by unfold goodOutput;exact Option.some_get _
  generalize call.run goodCaller = result at h ⊢
  cases result with
  | ok out => exact congrArg Except.ok (Option.some.inj h).symm
  | error halt => cases h

theorem positive_cost : selected.checked.cost goodCaller = 1 := by decide +kernel
theorem goodCapacity : AllocationInput 1 64 (selected.checked.cost goodCaller) goodCaller base goodMachine :=
  .inr ⟨by decide,wmod 130,(V3CallProducerRef.ArrayControls.initial (wmod 0)).2,by rw [positive_cost];decide⟩
theorem goodMember : V3CallProducerRef.admitted selected 16 16 1 64 goodCaller base goodMachine 20 :=
  ⟨(V3CallProducerRef.ArrayControls.initial (wmod 0)).1,by decide +kernel,by decide,by decide,
    by decide,by decide,by decide,by decide,rfl,goodCapacity⟩
theorem goodEntry : InterfaceV1.Entry (V3CallProducerRef.plan selected 16 16) 1 1 64 F goodCaller base goodMachine 20 :=
  V3CallProducerRef.coverage selected 16 16 1 64 goodCaller base goodMachine 20 goodMember

def scope : Ext Γ (rs ++ Γ) := Ext.append Γ rs
theorem form : V3CallProducerRef.Form Γ (.rets binders) scope := .tuple binders
theorem flags : InterfaceV1.NoAliasPromotion F selected.checked.frag scope := by
  intro R index live
  nomatch index

def successful_return := V3CallProducerRef.returns (body := body) (f := "argumentFails")
  (args := args) (ret := .rets binders) form selected 16 16 flags 1 64 goodCaller base goodMachine 20 goodEntry goodOutput source_success

end Solidity.Backend.Passes.ReferenceCallArgumentFailure
