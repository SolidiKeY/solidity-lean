import tests.«internal-flow».PublishedMemoryCalls
import Solidity.Backend.InternalFlow.ArgumentFailureTarget
namespace Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks
open Evm Evm.Memory
abbrev C := PublishedDirectCalls.Checks.C
abbrev A := PublishedDirectCalls.Checks.A
abbrev Caller := PublishedDirectCalls.Checks.Caller
abbrev Params : Ctx := [.val .uint,.val .uint,.mem A]
abbrev Input : Ctx := .mem A :: Params
abbrev Final : Ctx := .mem A :: Caller

def readArgs : Args C Caller [.val .uint,.mem A] :=
 .snoc (.snocMemory .nil A (.user "old") (.var .here rfl)) .uint (.user "marker")
   (.simple (.local (.there (.there .here))))
def readAt (index : Int) (fits : PrimTy.uint.inRange index = true) : Val C Caller .uint :=
 .readMem (.index .dyn (.var .here rfl) (.simple (.lit index fits)))
def badArgs : Args C Caller Params := .snoc readArgs .uint (.user "last") (readAt 2 rfl)
def goodArgs : Args C Caller Params := .snoc readArgs .uint (.user "last") (readAt 1 rfl)
def ret : CallRet Caller [.mem A] Final := .mem A (.user "result") rfl rfl
def body : Prog C Input (.mem A :: Input) :=
 .cons (.declMem A (.user "private") (some (.newArr (.lit 2 rfl) rfl)) rfl rfl)
  (.cons (.rebindMem (.there .here) (.alias (.var .here rfl))) .nil)
def expanded (args : Args C Caller Params) := Calls.expandMem args A (.user "result") rfl rfl body

def badExpanded : Calls.Program 1 PublishedDirectCalls.Checks.prefixProducer.frag (expanded badArgs) :=
 (Calls.compile 1 PublishedDirectCalls.Checks.prefixProducer.frag (expanded badArgs)).get (by decide +kernel)
def goodExpanded : Calls.Program 1 PublishedDirectCalls.Checks.prefixProducer.frag (expanded goodArgs) :=
 (Calls.compile 1 PublishedDirectCalls.Checks.prefixProducer.frag (expanded goodArgs)).get (by decide +kernel)
def badProducer : Calls.Statement 1 PublishedDirectCalls.Checks.prefixProducer.frag (.call "arguments" badArgs ret body) :=
 Calls.memoryReturn "arguments" badArgs A (.user "result") rfl rfl body badExpanded
def goodProducer : Calls.Statement 1 PublishedDirectCalls.Checks.prefixProducer.frag (.call "arguments" goodArgs ret body) :=
 Calls.memoryReturn "arguments" goodArgs A (.user "result") rfl rfl body goodExpanded
attribute [irreducible] badExpanded goodExpanded badProducer goodProducer

private theorem actual_get {α : Type} (r : TRes α) (h : r.toOption.isSome = true) :
 r = .ok (r.toOption.get h) := by cases r <;> first | rfl | cases h

private theorem actual_error {α : Type} (r : TRes α) (h : r.halt? = some THalt.revert) :
 r = .error .revert := by
 cases r with
 | ok value => cases h
 | error halt => exact congrArg Except.error (Option.some.inj h)

theorem prefix_execution : PublishedDirectCalls.Checks.callerPrefix.run PublishedDirectCalls.Checks.initial =
 .ok PublishedDirectCalls.Checks.caller := actual_get _ (by decide +kernel)
def goodValues : TEnv C PublishedDirectCalls.Checks.caller.st.H Params :=
 (goodArgs.evalT PublishedDirectCalls.Checks.caller.st).toOption.get (by decide +kernel)
theorem good_arguments : goodArgs.evalT PublishedDirectCalls.Checks.caller.st = .ok goodValues :=
 actual_get _ (by decide +kernel)
theorem failed_arguments : badArgs.evalT PublishedDirectCalls.Checks.caller.st = .error .revert :=
 actual_error _ (by decide +kernel)

def entry : Solidity.Out C PublishedDirectCalls.Checks.caller.st.H Input :=
 ret.enterT (PublishedDirectCalls.Checks.caller.st.withEnv goodValues)
def bodyOutput : Solidity.Out C entry.st.H (.mem A :: Input) :=
 (body.runR entry.st).toOption.get (by decide +kernel)
def exported : Solidity.Out C PublishedDirectCalls.Checks.caller.st.H Final :=
 ⟨bodyOutput.st.withEnv (ret.leaveT
  (TEnv.wk (entry.ext.trans bodyOutput.ext) Caller PublishedDirectCalls.Checks.caller.st.env)
  (TEnv.take [.mem A] (TEnv.drop body.ext bodyOutput.st.env))),entry.ext.trans bodyOutput.ext⟩
theorem body_execution : body.runR entry.st = .ok bodyOutput := actual_get _ (by decide +kernel)
theorem good_call : (.call "arguments" goodArgs ret body : Stmt C Caller Final).run PublishedDirectCalls.Checks.caller.st = .ok exported :=
 InternalFlow.call_return goodArgs ret body.ext body.runR _ goodValues good_arguments bodyOutput body_execution

theorem bad_call : (.call "arguments" badArgs ret body : Stmt C Caller Final).run PublishedDirectCalls.Checks.caller.st = .error .revert :=
 CallArgumentPrefix.call_failure badArgs ret body.ext body.runR _ .revert failed_arguments

theorem costs : PublishedDirectCalls.Checks.prefixProducer.cost PublishedDirectCalls.Checks.initial = 3 ∧
 badProducer.cost PublishedDirectCalls.Checks.caller.st = 0 ∧ goodProducer.cost PublishedDirectCalls.Checks.caller.st = 4 := by decide +kernel

theorem frame_rooms : 1 + PublishedDirectCalls.Checks.prefixProducer.need ≤ 128 ∧
 1 + badProducer.need ≤ 128 ∧ 1 + goodProducer.need ≤ 128 := by decide +kernel

theorem observations :
 (PublishedDirectCalls.Checks.caller.st.H.length,entry.st.H.length,bodyOutput.st.H.length,
  goodValues.1.1,goodValues.2.1.1,goodValues.2.2.1.map HRef.id,
  exported.st.env.1.map HRef.id,exported.st.env.2.1.map HRef.id,
  exported.st.env.2.2.1.map HRef.id,exported.st.env.2.2.2.1.1) =
 (1,2,3,11,42,some 0,some 2,some 0,some 0,42) := by
 simp only [Prod.mk.injEq]
 refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> decide +kernel

def prefixValues : TEnv C PublishedDirectCalls.Checks.caller.st.H [.val .uint,.mem A] :=
 (readArgs.evalT PublishedDirectCalls.Checks.caller.st).toOption.get (by decide +kernel)
theorem argument_prefix : readArgs.evalT PublishedDirectCalls.Checks.caller.st = .ok prefixValues :=
 actual_get _ (by decide +kernel)
theorem prefix_order : (prefixValues.1.1,prefixValues.2.1.map HRef.id) = (42,some 0) := by decide +kernel
theorem bad_read : (readAt 2 rfl).evalT PublishedDirectCalls.Checks.caller.st = .error .revert :=
 actual_error _ (by decide +kernel)

def finalRead (i : Idx Final (.mem A)) (n : Int) (fits : PrimTy.uint.inRange n = true) : Val C Final .uint :=
 .readMem (.index .dyn (.var i rfl) (.simple (.lit n fits)))
def lengthAt {Γ : Ctx} (i : Idx Γ (.mem A)) : Val C Γ .uint := .mlen (.var i rfl) rfl

theorem source_lengths :
 [((lengthAt (.here : Idx Caller (.mem A))).evalT PublishedDirectCalls.Checks.caller.st).toOption.map (fun v => v.1),
  ((lengthAt (.here : Idx Input (.mem A))).evalT entry.st).toOption.map (fun v => v.1),
  ((lengthAt (.here : Idx Final (.mem A))).evalT exported.st).toOption.map (fun v => v.1),
  ((lengthAt (.there .here : Idx Final (.mem A))).evalT exported.st).toOption.map (fun v => v.1)] =
 [some 2,some 0,some 2,some 2] := by decide +kernel

theorem source_contents :
 [((readAt 0 rfl).evalT PublishedDirectCalls.Checks.caller.st).toOption.map (fun v => v.1),
  ((readAt 1 rfl).evalT PublishedDirectCalls.Checks.caller.st).toOption.map (fun v => v.1),
  ((finalRead (.there .here) 0 rfl).evalT exported.st).toOption.map (fun v => v.1),
  ((finalRead (.there .here) 1 rfl).evalT exported.st).toOption.map (fun v => v.1),
  ((finalRead (.there (.there .here)) 0 rfl).evalT exported.st).toOption.map (fun v => v.1),
  ((finalRead (.there (.there .here)) 1 rfl).evalT exported.st).toOption.map (fun v => v.1),
  ((finalRead .here 0 rfl).evalT exported.st).toOption.map (fun v => v.1),
  ((finalRead .here 1 rfl).evalT exported.st).toOption.map (fun v => v.1)] =
 [some 7,some 11,some 7,some 11,some 7,some 11,some 0,some 0] := by decide +kernel

theorem wrong_argument_order : (goodValues.1.1,goodValues.2.1.1) ≠ (42,11) := by decide +kernel
theorem wrong_return_alias : exported.st.env.1.map HRef.id ≠ some 0 := by decide +kernel
theorem wrong_default_escape : exported.st.env.1.map HRef.id ≠ some 1 := by decide +kernel

theorem public_admission :
 (Calls.compile 1 PublishedDirectCalls.Checks.prefixProducer.frag
  (.cons (.call "arguments" badArgs ret body) .nil)).isSome = true ∧
 (Calls.compile 1 PublishedDirectCalls.Checks.prefixProducer.frag
  (.cons (.call "arguments" goodArgs ret body) .nil)).isSome = true := by decide +kernel


/-- Existing typed argument-declaration expansion, without result entry/body. -/
def argumentProgram : Prog C Caller (Params ++ Caller) := badArgs.declsThen .nil
def argumentProducer : Calls.Program 1 PublishedDirectCalls.Checks.prefixProducer.frag argumentProgram :=
 (Calls.compile 1 PublishedDirectCalls.Checks.prefixProducer.frag argumentProgram).get (by decide +kernel)
attribute [irreducible] argumentProducer

theorem argument_failure : argumentProgram.run PublishedDirectCalls.Checks.caller.st = .error .revert :=
 actual_error _ (by decide +kernel)
theorem argument_cost_room : argumentProducer.cost PublishedDirectCalls.Checks.caller.st = 0 ∧
 1 + argumentProducer.need ≤ 128 := by decide +kernel

theorem caller_fragment : PublishedDirectCalls.Checks.prefixProducer.frag = Frag.init Caller := by decide +kernel


#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.prefix_execution
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.good_arguments
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.failed_arguments
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.body_execution
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.good_call
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.bad_call
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.costs
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.frame_rooms
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.observations
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.argument_prefix
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.prefix_order
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.bad_read
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.source_lengths
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.source_contents
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.wrong_argument_order
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.wrong_return_alias
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.wrong_default_escape
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.public_admission
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.argument_failure
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.argument_cost_room
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks.caller_fragment
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.call_revert
#print axioms Solidity.Backend.InternalFlow.ArgumentFailureTarget.after_prefix
end Solidity.Backend.InternalFlow.ArgumentFailureTarget.Checks
