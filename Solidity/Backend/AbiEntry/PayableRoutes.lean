import Solidity.Backend.AbiEntry.PayableRoutesInterface
import Solidity.Backend.AbiEntry.SelectorRoutes

/-! Per-row payability within the existing typed/public compiler. Rejection is
terminal after a selector match; no fallback or later collision is retried. -/
namespace Solidity.Backend.AbiEntry.PayableRoutes
open Solidity.Evm
open Interface (RouteCtx PayableRouteTable payableRouteOutcome payableRouteResult)

def route (C : Contract) (table : PayableRouteTable) (fallback : Fin W) : Prog C RouteCtx RouteCtx :=
  match table with
  | [] => SelectorRoutes.writeLabel C fallback
  | (tag,label,payable)::rest => .cons (.ite (SelectorRoutes.selectorCondition C tag)
      (ValueGateBody.guard payable (SelectorRoutes.writeLabel C label)) (route C rest fallback)) .nil

theorem admitted (C : Contract) (table : PayableRouteTable) (fallback : Fin W) :
    inFragP (Frag.init RouteCtx) (route C table fallback)=some (Frag.init RouteCtx) := by
  induction table with
  | nil => exact SelectorRoutes.write_core C fallback _
  | cons row rest ih =>
    rcases row with ⟨tag,label,payable⟩
    have guarded := ValueGateBody.admitted (Frag.init RouteCtx) (SelectorRoutes.writeLabel C label) payable
      (Frag.init RouteCtx) (SelectorRoutes.write_core C label _)
    simp only [route,inFragP,inFrag,SelectorRoutes.condition_in,if_true]
    rw [guarded,ih]
    rfl

def compiled (C : Contract) (base : Nat) (table : PayableRouteTable) (fallback : Fin W) :
    Compiler.Compilation base (Frag.init RouteCtx) (route C table fallback) :=
  .core (Frag.init RouteCtx) (admitted C table fallback)

theorem selected (C : Contract) (base : Nat) (table : PayableRouteTable) (fallback : Fin W) :
    Compiler.compile base (Frag.init RouteCtx) (route C table fallback)=some (compiled C base table fallback) :=
  ValueGateBody.body_selected base _ _ _ (admitted C table fallback)

private def bodyCode (base : Nat) (label : Fin W) (payable : Bool) : List Instr :=
  (if payable then [] else [.callvalue,.push (.val (wmod 0)),.eq,.jumpi 1,.revert])++
    [.push (.val label),.mstore (base+1)]

private theorem body_code (C : Contract) (base : Nat) (label : Fin W) (payable : Bool) :
    compileProg base (ValueGateBody.guard payable (SelectorRoutes.writeLabel C label))=bodyCode base label payable := by
  cases payable with
  | true => exact SelectorRoutes.write_code C base label
  | false =>
    change [.callvalue,.push (.val (wmod 0)),.eq,.jumpi 1,.revert]++
      compileProg base (SelectorRoutes.writeLabel C label)=_
    rw [SelectorRoutes.write_code]
    rfl

private theorem cons_code (C : Contract) (base : Nat) (tag label : Fin W) (payable : Bool)
    (rest : PayableRouteTable) (fallback : Fin W) :
    compileProg base (route C ((tag,label,payable)::rest) fallback)=
      [.mload base,.push (.val tag),.eq,.iszero,.jumpi ((bodyCode base label payable).length+1)]++
        bodyCode base label payable++[.jump (compileProg base (route C rest fallback)).length]++
        compileProg base (route C rest fallback) := by
  simp only [route,compileProg,compileStmt,List.append_nil]
  rw [SelectorRoutes.condition_code,body_code]
  rfl

private theorem front (base : Nat) (tag selector : Fin W) (yes no : List Instr) (machine : Machine)
    (initial : machine.mem base=.val selector) :
    run ([.mload base,.push (.val tag),.eq,.iszero,.jumpi (yes.length+1)]++yes++[.jump no.length]++no) machine=
      if tag.val=selector.val then run (yes++[.jump no.length]++no) machine else run no machine := by
  by_cases same : tag.val=selector.val
  · simp only [run,List.cons_append,List.nil_append,List.append_assoc,exec_cons_zero,Instr.step,
      Machine.next,Out.bind,initial,same,decide_true,bword,if_true,if_false,
      Nat.one_ne_zero,decide_false,Bool.false_eq_true]
  · simp only [run,List.cons_append,List.nil_append,List.append_assoc,exec_cons_zero,Instr.step,
      Machine.next,Out.bind,initial,same,decide_false,decide_true,bword,if_true,if_false,
      Nat.one_ne_zero,Bool.false_eq_true,exec_skip_append,exec_cons_succ]

private theorem body_run (base : Nat) (label : Fin W) (payable : Bool) (rest : List Instr) (machine : Machine) :
    run (bodyCode base label payable++[.jump rest.length]++rest) machine=
      if payable || decide (machine.callvalue.val=0) then
        .ok {machine with mem := upd machine.mem (base+1) (.val label)} 0 else .revert := by
  simp only [bodyCode,List.append_assoc]
  rw [ValueGateBody.composed]
  simp only [run,List.cons_append,List.nil_append,exec_cons_zero,Instr.step,Machine.next,Out.bind,exec_length]

theorem run_route (C : Contract) (base : Nat) (table : PayableRouteTable) (fallback : Fin W)
    (machine : Machine) (selector : Fin W) (initial : machine.mem base=.val selector) :
    run (compileProg base (route C table fallback)) machine=payableRouteOutcome base table fallback selector machine := by
  induction table with
  | nil => rw [route,SelectorRoutes.write_code];rfl
  | cons row rest ih =>
    rcases row with ⟨tag,label,payable⟩
    rw [cons_code,front base tag selector _ _ machine initial]
    by_cases same : tag.val=selector.val
    · rw [if_pos same,body_run]
      simp only [payableRouteOutcome,payableRouteResult,List.find?_cons,decide_eq_true same,
        Option.map_some,Option.getD_some]
    · rw [if_neg same,ih]
      simp only [payableRouteOutcome,payableRouteResult,List.find?_cons,decide_eq_false same]

theorem executed (C : Contract) (base : Nat) (table : PayableRouteTable) (fallback : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (route C table fallback))
    (found : Compiler.compile base (Frag.init RouteCtx) (route C table fallback)=some result)
    (machine : Machine) (selector : Fin W) (initial : machine.mem base=.val selector) :
    run result.code machine=payableRouteOutcome base table fallback selector machine := by
  have same : result=compiled C base table fallback :=
    Option.some.inj (found.symm.trans (selected C base table fallback))
  rw [same]
  exact run_route C base table fallback machine selector initial

def certificate : Interface.PayableRoutesCertificate route where
  selected := fun C base table fallback => ⟨compiled C base table fallback,selected C base table fallback⟩
  executed := executed

/-- Public adapters for composition reuse the checked branch implementation. -/
def branchBody (base : Nat) (label : Fin W) (payable : Bool) : List Evm.Instr := bodyCode base label payable

theorem branchBody_code (C : Contract) (base : Nat) (label : Fin W) (payable : Bool) :
    compileProg base (ValueGateBody.guard payable (SelectorRoutes.writeLabel C label))=branchBody base label payable :=
  body_code C base label payable

theorem test_run (base : Nat) (tag selector : Fin W) (yes no : List Evm.Instr) (machine : Machine)
    (initial : machine.mem base=.val selector) :
    run ([.mload base,.push (.val tag),.eq,.iszero,.jumpi (yes.length+1)]++yes++[.jump no.length]++no) machine=
      if tag.val=selector.val then run (yes++[.jump no.length]++no) machine else run no machine :=
  front base tag selector yes no machine initial

theorem branchBody_run (base : Nat) (label : Fin W) (payable : Bool) (rest : List Evm.Instr) (machine : Machine) :
    run (branchBody base label payable++[.jump rest.length]++rest) machine=
      if payable || decide (machine.callvalue.val=0) then
        .ok {machine with mem := upd machine.mem (base+1) (.val label)} 0 else .revert :=
  body_run base label payable rest machine

/-- info: 'Solidity.Backend.AbiEntry.PayableRoutes.admitted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.PayableRoutes.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.PayableRoutes.run_route' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_route
/-- info: 'Solidity.Backend.AbiEntry.PayableRoutes.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.PayableRoutes.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
/-- info: 'Solidity.Backend.AbiEntry.PayableRoutes.branchBody_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms branchBody_code
/-- info: 'Solidity.Backend.AbiEntry.PayableRoutes.test_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms test_run
/-- info: 'Solidity.Backend.AbiEntry.PayableRoutes.branchBody_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms branchBody_run
end Solidity.Backend.AbiEntry.PayableRoutes
