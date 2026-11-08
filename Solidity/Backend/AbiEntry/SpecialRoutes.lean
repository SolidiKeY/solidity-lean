import Solidity.Backend.AbiEntry.SpecialRoutesInterface

/-! Typed receive/fallback continuation choice with declaration-derived flags.
Body execution and ordinary/getter precedence are separate obligations. -/
namespace Solidity.Backend.AbiEntry.SpecialRoutes
open Solidity.Evm
open Interface (RouteCtx SpecialRow specialResult specialRowOutcome specialOutcome sourceSpecial)

def endpoint (C : Contract) (row : Option SpecialRow) : Prog C RouteCtx RouteCtx :=
  match row with
  | none => .cons .revert .nil
  | some (label,payable) => ValueGateBody.guard payable (SelectorRoutes.writeLabel C label)
def condition (C : Contract) : Val C RouteCtx .bool :=
  .binop .eqB (by decide) rfl (.simple (.lit 0 rfl)) (.simple (.local .here))
def route (C : Contract) (receive fallback : Option SpecialRow) : Prog C RouteCtx RouteCtx :=
  .cons (.ite (condition C) (endpoint C (receive.orElse (fun _ => fallback))) (endpoint C fallback)) .nil

private theorem endpoint_core (C : Contract) (row : Option SpecialRow) :
    inFragP (Frag.init RouteCtx) (endpoint C row)=some (Frag.init RouteCtx) := by
  cases row with
  | none => rfl
  | some pair => exact ValueGateBody.admitted _ _ _ _ (SelectorRoutes.write_core C pair.1 _)

theorem admitted (C : Contract) (receive fallback : Option SpecialRow) :
    inFragP (Frag.init RouteCtx) (route C receive fallback)=some (Frag.init RouteCtx) := by
  simp only [route,condition,inFragP,inFrag,valIn,simpleIn,binInFrag]
  rw [endpoint_core,endpoint_core]
  rfl

def compiled (C : Contract) (base : Nat) (receive fallback : Option SpecialRow) :
    Compiler.Compilation base (Frag.init RouteCtx) (route C receive fallback) :=
  .core (Frag.init RouteCtx) (admitted C receive fallback)

theorem selected (C : Contract) (base : Nat) (receive fallback : Option SpecialRow) :
    Compiler.compile base (Frag.init RouteCtx) (route C receive fallback)=some (compiled C base receive fallback) :=
  ValueGateBody.body_selected base _ _ _ (admitted C receive fallback)

private theorem code (C : Contract) (base : Nat) (receive fallback : Option SpecialRow) :
    compileProg base (route C receive fallback)=
      [.push (.val (wmod 0)),.mload (base+1),.eq,.iszero,
        .jumpi ((compileProg base (endpoint C (receive.orElse (fun _ => fallback)))).length+1)]++
      compileProg base (endpoint C (receive.orElse (fun _ => fallback)))++
      [.jump (compileProg base (endpoint C fallback)).length]++compileProg base (endpoint C fallback) := by
  simp only [route,compileProg,compileStmt,condition,compileVal,compileSimple,List.append_nil]
  rfl

private theorem front (base : Nat) (size : Fin W) (yes no : List Evm.Instr) (machine : Machine)
    (initial : machine.mem (base+1)=.val size) :
    run ([.push (.val (wmod 0)),.mload (base+1),.eq,.iszero,.jumpi (yes.length+1)]++yes++[.jump no.length]++no) machine=
      if size.val=0 then run (yes++[.jump no.length]++no) machine else run no machine := by
  by_cases empty : size.val=0
  · simp only [run,List.cons_append,List.nil_append,List.append_assoc,exec_cons_zero,Instr.step,
      Machine.next,Out.bind,initial,wmod,Nat.zero_mod,empty,decide_true,bword,ite_true,ite_false,
      Nat.one_ne_zero,decide_false,Bool.false_eq_true]
  · simp only [run,List.cons_append,List.nil_append,List.append_assoc,exec_cons_zero,Instr.step,
      Machine.next,Out.bind,initial,wmod,Nat.zero_mod,empty,decide_false,decide_true,bword,ite_true,ite_false,
      Nat.one_ne_zero,Bool.false_eq_true,exec_skip_append,exec_cons_succ]

private theorem endpoint_run (C : Contract) (base : Nat) (row : Option SpecialRow) (rest : List Evm.Instr)
    (machine : Machine) :
    run (compileProg base (endpoint C row)++[.jump rest.length]++rest) machine=specialRowOutcome base row machine := by
  cases row with
  | none => rfl
  | some pair =>
    rcases pair with ⟨label,payable⟩
    have body : compileProg base (endpoint C (some (label,payable)))=
        (if payable then [] else [.callvalue,.push (.val (wmod 0)),.eq,.jumpi 1,.revert])++
          [.push (.val label),.mstore (base+1)] := by
      cases payable with
      | true => exact SelectorRoutes.write_code C base label
      | false =>
        change [.callvalue,.push (.val (wmod 0)),.eq,.jumpi 1,.revert]++
          compileProg base (SelectorRoutes.writeLabel C label)=_
        rw [SelectorRoutes.write_code]
        rfl
    rw [body]
    simp only [List.append_assoc]
    rw [ValueGateBody.composed]
    simp only [run,List.cons_append,List.nil_append,exec_cons_zero,Instr.step,Machine.next,Out.bind,
      exec_length,specialRowOutcome]

private theorem endpoint_alone (C : Contract) (base : Nat) (row : Option SpecialRow) (machine : Machine) :
    run (compileProg base (endpoint C row)) machine=specialRowOutcome base row machine := by
  cases row with
  | none => rfl
  | some pair =>
    rcases pair with ⟨label,payable⟩
    cases payable with
    | true =>
      change run (compileProg base (SelectorRoutes.writeLabel C label)) machine=_
      rw [SelectorRoutes.write_code]
      rfl
    | false =>
      change run ([.callvalue,.push (.val (wmod 0)),.eq,.jumpi 1,.revert]++
        compileProg base (SelectorRoutes.writeLabel C label)) machine=_
      have gate := ValueGateBody.composed false (compileProg base (SelectorRoutes.writeLabel C label)) machine
      have write : run [.push (.val label),.mstore (base+1)] machine=
          .ok {machine with mem := upd machine.mem (base+1) (.val label)} 0 := by
        simp only [run,exec_cons_zero,Instr.step,Machine.next,Out.bind]
        exact exec_length [] _
      simp only [Bool.false_eq_true,ite_false,SelectorRoutes.write_code] at gate
      rw [write] at gate
      simpa only [specialRowOutcome,SelectorRoutes.write_code] using gate

theorem run_route (C : Contract) (base : Nat) (receive fallback : Option SpecialRow)
    (machine : Machine) (size : Fin W) (initial : machine.mem (base+1)=.val size) :
    run (compileProg base (route C receive fallback)) machine=specialOutcome base receive fallback size machine := by
  rw [code,front base size _ _ machine initial]
  by_cases empty : size.val=0
  · rw [ite_eq_left empty,endpoint_run]
    simp only [specialOutcome,specialResult,ite_eq_left empty]
  · rw [ite_eq_right empty,endpoint_alone]
    simp only [specialOutcome,specialResult,ite_eq_right empty]

theorem executed (C : Contract) (base : Nat) (receive fallback : Option SpecialRow)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (route C receive fallback))
    (found : Compiler.compile base (Frag.init RouteCtx) (route C receive fallback)=some result)
    (machine : Machine) (size : Fin W) (initial : machine.mem (base+1)=.val size) :
    run result.code machine=specialOutcome base receive fallback size machine := by
  have same : result=compiled C base receive fallback := Option.some.inj (found.symm.trans (selected C base receive fallback))
  rw [same]
  exact run_route C base receive fallback machine size initial

def row (labels : Source.Decl → Fin W) (declaration : Source.Decl) : SpecialRow :=
  (labels declaration,declaration.specialPayable)
def receiveRow (E : Source.Env) (contract : String) (labels : Source.Decl → Fin W) : Option SpecialRow :=
  (E.special contract .receive).map (row labels)
def fallbackRow (E : Source.Env) (contract : String) (labels : Source.Decl → Fin W) : Option SpecialRow :=
  (E.special contract .fallback).map (row labels)

theorem source_lookup (E : Source.Env) (frame : Source.Fr) (labels : Source.Decl → Fin W)
    (size : Fin W) (length : size.val=frame.cd.length) :
    specialResult (receiveRow E frame.contract labels) (fallbackRow E frame.contract labels) size=
      (sourceSpecial E frame).map (row labels) := by
  cases bytes : frame.cd with
  | nil =>
    simp only [specialResult,length,bytes,List.length_nil,sourceSpecial,List.isEmpty_nil,ite_true,
      receiveRow,fallbackRow]
    cases E.special frame.contract .receive <;> rfl
  | cons b bs =>
    simp only [specialResult,length,bytes,List.length_cons,Nat.add_one_ne_zero,ite_false,sourceSpecial,
      List.isEmpty_cons,Bool.false_eq_true,fallbackRow]

theorem source_executed (E : Source.Env) (frame : Source.Fr) (labels : Source.Decl → Fin W)
    (C : Contract) (base : Nat)
    (result : Compiler.Compilation base (Frag.init RouteCtx)
      (route C (receiveRow E frame.contract labels) (fallbackRow E frame.contract labels)))
    (found : Compiler.compile base (Frag.init RouteCtx)
      (route C (receiveRow E frame.contract labels) (fallbackRow E frame.contract labels))=some result)
    (machine : Machine) (size : Fin W) (initial : machine.mem (base+1)=.val size)
    (length : size.val=frame.cd.length) :
    run result.code machine=specialRowOutcome base ((sourceSpecial E frame).map (row labels)) machine := by
  have reached := executed C base _ _ result found machine size initial
  simpa only [specialOutcome,source_lookup E frame labels size length] using reached

/-- Exact Source absence failure after the ordinary/getter branches miss. -/
theorem source_absent {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr) (fuel : Nat)
    (ordinary : global.pickFn frame frame.cd=none) (getter : global.pickGetter frame frame.cd=none)
    (absent : sourceSpecial E frame=none) :
    Source.dispatch global frame (fuel+1) frame.cd=Source.EM.halt (.revert []) := by
  unfold sourceSpecial at absent
  simp only [Source.dispatch,ordinary,getter,absent]

/-- A selected special value refusal occurs before reading or executing its body. -/
theorem source_rejection {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr) (fuel : Nat)
    (declaration : Source.Decl) (ordinary : global.pickFn frame frame.cd=none)
    (getter : global.pickGetter frame frame.cd=none) (chosen : sourceSpecial E frame=some declaration)
    (nonzero : frame.value.val≠0) (nonpayable : declaration.specialPayable=false) :
    Source.dispatch global frame (fuel+1) frame.cd=Source.EM.halt (.revert []) := by
  unfold sourceSpecial at chosen
  simp only [Source.dispatch,ordinary,getter,chosen,decide_eq_true nonzero,nonpayable,
    Bool.not_false,Bool.true_and,ite_true]
  rfl

def certificate : Interface.SpecialRoutesCertificate route where
  selected := fun C base receive fallback => ⟨compiled C base receive fallback,selected C base receive fallback⟩
  executed := executed
/-- info: 'Solidity.Backend.AbiEntry.SpecialRoutes.admitted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.SpecialRoutes.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.SpecialRoutes.run_route' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_route
/-- info: 'Solidity.Backend.AbiEntry.SpecialRoutes.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.SpecialRoutes.source_lookup' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms source_lookup
/-- info: 'Solidity.Backend.AbiEntry.SpecialRoutes.source_executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_executed
/-- info: 'Solidity.Backend.AbiEntry.SpecialRoutes.source_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_absent
/-- info: 'Solidity.Backend.AbiEntry.SpecialRoutes.source_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_rejection
/-- info: 'Solidity.Backend.AbiEntry.SpecialRoutes.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.SpecialRoutes
