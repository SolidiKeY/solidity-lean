import Solidity.Backend.AbiEntry.EntryRoutesInterface

/-! One typed continuation tree through the existing compiler. An ordinary
miss reaches the actual special selector; a matched rejection is terminal. -/
namespace Solidity.Backend.AbiEntry.EntryRoutes
open Solidity.Evm
open Interface (RouteCtx PayableRouteTable SpecialRow ordinaryResult entryRouteOutcome specialOutcome specialRowOutcome)

def chain (C : Contract) (table : PayableRouteTable) (receive fallback : Option SpecialRow) : Prog C RouteCtx RouteCtx :=
  match table with
  | [] => SpecialRoutes.route C receive fallback
  | (tag,label,payable)::rest => .cons (.ite (SelectorRoutes.selectorCondition C tag)
      (ValueGateBody.guard payable (SelectorRoutes.writeLabel C label)) (chain C rest receive fallback)) .nil

def route (C : Contract) (table : PayableRouteTable) (receive fallback : Option SpecialRow) : Prog C RouteCtx RouteCtx :=
  .cons (.ite (ShortRoutes.condition C) (SpecialRoutes.route C receive fallback) (chain C table receive fallback)) .nil

private theorem chain_core (C : Contract) (table : PayableRouteTable) (receive fallback : Option SpecialRow) :
    inFragP (Frag.init RouteCtx) (chain C table receive fallback)=some (Frag.init RouteCtx) := by
  induction table with
  | nil => exact SpecialRoutes.admitted C receive fallback
  | cons row rest ih =>
    rcases row with ⟨tag,label,payable⟩
    have guarded := ValueGateBody.admitted (Frag.init RouteCtx) (SelectorRoutes.writeLabel C label) payable
      (Frag.init RouteCtx) (SelectorRoutes.write_core C label _)
    simp only [chain,inFragP,inFrag,SelectorRoutes.condition_in,ite_true]
    rw [guarded,ih]
    rfl

theorem admitted (C : Contract) (table : PayableRouteTable) (receive fallback : Option SpecialRow) :
    inFragP (Frag.init RouteCtx) (route C table receive fallback)=some (Frag.init RouteCtx) := by
  simp only [route,ShortRoutes.condition,inFragP,inFrag,valIn,simpleIn,binInFrag]
  rw [SpecialRoutes.admitted,chain_core]
  rfl

def compiled (C : Contract) (base : Nat) (table : PayableRouteTable) (receive fallback : Option SpecialRow) :
    Compiler.Compilation base (Frag.init RouteCtx) (route C table receive fallback) :=
  .core (Frag.init RouteCtx) (admitted C table receive fallback)

theorem selected (C : Contract) (base : Nat) (table : PayableRouteTable) (receive fallback : Option SpecialRow) :
    Compiler.compile base (Frag.init RouteCtx) (route C table receive fallback)=some (compiled C base table receive fallback) :=
  ValueGateBody.body_selected base _ _ _ (admitted C table receive fallback)

private theorem chain_code (C : Contract) (base : Nat) (tag label : Fin W) (payable : Bool)
    (rest : PayableRouteTable) (receive fallback : Option SpecialRow) :
    compileProg base (chain C ((tag,label,payable)::rest) receive fallback)=
      [.mload base,.push (.val tag),.eq,.iszero,.jumpi ((PayableRoutes.branchBody base label payable).length+1)]++
      PayableRoutes.branchBody base label payable++
      [.jump (compileProg base (chain C rest receive fallback)).length]++compileProg base (chain C rest receive fallback) := by
  simp only [chain,compileProg,compileStmt,List.append_nil]
  rw [SelectorRoutes.condition_code,PayableRoutes.branchBody_code]
  rfl

private theorem chain_run (C : Contract) (base : Nat) (table : PayableRouteTable) (receive fallback : Option SpecialRow)
    (machine : Machine) (selector size : Fin W) (initial : machine.mem base=.val selector)
    (length : machine.mem (base+1)=.val size) :
    run (compileProg base (chain C table receive fallback)) machine=
      match ordinaryResult table selector with
      | none => specialOutcome base receive fallback size machine
      | some row => specialRowOutcome base (some row) machine := by
  induction table with
  | nil => exact SpecialRoutes.run_route C base receive fallback machine size length
  | cons row rest ih =>
    rcases row with ⟨tag,label,payable⟩
    rw [chain_code,PayableRoutes.test_run base tag selector _ _ machine initial]
    by_cases same : tag.val=selector.val
    · rw [ite_eq_left same,PayableRoutes.branchBody_run]
      simp only [ordinaryResult,List.find?_cons,decide_eq_true same,Option.map_some,specialRowOutcome]
    · rw [ite_eq_right same,ih]
      simp only [ordinaryResult,List.find?_cons,decide_eq_false same]

private theorem code (C : Contract) (base : Nat) (table : PayableRouteTable) (receive fallback : Option SpecialRow) :
    compileProg base (route C table receive fallback)=
      [.mload (base+1),.push (.val (wmod 4)),.gt,.iszero,
        .jumpi ((compileProg base (SpecialRoutes.route C receive fallback)).length+1)]++
      compileProg base (SpecialRoutes.route C receive fallback)++
      [.jump (compileProg base (chain C table receive fallback)).length]++compileProg base (chain C table receive fallback) := by
  simp only [route,compileProg,compileStmt,ShortRoutes.condition,compileVal,compileSimple,List.append_nil]
  rfl

private theorem length_front (base : Nat) (size : Fin W) (yes no : List Evm.Instr) (machine : Machine)
    (initial : machine.mem (base+1)=.val size) :
    run ([.mload (base+1),.push (.val (wmod 4)),.gt,.iszero,.jumpi (yes.length+1)]++yes++[.jump no.length]++no) machine=
      if size.val<4 then run (yes++[.jump no.length]++no) machine else run no machine := by
  by_cases small : size.val<4
  · simp only [run,List.cons_append,List.nil_append,List.append_assoc,exec_cons_zero,Instr.step,Machine.next,
      Out.bind,initial,wmod,Nat.mod_eq_of_lt (by decide : (4 : Nat)<W),small,decide_true,bword,ite_true,
      ite_false,Nat.one_ne_zero,decide_false,Bool.false_eq_true]
  · simp only [run,List.cons_append,List.nil_append,List.append_assoc,exec_cons_zero,Instr.step,Machine.next,
      Out.bind,initial,wmod,Nat.mod_eq_of_lt (by decide : (4 : Nat)<W),small,decide_false,decide_true,bword,
      ite_true,ite_false,Nat.one_ne_zero,Bool.false_eq_true,exec_skip_append,exec_cons_succ]

private theorem special_join (C : Contract) (base : Nat) (receive fallback : Option SpecialRow)
    (rest : List Evm.Instr) (machine : Machine) (size : Fin W) (length : machine.mem (base+1)=.val size) :
    run (compileProg base (SpecialRoutes.route C receive fallback)++[.jump rest.length]++rest) machine=
      specialOutcome base receive fallback size machine := by
  simp only [List.append_assoc,run,exec_append]
  change (run (compileProg base (SpecialRoutes.route C receive fallback)) machine).bind _=_
  rw [SpecialRoutes.run_route C base receive fallback machine size length]
  have nilrun : ∀ (k : Nat) (m : Machine),exec [] k m=.ok m k := fun _ _ => rfl
  unfold specialOutcome specialRowOutcome
  cases row : Interface.specialResult receive fallback size with
  | none => rfl
  | some pair =>
    cases allowed : pair.2 || decide (machine.callvalue.val=0) <;>
      simp only [allowed,Bool.false_eq_true,ite_true,ite_false,Out.bind,exec_cons_zero,Instr.step,nilrun,exec_length]

theorem run_route (C : Contract) (base : Nat) (table : PayableRouteTable) (receive fallback : Option SpecialRow)
    (machine : Machine) (selector size : Fin W) (initial : machine.mem base=.val selector)
    (length : machine.mem (base+1)=.val size) :
    run (compileProg base (route C table receive fallback)) machine=
      entryRouteOutcome base table receive fallback selector size machine := by
  rw [code,length_front base size _ _ machine length]
  by_cases small : size.val<4
  · rw [ite_eq_left small,special_join C base receive fallback _ machine size length]
    simp only [entryRouteOutcome,ite_eq_left small]
  · rw [ite_eq_right small,chain_run C base table receive fallback machine selector size initial length]
    simp only [entryRouteOutcome,ite_eq_right small]
    rfl

theorem executed (C : Contract) (base : Nat) (table : PayableRouteTable) (receive fallback : Option SpecialRow)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (route C table receive fallback))
    (found : Compiler.compile base (Frag.init RouteCtx) (route C table receive fallback)=some result)
    (machine : Machine) (selector size : Fin W) (initial : machine.mem base=.val selector)
    (length : machine.mem (base+1)=.val size) :
    run result.code machine=entryRouteOutcome base table receive fallback selector size machine := by
  have same : result=compiled C base table receive fallback := Option.some.inj (found.symm.trans (selected C base table receive fallback))
  rw [same]
  exact run_route C base table receive fallback machine selector size initial length

private theorem option_rows (left right : Option SpecialRow)
    (zero : left.getD (wmod 0,true)=right.getD (wmod 0,true))
    (one : left.getD (wmod 1,true)=right.getD (wmod 1,true)) : left=right := by
  cases left with
  | none => cases right with
    | none => rfl
    | some row =>
      have distinct : (wmod 0,true)≠(wmod 1,true) := by decide
      exact False.elim (distinct (zero.trans one.symm))
  | some row => cases right with
    | none =>
      have distinct : (wmod 0,true)≠(wmod 1,true) := by decide
      exact False.elim (distinct (zero.symm.trans one))
    | some other => exact congrArg some zero

def ordinaryRow (labels : Source.Decl → Fin W) (declaration : Source.Decl) : SpecialRow :=
  (labels declaration,declaration.fnMut == some .payable)

/-- Recover option-valued lookup from the existing general default-valued
Source theorem, without redoing selector/list eligibility proofs. -/
theorem source_ordinary {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (labels : Source.Decl → Fin W) (full : 4≤frame.cd.length) :
    ordinaryResult (SourcePayable.table global frame.contract labels) (Interface.rawSelectorWord frame)=
      (global.pickFn frame frame.cd).map (ordinaryRow labels) := by
  apply option_rows
  · exact SourcePayable.lookup global frame labels (wmod 0) full
  · exact SourcePayable.lookup global frame labels (wmod 1) full

def certificate : Interface.EntryRoutesCertificate route where
  selected := fun C base table receive fallback => ⟨compiled C base table receive fallback,selected C base table receive fallback⟩
  executed := executed
/-- info: 'Solidity.Backend.AbiEntry.EntryRoutes.admitted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.EntryRoutes.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.EntryRoutes.run_route' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_route
/-- info: 'Solidity.Backend.AbiEntry.EntryRoutes.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.EntryRoutes.source_ordinary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_ordinary
/-- info: 'Solidity.Backend.AbiEntry.EntryRoutes.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.EntryRoutes
