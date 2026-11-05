import Solidity.Backend.AbiEntry.ShortRoutesInterface

/-! The result local initially holds calldata length and is overwritten only
after branching. The selector local and all saved state are preserved. -/
namespace Solidity.Backend.AbiEntry.ShortRoutes
open Solidity.Evm
open Interface (RouteCtx PayableRouteTable shortRouteOutcome rawSelectorWord sourcePayableOutcome)

def condition (C : Contract) : Val C RouteCtx .bool :=
  .binop .lt rfl rfl (.simple (.local .here)) (.simple (.lit 4 rfl))
def route (C : Contract) (table : PayableRouteTable) (fallback short : Fin W) : Prog C RouteCtx RouteCtx :=
  .cons (.ite (condition C) (SelectorRoutes.writeLabel C short) (PayableRoutes.route C table fallback)) .nil

theorem admitted (C : Contract) (table : PayableRouteTable) (fallback short : Fin W) :
    inFragP (Frag.init RouteCtx) (route C table fallback short)=some (Frag.init RouteCtx) := by
  simp only [route,condition,inFragP,inFrag,valIn,simpleIn,binInFrag]
  rw [SelectorRoutes.write_core,PayableRoutes.admitted]
  rfl

def compiled (C : Contract) (base : Nat) (table : PayableRouteTable) (fallback short : Fin W) :
    Compiler.Compilation base (Frag.init RouteCtx) (route C table fallback short) :=
  .core (Frag.init RouteCtx) (admitted C table fallback short)

theorem selected (C : Contract) (base : Nat) (table : PayableRouteTable) (fallback short : Fin W) :
    Compiler.compile base (Frag.init RouteCtx) (route C table fallback short)=some (compiled C base table fallback short) :=
  ValueGateBody.body_selected base _ _ _ (admitted C table fallback short)

private theorem code (C : Contract) (base : Nat) (table : PayableRouteTable) (fallback short : Fin W) :
    compileProg base (route C table fallback short)=
      [.mload (base+1),.push (.val (wmod 4)),.gt,.iszero,.jumpi 3,.push (.val short),.mstore (base+1),
        .jump (compileProg base (PayableRoutes.route C table fallback)).length]++
          compileProg base (PayableRoutes.route C table fallback) := by
  simp only [route,compileProg,compileStmt,condition,compileVal,compileSimple,List.append_nil]
  rw [SelectorRoutes.write_code]
  rfl

private theorem branch (base : Nat) (short size : Fin W) (rest : List Evm.Instr) (machine : Machine)
    (initial : machine.mem (base+1)=.val size) :
    run ([.mload (base+1),.push (.val (wmod 4)),.gt,.iszero,.jumpi 3,.push (.val short),.mstore (base+1),
      .jump rest.length]++rest) machine=
      if size.val<4 then .ok {machine with mem := upd machine.mem (base+1) (.val short)} 0
      else run rest machine := by
  by_cases small : size.val<4
  · simp only [run,List.cons_append,List.nil_append,exec_cons_zero,Instr.step,Machine.next,Out.bind,
      initial,wmod,Nat.mod_eq_of_lt (by decide : (4 : Nat)<W),small,decide_true,bword,if_true,if_false,Nat.one_ne_zero,decide_false,
      Bool.false_eq_true,exec_length]
  · simp only [run,List.cons_append,List.nil_append,exec_cons_zero,exec_cons_succ,Instr.step,Machine.next,
      Out.bind,initial,wmod,Nat.mod_eq_of_lt (by decide : (4 : Nat)<W),small,decide_false,decide_true,bword,if_true,if_false,Nat.one_ne_zero,
      Bool.false_eq_true]

theorem run_route (C : Contract) (base : Nat) (table : PayableRouteTable) (fallback short : Fin W)
    (machine : Machine) (selector size : Fin W) (initial : machine.mem base=.val selector)
    (length : machine.mem (base+1)=.val size) :
    run (compileProg base (route C table fallback short)) machine=
      shortRouteOutcome base table fallback short selector size machine := by
  rw [code,branch base short size _ machine length]
  by_cases small : size.val<4
  · simp only [shortRouteOutcome,if_pos small]
  · simp only [shortRouteOutcome,if_neg small]
    exact PayableRoutes.run_route C base table fallback machine selector initial

theorem executed (C : Contract) (base : Nat) (table : PayableRouteTable) (fallback short : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (route C table fallback short))
    (found : Compiler.compile base (Frag.init RouteCtx) (route C table fallback short)=some result)
    (machine : Machine) (selector size : Fin W) (initial : machine.mem base=.val selector)
    (length : machine.mem (base+1)=.val size) :
    run result.code machine=shortRouteOutcome base table fallback short selector size machine := by
  have same : result=compiled C base table fallback short := Option.some.inj (found.symm.trans (selected C base table fallback short))
  rw [same]
  exact run_route C base table fallback short machine selector size initial length

theorem source_executed {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (labels : Source.Decl → Fin W) (fallback short : Fin W) (C : Contract) (base : Nat)
    (result : Compiler.Compilation base (Frag.init RouteCtx)
      (route C (SourcePayable.table global frame.contract labels) fallback short))
    (found : Compiler.compile base (Frag.init RouteCtx)
      (route C (SourcePayable.table global frame.contract labels) fallback short)=some result)
    (machine : Machine) (size : Fin W) (initial : machine.mem base=.val (rawSelectorWord frame))
    (length : machine.mem (base+1)=.val size) (bytes : size.val=frame.cd.length)
    (value : machine.callvalue.val=frame.value.val) :
    run result.code machine=if frame.cd.length<4 then
      .ok {machine with mem := upd machine.mem (base+1) (.val short)} 0
      else sourcePayableOutcome global frame labels fallback base machine := by
  have reached := executed C base _ fallback short result found machine (rawSelectorWord frame) size initial length
  by_cases small : frame.cd.length<4
  · simpa only [shortRouteOutcome,bytes,if_pos small] using reached
  · have full : 4≤frame.cd.length := Nat.le_of_not_gt small
    simpa only [shortRouteOutcome,bytes,if_neg small,Interface.payableRouteOutcome,
      SourcePayable.lookup global frame labels fallback full,value,sourcePayableOutcome] using reached

theorem source_short {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (short : frame.cd.length<4) : global.pickFn frame frame.cd=none := by
  unfold Source.Glob.pickFn
  apply List.find?_eq_none.mpr
  intro declaration _ yes
  have matched := (Bool.and_eq_true_iff.mp yes).2
  cases signature : declaration.fnSig E with
  | none => simp only [signature] at matched; cases matched
  | some pair =>
    rcases pair with ⟨parameters,returns⟩
    rw [signature] at matched
    have same := eq_of_beq matched
    have absent := SelectorMatch.short_no_match
      (SelectorMatch.sourceSelector global (Source.sigOf E.layout declaration.name parameters)) frame.cd short
    rw [SelectorMatch.source_bytes] at absent
    have reverse : (frame.cd.take 4==global.selector (Source.sigOf E.layout declaration.name parameters))=true :=
      beq_iff_eq.mpr same.symm
    rw [reverse] at absent
    cases absent

def certificate : Interface.ShortRoutesCertificate route where
  selected := fun C base table fallback short => ⟨compiled C base table fallback short,selected C base table fallback short⟩
  executed := executed
/-- info: 'Solidity.Backend.AbiEntry.ShortRoutes.admitted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.ShortRoutes.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.ShortRoutes.run_route' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_route
/-- info: 'Solidity.Backend.AbiEntry.ShortRoutes.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.ShortRoutes.source_executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_executed
/-- info: 'Solidity.Backend.AbiEntry.ShortRoutes.source_short' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_short
/-- info: 'Solidity.Backend.AbiEntry.ShortRoutes.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.ShortRoutes
