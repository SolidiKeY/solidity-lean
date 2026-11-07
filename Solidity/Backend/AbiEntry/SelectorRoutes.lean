import Solidity.Backend.AbiEntry.SelectorRoutesInterface
import Solidity.Backend.AbiEntry.ValueGateBody

/-! Intrinsically typed selector-local branches selected by the public compiler.
The initial selector cell is representation, not a supplied run or route result.
Source table construction and ABI loading/body dispatch are separate. -/
namespace Solidity.Backend.AbiEntry.SelectorRoutes
open Solidity.Evm
open Interface (RouteCtx RouteTable routeResult)

private def literal {C : Contract} {Γ : Ctx} (value : Fin W) : Val C Γ .uint :=
  .simple (.lit (value.val : Int) (PrimTy.inRange_uint_of_lt value.isLt))
private def condition (C : Contract) (selector : Fin W) : Val C RouteCtx .bool :=
  .binop .eqB (by decide) rfl (.simple (.local (.there .here))) (literal selector)
private def assignLabel (C : Contract) (label : Fin W) : Prog C RouteCtx RouteCtx :=
  .cons (.assignLocal .here (literal label)) .nil

def route (C : Contract) (table : RouteTable) (fallback : Fin W) : Prog C RouteCtx RouteCtx :=
  match table with
  | [] => assignLabel C fallback
  | (selector,label)::rest => .cons (.ite (condition C selector) (assignLabel C label) (route C rest fallback)) .nil

theorem admitted (C : Contract) (table : RouteTable) (fallback : Fin W) :
    inFragP (Frag.init RouteCtx) (route C table fallback)=some (Frag.init RouteCtx) := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨selector,label⟩
    simp only [route,inFragP,inFrag,condition,assignLabel,literal,valIn,simpleIn,
      binInFrag,Frag.guard,ite_true]
    rw [ih]
    rfl

def compiled (C : Contract) (base : Nat) (table : RouteTable) (fallback : Fin W) :
    Compiler.Compilation base (Frag.init RouteCtx) (route C table fallback) :=
  .core (Frag.init RouteCtx) (admitted C table fallback)

theorem selected (C : Contract) (base : Nat) (table : RouteTable) (fallback : Fin W) :
    Compiler.compile base (Frag.init RouteCtx) (route C table fallback)=some (compiled C base table fallback) :=
  ValueGateBody.body_selected base (Frag.init RouteCtx) (route C table fallback)
    (Frag.init RouteCtx) (admitted C table fallback)

private theorem literal_word (value : Fin W) : wmod (toWord (value.val : Int))=value := by
  simp only [toWord,Int.natCast_nonneg,if_true,Int.toNat_natCast]
  exact Fin.ext (Nat.mod_eq_of_lt value.isLt)

private theorem nil_code (C : Contract) (base : Nat) (fallback : Fin W) :
    compileProg base (route C [] fallback)=[.push (.val fallback),.mstore (base+1)] := by
  change ([.push (.val (wmod (toWord (fallback.val : Int)))),.mstore (base+1)] : List Instr)=_
  rw [literal_word]

private theorem cons_code (C : Contract) (base : Nat) (selector label : Fin W)
    (rest : RouteTable) (fallback : Fin W) :
    compileProg base (route C ((selector,label)::rest) fallback)=
      [.mload base,.push (.val selector),.eq,.iszero,.jumpi 3,.push (.val label),.mstore (base+1),
        .jump (compileProg base (route C rest fallback)).length]++compileProg base (route C rest fallback) := by
  simp only [route,compileProg,compileStmt,condition,assignLabel,literal,compileVal,compileSimple,
    List.append_nil,List.cons_append,List.nil_append]
  change [.mload base,.push (.val (wmod (toWord (selector.val : Int)))),.eq,.iszero,.jumpi 3,
    .push (.val (wmod (toWord (label.val : Int)))),.mstore (base+1),
    .jump (compileProg base (route C rest fallback)).length]++compileProg base (route C rest fallback)=_
  rw [literal_word,literal_word]
  rfl

private theorem branch (base : Nat) (tag label selector : Fin W) (rest : List Instr)
    (machine : Machine) (initial : machine.mem base=.val selector) :
    run ([.mload base,.push (.val tag),.eq,.iszero,.jumpi 3,.push (.val label),.mstore (base+1),
      .jump rest.length]++rest) machine=
      if tag.val=selector.val then .ok {machine with mem := upd machine.mem (base+1) (.val label)} 0
      else run rest machine := by
  by_cases same : tag.val=selector.val
  · simp only [run,List.cons_append,List.nil_append,exec_cons_zero,Instr.step,
      Machine.next,Out.bind,initial,same,decide_true,bword,if_true,if_false,
      Nat.one_ne_zero,decide_false,Bool.false_eq_true,exec_length]
  · simp only [run,List.cons_append,List.nil_append,exec_cons_zero,exec_cons_succ,Instr.step,
      Machine.next,Out.bind,initial,same,decide_false,decide_true,bword,if_true,if_false,
      Nat.one_ne_zero,Bool.false_eq_true]

theorem run_route (C : Contract) (base : Nat) (table : RouteTable) (fallback : Fin W)
    (machine : Machine) (selector : Fin W) (initial : machine.mem base=.val selector) :
    run (compileProg base (route C table fallback)) machine=
      .ok {machine with mem := upd machine.mem (base+1) (.val (routeResult table fallback selector))} 0 := by
  induction table with
  | nil => rw [nil_code];rfl
  | cons entry rest ih =>
    rcases entry with ⟨tag,label⟩
    rw [cons_code,branch base tag label selector _ machine initial]
    by_cases same : tag.val=selector.val
    · simp only [if_pos same,routeResult,List.find?_cons,decide_eq_true same,
        Option.map_some,Option.getD_some]
    · rw [if_neg same,ih]
      simp only [routeResult,List.find?_cons,decide_eq_false same]

theorem executed (C : Contract) (base : Nat) (table : RouteTable) (fallback : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (route C table fallback))
    (found : Compiler.compile base (Frag.init RouteCtx) (route C table fallback)=some result)
    (machine : Machine) (selector : Fin W) (initial : machine.mem base=.val selector) :
    run result.code machine=.ok
      {machine with mem := upd machine.mem (base+1) (.val (routeResult table fallback selector))} 0 := by
  have same : result=compiled C base table fallback :=
    Option.some.inj (found.symm.trans (selected C base table fallback))
  rw [same]
  exact run_route C base table fallback machine selector initial

/-- Public constructor adapters for other entry families in the same compiler. -/
def selectorCondition (C : Contract) (tag : Fin W) : Val C RouteCtx .bool := condition C tag
def writeLabel (C : Contract) (label : Fin W) : Prog C RouteCtx RouteCtx := assignLabel C label

theorem condition_in (C : Contract) (tag : Fin W) (frag : Frag RouteCtx) :
    valIn frag (selectorCondition C tag)=true := rfl

theorem write_core (C : Contract) (label : Fin W) (frag : Frag RouteCtx) :
    inFragP frag (writeLabel C label)=some frag := rfl

theorem condition_code (C : Contract) (base : Nat) (tag : Fin W) :
    compileVal base (selectorCondition C tag)=[.mload base,.push (.val tag),.eq] := by
  change ([.mload base,.push (.val (wmod (toWord (tag.val : Int)))),.eq] : List Instr)=_
  rw [literal_word]

theorem write_code (C : Contract) (base : Nat) (label : Fin W) :
    compileProg base (writeLabel C label)=[.push (.val label),.mstore (base+1)] :=
  nil_code C base label

def certificate : Interface.SelectorRoutesCertificate route where
  selected := fun C base table fallback => ⟨compiled C base table fallback,selected C base table fallback⟩
  executed := executed

/-- info: 'Solidity.Backend.AbiEntry.SelectorRoutes.admitted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.SelectorRoutes.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.SelectorRoutes.run_route' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_route
/-- info: 'Solidity.Backend.AbiEntry.SelectorRoutes.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.SelectorRoutes.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
/-- info: 'Solidity.Backend.AbiEntry.SelectorRoutes.condition_in' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms condition_in
/-- info: 'Solidity.Backend.AbiEntry.SelectorRoutes.write_core' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms write_core
/-- info: 'Solidity.Backend.AbiEntry.SelectorRoutes.condition_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms condition_code
/-- info: 'Solidity.Backend.AbiEntry.SelectorRoutes.write_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms write_code
end Solidity.Backend.AbiEntry.SelectorRoutes
