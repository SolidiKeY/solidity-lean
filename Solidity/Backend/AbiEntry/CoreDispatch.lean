import Solidity.Backend.AbiEntry.CoreDispatchInterface

/-! Finite first-match dispatch is nested existing typed conditionals. Actual
body code comes from the public compiler; its execution is never supplied.
Represented input and allocation bounds are those of the existing compiler. -/
namespace Solidity.Backend.AbiEntry.CoreDispatch
open Solidity.Evm
open Interface (DispatchBody DispatchRow dispatchTarget)
variable {C : Contract} {Γ : Ctx}

def route (frag : Frag Γ) (index : Idx Γ (.val .uint))
    (rows : List (DispatchRow C Γ frag)) (fallback : DispatchBody C Γ frag) : Prog C Γ Γ :=
  match rows with
  | [] => .cons (.block fallback.program) .nil
  | row::rest => SelectorBranches.program index row.tag row.target.program (route frag index rest fallback)

def outputFrag (frag : Frag Γ) (rows : List (DispatchRow C Γ frag)) (fallback : DispatchBody C Γ frag) : Frag Γ :=
  match rows with
  | [] => fallback.outFrag.restrict Γ
  | row::rest => (row.target.outFrag.restrict Γ).meet ((outputFrag frag rest fallback).restrict Γ)

theorem admitted (frag : Frag Γ) (index : Idx Γ (.val .uint))
    (rows : List (DispatchRow C Γ frag)) (fallback : DispatchBody C Γ frag) :
    inFragP frag (route frag index rows fallback)=some (outputFrag frag rows fallback) := by
  induction rows with
  | nil =>
    simp only [route,outputFrag,inFragP,inFrag,fallback.admitted,Option.map_some]
  | cons row rest ih =>
    exact SelectorBranches.admitted frag index row.tag row.target.program (route frag index rest fallback)
      row.target.outFrag (outputFrag frag rest fallback) row.target.admitted ih

def compiled (base : Nat) (frag : Frag Γ) (index : Idx Γ (.val .uint))
    (rows : List (DispatchRow C Γ frag)) (fallback : DispatchBody C Γ frag) :
    Compiler.Compilation base frag (route frag index rows fallback) :=
  .core (outputFrag frag rows fallback) (admitted frag index rows fallback)

def bodyCompiled (base : Nat) (frag : Frag Γ) (target : DispatchBody C Γ frag) :
    Compiler.Compilation base frag target.program :=
  CoreJoin.compiled base frag target.program target.outFrag target.admitted

theorem selected (base : Nat) (frag : Frag Γ) (index : Idx Γ (.val .uint))
    (rows : List (DispatchRow C Γ frag)) (fallback : DispatchBody C Γ frag) :
    Compiler.compile base frag (route frag index rows fallback)=some (compiled base frag index rows fallback) :=
  ValueGateBody.body_selected base frag _ _ (admitted frag index rows fallback)

theorem body_selected (base : Nat) (frag : Frag Γ) (target : DispatchBody C Γ frag) :
    Compiler.compile base frag target.program=some (bodyCompiled base frag target) :=
  CoreJoin.selected base frag target.program target.outFrag target.admitted

/-- Establish the whole intrinsic target before projecting its context-indexed body. -/
theorem target_hit (frag : Frag Γ) (row : DispatchRow C Γ frag) (rest : List (DispatchRow C Γ frag))
    (fallback : DispatchBody C Γ frag) (selector : Fin W) (matched : row.tag.val=selector.val) :
    dispatchTarget (row::rest) fallback selector=row.target := by
  simp only [dispatchTarget,List.find?_cons,decide_eq_true matched,Option.map_some,Option.getD_some]

theorem target_miss (frag : Frag Γ) (row : DispatchRow C Γ frag) (rest : List (DispatchRow C Γ frag))
    (fallback : DispatchBody C Γ frag) (selector : Fin W) (missed : row.tag.val≠selector.val) :
    dispatchTarget (row::rest) fallback selector=dispatchTarget rest fallback selector := by
  simp only [dispatchTarget,List.find?_cons,decide_eq_false missed]

theorem run_route (L base : Nat) (frag : Frag Γ) (index : Idx Γ (.val .uint))
    (rows : List (DispatchRow C Γ frag)) (fallback : DispatchBody C Γ frag)
    (state : State C Γ) (machine : Machine) (represented : Sim C L base frag state machine)
    (room : ∀ row ∈ rows, L+Prog.pushes row.target.program≤Lmax)
    (selector : Fin W) (initial : machine.mem (cellOf base index)=.val selector) :
    run (compiled base frag index rows fallback).code machine=
      run (compileProg base (dispatchTarget rows fallback selector).program) machine := by
  revert room
  induction rows with
  | nil =>
    intro _
    change run (compileProg base fallback.program++[]) machine=run (compileProg base fallback.program) machine
    rw [List.append_nil]
  | cons row rest ih =>
    intro room
    have rowRoom : L+Prog.pushes row.target.program≤Lmax := room row List.mem_cons_self
    have tailRoom : ∀ next ∈ rest, L+Prog.pushes next.target.program≤Lmax :=
      fun next member => room next (List.mem_cons_of_mem _ member)
    have step : run (compiled base frag index (row::rest) fallback).code machine=
        if row.tag.val=selector.val then run (bodyCompiled base frag row.target).code machine else
          run (compiled base frag index rest fallback).code machine :=
      CoreJoin.branch_outcome L base frag index row.tag row.target.program (route frag index rest fallback)
        row.target.outFrag (outputFrag frag rest fallback) row.target.admitted (admitted frag index rest fallback)
        (compiled base frag index (row::rest) fallback) (bodyCompiled base frag row.target)
        (compiled base frag index rest fallback) (selected base frag index (row::rest) fallback)
        (body_selected base frag row.target) (selected base frag index rest fallback)
        state machine represented rowRoom selector initial
    rw [step]
    by_cases matched : row.tag.val=selector.val
    · rw [ite_eq_left matched,target_hit frag row rest fallback selector matched]
      rfl
    · rw [ite_eq_right matched,target_miss frag row rest fallback selector matched]
      exact ih tailRoom

theorem executed (L base : Nat) (frag : Frag Γ) (index : Idx Γ (.val .uint))
    (rows : List (DispatchRow C Γ frag)) (fallback : DispatchBody C Γ frag)
    (result : Compiler.Compilation base frag (route frag index rows fallback))
    (found : Compiler.compile base frag (route frag index rows fallback)=some result)
    (state : State C Γ) (machine : Machine) (represented : Sim C L base frag state machine)
    (room : ∀ row ∈ rows, L+Prog.pushes row.target.program≤Lmax)
    (selector : Fin W) (initial : machine.mem (cellOf base index)=.val selector) :
    run result.code machine=run (compileProg base (dispatchTarget rows fallback selector).program) machine := by
  have same : result=compiled base frag index rows fallback := Option.some.inj (found.symm.trans (selected base frag index rows fallback))
  rw [same]
  exact run_route L base frag index rows fallback state machine represented room selector initial

def certificate : Interface.CoreDispatchCertificate route where
  bodies_selected := fun base frag target => ⟨bodyCompiled base frag target,body_selected base frag target,rfl⟩
  selected := fun base frag index rows fallback => ⟨compiled base frag index rows fallback,selected base frag index rows fallback⟩
  executed := executed

/-- info: 'Solidity.Backend.AbiEntry.CoreDispatch.admitted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.CoreDispatch.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.CoreDispatch.body_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms body_selected
/-- info: 'Solidity.Backend.AbiEntry.CoreDispatch.target_hit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms target_hit
/-- info: 'Solidity.Backend.AbiEntry.CoreDispatch.target_miss' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms target_miss
/-- info: 'Solidity.Backend.AbiEntry.CoreDispatch.run_route' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_route
/-- info: 'Solidity.Backend.AbiEntry.CoreDispatch.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.CoreDispatch.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.CoreDispatch
