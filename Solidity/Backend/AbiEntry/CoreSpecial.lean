import Solidity.Backend.AbiEntry.CoreSpecialInterface

/-! Actual typed receive/fallback continuations reuse finite dispatch on the
size local and the existing value guard. No endpoint run or result is assumed. -/
namespace Solidity.Backend.AbiEntry.CoreSpecial
open Solidity.Evm
open Interface (DispatchBody DispatchRow SpecialBody specialBodyChoice dispatchTarget)
variable {C : Contract} {Γ : Ctx}

def endpoint (frag : Frag Γ) : Option (SpecialBody C Γ frag) → DispatchBody C Γ frag
  | none => ⟨Γ,.cons .revert .nil,frag,rfl⟩
  | some target => ⟨target.body.outCtx,ValueGateBody.guard target.payable target.body.program,target.body.outFrag,
      ValueGateBody.admitted frag target.body.program target.payable target.body.outFrag target.body.admitted⟩

def rows (frag : Frag Γ) (receive fallback : Option (SpecialBody C Γ frag)) : List (DispatchRow C Γ frag) :=
  [⟨wmod 0,endpoint frag (receive.orElse (fun _ => fallback))⟩]

def route (frag : Frag Γ) (index : Idx Γ (.val .uint)) (receive fallback : Option (SpecialBody C Γ frag)) : Prog C Γ Γ :=
  CoreDispatch.route frag index (rows frag receive fallback) (endpoint frag fallback)

def compiled (base : Nat) (frag : Frag Γ) (index : Idx Γ (.val .uint)) (receive fallback : Option (SpecialBody C Γ frag)) :
    Compiler.Compilation base frag (route frag index receive fallback) :=
  CoreDispatch.compiled base frag index (rows frag receive fallback) (endpoint frag fallback)

theorem selected (base : Nat) (frag : Frag Γ) (index : Idx Γ (.val .uint)) (receive fallback : Option (SpecialBody C Γ frag)) :
    Compiler.compile base frag (route frag index receive fallback)=some (compiled base frag index receive fallback) :=
  CoreDispatch.selected base frag index (rows frag receive fallback) (endpoint frag fallback)

theorem endpoint_selected (base : Nat) (frag : Frag Γ) (row : Option (SpecialBody C Γ frag)) :
    Compiler.compile base frag (endpoint frag row).program=some (CoreDispatch.bodyCompiled base frag (endpoint frag row)) :=
  CoreDispatch.body_selected base frag (endpoint frag row)

theorem endpoint_code (base : Nat) (frag : Frag Γ) (row : Option (SpecialBody C Γ frag)) :
    compileProg base (endpoint frag row).program=match row with
      | none => [.revert]
      | some target => compileProg base (ValueGateBody.guard target.payable target.body.program) := by
  cases row <;> rfl

theorem endpoint_pushes (frag : Frag Γ) (row : Option (SpecialBody C Γ frag)) :
    Prog.pushes (endpoint frag row).program=match row with
      | none => 0
      | some target => Prog.pushes target.body.program := by
  cases row with
  | none => rfl
  | some target =>
    change Prog.pushes (ValueGateBody.guard target.payable target.body.program)=Prog.pushes target.body.program
    cases target.payable with
    | false => exact Nat.zero_add _
    | true => rfl

theorem target_choice (frag : Frag Γ) (receive fallback : Option (SpecialBody C Γ frag)) (size : Fin W) :
    dispatchTarget (rows frag receive fallback) (endpoint frag fallback) size=
      endpoint frag (specialBodyChoice receive fallback size) := by
  by_cases empty : size.val=0
  · rw [specialBodyChoice,if_pos empty]
    have hit : (wmod 0).val=size.val := empty.symm
    exact CoreDispatch.target_hit frag _ [] (endpoint frag fallback) size hit
  · rw [specialBodyChoice,if_neg empty]
    have missed : (wmod 0).val≠size.val := fun impossible => empty impossible.symm
    change dispatchTarget [⟨wmod 0,endpoint frag (receive.orElse (fun _ => fallback))⟩] (endpoint frag fallback) size=_
    rw [CoreDispatch.target_miss frag _ [] (endpoint frag fallback) size missed]
    rfl

theorem executed (L base : Nat) (frag : Frag Γ) (index : Idx Γ (.val .uint))
    (receive fallback : Option (SpecialBody C Γ frag))
    (result : Compiler.Compilation base frag (route frag index receive fallback))
    (found : Compiler.compile base frag (route frag index receive fallback)=some result)
    (state : State C Γ) (machine : Machine) (represented : Sim C L base frag state machine)
    (room : L+Prog.pushes (endpoint frag (receive.orElse (fun _ => fallback))).program≤Lmax)
    (size : Fin W) (initial : machine.mem (cellOf base index)=.val size) :
    run result.code machine=run (compileProg base (endpoint frag (specialBodyChoice receive fallback size)).program) machine := by
  have rowsRoom : ∀ row ∈ rows frag receive fallback,L+Prog.pushes row.target.program≤Lmax := by
    intro row member
    have same : row=⟨wmod 0,endpoint frag (receive.orElse (fun _ => fallback))⟩ := List.mem_singleton.mp member
    subst row
    exact room
  rw [CoreDispatch.executed L base frag index (rows frag receive fallback) (endpoint frag fallback) result found
    state machine represented rowsRoom size initial,target_choice]

/-- Nonempty input reaches the fallback body without any receive representation/resource premise. -/
theorem nonempty (base : Nat) (frag : Frag Γ) (index : Idx Γ (.val .uint))
    (receive fallback : Option (SpecialBody C Γ frag))
    (result : Compiler.Compilation base frag (route frag index receive fallback))
    (found : Compiler.compile base frag (route frag index receive fallback)=some result)
    (machine : Machine) (size : Fin W) (initial : machine.mem (cellOf base index)=.val size) (notEmpty : size.val≠0) :
    run result.code machine=run (compileProg base (endpoint frag fallback).program) machine := by
  have same : result=compiled base frag index receive fallback := Option.some.inj (found.symm.trans (selected base frag index receive fallback))
  rw [same]
  have step : run (compiled base frag index receive fallback).code machine=
      if (wmod 0).val=size.val then
        run ((CoreDispatch.bodyCompiled base frag (endpoint frag (receive.orElse (fun _ => fallback)))).code++
          [.jump (CoreDispatch.compiled base frag index [] (endpoint frag fallback)).code.length]++
          (CoreDispatch.compiled base frag index [] (endpoint frag fallback)).code) machine
      else run (CoreDispatch.compiled base frag index [] (endpoint frag fallback)).code machine :=
    SelectorBranches.executed base frag index (wmod 0) (endpoint frag (receive.orElse (fun _ => fallback))).program
      (CoreDispatch.route frag index [] (endpoint frag fallback))
      (endpoint frag (receive.orElse (fun _ => fallback))).outFrag (CoreDispatch.outputFrag frag [] (endpoint frag fallback))
      (endpoint frag (receive.orElse (fun _ => fallback))).admitted (CoreDispatch.admitted frag index [] (endpoint frag fallback))
      (compiled base frag index receive fallback) (CoreDispatch.bodyCompiled base frag (endpoint frag (receive.orElse (fun _ => fallback))))
      (CoreDispatch.compiled base frag index [] (endpoint frag fallback)) (selected base frag index receive fallback)
      (CoreDispatch.body_selected base frag (endpoint frag (receive.orElse (fun _ => fallback))))
      (CoreDispatch.selected base frag index [] (endpoint frag fallback)) machine size initial
  have missed : (wmod 0).val≠size.val := fun impossible => notEmpty impossible.symm
  rw [step,if_neg missed]
  change run (compileProg base (endpoint frag fallback).program++[]) machine=_
  rw [List.append_nil]

def certificate : Interface.CoreSpecialCertificate endpoint route where
  endpoint_code := endpoint_code
  selected := fun base frag index receive fallback => ⟨compiled base frag index receive fallback,selected base frag index receive fallback⟩
  executed := executed

/-- info: 'Solidity.Backend.AbiEntry.CoreSpecial.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.CoreSpecial.endpoint_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms endpoint_selected
/-- info: 'Solidity.Backend.AbiEntry.CoreSpecial.endpoint_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms endpoint_code
/-- info: 'Solidity.Backend.AbiEntry.CoreSpecial.endpoint_pushes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms endpoint_pushes
/-- info: 'Solidity.Backend.AbiEntry.CoreSpecial.target_choice' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms target_choice
/-- info: 'Solidity.Backend.AbiEntry.CoreSpecial.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.CoreSpecial.nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonempty
/-- info: 'Solidity.Backend.AbiEntry.CoreSpecial.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.CoreSpecial
