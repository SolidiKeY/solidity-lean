import Solidity.Backend.AbiEntry.CoreSpecial

/-! Actual receive/fallback body execution, value rejection and incoming typed
local reads. Source fallback calldata-parameter binding remains separate. -/
namespace Solidity.Backend.AbiEntry.CoreSpecialControls
open Solidity.Evm
open Interface (DispatchBody SpecialBody)
private def C : Contract := {vars := []}
private abbrev Γ : Ctx := [.val .uint,.val .uint]
private def state (size : Fin W) : State C Γ :=
  ((freshT C 0 W_pos (wmod 0)).push (t := .val .uint) ⟨9,by decide⟩).push (t := .val .uint)
    ⟨(size.val : Int),PrimTy.inRange_uint_of_lt size.isLt⟩
private def machine (size : Fin W) : Machine :=
  {Machine.init with
    mem := fun address => if address=0 then .val (wmod 9) else if address=1 then .val size else .val (wmod 71)
    stack := [.val (wmod 258),.val (wmod 513)]}
private theorem represented (size : Fin W) : Sim C 1 0 (Frag.init Γ) (state size) (machine size) := by
  have fresh : Sim C 1 0 (Frag.init []) (freshT C 0 W_pos (wmod 0)) (Machine.init (fun _ => 0) (wmod 0)) :=
    Sim.init C 0 W_pos (fun _ => 0) (wmod 0) rfl
  refine ⟨fresh.store,?_,?_,fresh.net,fresh.netSelf,fresh.bound,?_,fresh.env,fresh.funds,fresh.oracle⟩
  · intro p index
    cases index with
    | here => exact ReprV.uint_of rfl
    | there index => cases index with
      | here => exact ReprV.uint_of rfl
      | there index => nomatch index
  · intro R index
    cases index with | there index => cases index with | there index => nomatch index
  · intro R index
    cases index with | there index => cases index with | there index => nomatch index
private abbrev Body := DispatchBody C Γ (Frag.init Γ)
private abbrev Special := SpecialBody C Γ (Frag.init Γ)
private def receiveBody : Body :=
  {outCtx := Γ,program := .cons (.assignLocal (.there .here) (.simple (.lit 11 (by decide)))) .nil
   outFrag := Frag.init Γ,admitted := by rfl}
private def fallbackBody : Body :=
  {outCtx := .val .bool::Γ
   program := .cons (.declLocal .bool (.user "argumentIsNine") (some
     (.binop .eqB rfl rfl (.simple (.local (.there .here))) (.simple (.lit 9 (by decide)))))) .nil
   outFrag := Frag.init (.val .bool::Γ),admitted := by rfl}
private def revertingBody : Body :=
  {outCtx := Γ,program := .cons .revert .nil,outFrag := Frag.init Γ,admitted := by rfl}
private def recv : Special := ⟨true,receiveBody⟩
private def fb : Special := ⟨false,fallbackBody⟩
private def whole (receive fallback : Option Special) := CoreSpecial.compiled (C := C) (Γ := Γ) 0 (Frag.init Γ) .here receive fallback
private def receiveOut (size : Fin W) : Machine := {machine size with mem := upd (machine size).mem 0 (.val (wmod 11))}
private def fallbackOut (size : Fin W) : Machine := {machine size with mem := upd (machine size).mem 2 (.val (bword true))}
private theorem actual (receive fallback : Option Special) (size : Fin W)
    (room : 1+Prog.pushes (CoreSpecial.endpoint (C := C) (Γ := Γ) (Frag.init Γ) (receive.orElse (fun _ => fallback))).program≤Lmax) :
    run (whole receive fallback).code (machine size)=run
      (compileProg 0 (CoreSpecial.endpoint (C := C) (Γ := Γ) (Frag.init Γ) (Interface.specialBodyChoice receive fallback size)).program) (machine size) :=
  CoreSpecial.executed (C := C) (Γ := Γ) 1 0 (Frag.init Γ) .here receive fallback (whole receive fallback)
    (CoreSpecial.selected (C := C) (Γ := Γ) 0 (Frag.init Γ) .here receive fallback) (state size) (machine size) (represented size) room size rfl

private theorem recvRoom : 1+Prog.pushes (CoreSpecial.endpoint (C := C) (Γ := Γ) (Frag.init Γ) (some recv)).program≤Lmax := by
  rw [CoreSpecial.endpoint_pushes]
  decide
private theorem fbRoom : 1+Prog.pushes (CoreSpecial.endpoint (C := C) (Γ := Γ) (Frag.init Γ) (some fb)).program≤Lmax := by
  rw [CoreSpecial.endpoint_pushes]
  decide
private theorem emptyRoom : 1+Prog.pushes (CoreSpecial.endpoint (C := C) (Γ := Γ) (Frag.init Γ) (none : Option Special)).program≤Lmax := by
  rw [CoreSpecial.endpoint_pushes]
  decide

private theorem fallback_code : compileProg 0 (CoreSpecial.endpoint (C := C) (Γ := Γ) (Frag.init Γ) (some fb)).program=
    [.callvalue,.push (.val (wmod 0)),.eq,.jumpi 1,.revert,.mload 0,.push (.val (wmod 9)),.eq,.mstore 2] := by rfl
private theorem fallback_run (size : Fin W) :
    run (compileProg 0 (CoreSpecial.endpoint (C := C) (Γ := Γ) (Frag.init Γ) (some fb)).program) (machine size)=
      .ok (fallbackOut size) 0 := by
  have argument : (machine size).mem 0=.val (wmod 9) := rfl
  have allowed : (false || decide ((machine size).callvalue.val=0))=true := rfl
  rw [fallback_code]
  have splitCode : ([.callvalue,.push (.val (wmod 0)),.eq,.jumpi 1,.revert,
      .mload 0,.push (.val (wmod 9)),.eq,.mstore 2] : List Evm.Instr)=
      (if (false : Bool) then [] else [.callvalue,.push (.val (wmod 0)),.eq,.jumpi 1,.revert])++
        [.mload 0,.push (.val (wmod 9)),.eq,.mstore 2] := rfl
  rw [splitCode]
  rw [ValueGateBody.composed,if_pos allowed]
  simp only [run,exec_cons_zero,Instr.step,Machine.next,Out.bind,argument]
  rfl

theorem public_selections :
    Compiler.compile 0 (Frag.init Γ) (CoreSpecial.route (C := C) (Γ := Γ) (Frag.init Γ) .here (some recv) (some fb))=some (whole (some recv) (some fb)) ∧
    Compiler.compile 0 (Frag.init Γ) (CoreSpecial.endpoint (C := C) (Γ := Γ) (Frag.init Γ) (some fb)).program=
      some (CoreDispatch.bodyCompiled (C := C) (Γ := Γ) 0 (Frag.init Γ) (CoreSpecial.endpoint (C := C) (Γ := Γ) (Frag.init Γ) (some fb))) :=
  ⟨CoreSpecial.selected (C := C) (Γ := Γ) 0 (Frag.init Γ) .here (some recv) (some fb),CoreSpecial.endpoint_selected (C := C) (Γ := Γ) 0 (Frag.init Γ) (some fb)⟩

theorem empty_prefers_receive :
    run (whole (some recv) (some fb)).code (machine (wmod 0))=.ok (receiveOut (wmod 0)) 0 := by
  exact (actual (some recv) (some fb) (wmod 0) recvRoom).trans (by rfl)

theorem empty_without_receive_uses_fallback :
    run (whole none (some fb)).code (machine (wmod 0))=.ok (fallbackOut (wmod 0)) 0 := by
  exact (actual none (some fb) (wmod 0) fbRoom).trans (fallback_run (wmod 0))

/-- Even an arbitrary unused receive body needs no representation/allocation fact on nonempty input. -/
theorem nonempty_ignores_receive (receive : Option Special) (size : Fin W) (notEmpty : size.val≠0) :
    run (whole receive (some fb)).code (machine size)=.ok (fallbackOut size) 0 := by
  exact (CoreSpecial.nonempty (C := C) (Γ := Γ) 0 (Frag.init Γ) .here receive (some fb) (whole receive (some fb))
    (CoreSpecial.selected (C := C) (Γ := Γ) 0 (Frag.init Γ) .here receive (some fb))
    (machine size) size rfl notEmpty).trans (fallback_run size)

theorem missing_fallback_rejects_nonempty : run (whole (some recv) none).code (machine (wmod 3))=.revert := by
  rw [CoreSpecial.nonempty (C := C) (Γ := Γ) 0 (Frag.init Γ) .here (some recv) none (whole (some recv) none)
    (CoreSpecial.selected (C := C) (Γ := Γ) 0 (Frag.init Γ) .here (some recv) none) (machine (wmod 3)) (wmod 3) rfl (by decide)]
  rfl

theorem absent_endpoints (size : Fin W) : run (whole none none).code (machine size)=.revert := by
  have chosen : Interface.specialBodyChoice (none : Option Special) none size=none := by
    unfold Interface.specialBodyChoice
    split <;> rfl
  have execution : run (whole none none).code (machine size)=run
      (compileProg 0 (CoreSpecial.endpoint (C := C) (Γ := Γ) (Frag.init Γ)
        (Interface.specialBodyChoice (none : Option Special) none size)).program) (machine size) :=
    actual none none size emptyRoom
  apply execution.trans
  rw [chosen,CoreSpecial.endpoint_code (C := C) (Γ := Γ)]
  rfl

private theorem whole_code (rpay fpay : Bool) :
    (whole (some ⟨rpay,receiveBody⟩) (some ⟨fpay,fallbackBody⟩)).code=
      [.mload 1,.push (.val (wmod 0)),.eq,.iszero,.jumpi ((if rpay then 0 else 5)+3)]++
      (if rpay then [] else [.callvalue,.push (.val (wmod 0)),.eq,.jumpi 1,.revert])++
      [.push (.val (wmod 11)),.mstore 0,.jump ((if fpay then 0 else 5)+4)]++
      (if fpay then [] else [.callvalue,.push (.val (wmod 0)),.eq,.jumpi 1,.revert])++
      [.mload 0,.push (.val (wmod 9)),.eq,.mstore 2] := by
  cases rpay <;> cases fpay <;> rfl

theorem payable_receive_every_value (value : Fin W) :
    run (whole (some recv) (some fb)).code {machine (wmod 0) with callvalue := value}=
      .ok {receiveOut (wmod 0) with callvalue := value} 0 := by
  simp only [recv,fb]
  rw [whole_code true false]
  simp only [List.cons_append,List.nil_append,if_true,if_false,Nat.zero_add,run,exec,
    Instr.step,Machine.next,Out.bind,machine,receiveOut,bword,wmod,Nat.zero_mod,
    decide_true,decide_false,Bool.false_eq_true,Nat.one_ne_zero]

/-- Receive value rejection is terminal even when a payable fallback would succeed. -/
theorem nonpayable_receive_terminal :
    run (whole (some ⟨false,receiveBody⟩) (some ⟨true,fallbackBody⟩)).code
      {machine (wmod 0) with callvalue := wmod 17}=.revert ∧
    run (compileProg 0 (CoreSpecial.endpoint (C := C) (Γ := Γ) (Frag.init Γ) (some ⟨true,fallbackBody⟩)).program)
      {machine (wmod 0) with callvalue := wmod 17}=.ok {fallbackOut (wmod 0) with callvalue := wmod 17} 0 :=
  by
  constructor
  · rw [whole_code false true]
    simp only [List.cons_append,List.nil_append,if_true,if_false,Nat.zero_add,run,exec,
      Instr.step,Machine.next,Out.bind,machine,bword,wmod,Nat.zero_mod,
      decide_true,decide_false,Bool.false_eq_true,Nat.one_ne_zero]
    rfl
  · have bodyCode : compileProg 0 (CoreSpecial.endpoint (C := C) (Γ := Γ) (Frag.init Γ) (some ⟨true,fallbackBody⟩)).program=
        [.mload 0,.push (.val (wmod 9)),.eq,.mstore 2] := rfl
    rw [bodyCode]
    simp only [run,exec_cons_zero,Instr.step,Machine.next,Out.bind]
    rfl

theorem nonpayable_fallback_before_argument :
    run (whole (some recv) (some fb)).code
      {machine (wmod 3) with
        callvalue := wmod 17
        mem := fun address => if address=1 then .val (wmod 3) else .slot (.root 0)}=.revert := by
  let initial : Machine := {machine (wmod 3) with
    callvalue := wmod 17
    mem := fun address => if address=1 then .val (wmod 3) else .slot (.root 0)}
  have dispatch : run (whole (some recv) (some fb)).code initial=
      run (compileProg 0 (CoreSpecial.endpoint (C := C) (Γ := Γ) (Frag.init Γ) (some fb)).program) initial :=
    CoreSpecial.nonempty (C := C) (Γ := Γ) 0 (Frag.init Γ) .here
    (some recv) (some fb) (whole (some recv) (some fb))
    (CoreSpecial.selected (C := C) (Γ := Γ) 0 (Frag.init Γ) .here (some recv) (some fb))
    initial (wmod 3) rfl (by decide)
  apply dispatch.trans
  have bodyCode : compileProg 0 (CoreSpecial.endpoint (C := C) (Γ := Γ) (Frag.init Γ) (some fb)).program=
      (if (false : Bool) then [] else [.callvalue,.push (.val (wmod 0)),.eq,.jumpi 1,.revert])++
        [.mload 0,.push (.val (wmod 9)),.eq,.mstore 2] := rfl
  rw [bodyCode,ValueGateBody.composed]
  rfl

theorem reverting_fallback : run (whole (some recv) (some ⟨true,revertingBody⟩)).code (machine (wmod 3))=.revert :=
  (CoreSpecial.nonempty (C := C) (Γ := Γ) 0 (Frag.init Γ) .here (some recv) (some ⟨true,revertingBody⟩)
    (whole (some recv) (some ⟨true,revertingBody⟩))
    (CoreSpecial.selected (C := C) (Γ := Γ) 0 (Frag.init Γ) .here (some recv) (some ⟨true,revertingBody⟩))
    (machine (wmod 3)) (wmod 3) rfl (by decide)).trans (by rfl)

theorem incoming_local_and_saved_state :
    (fallbackOut (wmod 3)).mem 0=.val (wmod 9) ∧ (fallbackOut (wmod 3)).mem 1=.val (wmod 3) ∧
    (fallbackOut (wmod 3)).mem 2=.val (bword true) ∧ (fallbackOut (wmod 3)).mem 3=.val (wmod 71) ∧
    (fallbackOut (wmod 3)).stack=[.val (wmod 258),.val (wmod 513)] ∧
    (fallbackOut (wmod 3)).store=(machine (wmod 3)).store ∧ (fallbackOut (wmod 3)).bal=(machine (wmod 3)).bal :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.AbiEntry.CoreSpecialControls.public_selections' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms public_selections
/-- info: 'Solidity.Backend.AbiEntry.CoreSpecialControls.empty_prefers_receive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_prefers_receive
/-- info: 'Solidity.Backend.AbiEntry.CoreSpecialControls.empty_without_receive_uses_fallback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_without_receive_uses_fallback
/-- info: 'Solidity.Backend.AbiEntry.CoreSpecialControls.nonempty_ignores_receive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonempty_ignores_receive
/-- info: 'Solidity.Backend.AbiEntry.CoreSpecialControls.missing_fallback_rejects_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms missing_fallback_rejects_nonempty
/-- info: 'Solidity.Backend.AbiEntry.CoreSpecialControls.absent_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms absent_endpoints
/-- info: 'Solidity.Backend.AbiEntry.CoreSpecialControls.payable_receive_every_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms payable_receive_every_value
/-- info: 'Solidity.Backend.AbiEntry.CoreSpecialControls.nonpayable_receive_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonpayable_receive_terminal
/-- info: 'Solidity.Backend.AbiEntry.CoreSpecialControls.nonpayable_fallback_before_argument' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonpayable_fallback_before_argument
/-- info: 'Solidity.Backend.AbiEntry.CoreSpecialControls.reverting_fallback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reverting_fallback
/-- info: 'Solidity.Backend.AbiEntry.CoreSpecialControls.incoming_local_and_saved_state' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms incoming_local_and_saved_state
end Solidity.Backend.AbiEntry.CoreSpecialControls
