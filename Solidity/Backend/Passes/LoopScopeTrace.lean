import Solidity.Backend.Passes.LoopScopeObservations

/-! Kernel finite-turn witnesses for the ACTUAL emitted loop. These use the
published loopIterN/loopRun_of_iterN semantics; no native evaluation of looping
semantics or alternate interpreter supplies the observation vectors. -/
namespace Solidity.Backend.Passes.LoopScopeTrace
open Evm Evm.Memory Evm.Compiler
open MemoryCallControls (C A initial base machine)
open LoopScopeControls

private def okMachine : Evm.Out → Option Machine
  | .ok m 0 => some m
  | _ => none
private theorem machine_get {out : Evm.Out} {m : Machine} (h : some m = okMachine out) :
    out = .ok m 0 := by
  cases out with
  | ok actual skip =>
    cases skip with
    | zero => exact congrArg (fun m => Evm.Out.ok m 0) (Option.some.inj h).symm
    | succ k => cases h
  | revert => cases h
  | fault => cases h

noncomputable def preparedTarget : Machine :=
  (okMachine (run preparation.code machine)).get (by decide +kernel)
theorem preparation_target : run preparation.code machine = .ok preparedTarget 0 :=
  machine_get (Option.some_get _)

private def finished : Machine ⊕ Evm.Out → Option Evm.Out
  | .inr result => some result
  | .inl _ => none

noncomputable def terminal : Evm.Out :=
  (finished (loopIterN (run conditionCompiled.code) (run bodyCompiled.code) 2 preparedTarget)).get
    (by decide +kernel)

theorem two_turns : loopIterN (run conditionCompiled.code) (run bodyCompiled.code) 2 preparedTarget =
    .inr terminal := by
  have h : some terminal = finished
      (loopIterN (run conditionCompiled.code) (run bodyCompiled.code) 2 preparedTarget) := Option.some_get _
  generalize hx : loopIterN (run conditionCompiled.code) (run bodyCompiled.code) 2 preparedTarget = result at h ⊢
  cases result with
  | inl m => cases h
  | inr actual => exact congrArg Sum.inr (Option.some.inj h).symm

noncomputable def loopTarget : Machine := (okMachine terminal).get (by decide +kernel)
theorem terminal_ok : terminal = .ok loopTarget 0 := machine_get (Option.some_get _)

theorem emitted_loop : enclosed.code = [.loop conditionCompiled.code bodyCompiled.code] := rfl

theorem loop_target : run enclosed.code preparedTarget = .ok loopTarget 0 := by
  rw [emitted_loop]
  change (loopRun (run conditionCompiled.code) (run bodyCompiled.code) preparedTarget).bind
    (fun m k => .ok m k) = .ok loopTarget 0
  rw [loopRun_of_iterN two_turns,terminal_ok]
  rfl

noncomputable def finalTarget : Machine :=
  (okMachine (run suffix.code loopTarget)).get (by decide +kernel)
theorem suffix_target : run suffix.code loopTarget = .ok finalTarget 0 := machine_get (Option.some_get _)

def code : List Evm.Instr := preparation.code ++ (enclosed.code ++ suffix.code)
theorem whole_target : run code machine = .ok finalTarget 0 := by
  rw [code,run_append_ok preparation_target,run_append_ok loop_target,suffix_target]

theorem final_stack : finalTarget.stack = [] := by
  apply List.length_eq_zero_iff.mp
  decide +kernel

/-- Only the SUCCESSFUL actual emitted run uses raw saved-tail transport.
Fault/divergence continue to require the independent typed Input law. -/
theorem whole_target_tail (tail : List Word) :
    run code {machine with stack := tail} = .ok {finalTarget with stack := tail} 0 := by
  have h := run_tail code machine tail (by rw [whole_target]; intro impossible; cases impossible)
  rw [whole_target] at h
  simpa only [appendTail,appendOut,show machine.stack = [] from rfl,final_stack,List.nil_append] using h

private def words (m : Machine) (addresses : List Nat) : Option (List Nat) :=
  (m.stack ++ addresses.map m.mem).mapM fun w => match w with
    | .val value => some value.val
    | .slot _ => none

def addresses : List Nat := [0,127,1,2,3,4,256,257,258,259,260]

theorem preparation_vector : words {preparedTarget with stack := [w[77],w[88]]} addresses =
    some [77,88,258,99,256,42,256,0,1,7,0,0,0] := by decide +kernel
theorem loop_vector : words {loopTarget with stack := [w[77],w[88]]} addresses =
    some [77,88,261,99,256,0,258,258,1,7,2,0,0] := by decide +kernel
theorem final_vector : words {finalTarget with stack := [w[77],w[88]]} addresses =
    some [77,88,261,99,256,0,258,0,1,8,2,9,0] := by decide +kernel

theorem corrupt_tail : words {finalTarget with stack := [w[88],w[77]]} addresses ≠
    some [77,88,261,99,256,0,258,0,1,8,2,9,0] := by decide +kernel

private def cell (out : Evm.Out) (address : Nat) : Option Nat :=
  match out with
  | .ok m _ => match m.mem address with | .val value => some value.val | _ => none
  | _ => none

theorem actual_cursor : cell (run enclosed.code preparedTarget) 0 = some 261 := by
  rw [loop_target]
  decide +kernel

theorem new_identity :
    (TEnv.get (.here : Idx LoopScopeControls.Γ (.mem A)) loopOut.st.env).map (·.id) = some 1 := by
  decide +kernel
private theorem actual_pointer : cell (run enclosed.code preparedTarget) 3 = some 258 := by
  rw [loop_target]
  decide +kernel

/-- The ACTUAL emitted loop forces the newly reached reference's selected
base, while retaining the complete indexed cost and representation relation. -/
theorem selected_new_base {mb nb : Nat → Fin W} {next : Machine}
    (execution : run enclosed.code preparedTarget = .ok next 0)
    (output : MappedOutput checked 1 128 mb prepared.st preparedTarget loopOut.st next nb) :
    nb 1 = wmod 258 := by
  rcases output with ⟨amount,ext,hcost,state,hbase,hgrowth⟩
  obtain ⟨ref,henv,hptr⟩ := state.pointers (.here : Idx LoopScopeControls.Γ (.mem A))
  have ids := congrArg (Option.map (fun ref => ref.id)) henv
  rw [new_identity] at ids
  have id : ref.id = 1 := (Option.some.inj ids).symm
  change next.mem 3 = .val (nb ref.id) at hptr
  rw [id] at hptr
  have observed := actual_pointer
  rw [execution] at observed
  change (match next.mem 3 with | .val value => some value.val | _ => none) = some 258 at observed
  rw [hptr] at observed
  apply Fin.ext
  exact Option.some.inj observed

def oldOnly : Nat → Fin W := fun id => if id = 0 then wmod 256 else wmod 0

theorem stale_map_refused {mb : Nat → Fin W} {next : Machine}
    (execution : run enclosed.code preparedTarget = .ok next 0) :
    ¬ MappedOutput checked 1 128 mb prepared.st preparedTarget loopOut.st next oldOnly := by
  intro output
  have bad := congrArg Fin.val (selected_new_base execution output)
  change 0 = 258 at bad
  cases bad

end Solidity.Backend.Passes.LoopScopeTrace
