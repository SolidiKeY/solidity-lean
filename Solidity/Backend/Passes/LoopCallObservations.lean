import Solidity.Backend.Passes.LoopCallApplication

/-! Complete caller/private-frame/heap/cursor/stack observations for the
actual emitted call after the loop. Orphaned objects are retained as well. -/
namespace Solidity.Backend.Passes.LoopCallObservations
open Evm Evm.Memory Evm.Compiler
open MemoryCallControls (C A initial base machine)
open LoopScopeControls
open LoopScopeTrace (preparedTarget loopTarget)
open LoopCallControls

private def okMachine : Evm.Out → Option Machine
  | .ok m 0 => some m | _ => none
noncomputable def target : Machine := (okMachine (run producer.code loopTarget)).get (by decide +kernel)
theorem target_run : run producer.code loopTarget = .ok target 0 := by
  have h : some target = okMachine (run producer.code loopTarget) := Option.some_get _
  generalize run producer.code loopTarget = value at h ⊢
  cases value with
  | ok m skip =>
    cases skip with
    | zero => exact congrArg (fun m => Evm.Out.ok m 0) (Option.some.inj h).symm
    | succ n => cases h
  | revert => cases h
  | fault => cases h

def code : List Evm.Instr := preparation.code ++ (enclosed.code ++ producer.code)
theorem whole_target : run code machine = .ok target 0 := by
  rw [code,run_append_ok LoopScopeTrace.preparation_target,
    run_append_ok LoopScopeTrace.loop_target,target_run]

theorem final_stack : target.stack = [] := by
  apply List.length_eq_zero_iff.mp
  decide +kernel

theorem whole_target_tail (tail : List Word) :
    run code {machine with stack := tail} = .ok {target with stack := tail} 0 := by
  have h := run_tail code machine tail (by rw [whole_target]; intro impossible; cases impossible)
  rw [whole_target] at h
  simpa only [appendTail,appendOut,show machine.stack = [] from rfl,final_stack,List.nil_append] using h

def addresses : List Nat := [0,127,1,2,3,4,5,6,256,257,258,259,260,261,262,263,264,265,266]
private def words (m : Machine) : Option (List Nat) :=
  (m.stack ++ addresses.map m.mem).mapM fun w => match w with
    | .val n => some n.val | .slot _ => none

theorem complete_target_vector : words {target with stack := [w[77],w[88]]} =
    some [77,88,267,99,256,0,258,262,262,262,1,7,2,0,7,0,2,33,34,1,44] := by decide +kernel

theorem skipped_call : words {loopTarget with stack := [w[77],w[88]]} ≠
    some [77,88,267,99,256,0,258,262,262,262,1,7,2,0,7,0,2,33,34,1,44] := by decide +kernel

theorem corrupt_tail : words {target with stack := [w[88],w[77]]} ≠
    some [77,88,267,99,256,0,258,262,262,262,1,7,2,0,7,0,2,33,34,1,44] := by decide +kernel

private def arrayAt {H : HTy} (hp : Heap H) (id i : Nat) : Option Int := do
  if h : H[id]? = some A then
    let value ← hp.index (⟨id,h⟩ : HRef H A) .dyn (indexValue (wmod i))
    pure value.val
  else none
private def lengthAt {H : HTy} (hp : Heap H) (id : Nat) : Option Int :=
  if h : H[id]? = some A then some (hp.len (⟨id,h⟩ : HRef H A) .dyn) else none

private def sourceVector (σ : State C Returned) : Option (List Int) := do
  let returned ← TEnv.get (.here : Idx Returned (.mem A)) σ.env
  let live ← TEnv.get (.there .here : Idx Returned (.mem A)) σ.env
  let old ← TEnv.get (.there (.there (.there .here)) : Idx Returned (.mem A)) σ.env
  let flag := TEnv.get (.there (.there .here) : Idx Returned (.val .uint)) σ.env
  let oldLength ← lengthAt σ.heap 0
  let oldValue ← arrayAt σ.heap 0 0
  let liveLength ← lengthAt σ.heap 1
  let liveFirst ← arrayAt σ.heap 1 0
  let liveSecond ← arrayAt σ.heap 1 1
  let defaultLength ← lengthAt σ.heap 2
  let returnedLength ← lengthAt σ.heap 3
  let left ← arrayAt σ.heap 3 0
  let right ← arrayAt σ.heap 3 1
  let reboundLength ← lengthAt σ.heap 4
  let reboundValue ← arrayAt σ.heap 4 0
  pure [σ.H.length,old.id,live.id,returned.id,flag.val,oldLength,oldValue,
    liveLength,liveFirst,liveSecond,defaultLength,returnedLength,left,right,reboundLength,reboundValue]

theorem complete_source_vector : sourceVector result.st =
    some [5,0,1,3,0,1,7,2,0,7,0,2,33,34,1,44] := by decide +kernel

theorem return_identity :
    (TEnv.get (.here : Idx Returned (.mem A)) result.st.env).map (·.id) = some 3 := by decide +kernel

private theorem actual_return_pointer : target.mem 4 = w[262] := by decide +kernel

/-- The actual return ID3/pointer262 forces the selected extended map; no
claim that every unused pre-call map entry had a unique value is made. -/
theorem selected_return_base {nb ob : Nat → Fin W} {next : Machine}
    (execution : run producer.code loopTarget = .ok next 0)
    (output : MappedOutput checkedCall 1 128 nb loopOut.st loopTarget result.st next ob) :
    ob 3 = wmod 262 := by
  obtain ⟨ref,henv,hptr⟩ := output.1.pointers (.here : Idx Returned (.mem A))
  have ids := congrArg (Option.map (fun ref => ref.id)) henv
  rw [return_identity] at ids
  have id : ref.id = 3 := (Option.some.inj ids).symm
  change next.mem 4 = .val (ob ref.id) at hptr
  rw [id] at hptr
  have same : next = target := (Evm.Out.ok.inj (execution.symm.trans target_run)).1
  subst next
  exact Word.val.inj (hptr.symm.trans actual_return_pointer)

def priorOnly : Nat → Fin W := fun id => if id = 0 then wmod 256 else if id = 1 then wmod 258 else wmod 0

theorem stale_return_map_refused {nb : Nat → Fin W} {next : Machine}
    (execution : run producer.code loopTarget = .ok next 0) :
    ¬ MappedOutput checkedCall 1 128 nb loopOut.st loopTarget result.st next priorOnly := by
  intro output
  have bad := congrArg Fin.val (selected_return_base execution output)
  change 0 = 262 at bad
  cases bad

end Solidity.Backend.Passes.LoopCallObservations
