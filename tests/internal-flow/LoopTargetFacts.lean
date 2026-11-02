import tests.«internal-flow».LoopLocalFrameChecks
import Solidity.Backend.InternalFlow.LoopLocalTarget
import Solidity.Backend.InternalFlow.StoragePrefixFrame
import Solidity.Evm.Compiler
import Solidity.Syntax.Splice
namespace Solidity.Backend.InternalFlow.LoopTargetChecks
open Evm Evm.Memory PublishedDirectCalls
open Controls (contract arrayType)
abbrev C := contract
local instance : InContract := ⟨C⟩
abbrev Caller := AllocationFrameChecks.CallerCtx
abbrev Turn := LoopLocalChecks.Iteration

def initial : State C [] :=
  {State.init C with tx := LoopLocalChecks.initial.tx, selfBalance := LoopLocalChecks.initial.selfBalance}
def bases : Nat → Fin W := fun _ => wmod 0
def machine : Evm.Machine :=
  {stack := [Evm.Word.val (wmod 77)],store := WordStore.zero,
    bal := fun _ => 11,bal₀ := fun _ => 11,self := wmod 9,
    caller := wmod 9,callvalue := wmod 7,timestamp := wmod 11,
    mem := fun a => if a = 0 then Evm.Word.val (wmod 256)
      else if a = 127 then Evm.Word.val (wmod 99) else Evm.Word.val (wmod 0)}
theorem noRef {R : RefTy} (r : HRef [] R) : False := by cases r.get?

theorem initial_repr : StateRepr 1 1 128 (Frag.init []) initial bases machine ∧
    StructAllocatorRepr initial.heap bases 128 (wmod 256) machine := by
  have hh : HeapRepr initial.heap bases 128 machine :=
    ⟨fun r => (noRef r).elim,fun r => (noRef r).elim,fun r => (noRef r).elim⟩
  have hs : StructHeapRepr initial.heap bases 128 machine :=
    ⟨fun r => (noRef r).elim,fun r => (noRef r).elim,fun r => (noRef r).elim⟩
  have hx : StructArraySeparated initial.heap bases := fun _ r => (noRef r).elim
  have hc := Sim.init C 11 (by decide +kernel) (fun _ => 11) (wmod 9) rfl
  refine ⟨⟨?_,hh,?_,by decide,hs,hx,?_⟩,⟨⟨hh,?_,fun r => (noRef r).elim⟩,hs,hx,fun r => (noRef r).elim⟩⟩
  · refine ⟨hc.store,?_,?_,hc.net,hc.netSelf,hc.bound,?_,?_,?_,?_⟩
    · intro p i; nomatch i
    · intro R i; nomatch i
    · intro R i; nomatch i
    · unfold EnvSim; decide +kernel
    · rfl
    · intro addr amt x y hx hy; rfl
  · intro R i; nomatch i
  · intro s f R r hf; exact (noRef r).elim
  · refine ⟨by decide,by decide,rfl,?_⟩
    intro a ha
    change 256 ≤ a at ha
    simp only [machine]
    split <;> rename_i he
    · omega
    · split <;> rename_i he
      · omega
      · rfl

private theorem actual_get {α : Type} (result : TRes α) (h : result.toOption.isSome = true) :
    result = .ok (result.toOption.get h) := by
  cases result with
  | error e => cases h
  | ok value => rfl

def storagePrefix : Prog C [] [] := (sol{
  p = 7; t = 9; a.push(13); a.push(17);
} : Prog C [] [])
def stored : Solidity.Out C [] [] := (storagePrefix.run initial).toOption.get (by decide +kernel)
def storageCode : List Evm.Instr := Evm.compileProg 1 storagePrefix
theorem actual_storage : storagePrefix.run initial = .ok stored := actual_get _ (by decide +kernel)

def memoryPrefix : Prog C [] Caller := (sol{
  uint protectedOuter = 17; uint count = 9;
  uint[] memory old = new uint[](2); old[0] = 7; old[1] = 11;
  uint[] memory same = old;
} : Prog C [] Caller)
def before : Calls.Program 1 (Frag.init []) memoryPrefix :=
  (Calls.compile 1 (Frag.init []) memoryPrefix).get (by decide +kernel)
attribute [irreducible] before

def caller : Solidity.Out C stored.st.H Caller := (memoryPrefix.run stored.st).toOption.get (by decide +kernel)
theorem actual_memory : memoryPrefix.run stored.st = .ok caller := actual_get _ (by decide +kernel)


def bodyCompiled : Memory.CompiledProg 1 before.frag LoopLocalChecks.body :=
  (Memory.compileProg 1 before.frag LoopLocalChecks.body).get (by decide +kernel)
def conditionCompiled : CompiledVal 1 before.frag LoopLocalChecks.condition :=
  (Memory.compileVal 1 before.frag LoopLocalChecks.condition).get (by decide +kernel)
def cert : LoopCert 1 before.frag LoopLocalChecks.condition LoopLocalChecks.body
    conditionCompiled.code bodyCompiled.code :=
  ⟨conditionCompiled.cert,bodyCompiled.frag,bodyCompiled.cert,by decide +kernel⟩
theorem condition_selected : Memory.compileVal 1 before.frag LoopLocalChecks.condition = some conditionCompiled :=
  (Option.some_get (by decide +kernel)).symm
theorem body_selected : Memory.compileProg 1 before.frag LoopLocalChecks.body = some bodyCompiled :=
  (Option.some_get (by decide +kernel)).symm
theorem body_stable : bodyCompiled.frag.restrict Caller = before.frag := by decide +kernel

def selected : Loops.CompiledStmt 1 before.frag
    (.loop .auto LoopLocalChecks.condition LoopLocalChecks.body) :=
  ⟨before.frag,[.loop conditionCompiled.code bodyCompiled.code],
    .loop .auto LoopLocalChecks.condition LoopLocalChecks.body conditionCompiled.code bodyCompiled.code
      bodyCompiled.frag conditionCompiled.cert bodyCompiled.cert body_stable⟩
theorem selector_code : selected.code = [.loop conditionCompiled.code bodyCompiled.code] := rfl

theorem public_selected : Loops.compileStmt 1 before.frag
    (.loop .auto LoopLocalChecks.condition LoopLocalChecks.body) = some selected :=
  LoopLocalTarget.compile_loop_equation .auto conditionCompiled condition_selected bodyCompiled body_selected body_stable

theorem storage_reached : ∃ m, run storageCode machine = .ok m 0 ∧
    StateRepr 3 1 128 (Frag.init []) stored.st bases m ∧
    StructAllocatorRepr stored.st.heap bases 128 (wmod 256) m ∧ m.stack = machine.stack :=
  LoopLocalTarget.storage_prefix initial_repr.1 initial_repr.2 rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) stored actual_storage

private def resultEq {α : Type} [DecidableEq α] : DecidableEq (TRes α)
  | .ok a,.ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a,.error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _,.error _ => isFalse (by intro h; cases h)
  | .error _,.ok _ => isFalse (by intro h; cases h)
local instance {α : Type} [DecidableEq α] : DecidableEq (TRes α) := resultEq

def start : Solidity.Out C caller.st.H Caller := ⟨caller.st,List.prefix_refl _⟩
def firstBody : Solidity.Out C caller.st.H Turn :=
  (LoopLocalChecks.body.runR caller.st).toOption.get (by decide +kernel)
def first : Solidity.Out C caller.st.H Caller := ⟨firstBody.st.drop LoopLocalChecks.body.ext,firstBody.ext⟩
def secondBody : Solidity.Out C first.st.H Turn :=
  (LoopLocalChecks.body.runR first.st).toOption.get (by decide +kernel)
def finalOut : Solidity.Out C caller.st.H Caller :=
  ⟨secondBody.st.drop LoopLocalChecks.body.ext,first.ext.trans secondBody.ext⟩
theorem first_run : LoopLocalChecks.body.runR caller.st = .ok firstBody := actual_get _ (by decide +kernel)
theorem second_run : LoopLocalChecks.body.runR first.st = .ok secondBody := actual_get _ (by decide +kernel)
theorem conditions : LoopLocalChecks.condition.evalT start.st = .ok true ∧
    LoopLocalChecks.condition.evalT first.st = .ok true ∧
    LoopLocalChecks.condition.evalT finalOut.st = .ok false := by decide +kernel

theorem source_horizon : TLoop.iterN (scopedLoopBody LoopLocalChecks.body)
    (fun o => LoopLocalChecks.condition.evalT o.st) 3 start = .inr (.ok finalOut) := by
  have hs0 : scopedLoopBody LoopLocalChecks.body start = .ok first := by
    unfold scopedLoopBody
    change (LoopLocalChecks.body.runR caller.st).map _ = _
    rw [first_run]
    rfl
  have hs1 : scopedLoopBody LoopLocalChecks.body first = .ok finalOut := by
    unfold scopedLoopBody
    rw [second_run]
    rfl
  simp only [TLoop.iterN,TLoop.step,conditions.1,hs0,conditions.2.1,hs1,conditions.2.2]

theorem source_run : (Stmt.loop .auto LoopLocalChecks.condition LoopLocalChecks.body).run caller.st = .ok finalOut :=
  TLoop.run_of_iterN source_horizon

def observe (out : Solidity.Out C caller.st.H Caller) : LoopLocalChecks.Observation :=
  let array := (out.st.storage.get (f := "a") (T := .ref arrayType) rfl).view
  ⟨out.st.H.length,out.st.env.1.map HRef.id,out.st.env.2.1.map HRef.id,
    AllocationFrameChecks.contents out.st .here,AllocationFrameChecks.contents out.st (.there .here),
    out.st.env.2.2.1.1,out.st.env.2.2.2.1.1,
    (out.st.storage.get Controls.persistent.declared).view.1,
    (out.st.storage.get Controls.transient.declared).view.1,
    array.n,array.elems.toList.map (fun v => v.view.1),out.st.tx.msgSender.1,out.st.tx.msgValue.1,out.st.selfBalance.1⟩
theorem source_vectors : (observe start,observe first,observe finalOut) =
    (LoopLocalChecks.zeroObservation,LoopLocalChecks.oneObservation,LoopLocalChecks.twoObservation) := by decide +kernel

theorem allocation_costs :
    (allocationCostProg LoopLocalChecks.body caller.st,allocationCostProg LoopLocalChecks.body first.st) = (2,2) := by decide +kernel
theorem before_cost : before.cost stored.st = 3 := by decide +kernel
theorem before_frame : 1 + before.need ≤ 128 := by decide +kernel
theorem body_frame : 1 + frameNeedProg LoopLocalChecks.body ≤ 128 := by decide +kernel

theorem prefix_capacity (tail : Nat) (room : 256 + (3 + tail) < W) :
    ∃ m base, run (storageCode ++ before.code) machine = .ok m 0 ∧
      StateRepr 3 1 128 before.frag caller.st base m ∧ m.stack = machine.stack ∧
      AllocationInput 1 128 tail caller.st base m := by
  obtain ⟨m0,hs,repr,alloc,stack⟩ := storage_reached
  have capacity : AllocationInput 1 128 (before.cost stored.st + tail) stored.st bases m0 :=
    .inr ⟨by decide,wmod 256,alloc,by simpa only [before_cost,show (wmod 256).val = 256 from by decide +kernel] using room⟩
  obtain ⟨m,base,ht,hr,hk,he,hg⟩ := PublishedDirectCalls.program_endpoint
    (C := C) (b := 1) (L := 3) (frame := 128) (σ := stored.st) (base := bases) (m := m0)
    before repr before_frame (capacity.of_le (Nat.le_add_right _ _)) caller actual_memory
  refine ⟨m,base,?_,hr,hk.trans stack,hg.nextInput capacity⟩
  rw [run_append_ok hs]
  exact ht

theorem reached_room {base : Nat → Fin W} {m : Evm.Machine}
    (input : AllocationInput 1 128 4 caller.st base m) :
    LoopRoom 1 128 LoopLocalChecks.condition LoopLocalChecks.body caller.st base m := by
  apply LoopLocalTarget.room_two_turns LoopLocalChecks.condition LoopLocalChecks.body caller.st
    firstBody secondBody first_run second_run conditions.2.2 base m
  simpa only [show firstBody.st.drop LoopLocalChecks.body.ext = first.st from rfl,
    show allocationCostProg LoopLocalChecks.body caller.st = 2 from congrArg Prod.fst allocation_costs,
    show allocationCostProg LoopLocalChecks.body first.st = 2 from congrArg Prod.snd allocation_costs] using input

theorem counter_values : (start.st.env.2.2.1.1,first.st.env.2.2.1.1,finalOut.st.env.2.2.1.1) = (9,10,11) :=
  congrArg (fun triple => (triple.1.counter,triple.2.1.counter,triple.2.2.counter)) source_vectors

theorem final_different_start : finalOut ≠ start := by
  intro same
  have bad := congrArg (fun o : Solidity.Out C caller.st.H Caller => o.st.env.2.2.1.1) same
  have hf := congrArg (fun p => p.2.2) counter_values
  have hi := congrArg Prod.fst counter_values
  have impossible : (11 : Int) = 9 := (hf.symm.trans bad).trans hi
  cases impossible

theorem final_different_first : finalOut ≠ first := by
  intro same
  have bad := congrArg (fun o : Solidity.Out C caller.st.H Caller => o.st.env.2.2.1.1) same
  have hf := congrArg (fun p => p.2.2) counter_values
  have hi := congrArg (fun p => p.2.1) counter_values
  have impossible : (11 : Int) = 10 := (hf.symm.trans bad).trans hi
  cases impossible

theorem exact_loop_cost {amount : Nat}
    (pref : LoopPrefix LoopLocalChecks.condition LoopLocalChecks.body caller.st finalOut amount) : amount = 4 := by
  have cost := LoopLocalTarget.two_turn_cost (C := C) LoopLocalChecks.condition LoopLocalChecks.body caller.st
    firstBody secondBody first_run second_run conditions.2.2 final_different_start final_different_first pref
  simpa only [show firstBody.st.drop LoopLocalChecks.body.ext = first.st from rfl,
    show allocationCostProg LoopLocalChecks.body caller.st = 2 from congrArg Prod.fst allocation_costs,
    show allocationCostProg LoopLocalChecks.body first.st = 2 from congrArg Prod.snd allocation_costs] using cost

def scratchOne : HRef finalOut.st.H arrayType := ⟨1,by decide +kernel⟩
def scratchTwo : HRef finalOut.st.H arrayType := ⟨2,by decide +kernel⟩
theorem source_new_objects :
    (firstBody.st.env.1.1,firstBody.st.env.2.1.map HRef.id,
      secondBody.st.env.1.1,secondBody.st.env.2.1.map HRef.id,
      (finalOut.st.heap.get scratchOne).1.map Subtype.val,
      (finalOut.st.heap.get scratchTwo).1.map Subtype.val) =
      (77,some 1,77,some 2,[10],[11]) := by decide +kernel

def program : Prog C Caller Caller := .cons (.loop .auto LoopLocalChecks.condition LoopLocalChecks.body) .nil
def programCompiled : Loops.CompiledProg 1 before.frag program :=
  ⟨before.frag,selected.code,.cons selected.cert (.nil before.frag)⟩
theorem public_program_selected : Loops.compileProg 1 before.frag program = some programCompiled := by
  change ((Loops.compileStmt 1 before.frag (.loop .auto LoopLocalChecks.condition LoopLocalChecks.body)).bind
    fun head => (Loops.compileProg 1 head.frag .nil).bind fun tail =>
      some (⟨tail.frag,head.code ++ tail.code,.cons head.cert tail.cert⟩ : Loops.CompiledProg 1 before.frag program)) = _
  rw [public_selected]
  rfl

def checked : Compiler.Compilation 1 before.frag program := .memoryLoops programCompiled

theorem checked_code : checked.code = selected.code := by rfl
theorem checked_frame : checked.requiredFrame = 6 := by decide +kernel

theorem program_room {base : Nat → Fin W} {m : Evm.Machine}
    (room : LoopRoom 1 128 LoopLocalChecks.condition LoopLocalChecks.body caller.st base m) :
    Loops.Room programCompiled.cert 128 caller.st base m := by
  exact Loops.room_singleton conditionCompiled.cert bodyCompiled.cert body_stable room

theorem checked_result : checked.memoryLoopsResult (by unfold checked; rfl) = programCompiled := by
  unfold checked
  rfl

theorem program_need : programCompiled.cert.need = 6 := by
  have h := checked_frame
  unfold checked at h
  exact h

attribute [irreducible] bodyCompiled conditionCompiled cert selected programCompiled checked
end Solidity.Backend.InternalFlow.LoopTargetChecks

#print axioms Solidity.Backend.InternalFlow.LoopLocalTarget.captured
#print axioms Solidity.Backend.InternalFlow.LoopLocalTarget.outcome
#print axioms Solidity.Backend.InternalFlow.LoopLocalTarget.two_turn_prefixes
#print axioms Solidity.Backend.InternalFlow.LoopLocalTarget.room_two_turns
#print axioms Solidity.Backend.InternalFlow.LoopLocalTarget.compile_loop_equation
#print axioms Solidity.Backend.InternalFlow.LoopLocalTarget.storage_prefix
#print axioms Solidity.Backend.InternalFlow.LoopLocalTarget.two_turn_cost
#print axioms Solidity.Backend.InternalFlow.LoopLocalTarget.endpoint
#print axioms Solidity.Backend.InternalFlow.LoopLocalTarget.room_initial_not_true
#print axioms Solidity.Backend.InternalFlow.LoopLocalTarget.storage_grows
#print axioms Solidity.Backend.InternalFlow.LoopLocalTarget.revert_endpoint
#print axioms Solidity.Backend.InternalFlow.LoopLocalTarget.diverge_endpoint
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.noRef
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.initial_repr
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.actual_storage
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.actual_memory
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.condition_selected
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.body_selected
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.body_stable
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.selector_code
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.public_selected
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.storage_reached
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.first_run
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.second_run
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.conditions
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.source_horizon
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.source_run
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.source_vectors
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.allocation_costs
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.before_cost
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.before_frame
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.body_frame
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.prefix_capacity
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.reached_room
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.counter_values
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.final_different_start
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.final_different_first
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.exact_loop_cost
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.source_new_objects
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.public_program_selected
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.checked_code
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.checked_frame
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.program_room
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.checked_result
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.program_need
