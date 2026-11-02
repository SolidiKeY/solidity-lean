import tests.«internal-flow».LoopTargetEndpoint
namespace Solidity.Backend.InternalFlow.LoopTargetChecks
open Evm Evm.Memory LocalStoreFlow

private theorem reflect_error {α : Type} (r : TRes α) (halt : THalt)
    (seen : r.halt? = some halt) : r = .error halt := by
  cases r with
  | ok v => cases seen
  | error h => exact congrArg Except.error (Option.some.inj seen)

def badCondition : CompiledVal 1 before.frag LoopLocalChecks.badCondition :=
  (Memory.compileVal 1 before.frag LoopLocalChecks.badCondition).get (by decide +kernel)
def badCert : LoopCert 1 before.frag LoopLocalChecks.badCondition LoopLocalChecks.body
    badCondition.code bodyCompiled.code :=
  ⟨badCondition.cert,bodyCompiled.frag,bodyCompiled.cert,body_stable⟩

theorem bad_condition_source : LoopLocalChecks.badCondition.evalT caller.st = .error .revert :=
  reflect_error _ _ (by decide +kernel)
theorem bad_loop_source : (Stmt.loop .auto LoopLocalChecks.badCondition LoopLocalChecks.body).run caller.st = .error .revert := by
  rw [Stmt.run_loop]
  apply TLoop.run_of_iterN (n := 1)
  simp only [TLoop.iterN,TLoop.step,bad_condition_source]

theorem condition_revert_target : run [.loop badCondition.code bodyCompiled.code] prefixMachine = .revert := by
  obtain ⟨base0,base1,whole,repr0,repr1,input,room,cost,he,hg,total,stack,cursor,env⟩ := complete_endpoint
  have stopped : LoopLocalChecks.badCondition.evalT caller.st ≠ .ok true := by
    rw [bad_condition_source]
    intro h; cases h
  have capacity : LoopRoom 1 128 LoopLocalChecks.badCondition LoopLocalChecks.body caller.st base0 prefixMachine :=
    LoopLocalTarget.room_initial_not_true LoopLocalChecks.badCondition LoopLocalChecks.body
    caller.st base0 prefixMachine stopped
  exact LoopLocalTarget.revert_endpoint (C := C) (b := 1) (L := 3) (frame := 128)
    (σ := caller.st) (base := base0) (m := prefixMachine) badCert .auto repr0 body_frame capacity bad_loop_source

attribute [irreducible] badCondition badCert

def spin : Prog C Caller Caller := .nil
def trueCondition : CompiledVal (C := C) 1 before.frag (.simple (.bool true)) :=
  (Memory.compileVal 1 before.frag (.simple (.bool true))).get (by decide +kernel)
def spinCompiled : Memory.CompiledProg 1 before.frag spin :=
  (Memory.compileProg 1 before.frag spin).get (by decide +kernel)
def spinCert : LoopCert 1 before.frag (.simple (.bool true)) spin trueCondition.code spinCompiled.code :=
  ⟨trueCondition.cert,spinCompiled.frag,spinCompiled.cert,by decide +kernel⟩

attribute [irreducible] trueCondition spinCompiled spinCert

theorem spin_horizon (n : Nat) : TLoop.iterN (scopedLoopBody spin)
    (fun _ => (.ok true : TRes Bool)) n start = .inl start := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem spin_source : (Stmt.loop .auto (.simple (.bool true)) spin).run caller.st = .error .diverge :=
  loop_all_prefixes_running (scopedLoopBody spin) (fun _ => .ok true) start
    (fun n => ⟨start,spin_horizon n⟩)

theorem divergence_target : run [.loop trueCondition.code spinCompiled.code] prefixMachine = .fault := by
  obtain ⟨base0,base1,whole,repr0,repr1,input,room,cost,he,hg,total,stack,cursor,env⟩ := complete_endpoint
  have capacity : LoopRoom 1 128 (.simple (.bool true)) spin caller.st base0 prefixMachine :=
    loopRoom_nonallocating _ _ rfl _ _ _
  exact LoopLocalTarget.diverge_endpoint (C := C) (b := 1) (L := 3) (frame := 128)
    (σ := caller.st) (base := base0) (m := prefixMachine) spinCert .auto repr0 (by decide +kernel) capacity spin_source

theorem revert_not_fault : run [.loop badCondition.code bodyCompiled.code] prefixMachine ≠ .fault := by
  rw [condition_revert_target]
  intro h; cases h

theorem divergence_not_revert : run [.loop trueCondition.code spinCompiled.code] prefixMachine ≠ .revert := by
  rw [divergence_target]
  intro h; cases h

def falseCondition : CompiledVal (C := C) 1 before.frag (.simple (.bool false)) :=
  (Memory.compileVal 1 before.frag (.simple (.bool false))).get (by decide +kernel)
def skippedCert : LoopCert 1 before.frag (.simple (.bool false)) LoopLocalChecks.body
    falseCondition.code bodyCompiled.code :=
  ⟨falseCondition.cert,bodyCompiled.frag,bodyCompiled.cert,body_stable⟩

theorem skipped_source : (Stmt.loop .auto (.simple (.bool false)) LoopLocalChecks.body).run caller.st = .ok start := by
  apply TLoop.run_of_iterN (n := 1)
  rfl

theorem skipped_room (base : Nat → Fin W) : LoopRoom 1 128 (.simple (.bool false))
    LoopLocalChecks.body caller.st base prefixMachine :=
  LoopLocalTarget.room_initial_not_true _ _ _ _ _ (by intro h; cases h)

theorem skipped_target : run [.loop falseCondition.code bodyCompiled.code] prefixMachine = .ok prefixMachine 0 := by
  have finite : loopIterN (fun m => exec falseCondition.code 0 m)
      (fun m => exec bodyCompiled.code 0 m) 1 prefixMachine = .inr (.ok prefixMachine 0) := by
    rfl
  have ended := loopRun_of_iterN finite
  change ((Instr.step (.loop falseCondition.code bodyCompiled.code) prefixMachine).bind
    (fun m k => exec [] k m)) = _
  simp only [Instr.step,ended,Out.ok_bind]
  rfl

theorem wrong_capacity (base : Nat → Fin W) : ¬ AllocationInput 1 128 W caller.st base prefixMachine := by
  intro input
  rcases input with zero | ⟨hb,cursor,alloc,space⟩
  · exact (Nat.ne_of_gt W_pos) zero
  · omega

theorem wrong_frame (base : Nat → Fin W) : ¬ StateRepr 3 1 4 before.frag caller.st base prefixMachine := by
  intro repr
  have bad := repr.locals
  change 5 ≤ 4 at bad
  omega

theorem assert_refused : (Memory.compileProg 1 before.frag LoopLocalChecks.failingBody).isSome = false := by decide +kernel

def byteBody : Prog C Caller Caller := .cons (.revertData [.bytes [0xde,0,0xad]]) .nil
theorem bytes_refused : (Memory.compileProg 1 before.frag byteBody).isSome = false := by decide +kernel

theorem panic_source : (Stmt.loop .auto LoopLocalChecks.condition LoopLocalChecks.failingBody).run caller.st = .error .panic := by
  have finite : TLoop.iterN (scopedLoopBody LoopLocalChecks.failingBody)
      (fun o => LoopLocalChecks.condition.evalT o.st) 2 start = .inr (.error .panic) := by
    have certificate : (match TLoop.iterN (scopedLoopBody LoopLocalChecks.failingBody)
        (fun o => LoopLocalChecks.condition.evalT o.st) 2 start with
      | .inr (.error halt) => decide (halt = .panic) | _ => false) = true := by decide +kernel
    cases h : TLoop.iterN (scopedLoopBody LoopLocalChecks.failingBody)
        (fun o => LoopLocalChecks.condition.evalT o.st) 2 start with
    | inl out => rw [h] at certificate; cases certificate
    | inr result => cases result with
      | ok out => rw [h] at certificate; cases certificate
      | error halt =>
        rw [h] at certificate
        have same : halt = .panic := of_decide_eq_true certificate
        rw [same]
  exact TLoop.run_of_iterN finite

theorem bytes_source : byteBody.run caller.st = .error (.revertWith [0xde,0,0xad]) := by rfl

theorem bytes_not_bare : byteBody.run caller.st ≠ .error .revert := by
  rw [bytes_source]
  intro wrong; cases wrong
end Solidity.Backend.InternalFlow.LoopTargetChecks

#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.bad_condition_source
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.bad_loop_source
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.condition_revert_target
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.spin_horizon
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.spin_source
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.divergence_target
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.revert_not_fault
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.divergence_not_revert
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.skipped_source
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.skipped_room
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.skipped_target
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.wrong_capacity
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.wrong_frame
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.assert_refused
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.bytes_refused
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.panic_source
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.bytes_source
#print axioms Solidity.Backend.InternalFlow.LoopTargetChecks.bytes_not_bare
