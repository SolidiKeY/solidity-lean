import Solidity.Lowering.V08.SourceAbiControls

/-! Keccak reads an actually reached memory-byte object. The argument execution
and heap lookup are separate producer obligations, inhabited below by the
published ABI expression. No second allocation or hash implementation is added.
Canonical compiler, frame, admission and SourceSpec transport remain open. -/
namespace Solidity.Lowering.V08.SourceMemoryKeccak
open Solidity Source

def expression {E : Source.Env} {Γ : RCtx}
    (argument : RExpr E Γ (.bytes .memory)) : RExpr E Γ STy.bytes32 :=
  .builtin .keccak256 (.cons argument .nil) rfl

theorem execute {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (horizon : Nat) (argument : RExpr E Γ (.bytes .memory))
    (locals next : Source.Locals E.layout Γ) (state reached : Source.St E)
    (address : Nat) (bytes : Roadmap.Bytes)
    (arguments : (Source.evalE global frame (horizon+1) argument).run (locals,state) =
      (.ok (.val (.memRef rfl address)),(next,reached)))
    (object : reached.heap.get address = some ⟨.bytes .memory, .bytes bytes⟩) :
    (Source.evalE global frame (horizon+4) (expression argument)).run (locals,state) =
      (.ok (.val (Source.mkBytes (n := 32) (h := by decide +kernel)
        (Source.wordBytes (global.fixed.hash bytes)))),(next,reached)) := by
  simp only [ExceptT.run] at arguments
  change (Source.evalBuiltin global frame (horizon+3) .keccak256
    (.cons argument .nil) STy.bytes32).run (locals,state) = _
  simp only [Source.evalBuiltin, Source.evalArgs,
      Source.convRV, Source.bytesOfRV, Source.ret32, Source.heapBytes, Source.heapObj,
      Source.EM.st, arguments, object, reduceCtorEq, decide_false, Bool.false_or,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte, STy.bytes32,
      STy.loc?, ↓reduceDIte, bind, pure, ExceptT.bind, ExceptT.pure,
      ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure, StateT.get,
      get, getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift,
      ExceptT.lift, Functor.map, StateT.map]

/-- Inhabited allocation-to-hash application for arbitrary bytes and both ABI modes.
The entire actual allocation state is retained, including old objects. -/
theorem literal_execution {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (horizon : Nat) (packed : Bool) (bytes : Roadmap.Bytes)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.evalE global frame (horizon+7)
      (expression (SourceAbi.literal packed bytes))).run (locals,state) =
      (.ok (.val (Source.mkBytes (n := 32) (h := by decide +kernel)
        (Source.wordBytes (global.fixed.hash
          (if packed then bytes else Source.abiLayout [(true,bytes)]))))),
       (locals,SourceKeccak.afterLiteral state
         (if packed then bytes else Source.abiLayout [(true,bytes)]))) := by
  apply execute global frame (horizon+3) (SourceAbi.literal packed bytes)
    locals locals state _ state.heap.next _
  · exact SourceAbi.literal_execution global frame horizon packed bytes locals state
  · exact SourceKeccak.allocated state _

/-- The existing effecting argument producer is really reached: caller write/read,
hash allocation and ABI allocation precede this final hash. -/
theorem mixed_execution (pipeline : Roadmap.Pipeline) (static packed : Bool) :
    (Source.evalE (SourceCustomErrorControls.global pipeline)
      {SourceCustomErrorControls.frame with static:=static} 20
      (expression (.abiEncode (if packed then .encodePacked else .encode)
        SourceAbiControls.arguments))).run
        (SourceCustomErrorControls.locals,SourceCustomErrorControls.populated) =
      (.ok (.val (Source.mkBytes (n := 32) (h := by decide +kernel)
        (Source.wordBytes ((SourceCustomErrorControls.global pipeline).fixed.hash
          (SourceAbiControls.data packed pipeline))))),
       (.cons (.bool false) .nil,
        SourceKeccak.afterLiteral
          (SourceKeccak.afterLiteral SourceCustomErrorControls.populated
            SourceCustomErrorControls.binary) (SourceAbiControls.data packed pipeline))) := by
  apply execute (SourceCustomErrorControls.global pipeline)
    {SourceCustomErrorControls.frame with static:=static} 16 _
    SourceCustomErrorControls.locals (.cons (.bool false) .nil)
    SourceCustomErrorControls.populated _ 2 _
  · exact SourceAbiControls.mixed_complete pipeline static packed
  · exact SourceKeccak.allocated _ _

theorem literal_transport {E : Source.Env} {Γ : RCtx} (global : Glob E)
    (pin : global.fixed.Keccak) (frame : Fr) (horizon : Nat)
    (packed : Bool) (bytes : Roadmap.Bytes) (locals : Source.Locals E.layout Γ)
    (state : Source.St E) :
    (Source.evalE global frame (horizon+7)
      (expression (SourceAbi.literal packed bytes))).run (locals,state) =
      (.ok (.val (Source.mkBytes (n := 32) (h := by decide +kernel)
        (Semantics.wordBytes (keccakBytes
          ((if packed then bytes else Source.abiLayout [(true,bytes)]).map
            (fun b => (b.toNat : Int)))).1.toNat))),
       (locals,SourceKeccak.afterLiteral state
         (if packed then bytes else Source.abiLayout [(true,bytes)]))) := by
  rw [literal_execution, CryptoObservations.fixed_keccak_bytes global.fixed pin]

theorem zero_horizon {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (argument : RExpr E Γ (.bytes .memory)) (locals : Source.Locals E.layout Γ)
    (state : Source.St E) :
    (Source.evalE global frame 0 (expression argument)).run (locals,state) =
      (.error .timeout,(locals,state)) := rfl

theorem mixed_vector (pipeline : Roadmap.Pipeline) (packed : Bool) :
    let final := SourceKeccak.afterLiteral (SourceKeccak.afterLiteral SourceCustomErrorControls.populated SourceCustomErrorControls.binary) (SourceAbiControls.data packed pipeline)
    (final.ex.world.accounts SourceCustomErrorControls.sender).balance.val = 93 ∧
    (final.ex.world.accounts SourceCustomErrorControls.self).balance.val = 7 ∧
    (final.ex.world.accounts SourceCustomErrorControls.self).code = some 0 ∧
    (final.ex.world.accounts SourceCustomErrorControls.self).nonce = 1 ∧
    (final.ex.world.accounts SourceCustomErrorControls.self).storage.read SourceCustomErrorControls.saved = some (.bool true) ∧
    (final.ex.transient.cells SourceCustomErrorControls.self).read SourceCustomErrorControls.scratch = some (.bool true) ∧
    final.ex.journal.length = 3 ∧ final.heap.next = 3 ∧
    final.heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    final.heap.get 1 = some ⟨.bytes .memory,.bytes SourceCustomErrorControls.binary⟩ ∧
    final.heap.get 2 = some ⟨.bytes .memory,.bytes (SourceAbiControls.data packed pipeline)⟩ ∧
    final.events = SourceCustomErrorControls.populated.events ∧ final.logs = SourceCustomErrorControls.populated.logs ∧ final.fnLocals = SourceCustomErrorControls.populated.fnLocals :=
  SourceAbiControls.mixed_vector pipeline packed
/-- These are input/object/order distinctions, not a hash noncollision claim. -/
theorem wrong_order (pipeline : Roadmap.Pipeline) :
    SourceAbiControls.data false pipeline ≠ SourceAbiControls.reversedData pipeline :=
  SourceAbiControls.different_ordered_bytes pipeline

theorem wrong_allocator (pipeline : Roadmap.Pipeline) (packed : Bool) :
    (SourceKeccak.afterLiteral
      (SourceKeccak.afterLiteral SourceCustomErrorControls.populated
        SourceCustomErrorControls.binary) (SourceAbiControls.data packed pipeline)).heap.next ≠ 4 := by
  change (3 : Nat) ≠ 4
  decide +kernel

theorem old_object_retained (pipeline : Roadmap.Pipeline) (packed : Bool) :
    (SourceKeccak.afterLiteral
      (SourceKeccak.afterLiteral SourceCustomErrorControls.populated
        SourceCustomErrorControls.binary) (SourceAbiControls.data packed pipeline)).heap.get 0 =
      some ⟨.bytes .memory,.bytes [0,255]⟩ := rfl

/-- info: 'Solidity.Lowering.V08.SourceMemoryKeccak.execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms execute
/-- info: 'Solidity.Lowering.V08.SourceMemoryKeccak.literal_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms literal_execution
/-- info: 'Solidity.Lowering.V08.SourceMemoryKeccak.mixed_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mixed_execution
/-- info: 'Solidity.Lowering.V08.SourceMemoryKeccak.literal_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms literal_transport
/-- info: 'Solidity.Lowering.V08.SourceMemoryKeccak.zero_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_horizon
/-- info: 'Solidity.Lowering.V08.SourceMemoryKeccak.mixed_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mixed_vector
/-- info: 'Solidity.Lowering.V08.SourceMemoryKeccak.wrong_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wrong_order
/-- info: 'Solidity.Lowering.V08.SourceMemoryKeccak.wrong_allocator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wrong_allocator
/-- info: 'Solidity.Lowering.V08.SourceMemoryKeccak.old_object_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms old_object_retained

/-- Argument failure propagates its exact halt and complete reached machine.
It neither invokes hashing nor rolls back prior argument effects. -/
theorem argument_failure {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (horizon : Nat) (argument : RExpr E Γ (.bytes .memory))
    (locals next : Source.Locals E.layout Γ) (state reached : Source.St E)
    (reason : Source.Halt)
    (arguments : (Source.evalE global frame (horizon+1) argument).run (locals,state) =
      (.error reason,(next,reached))) :
    (Source.evalE global frame (horizon+4) (expression argument)).run (locals,state) =
      (.error reason,(next,reached)) := by
  simp only [ExceptT.run] at arguments
  change (Source.evalBuiltin global frame (horizon+3) .keccak256
    (.cons argument .nil) STy.bytes32).run (locals,state) = _
  simp only [Source.evalBuiltin, Source.evalArgs, arguments, reduceCtorEq,
    decide_false, Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.run, ExceptT.mk,
    StateT.bind, StateT.pure]

/-- A successful argument can still return a malformed reference. This is a
refusal control, not an admitted SourceSpec machine or an ABI decoder claim. -/
theorem dangling_failure {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (horizon : Nat) (argument : RExpr E Γ (.bytes .memory))
    (locals next : Source.Locals E.layout Γ) (state reached : Source.St E)
    (address : Nat)
    (arguments : (Source.evalE global frame (horizon+1) argument).run (locals,state) =
      (.ok (.val (.memRef rfl address)),(next,reached)))
    (missing : reached.heap.get address = none) :
    (Source.evalE global frame (horizon+4) (expression argument)).run (locals,state) =
      (.error (.stuck "dangling memory reference"),(next,reached)) := by
  simp only [ExceptT.run] at arguments
  change (Source.evalBuiltin global frame (horizon+3) .keccak256
    (.cons argument .nil) STy.bytes32).run (locals,state) = _
  simp only [Source.evalBuiltin, Source.evalArgs, Source.convRV, Source.bytesOfRV,
    Source.heapBytes, Source.heapObj, Source.EM.st, Source.EM.halt,
    arguments, missing, reduceCtorEq, decide_false, Bool.false_or, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, STy.loc?, ↓reduceDIte, bind, pure, ExceptT.bind,
    ExceptT.pure, ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure,
    StateT.get, get, getThe, MonadStateOf.get, liftM, monadLift,
    MonadLift.monadLift, ExceptT.lift, Functor.map, StateT.map, throw, throwThe, MonadExceptOf.throw]

/-- The existing real ABI prefix writes the caller local before timing out.
The complete original machine survives, including all old byte objects/logs. -/
theorem mixed_timeout (pipeline : Roadmap.Pipeline) (static packed : Bool) :
    (Source.evalE (SourceCustomErrorControls.global pipeline)
      {SourceCustomErrorControls.frame with static:=static} 9
      (expression (.abiEncode (if packed then .encodePacked else .encode)
        SourceAbiControls.arguments))).run
      (SourceCustomErrorControls.locals,SourceCustomErrorControls.populated) =
      (.error .timeout,(.cons (.bool false) .nil,SourceCustomErrorControls.populated)) := by
  apply argument_failure (SourceCustomErrorControls.global pipeline)
    {SourceCustomErrorControls.frame with static:=static} 5 _
    SourceCustomErrorControls.locals (.cons (.bool false) .nil)
    SourceCustomErrorControls.populated SourceCustomErrorControls.populated .timeout
  exact SourceAbiControls.insufficient_after_effects pipeline static packed

def memoryLocals {E : Source.Env} (address : Nat) :
    Source.Locals E.layout [.bytes .memory] := .cons (.memRef rfl address) .nil

theorem dangling_client (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalE (SourceCustomErrorControls.global pipeline)
      {SourceCustomErrorControls.frame with static:=static} 4
      (expression (.local .here))).run
      (memoryLocals 99,SourceCustomErrorControls.populated) =
      (.error (.stuck "dangling memory reference"),
        (memoryLocals 99,SourceCustomErrorControls.populated)) := by
  apply dangling_failure (SourceCustomErrorControls.global pipeline)
    {SourceCustomErrorControls.frame with static:=static} 0 (.local .here)
    (memoryLocals 99) (memoryLocals 99) SourceCustomErrorControls.populated
    SourceCustomErrorControls.populated 99
  · rfl
  · rfl

/-- Object zero is valid but stale: actual execution reads its original bytes,
not the bytes in a newly allocated object. No hash inequality is asserted. -/
theorem stale_client (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalE (SourceCustomErrorControls.global pipeline)
      {SourceCustomErrorControls.frame with static:=static} 4
      (expression (.local .here))).run
      (memoryLocals 0,SourceCustomErrorControls.populated) =
      (.ok (.val (Source.mkBytes (n := 32) (h := by decide +kernel)
        (Source.wordBytes ((SourceCustomErrorControls.global pipeline).fixed.hash [0,255])))),
        (memoryLocals 0,SourceCustomErrorControls.populated)) := by
  apply execute (SourceCustomErrorControls.global pipeline)
    {SourceCustomErrorControls.frame with static:=static} 0 (.local .here)
    (memoryLocals 0) (memoryLocals 0) SourceCustomErrorControls.populated
    SourceCustomErrorControls.populated 0 [0,255]
  · rfl
  · rfl

theorem wrong_timeout_rollback (pipeline : Roadmap.Pipeline) (static packed : Bool) :
    (Source.evalE (SourceCustomErrorControls.global pipeline)
      {SourceCustomErrorControls.frame with static:=static} 9
      (expression (.abiEncode (if packed then .encodePacked else .encode)
        SourceAbiControls.arguments))).run
      (SourceCustomErrorControls.locals,SourceCustomErrorControls.populated) ≠
      (.error .timeout,(SourceCustomErrorControls.locals,SourceCustomErrorControls.populated)) := by
  rw [mixed_timeout]
  intro same
  cases same

theorem wrong_dangling_timeout (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalE (SourceCustomErrorControls.global pipeline)
      {SourceCustomErrorControls.frame with static:=static} 4
      (expression (.local .here))).run
      (memoryLocals 99,SourceCustomErrorControls.populated) ≠
      (.error .timeout,(memoryLocals 99,SourceCustomErrorControls.populated)) := by
  rw [dangling_client]
  intro same
  cases same

/-- info: 'Solidity.Lowering.V08.SourceMemoryKeccak.argument_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms argument_failure
/-- info: 'Solidity.Lowering.V08.SourceMemoryKeccak.dangling_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dangling_failure
/-- info: 'Solidity.Lowering.V08.SourceMemoryKeccak.mixed_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mixed_timeout
/-- info: 'Solidity.Lowering.V08.SourceMemoryKeccak.dangling_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dangling_client
/-- info: 'Solidity.Lowering.V08.SourceMemoryKeccak.stale_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stale_client
/-- info: 'Solidity.Lowering.V08.SourceMemoryKeccak.wrong_timeout_rollback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_timeout_rollback
/-- info: 'Solidity.Lowering.V08.SourceMemoryKeccak.wrong_dangling_timeout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_dangling_timeout

end Solidity.Lowering.V08.SourceMemoryKeccak
