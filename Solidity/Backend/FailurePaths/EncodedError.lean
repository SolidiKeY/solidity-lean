import Solidity.Backend.FailurePaths.Returns
import Solidity.Backend.FailurePaths.FramedEmission

/-! Custom errors with a genuinely evaluated local argument. General encoding
is the existing explicit EncodingAt producer premise. The Source statement
run and checked payload emission are derived here, not supplied as premises.
This is an encoder/emitter boundary, not automatic runtime error compilation. -/
namespace Solidity.Backend.FailurePaths.EncodedError
open Source EM
variable {E : Source.Env} {Γ : RCtx} {τ : STy}

def arguments (i : Source.Idx Γ τ) (same : τ.implicit E.isBase E.mapFree τ = true) : RConvArgs E Γ [τ] :=
  .cons (.local i) same .nil

def values (v : Source.Val E.layout τ) : Source.Vals E.layout [τ] := .cons v .nil

def statement {R : List STy} (error : Decl) (typed : error.paramTys E = some [τ])
    (i : Source.Idx Γ τ) (same : τ.implicit E.isBase E.mapFree τ = true) : RStmt E R false .body Γ Γ :=
  .revertError error typed (arguments i same)

def packet (global : Glob E) (error : Decl) (data : Roadmap.Bytes) : Roadmap.Bytes :=
  global.selector (sigOf E.layout error.name [τ]) ++ data

theorem arguments_run (global : Glob E) (frame : Fr) (extra : Nat)
    (i : Source.Idx Γ τ) (same : τ.implicit E.isBase E.mapFree τ = true)
    (locals : Source.Locals E.layout Γ) (initial : St E) :
    (evalConvArgs global frame (extra+2) (arguments i same)).run (locals,initial) =
      (.ok (values (locals.get i)),(locals,initial)) := by
  simp only [arguments,evalConvArgs,evalE,convRV,pure_bind]
  rfl

/-- G41 supplies only the actual encoder equation. Local argument evaluation,
statement selection of the error selector and the final failure are derived. -/
theorem source_run {R : List STy} (global : Glob E) (frame : Fr) (extra parameters : Nat)
    (error : Decl) (typed : error.paramTys E = some [τ])
    (i : Source.Idx Γ τ) (same : τ.implicit E.isBase E.mapFree τ = true)
    (locals : Source.Locals E.layout Γ) (initial reached : St E) (data : Roadmap.Bytes)
    (encoded : Premises.EncodingAt frame (extra+2) (values (locals.get i)).toR initial reached data) :
    (execS global frame (extra+3) parameters none
      (statement (R:=R) error typed i same) locals).run (Source.L0 E,initial) =
      (.error (.revert (packet (τ:=τ) global error data)),(Source.L0 E,reached)) := by
  have args :
      (sub locals (evalConvArgs global frame (extra+2) (arguments i same)) : EM E [] _).run
        (Source.L0 E,initial) =
        (.ok (values (locals.get i),locals),(Source.L0 E,initial)) := by
    have evaluated := arguments_run global frame extra i same locals initial
    simp only [ExceptT.run] at evaluated
    simp only [EM.sub,ExceptT.run,ExceptT.mk,evaluated]
  rw [statement,execS,Hoare.run_bind,args]
  change (do
    let data ← encodeVals frame (extra+2) false (values (locals.get i)).toR
    halt (.revert (packet (τ:=τ) global error data))).run (Source.L0 E,initial) = _
  rw [Hoare.run_bind,encoded]
  rfl

/-- An actual incomplete encoder remains timeout at the statement boundary;
it is never reclassified as a completed revert. H16 supplies the premise. -/
theorem source_incomplete {R : List STy} (global : Glob E) (frame : Fr) (extra parameters : Nat)
    (error : Decl) (typed : error.paramTys E = some [τ])
    (i : Source.Idx Γ τ) (same : τ.implicit E.isBase E.mapFree τ = true)
    (locals : Source.Locals E.layout Γ) (initial reached : St E)
    (incomplete : Premises.IncompleteAt
      (encodeVals frame (extra+2) false (values (locals.get i)).toR : EM E [] Roadmap.Bytes)
      (Source.L0 E,initial) (Source.L0 E,reached)) :
    (execS global frame (extra+3) parameters none
      (statement (R:=R) error typed i same) locals).run (Source.L0 E,initial) =
      (.error .timeout,(Source.L0 E,reached)) := by
  have args :
      (sub locals (evalConvArgs global frame (extra+2) (arguments i same)) : EM E [] _).run
        (Source.L0 E,initial) =
        (.ok (values (locals.get i),locals),(Source.L0 E,initial)) := by
    have evaluated := arguments_run global frame extra i same locals initial
    simp only [ExceptT.run] at evaluated
    simp only [EM.sub,ExceptT.run,ExceptT.mk,evaluated]
  rw [statement,execS,Hoare.run_bind,args]
  change (do
    let data ← encodeVals frame (extra+2) false (values (locals.get i)).toR
    halt (.revert (packet (τ:=τ) global error data))).run (Source.L0 E,initial) = _
  rw [Hoare.run_bind,incomplete]



/-- H16's actual argument-evaluator timeout is propagated through the real
error statement, including effectful reached state and discarded inner locals.
No failure-point classification or argument execution is invented. -/
theorem arguments_incomplete {R : List STy} {types : List STy}
    (global : Glob E) (frame : Fr) (fuel parameters : Nat)
    (error : Decl) (typed : error.paramTys E = some types) (args : RConvArgs E Γ types)
    (locals last : Source.Locals E.layout Γ) (initial reached : St E)
    (incomplete : Premises.IncompleteAt (evalConvArgs global frame fuel args)
      (locals,initial) (last,reached)) :
    (execS global frame (fuel+1) parameters none
      (.revertError error typed args : RStmt E R false .body Γ Γ) locals).run (Source.L0 E,initial) =
      (.error .timeout,(Source.L0 E,reached)) := by
  have evaluated := incomplete
  simp only [Premises.IncompleteAt,ExceptT.run] at evaluated
  rw [execS,Hoare.run_bind]
  simp only [EM.sub,ExceptT.run,ExceptT.mk,evaluated]

/-- info: 'Solidity.Backend.FailurePaths.EncodedError.arguments_incomplete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms arguments_incomplete

/-- Actual Source failure and the reached byte frame of the existing emitter.
The frame premise relates the numeric and byte machines, not the whole Source
world. G41's encoder fact remains explicit. -/
theorem emitted_frame {R : List STy} (global : Glob E) (frame : Fr) (extra parameters offset : Nat)
    (error : Decl) (typed : error.paramTys E = some [τ])
    (i : Source.Idx Γ τ) (same : τ.implicit E.isBase E.mapFree τ = true)
    (locals : Source.Locals E.layout Γ) (initial reached : St E) (data : Roadmap.Bytes)
    (encoded : Premises.EncodingAt frame (extra+2) (values (locals.get i)).toR initial reached data)
    (slice : Failure.Slice.Machine) (numeric : Evm.Machine) (live : Nat → Prop)
    (represented : MemoryOps.Physical.WordFrame numeric slice.memory live)
    (suffix : Backend.Program) (fits : Failure.Fits offset (packet (τ:=τ) global error data))
    (room : slice.stack.length+2≤1024)
    (apart : ∀ c, live c →
      offset+(packet (τ:=τ) global error data).length≤32*c ∨ 32*c+32≤offset) :
    (execS global frame (extra+3) parameters none
      (statement (R:=R) error typed i same) locals).run (Source.L0 E,initial) =
      (.error (.revert (packet (τ:=τ) global error data)),(Source.L0 E,reached)) ∧
    ∃ emitted,
      Failure.Slice.checkedRun
        (Failure.emit offset (.custom (packet (τ:=τ) global error data)) ++ suffix) slice =
        some (emitted,some (.revert (packet (τ:=τ) global error data))) ∧
      MemoryOps.Physical.WordFrame numeric emitted.memory live ∧ emitted.stack=slice.stack ∧
      Failure.Slice.getBytes emitted.memory offset (packet (τ:=τ) global error data).length =
        packet (τ:=τ) global error data := by
  have source := source_run (R:=R) global frame extra parameters error typed i same locals initial reached data encoded
  generalize packetEq : packet (τ:=τ) global error data = bytes at *
  refine ⟨source,{slice with memory:=Failure.Slice.putBytes slice.memory offset bytes},?_,?_,rfl,?_⟩
  · exact Failure.checkedRun_emit_suffix offset (.custom bytes) suffix slice fits room
  · exact @FramedEmission.preserve_bytes numeric slice.memory live represented offset bytes apart
  · exact Failure.Slice.getBytes_putBytes slice.memory offset bytes

/-- The caller supplies its actual operation-list journal witness. Source
journal rollback and local persistent/transient/machine restoration are then
proved, without restoring the Source heap or claiming full transaction semantics. -/
theorem world_unwind {R : List STy} (global : Glob E) (frame : Fr) (extra parameters offset : Nat)
    (error : Decl) (typed : error.paramTys E = some [τ])
    (i : Source.Idx Γ τ) (same : τ.implicit E.isBase E.mapFree τ = true)
    (locals : Source.Locals E.layout Γ) (initial reached caller : St E) (data : Roadmap.Bytes)
    (encoded : Premises.EncodingAt frame (extra+2) (values (locals.get i)).toR initial reached data)
    (ops : List (Source.Op E.layout E.lay E.lay))
    (journal : reached.ex=caller.ex.run ops)
    (saved bytes : Failure.Slice.Machine)
    (fits : Failure.Fits offset (packet (τ:=τ) global error data)) (room : bytes.stack.length+2≤1024) :
    (execS global frame (extra+3) parameters none
      (statement (R:=R) error typed i same) locals).run (Source.L0 E,initial) =
      (.error (.revert (packet (τ:=τ) global error data)),(Source.L0 E,reached)) ∧
    (caller.ex.enter frame.this frame.sender frame.value frame.cd frame.static).rollback reached.ex=caller.ex ∧
    Failure.Local.execute (Failure.Local.save (MemoryOps.Physical.worldJournal caller.ex saved))
      offset (.custom (packet (τ:=τ) global error data))
      (MemoryOps.Physical.worldJournal reached.ex bytes) =
      some (MemoryOps.Physical.worldJournal caller.ex saved,.revert (packet (τ:=τ) global error data)) := by
  refine ⟨source_run global frame extra parameters error typed i same locals initial reached data encoded,?_,?_⟩
  · rw [journal]
    exact Source.rollback_run caller.ex ops frame.this frame.sender frame.value frame.cd frame.static
  · exact Failure.Local.execute_failure _ offset (packet (τ:=τ) global error data) _ fits room

/-- Conditional consumer of the exact existing P7 producer statement. The
source statement and suffix-absorbing byte emitter are still derived here.
This theorem supplies no nonempty-payload P7 producer instance. -/
theorem transient_transport {R : List STy} (global : Glob E) (frame : Fr)
    (extra parameters offset : Nat) (error : Decl) (typed : error.paramTys E = some [τ])
    (i : Source.Idx Γ τ) (same : τ.implicit E.isBase E.mapFree τ = true)
    (locals : Source.Locals E.layout Γ) (initial reached : St E) (data : Roadmap.Bytes)
    (encoded : Premises.EncodingAt frame (extra+2) (values (locals.get i)).toR initial reached data)
    (target : Transient.State) (slice : Failure.Slice.Machine) (cells : List Nat)
    (transport : Premises.TransientPayloadAt frame
      (Failure.emit offset (.custom (packet (τ:=τ) global error data))) target slice cells offset
      (packet (τ:=τ) global error data))
    (suffix : Backend.Program) (fits : Failure.Fits offset (packet (τ:=τ) global error data))
    (room : slice.stack.length+2≤1024)
    (apart : ∀ c, c∈cells →
      offset+(packet (τ:=τ) global error data).length≤32*c ∨ 32*c+32≤offset) :
    (execS global frame (extra+3) parameters none
      (statement (R:=R) error typed i same) locals).run (Source.L0 E,initial) =
      (.error (.revert (packet (τ:=τ) global error data)),(Source.L0 E,reached)) ∧
    (∃ emitted,
      Failure.Slice.checkedRun
        (Failure.emit offset (.custom (packet (τ:=τ) global error data)) ++ suffix) slice =
        some (emitted,some (.revert (packet (τ:=τ) global error data))) ∧
      MemoryOps.Physical.WordFrame target.machine emitted.memory (fun c=>c∈cells) ∧
      emitted.stack=slice.stack ∧
      Failure.Slice.getBytes emitted.memory offset (packet (τ:=τ) global error data).length =
        packet (τ:=τ) global error data) ∧
    Transient.callbackInFrame frame (Failure.emit offset (.custom (packet (τ:=τ) global error data))) target =
      .error .reverted target := by
  have derived := emitted_frame (R:=R) global frame extra parameters offset error typed i same
    locals initial reached data encoded slice target.machine (fun c=>c∈cells) transport.1 suffix fits room apart
  exact ⟨derived.1,derived.2,transport.2.2⟩

/-- info: 'Solidity.Backend.FailurePaths.EncodedError.emitted_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms emitted_frame
/-- info: 'Solidity.Backend.FailurePaths.EncodedError.world_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms world_unwind
/-- info: 'Solidity.Backend.FailurePaths.EncodedError.transient_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transient_transport

/-- info: 'Solidity.Backend.FailurePaths.EncodedError.arguments_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms arguments_run
/-- info: 'Solidity.Backend.FailurePaths.EncodedError.source_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_run
/-- info: 'Solidity.Backend.FailurePaths.EncodedError.source_incomplete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_incomplete
end Solidity.Backend.FailurePaths.EncodedError
