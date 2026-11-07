import Solidity.Backend.FailurePaths.EncodedError

/-! Consumers of actual nonhalting encoder prefixes in the existing checked
byte slice. No interpreter or source AST is introduced. The prefix result is
an explicit producer fact; complete terminal execution is derived here. -/
namespace Solidity.Backend.FailurePaths.PrefixFailure
open Source
open Failure.Slice

theorem run_append (headCode suffix : Backend.Program) (entry reached : Machine)
    (first : run headCode entry = some (reached,none)) :
    run (headCode ++ suffix) entry = run suffix reached := by
  induction headCode generalizing entry with
  | nil => cases first; rfl
  | cons instruction rest ih =>
    cases actual : step instruction entry with
    | none => simp only [run,actual,bind,Option.bind] at first; cases first
    | some pair =>
      rcases pair with ⟨middle,outcome⟩
      cases outcome with
      | none =>
        simp only [run,actual,bind,Option.bind] at first
        simpa only [List.cons_append,run,actual,bind,Option.bind] using ih middle first
      | some result =>
        simp only [run,actual,bind,Option.bind] at first
        cases first

theorem safe_append (headCode suffix : Backend.Program) (entry reached : Machine)
    (first : run headCode entry = some (reached,none))
    (safe : stackSafe headCode entry = true) :
    stackSafe (headCode ++ suffix) entry = stackSafe suffix reached := by
  induction headCode generalizing entry with
  | nil => cases first; rfl
  | cons instruction rest ih =>
    cases actual : step instruction entry with
    | none => simp only [run,actual,bind,Option.bind] at first; cases first
    | some pair =>
      rcases pair with ⟨middle,outcome⟩
      cases outcome with
      | none =>
        simp only [run,actual,bind,Option.bind] at first
        simp only [stackSafe,actual] at safe
        have bounds := Bool.and_eq_true_iff.mp safe
        simpa only [List.cons_append,stackSafe,actual,bounds.1,Bool.true_and] using
          ih middle first bounds.2
      | some result =>
        simp only [run,actual,bind,Option.bind] at first
        cases first

theorem checked_append (headCode suffix : Backend.Program) (entry reached : Machine)
    (first : checkedRun headCode entry = some (reached,none)) :
    checkedRun (headCode ++ suffix) entry = checkedRun suffix reached := by
  have safe : stackSafe headCode entry = true := by
    unfold checkedRun at first
    split at first
    · assumption
    · cases first
  have actual : run headCode entry = some (reached,none) := by
    simpa only [checkedRun,safe,↓reduceIte] using first
  simp only [checkedRun,safe_append headCode suffix entry reached actual safe,
    run_append headCode suffix entry reached actual]

/-- The prefix producer supplies its real nonhalting run. The same checked
runner executes the terminal, preserves the reached memory and arbitrary saved
tail, and absorbs every suffix. No completed revert run is a premise. -/
theorem terminal_revert (headCode suffix : Backend.Program) (entry reached : Machine)
    (offset : Nat) (payload : Roadmap.Bytes) (tail : List Roadmap.Word)
    (fits : Failure.Fits offset payload)
    (first : checkedRun headCode entry = some (reached,none))
    (layout : reached.stack = ⟨offset,fits.1⟩ :: ⟨payload.length,fits.2.1⟩ :: tail)
    (contents : getBytes reached.memory offset payload.length = payload)
    (room : tail.length+2≤1024) :
    checkedRun (headCode ++ (.op .REVERT :: suffix)) entry =
      some ({reached with stack:=tail},some (.revert payload)) := by
  rw [checked_append headCode (.op .REVERT :: suffix) entry reached first]
  have safe : stackSafe (.op .REVERT :: suffix) reached = true := by
    simp only [stackSafe,step,layout,List.length_cons,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨by omega,by omega⟩
  simp only [checkedRun,safe,↓reduceIte,run,step,layout,contents]
  rfl


/-- A known public writer prefix, used only to inhabit the consumer controls.
This is the existing emitter before its terminal, not a new encoder. -/
def writer (offset : Nat) (payload : Roadmap.Bytes) : Backend.Program :=
  Failure.writes offset payload ++ [Failure.pushNat payload.length,Failure.pushNat offset]

def prepared (entry : Machine) (offset : Nat) (payload : Roadmap.Bytes)
    (fits : Failure.Fits offset payload) : Machine :=
  ⟨⟨offset,fits.1⟩ :: ⟨payload.length,fits.2.1⟩ :: entry.stack,
    putBytes entry.memory offset payload⟩

theorem writer_run (entry : Machine) (offset : Nat) (payload : Roadmap.Bytes)
    (fits : Failure.Fits offset payload) :
    run (writer offset payload) entry = some (prepared entry offset payload fits,none) := by
  rw [writer,Failure.run_writes offset payload _ entry fits.2.2]
  rw [Failure.run_pushNat payload.length fits.2.1,Failure.run_pushNat offset fits.1]
  rfl

theorem writer_safe (entry : Machine) (offset : Nat) (payload : Roadmap.Bytes)
    (fits : Failure.Fits offset payload) (room : entry.stack.length+2≤1024) :
    stackSafe (writer offset payload) entry = true := by
  apply Failure.stackSafe_writes offset payload _ entry fits.2.2 room
  rw [Failure.stackSafe_pushNat payload.length fits.2.1,Failure.stackSafe_pushNat offset fits.1]
  simp only [stackSafe,List.length_cons,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨by omega,by omega,by omega⟩

theorem writer_checked (entry : Machine) (offset : Nat) (payload : Roadmap.Bytes)
    (fits : Failure.Fits offset payload) (room : entry.stack.length+2≤1024) :
    checkedRun (writer offset payload) entry = some (prepared entry offset payload fits,none) := by
  simp only [checkedRun,writer_safe entry offset payload fits room,↓reduceIte]
  exact writer_run entry offset payload fits

theorem public_emitter (offset : Nat) (payload : Roadmap.Bytes) :
    writer offset payload ++ [.op .REVERT] = Failure.emit offset (.custom payload) := by
  simp only [writer,Failure.emit,Failure.Input.bytes,Failure.Input.terminal,List.append_assoc]
  rfl

/-- A Source codec producer and a target nonhalting-prefix producer are explicit
separate premises. The terminal source/target failure is derived, with the exact
reached memory and caller stack. No public runtime encoder selection, complete
initial Source/target representation or failure-frame transport is inferred. -/
theorem source_terminal {E : Source.Env} {Γ : RCtx} {τ : STy} {R : List STy}
    (global : Glob E) (frame : Fr) (extra parameters offset : Nat)
    (error : Decl) (typed : error.paramTys E = some [τ])
    (i : Source.Idx Γ τ) (same : τ.implicit E.isBase E.mapFree τ = true)
    (locals : Source.Locals E.layout Γ) (initial finalSource : St E) (data : Roadmap.Bytes)
    (encoded : Premises.EncodingAt frame (extra+2) (EncodedError.values (locals.get i)).toR initial finalSource data)
    (headCode suffix : Backend.Program) (entry ready : Machine)
    (fits : Failure.Fits offset (EncodedError.packet (τ:=τ) global error data))
    (first : checkedRun headCode entry = some (ready,none))
    (layout : ready.stack = ⟨offset,fits.1⟩ ::
      ⟨(EncodedError.packet (τ:=τ) global error data).length,fits.2.1⟩ :: entry.stack)
    (contents : getBytes ready.memory offset (EncodedError.packet (τ:=τ) global error data).length =
      EncodedError.packet (τ:=τ) global error data)
    (room : entry.stack.length+2≤1024) :
    (execS global frame (extra+3) parameters none
      (EncodedError.statement (R:=R) error typed i same) locals).run (Source.L0 E,initial) =
      (.error (.revert (EncodedError.packet (τ:=τ) global error data)),(Source.L0 E,finalSource)) ∧
    checkedRun (headCode ++ (.op .REVERT :: suffix)) entry =
      some ({ready with stack:=entry.stack},some (.revert (EncodedError.packet (τ:=τ) global error data))) := by
  have source := EncodedError.source_run (R:=R) global frame extra parameters error typed i same
    locals initial finalSource data encoded
  generalize packetEq : EncodedError.packet (τ:=τ) global error data = payload at *
  exact ⟨source,terminal_revert headCode suffix entry ready offset payload entry.stack fits first layout contents room⟩


theorem source_writer {E : Source.Env} {Γ : RCtx} {τ : STy} {R : List STy}
    (global : Glob E) (frame : Fr) (extra parameters offset : Nat)
    (error : Decl) (typed : error.paramTys E = some [τ])
    (i : Source.Idx Γ τ) (same : τ.implicit E.isBase E.mapFree τ = true)
    (locals : Source.Locals E.layout Γ) (initial finalSource : St E) (data : Roadmap.Bytes)
    (encoded : Premises.EncodingAt frame (extra+2) (EncodedError.values (locals.get i)).toR initial finalSource data)
    (entry : Machine) (suffix : Backend.Program)
    (fits : Failure.Fits offset (EncodedError.packet (τ:=τ) global error data))
    (room : entry.stack.length+2≤1024) :
    (execS global frame (extra+3) parameters none
      (EncodedError.statement (R:=R) error typed i same) locals).run (Source.L0 E,initial) =
      (.error (.revert (EncodedError.packet (τ:=τ) global error data)),(Source.L0 E,finalSource)) ∧
    checkedRun (writer offset (EncodedError.packet (τ:=τ) global error data) ++ (.op .REVERT :: suffix)) entry =
      some ({entry with memory:=putBytes entry.memory offset (EncodedError.packet (τ:=τ) global error data)},
        some (.revert (EncodedError.packet (τ:=τ) global error data))) := by
  have source := EncodedError.source_run (R:=R) global frame extra parameters error typed i same
    locals initial finalSource data encoded
  generalize packetEq : EncodedError.packet (τ:=τ) global error data = payload at *
  refine ⟨source,?_⟩
  exact terminal_revert (writer offset payload) suffix entry (prepared entry offset payload fits)
    offset payload entry.stack fits (writer_checked entry offset payload fits room) rfl
    (getBytes_putBytes entry.memory offset payload) room

theorem swapped_layout_refused (entry : Machine) (offset : Nat) (payload : Roadmap.Bytes)
    (fits : Failure.Fits offset payload) (different : offset ≠ payload.length) :
    (prepared entry offset payload fits).stack ≠
      ⟨payload.length,fits.2.1⟩ :: ⟨offset,fits.1⟩ :: entry.stack := by
  intro equal
  exact different (congrArg Fin.val (List.cons.inj equal).1)

/-- info: 'Solidity.Backend.FailurePaths.PrefixFailure.source_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_writer
/-- info: 'Solidity.Backend.FailurePaths.PrefixFailure.swapped_layout_refused' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms swapped_layout_refused

/-- info: 'Solidity.Backend.FailurePaths.PrefixFailure.writer_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms writer_run
/-- info: 'Solidity.Backend.FailurePaths.PrefixFailure.writer_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms writer_safe
/-- info: 'Solidity.Backend.FailurePaths.PrefixFailure.writer_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms writer_checked
/-- info: 'Solidity.Backend.FailurePaths.PrefixFailure.public_emitter' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms public_emitter
/-- info: 'Solidity.Backend.FailurePaths.PrefixFailure.source_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_terminal

/-- info: 'Solidity.Backend.FailurePaths.PrefixFailure.run_append' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms run_append
/-- info: 'Solidity.Backend.FailurePaths.PrefixFailure.safe_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms safe_append
/-- info: 'Solidity.Backend.FailurePaths.PrefixFailure.checked_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms checked_append
/-- info: 'Solidity.Backend.FailurePaths.PrefixFailure.terminal_revert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms terminal_revert
end Solidity.Backend.FailurePaths.PrefixFailure
