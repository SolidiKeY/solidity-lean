import Solidity.Examples.Tactics.ExternalTryWitness
import Solidity.Calculus.Sound.ExternalTryWitness

/-!
# State-specific external try diamonds

These use a proved normal execution plus a checked postcondition, not source
validity. The input oracle is explicit. No box annotation is used. Callback
refusal remains the one proved in `Counterexamples/DiamondTry.lean`.
-/

namespace Solidity.Examples.Tactics.ExternalTryFormula
open Semantics
open ExternalTryWitness
local instance : InContract := ⟨Probe⟩
open scoped Scoped

/-- The successful deterministic run's exact final state, used only below. -/
def finalState : State Probe [] :=
  (Prog.runT (input (.ok [⟨9, rfl⟩])) probe).toOption.getD (State.init Probe)

/-- The explicit oracle and decoded word 9 really produce this final state. -/
theorem normal_witness :
    Prog.runFrames (input (.ok [⟨9, rfl⟩])) probe .nil = .ok finalState := by
  rfl

/-- The postcondition reads actual storage after the run. -/
theorem checked_post : holds finalState (dl!{ tag = 9 ∧ reasonCode = 0 } : Fml Probe []) := by
  constructor <;> rfl

/-- A source-shaped diamond supported precisely at this input state. -/
theorem deterministic_formula : holds (input (.ok [⟨9, rfl⟩]))
    (dl!{ ⟨ try I(7).fetch() returns (uint v) { tag = v; }
      catch Error(string memory) { tag = 2; }
      catch Panic(uint c) { tag = 3; reasonCode = c; }
      catch { tag = 4; }; ⟩ (tag = 9 ∧ reasonCode = 0) } : Fml Probe []) := by
  exact holds_diamond_of_normal normal_witness checked_post

/-- A nearby incorrect postcondition is refused at that same concrete state. -/
theorem wrong_post : ¬ holds finalState (dl!{ tag = 8 } : Fml Probe []) := by
  unfold holds
  decide +kernel

/-- Missing oracle entries cannot supply the explicit normal witness required
by the helper, regardless of the proposed final state. -/
theorem missing_refused (τ : State Probe []) :
    Prog.runFrames (State.init Probe) probe .nil ≠ .ok τ := by
  intro h
  have bad : (Prog.run (State.init Probe) probe).halt? = none := by
    cases hw : Prog.run (State.init Probe) probe with
    | error e => simp only [Prog.runFrames, hw, bind, Except.bind] at h; cases h
    | ok o => rfl
  rw [missing_entry] at bad
  cases bad

/-- Malformed success returns cannot supply a normal witness either. -/
theorem malformed_refused (τ : State Probe []) :
    Prog.runFrames (input (.ok [])) probe .nil ≠ .ok τ := by
  intro h
  have bad : (Prog.run (input (.ok [])) probe).halt? = none := by
    cases hw : Prog.run (input (.ok [])) probe with
    | error e => simp only [Prog.runFrames, hw, bind, Except.bind] at h; cases h
    | ok o => rfl
  rw [malformed_return] at bad
  cases bad

/-- An explicit oracle failure still has an ordinary, state-specific normal
catch execution. These are not universal source obligations. -/
def catchFinal (r : ExtResult) : State Probe [] :=
  (Prog.runT (input r) probe).toOption.getD (State.init Probe)

/-- Error normal execution and its two storage observations. -/
theorem error_formula : holds (input (.error []))
    (dl!{ ⟨ try I(7).fetch() returns (uint v) { tag = v; }
      catch Error(string memory) { tag = 2; }
      catch Panic(uint c) { tag = 3; reasonCode = c; }
      catch { tag = 4; }; ⟩ (tag = 2 ∧ reasonCode = 0) } : Fml Probe []) := by
  apply holds_diamond_of_normal (τ := catchFinal (.error [])) (by rfl)
  constructor <;> rfl

/-- Panic normal execution retains the decoded code. -/
theorem panic_formula : holds (input (.panic ⟨17, rfl⟩))
    (dl!{ ⟨ try I(7).fetch() returns (uint v) { tag = v; }
      catch Error(string memory) { tag = 2; }
      catch Panic(uint c) { tag = 3; reasonCode = c; }
      catch { tag = 4; }; ⟩ (tag = 3 ∧ reasonCode = 17) } : Fml Probe []) := by
  apply holds_diamond_of_normal (τ := catchFinal (.panic ⟨17, rfl⟩)) (by rfl)
  constructor <;> rfl

/-- Catch-all normal execution preserves the other observed root. -/
theorem other_formula : holds (input (.other []))
    (dl!{ ⟨ try I(7).fetch() returns (uint v) { tag = v; }
      catch Error(string memory) { tag = 2; }
      catch Panic(uint c) { tag = 3; reasonCode = c; }
      catch { tag = 4; }; ⟩ (tag = 4 ∧ reasonCode = 0) } : Fml Probe []) := by
  apply holds_diamond_of_normal (τ := catchFinal (.other [])) (by rfl)
  constructor <;> rfl

/-- The caller local survives payload allocation; its scope is popped by the
nonempty frame after both the payload body and the remaining statement run. -/
def payload : Prog Probe [] [.val .uint] := sol{
  uint sentinel = 31;
  try I(7).fetch() { tag = 99; }
  catch (bytes memory data) { tag = data.length; reasonCode = data[1]; }
  reasonCode += sentinel;
}

def payloadFrames : Frames Probe [.val .uint] [] := .pop .block payload.ext .nil

def payloadInput : State Probe [] := input (.other [5, 7])
def payloadFinal : State Probe [] :=
  (Prog.runFrames payloadInput payload payloadFrames).toOption.getD (State.init Probe)

private theorem normal_of_halt_none {α : Type} (r : TRes α) (fallback : α)
    (h : r.halt? = none) : r = .ok (r.toOption.getD fallback) := by
  cases r with
  | error e => cases h
  | ok a => rfl

/-- The raw catch actually allocates and returns, then pops its scopes. -/
theorem payload_witness : Prog.runFrames payloadInput payload payloadFrames = .ok payloadFinal := by
  exact normal_of_halt_none _ _ (by decide +kernel)

/-- Ordered postcondition: payload length, second byte plus surviving local. -/
theorem payload_post : holds payloadFinal (dl!{ tag = 2 ∧ reasonCode = 38 } : Fml Probe []) := by
  constructor <;> (unfold holds; decide +kernel)

/-- The source formula retains the caller local in its final context; the
separate `payload_witness` above checks the explicit scope-pop frame. -/
def payloadOpenFinal : State Probe [.val .uint] :=
  (Prog.runFrames payloadInput payload .nil).toOption.getD
    ((State.init Probe).push (t := .val .uint) ⟨0, rfl⟩)

/-- The helper consumes the exact normal source-shaped run and checks its
postcondition. The local is still in scope at this formula's postcondition. -/
theorem payload_formula : holds payloadInput
    (dl!{ ⟨ uint sentinel = 31;
      try I(7).fetch() { tag = 99; }
      catch (bytes memory data) { tag = data.length; reasonCode = data[1]; };
      reasonCode += sentinel;
    ⟩ (tag = 2 ∧ reasonCode = 38) } : Fml Probe []) := by
  apply holds_diamond_of_normal (τ := payloadOpenFinal)
    (normal_of_halt_none _ _ (by decide +kernel))
  constructor <;> (unfold holds; decide +kernel)

/-- Error payloads use the existing ABI decoder before binding the reason. -/
def reason : Prog Probe [] [] := sol{
  try I(7).fetch() { tag = 99; }
  catch Error(string memory data) { tag = data.length; reasonCode = data[1]; }
  catch { tag = 8; }
}

def reasonInput : State Probe [] := input (.error [65, 66])
def reasonFinal : State Probe [] :=
  (Prog.runFrames reasonInput reason .nil).toOption.getD (State.init Probe)

/-- Decoded Error reason length and second byte, in order. -/
theorem reason_formula : holds reasonInput
    (dl!{ ⟨ try I(7).fetch() { tag = 99; }
      catch Error(string memory data) { tag = data.length; reasonCode = data[1]; }
      catch { tag = 8; }; ⟩ (tag = 2 ∧ reasonCode = 66) } : Fml Probe []) := by
  apply holds_diamond_of_normal (τ := reasonFinal)
    (normal_of_halt_none _ _ (by decide +kernel))
  constructor <;> (unfold holds; decide +kernel)

/-- Malformed Error ABI bytes are not invented into a decoded reason. -/
theorem malformed_reason : CatchKind.reason.decode [1, 2] = none := by
  decide +kernel

/-- The deterministic helper cannot be applied to the callback goal, even
with a proved concrete normal run and postcondition. The old refusal proves it. -/
theorem callback_helper_refused (pay : Bool) :
    ¬ holdsC .tt pay (input (.ok [⟨9, rfl⟩]))
      (dl!{ ⟨ try I(7).fetch() returns (uint v) { tag = v; }
        catch Error(string memory) { tag = 2; }
        catch Panic(uint c) { tag = 3; reasonCode = c; }
        catch { tag = 4; }; ⟩ true } : Fml Probe []) := by
  intro h
  fail_if_success have bad := (show holdsC .tt pay (input (.ok [⟨9, rfl⟩]))
      (dl!{ ⟨ try I(7).fetch() returns (uint v) { tag = v; }
        catch Error(string memory) { tag = 2; }
        catch Panic(uint c) { tag = 3; reasonCode = c; }
        catch { tag = 4; }; ⟩ true } : Fml Probe []) from
      holds_diamond_of_normal normal_witness (show holds finalState (.tt : Fml Probe []) from True.intro))
  exact callback_refused pay h

/-- A zero receiver fails before any catch; it cannot supply a normal witness. -/
theorem zero_refused (τ : State Probe []) :
    Prog.runFrames (input (.other []))
      (sol{ try I(0).fetch() { tag = 1; } catch { tag = 2; } } : Prog Probe [] []) .nil ≠ .ok τ := by
  intro h
  change (Except.error THalt.revert : TRes (State Probe [])) = .ok τ at h
  cases h

/-- info: Except.ok (some "2", some "38") -/
#guard_msgs in
#eval (Prog.runFrames payloadInput payload payloadFrames).map
  (fun s => (Tools.fmtRoot s.storage "tag", Tools.fmtRoot s.storage "reasonCode"))

/-- info: Except.ok (some "2", some "66") -/
#guard_msgs in
#eval (Prog.runFrames reasonInput reason .nil).map
  (fun s => (Tools.fmtRoot s.storage "tag", Tools.fmtRoot s.storage "reasonCode"))

end Solidity.Examples.Tactics.ExternalTryFormula
