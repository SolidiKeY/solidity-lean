import Solidity.Frontend.Import
import Solidity.Tools.Run
import Solidity.Calculus.Close
import Solidity.Calculus.Closers
import Solidity.Calculus.Surface
import Solidity.Semantics.RevertMemory

/-!
# Error operands and catchable self-call panics

The compiler-validated source contains positive and deliberately false
assertions. Finite kernel certificates below are lifted to the unbounded
run by `runF_approx`; executable reference EVM checks are separate.
No source-equivalence or callback-completeness theorem is assumed.
-/

solc_import "../../../tests/solc/CallExceptions.ast.json" hash 0x13163372312c84bc
  as Imported.CallExceptions testing

namespace Solidity.Examples.Tactics.CallExceptions

abbrev Source : Contract := Imported.CallExceptions
local instance : InContract := ⟨Source⟩
open scoped Scoped

private def σ₇ : State Source [] :=
  { State.init Source with tx := { selfAddress := ⟨7, rfl⟩ } }

/-- All source bodies are admitted and elaborated, including the negative tests. -/
example : Imported.CallExceptions.report.all (·.status == .elaborated) = true := by
  decide +kernel

/-- `require(true, E(failAssert()))` still evaluates the error argument. -/
theorem true_argument_panics :
    (Prog.run σ₇ Imported.CallExceptions.requireTrueArg).halt? = some .panic := by
  decide +kernel

/-- `require(false, E(failAssert()))` panics before the require can revert. -/
theorem false_argument_panics :
    (Prog.run σ₇ Imported.CallExceptions.requireFalseArg).halt? = some .panic := by
  decide +kernel

/-- `revert E(failAssert())` evaluates its argument before discarding the frame. -/
theorem revert_argument_panics :
    (Prog.run σ₇ Imported.CallExceptions.revertArg).halt? = some .panic := by
  decide +kernel

/-- An erased event's argument is still evaluated: `emit Seen(failAssert())`. -/
theorem event_argument_panics :
    (Prog.run σ₇ Imported.CallExceptions.emitArg).halt? = some .panic := by
  decide +kernel

/-- The caller computes `failAssert()` before entering `try this.echo(...)`;
its panic cannot be intercepted by that try's catch clause. -/
theorem caller_argument_panics :
    (Prog.run σ₇ Imported.CallExceptions.callerArgument).halt? = some .panic := by
  decide +kernel

/-- The false require box used to become vacuously true when its argument
was skipped. A panic is rejected by the box, so this formula is invalid. -/
theorem false_require_box_invalid :
    ¬ (⊨ᶠ dl!{ [ require(false, E(failAssert())); ] true }) :=
  fun h => Modality.afterRunTR_not_panic (h σ₇) (by decide +kernel)

/-- The corresponding true-condition claim is invalid for the same reason. -/
theorem true_require_box_invalid :
    ¬ (⊨ᶠ dl!{ [ require(true, E(failAssert())); ] true }) :=
  fun h => Modality.afterRunTR_not_panic (h σ₇) (by decide +kernel)

/-- Skipping an argument of `revert E(...)` would also unsoundly close this box. -/
theorem revert_box_invalid :
    ¬ (⊨ᶠ dl!{ [ revert E(failAssert()); ] true }) :=
  fun h => Modality.afterRunTR_not_panic (h σ₇) (by decide +kernel)

/-- `require(true, E(7))` returns, and `tick()` executes exactly once. -/
theorem true_controls_return :
    (Prog.run σ₇ Imported.CallExceptions.totalTrue).toOption.isSome = true ∧
    (Prog.run σ₇ Imported.CallExceptions.selectorArg).toOption.isSome = true ∧
    (Prog.run σ₇ Imported.CallExceptions.trueEffect).toOption.isSome = true := by
  decide +kernel

/-- A literal exponent keeps its signed custom-error parameter context;
forcing it must not replace it with a uint local. -/
theorem signed_literal_context :
    (Prog.run σ₇ Imported.CallExceptions.signedPayload).toOption.isSome = true :=
  (Prog.runF_approx 8 _ σ₇).returned (by decide +kernel)

/-- Fixed-byte custom errors retain declaration widths through eager captures,
implicit widening, returned values, selector projection and rollback. -/
theorem custom_bytes_payloads :
    (Prog.run σ₇ Imported.CallExceptions.customBytesPayloads).toOption.isSome = true :=
  (Prog.runF_approx 8 _ σ₇).returned (by decide +kernel)

/-- The previous right-aligned encoding cannot establish a false assertion. -/
theorem wrong_custom_bytes_payload :
    (Prog.run σ₇ Imported.CallExceptions.wrongCustomBytesPayload).halt? = some .panic :=
  Prog.run_halt_of_runF _ σ₇ 8 (by decide +kernel) (by decide +kernel)

private def observe_enum := sol{ uint r = enumCode(); assert(r == 33); }

/-- A bad self-call enum conversion binds Panic(0x21). -/
theorem exact_enum : (Prog.run σ₇ observe_enum).toOption.isSome = true :=
  (Prog.runF_approx 8 _ σ₇).returned (by decide +kernel)

private def observe_unset := sol{ uint r = unsetCode(); assert(r == 81); }

/-- An unset self-call internal function binds Panic(0x51). -/
theorem exact_unset : (Prog.run σ₇ observe_unset).toOption.isSome = true :=
  (Prog.runF_approx 8 _ σ₇).returned (by decide +kernel)

private def observe_argument := sol{ uint r = unsetArgCode(); assert(r == 1); }

/-- A failing operand takes priority over the unset function value. -/
theorem exact_argument : (Prog.run σ₇ observe_argument).toOption.isSome = true :=
  (Prog.runF_approx 8 _ σ₇).returned (by decide +kernel)

private def observe_order := sol{ uint r = failureCode(); assert(r == 18); }

/-- Division by zero precedes the next argument's uint8 overflow. -/
theorem exact_order : (Prog.run σ₇ observe_order).toOption.isSome = true :=
  (Prog.runF_approx 8 _ σ₇).returned (by decide +kernel)

private def observe_reason := sol{ uint r = reasonCode(); assert(r == 18); }

/-- The failing condition precedes the string reason producer. -/
theorem exact_reason : (Prog.run σ₇ observe_reason).toOption.isSome = true :=
  (Prog.runF_approx 8 _ σ₇).returned (by decide +kernel)

private def observe_assigned := sol{ uint r = assignedCall(); assert(r == 7); }

/-- An assigned internal function value still dispatches successfully. -/
theorem exact_assigned : (Prog.run σ₇ observe_assigned).toOption.isSome = true :=
  (Prog.runF_approx 8 _ σ₇).returned (by decide +kernel)

private def observe_validEnum := sol{ uint r = enumRead(1); assert(r == 1); }

/-- An in-range enum conversion still returns its value. -/
theorem exact_validEnum : (Prog.run σ₇ observe_validEnum).toOption.isSome = true :=
  (Prog.runF_approx 8 _ σ₇).returned (by decide +kernel)

/-- `catch (bytes memory d)` observes the 36-byte length, selector and code
of both panic encodings. Full direct returndata is checked by the EVM suite. -/
theorem raw_payloads :
    (Prog.run σ₇ Imported.CallExceptions.rawEnumPayload).toOption.isSome = true ∧
    (Prog.run σ₇ Imported.CallExceptions.rawUnsetPayload).toOption.isSome = true := by
  constructor
  · exact (Prog.runF_approx 8 _ σ₇).returned (by decide +kernel)
  · exact (Prog.runF_approx 8 _ σ₇).returned (by decide +kernel)

/-- `Snapshot(ticks, tick())` encodes the earlier value before the effect;
callee writes roll back while its immutable error bytes survive. -/
theorem snapshot_and_rollback :
    (Prog.run σ₇ Imported.CallExceptions.snapshot).toOption.isSome = true ∧
    (Prog.run σ₇ Imported.CallExceptions.rollback).toOption.isSome = true := by
  constructor
  · exact (Prog.runF_approx 8 _ σ₇).returned (by decide +kernel)
  · exact (Prog.runF_approx 8 _ σ₇).returned (by decide +kernel)

/-- The deliberately false source assertions must panic, including guesses
that an enum/unset-call code is 1 or that the later overflow runs first. -/
theorem negative_source_assertions :
    (Prog.run σ₇ Imported.CallExceptions.falseEffectExpectation).halt? = some .panic ∧
    (Prog.run σ₇ Imported.CallExceptions.wrongEnumCode).halt? = some .panic ∧
    (Prog.run σ₇ Imported.CallExceptions.wrongUnsetCode).halt? = some .panic ∧
    (Prog.run σ₇ Imported.CallExceptions.wrongFailureCode).halt? = some .panic := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide +kernel
  · exact Prog.run_halt_of_runF _ σ₇ 8 (by decide +kernel) (by decide +kernel)
  · exact Prog.run_halt_of_runF _ σ₇ 8 (by decide +kernel) (by decide +kernel)
  · exact Prog.run_halt_of_runF _ σ₇ 8 (by decide +kernel) (by decide +kernel)

/-- A wrong source panic-code assertion is semantically invalid, rather
than an obligation allowed to become pending or vacuously proved. -/
theorem wrong_enum_invalid : ¬ (⊨ᶠ dl!{ [ wrongEnumCode(); ] true }) :=
  fun h => Modality.afterRunTR_not_panic (h σ₇) (by decide +kernel)

/-- The exact enum code also reaches the existing symbolic catch rule. -/
theorem enum_code :
    ⊨ᶠ dl!{ ∀ uint x; [ try this.enumRead(x) returns (uint r) { }
      catch Panic(uint c) { assert(c == 33); } catch { }; ] true } := by
  sol_symex
  sol_close

/-- The exact unset-function payload reaches the symbolic catch rule. -/
theorem unset_code :
    ⊨ᶠ dl!{ [ try this.unsetCall(7) returns (uint r) { }
      catch Panic(uint c) { assert(c == 81); } catch { }; ] true } := by
  sol_symex
  sol_close

namespace EventImport

open Lean Solidity.Frontend

private def event (id : Int) (params : List String) : Json := Json.mkObj [
  ("nodeType", .str "EventDefinition"), ("id", toJson id), ("name", .str "Seen"),
  ("parameters", Json.mkObj [("parameters", toJson (params.map fun name => Json.mkObj [
    ("nodeType", .str "VariableDeclaration"), ("name", .str name)]))])]
private def literal (n : Nat) : Json := Json.mkObj [
  ("nodeType", .str "Literal"), ("kind", .str "number"), ("value", .str (toString n)),
  ("typeDescriptions", Json.mkObj [("typeString", .str s!"int_const {n}")])]
private def emission (ref : Option Int) (names : List String) : Json :=
  let callee := Json.mkObj ([ ("nodeType", .str "Identifier"), ("name", .str "Seen") ] ++
    (ref.toList.map fun id => ("referencedDeclaration", toJson id)))
  Json.mkObj [("nodeType", .str "EmitStatement"), ("eventCall", Json.mkObj [
    ("nodeType", .str "FunctionCall"), ("kind", .str "functionCall"),
    ("expression", callee), ("names", toJson names),
    ("arguments", toJson [literal 22, literal 11])])]
private def context : PState := { declarations := [event 1 ["one"], event 2 ["first", "second"]] }

-- Exact identities resolve overloads; positional operands retain source order.
-- Named event operands have different legacy/viaIR schedules and are refused.
#guard !((stmt (emission (some 2) ["second", "first"])).run' context).isOk
#guard !((stmt (emission (some 2) ["first", "second"])).run' context).isOk
#guard ((stmt (emission (some 2) [])).run' context).toOption ==
  some ["emit «Seen»(22, 11)"]
#guard !((stmt (emission none [])).run' context).isOk
#guard !((stmt (emission (some 999) [])).run' context).isOk
#guard !((stmt (emission (some 1) [])).run' context).isOk
#guard !((stmt (emission (some 2) ["first", "first"])).run' context).isOk

end EventImport

namespace ModelReferences

/-- This tests every admitted typed state. Solidity source analysis rejects
an uninitialized storage alias; this is not a claim about legal source. -/
def Refs : Contract := contract!{
  struct S { uint x; }
  error E(uint x);
  error Pair(uint x, uint y);
  function failAssert() pure returns (uint r) { assert(false); r = 0; }
}
local instance : InContract := ⟨Refs⟩

private def unsetField := sol{ S storage p; require(true, E(p.x)); }
private def firstRead := sol{ S storage p; require(true, Pair(p.x, failAssert())); }

/-- A raw-pure field `p.x` can still fail through an unset alias. -/
theorem unset_field_fails : (Prog.run (State.init Refs) unsetField).halt? = some .revert := by
  decide +kernel

/-- An earlier alias read finishes before a later argument's failed assertion. -/
theorem first_read_wins : (Prog.run (State.init Refs) firstRead).halt? = some .revert := by
  decide +kernel

/-- Discarding the raw-pure field would incorrectly establish this diamond. -/
theorem unset_field_diamond_invalid :
    ¬ (⊨ᶠ dl!{ ⟨ S storage p; require(true, E(p.x)); ⟩ true }) :=
  fun h => Modality.afterRunTR_diamond_fail (h (State.init _)) (by decide +kernel)

end ModelReferences

namespace NativeErrorBytes

/-- Native selector projections retain their bytes4 source width before
implicit widening to the error parameter's bytes8. -/
def Source : Contract := contract!{
  error Wide(bytes8 value);
  function echo(uint x) pure returns (uint r) { r = x; }
  function failSelector() { revert Wide(this.echo.selector); }
}
local instance : InContract := ⟨Source⟩
private def σ : State Source [] :=
  { State.init Source with tx := { selfAddress := ⟨7, rfl⟩ } }
private def observe := sol{
  bytes4 s = this.echo.selector;
  try this.failSelector() { assert(false); }
  catch (bytes memory d) {
    assert(d.length == 36 && d[4] == s[0] && d[5] == s[1] &&
      d[6] == s[2] && d[7] == s[3] && d[8] == 0 && d[35] == 0);
  }
}
theorem selector_widening : (Prog.run σ observe).toOption.isSome = true :=
  (Prog.runF_approx 8 _ σ).returned (by decide +kernel)

end NativeErrorBytes
end Solidity.Examples.Tactics.CallExceptions
