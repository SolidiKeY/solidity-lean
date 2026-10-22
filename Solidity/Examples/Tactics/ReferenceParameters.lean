import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.Close
import Solidity.Calculus.Spec
import Solidity.Calculus.Print
import Solidity.Calculus.SolkeyFragment
import Solidity.Syntax.Splice

/-!
# Reference parameters

Storage aliases and memory identities are captured in argument order.
Copies from storage precede effects in later arguments.
-/

namespace Solidity.Examples.Tactics.ReferenceParameters

open Semantics
open scoped Scoped

def Calls : Contract := contract!{
  Token tok; Token other;
  uint[] values; uint[][] rows;
  mapping(uint => uint) counts;
  function mix(uint a, Token storage t, uint[] memory xs, uint b) returns (uint) {
    t.value = a; xs[0] = b; return t.value + xs[0];
  }
  function sameStorage(Token storage a, Token storage b) {
    a.value = 7; assert(b.value == 7); a = other; a.value = 8;
  }
  function sameMemory(uint[] memory a, uint[] memory b) {
    a[0] = 5; assert(b[0] == 5);
    a = new uint[](1); a[0] = 8; assert(b[0] == 5);
  }
  function credit(mapping(uint => uint) storage m, uint k) { m[k] = 1; }
  function mutate() returns (uint) { values[0] = 9; return 0; }
  function observe(uint before, uint[] memory a, uint ignored, Token storage t) returns (uint) {
    assert(before == 1); assert(a[0] == 1); t.value = a[0]; return a[0];
  }
  function bad() returns (uint) { assert(false); return 0; }
  function take(uint[] storage a, uint ignored) { a.push(1); }
  function getter(uint[] storage a) returns (uint[] storage r) { r = a; }
  function rootGetter() returns (uint[] storage r) { r = values; }
  function allocateUse(uint[] memory a) { assert(a.length == 2); }
  requires a.length > 0;
  ensures \result == a[0];
  function first(uint[] memory a) returns (uint) { return a[0]; }
  function lengthNonnegative(uint[] memory a) { assert(a.length >= 0); }
}

local instance : InContract := ⟨Calls⟩

private def aliases := sol{
  uint[] memory xs = new uint[](1);
  uint r = mix(2, tok, xs, 3);
  assert(r == 5); assert(tok.value == 2); assert(xs[0] == 3);
  sameStorage(tok, tok);
  assert(tok.value == 7); assert(other.value == 8);
  sameMemory(xs, xs); assert(xs[0] == 5);
  credit(counts, 4); assert(counts[4] == 1);
}

theorem aliases_run : (Prog.run (State.init Calls) aliases).toOption.isSome = true := by
  decide +kernel

private def copies := sol{
  delete values;
  values.push(1);
  uint r = observe(values[0], values, mutate(), tok);
  assert(r == 1); assert(tok.value == 1); assert(values[0] == 9);
}

theorem copies_run : (Prog.run (State.init Calls) copies).toOption.isSome = true := by
  decide +kernel

private def priority := sol{ take(rows[0], bad()); }

theorem reference_failure_first :
    (Prog.run (State.init Calls) priority).halt? = some .revert := by
  decide +kernel

private def receiver := sol{
  getter(values).push(4);
  assert(values[0] == 4);
  getter(values).pop();
  assert(values.length == 0);
  take(rootGetter(), 0); assert(values[0] == 1);
  allocateUse(new uint[](2));
}

theorem receiver_run : (Prog.run (State.init Calls) receiver).toOption.isSome = true := by
  decide +kernel

theorem mapping_proved : ⊨ᶠ dl!{ [ credit(counts, 4); ] counts[4] == 1 } := by
  sol_symex
  sol_close

theorem memory_spec : ⊨ᶠ spec!{first} := by
  sol_symex
  sol_close

theorem memory_input_length : ⊨ᶠ spec!{lengthNonnegative} := by
  sol_symex
  sol_close

example : ¬ holds ((State.init Calls).push (t := .mem (.array Ty.uint)) none)
    (Fml.refInputs Calls [.mem (.array Ty.uint)]) := by
  intro h
  change Upd.afterT .diamond _ _ _ at h
  exact Upd.afterT.of_noExh h (by rfl) (by decide +kernel)

example : ¬ holds ((State.init Calls).push (t := .alias (.array Ty.uint)) none)
    (Fml.refInputs Calls [.alias (.array Ty.uint)]) := by
  intro h
  change Upd.afterT .diamond _ _ _ at h
  exact Upd.afterT.of_noExh h (by rfl) (by decide +kernel)

/-- info: reference calls roundtrip through both source printers -/
#guard_msgs in
run_meta do
  for name in [``aliases, ``copies, ``priority, ``receiver] do
    let info ← Lean.getConstInfo name
    let original := info.value!
    let some ss ← Delab.withPrinter original false (Delab.ppProgS [] original)
      | throwError "reference call printer failed: {name}"
    let printed ← `(sol[Calls]{ $[$ss;]* })
    let parsed ← Lean.Elab.Term.TermElabM.run' do
      let p ← Lean.Elab.Term.elabTermEnsuringType printed info.type
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      pure p
    let state := Lean.mkApp (Lean.mkConst ``State.init) (Lean.mkConst ``Calls)
    let originalRun ← Lean.Meta.mkAppM ``Prog.run #[state, original]
    let parsedRun ← Lean.Meta.mkAppM ``Prog.run #[state, parsed]
    unless ← Lean.Meta.isDefEq originalRun parsedRun do
      throwError "reference call roundtrip changed execution of {name}: {printed}"
    let shownExpr ← Lean.Meta.mkAppM ``Prog.show #[Lean.toExpr ([] : List Var), original]
    let shown ← unsafe Lean.Meta.evalExpr String (Lean.mkConst ``String) shownExpr
    let .ok stx := Lean.Parser.runParserCategory (← Lean.getEnv) `term s!"sol[Calls]\{ {shown} }"
      | throwError "reference call display does not parse: {shown}"
    let parsed ← Lean.Elab.Term.TermElabM.run' do
      let p ← Lean.Elab.Term.elabTermEnsuringType stx info.type
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      pure p
    let parsedRun ← Lean.Meta.mkAppM ``Prog.run #[state, parsed]
    unless ← Lean.Meta.isDefEq originalRun parsedRun do
      throwError "reference call display roundtrip changed execution of {name}: {shown}"
    let shownAgainExpr ← Lean.Meta.mkAppM ``Prog.show #[Lean.toExpr ([] : List Var), parsed]
    let shownAgain ← unsafe Lean.Meta.evalExpr String (Lean.mkConst ``String) shownAgainExpr
    unless shown == shownAgain do
      throwError "reference call display is not stable for {name}: {shownAgain}"
  Lean.logInfo "reference calls roundtrip through both source printers"

end Solidity.Examples.Tactics.ReferenceParameters
