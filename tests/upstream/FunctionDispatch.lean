import Solidity.Tools.Upstream
import Solidity.Calculus.LinearCountermodel

/-! Kernel regressions for typed reference-return dispatch and effectful while heads. -/
namespace Solidity.Upstream.Group05
open Semantics

def MemoryValues : Contract := contract!{
  bytes source;
  uint calls;
  function () returns (bytes memory) f;
  function other() returns (bytes memory r) { return hex"7a"; }
  function first() returns (bytes memory r) { calls++; f = other; return source; }
  function invoke() returns (uint r) { bytes memory b = f(); return b.length; }
}

def memoryAlias := sol[MemoryValues]{
  source = hex"616263";
  f = first;
  bytes memory b = f();
  assert(calls == 1);
  assert(b.length == 3);
  assert(b[0] == bytes1(0x61));
  b[0] = bytes1(0x64);
  assert(b[0] == bytes1(0x64));
  assert(source[0] == bytes1(0x61));
  bytes memory c = f();
  assert(c.length == 1);
  assert(c[0] == bytes1(0x7a));
  assert(calls == 1);
}

theorem memoryAlias_run :
    (Prog.run (State.ofStorage (Storage.init MemoryValues)) memoryAlias).halt? = none := by
  decide +kernel

def unassigned := sol[MemoryValues]{ bytes memory b = f(); }
theorem unassigned_reverts :
    (Prog.run (State.ofStorage (Storage.init MemoryValues)) unassigned).halt? = some .revert := by
  decide +kernel

def wrongByte := sol[MemoryValues]{
  f = other;
  bytes memory b = f();
  assert(b[0] == bytes1(0x61));
}
theorem wrongByte_panics :
    (Prog.run (State.ofStorage (Storage.init MemoryValues)) wrongByte).halt? = some .panic := by
  decide +kernel

def pointerPanic := sol[MemoryValues]{
  bool caught = false;
  try this.invoke() returns (uint n) { assert(false); }
  catch Panic(uint code) { caught = true; assert(code == 81); }
  catch { assert(false); }
  assert(caught);
}
def deployedMemoryState : State MemoryValues [] :=
  let σ := State.ofStorage (Storage.init MemoryValues)
  { σ with tx := { σ.tx with selfAddress := ⟨7, by decide +kernel⟩ } }

theorem pointerPanic_exact :
    (Prog.run deployedMemoryState pointerPanic).halt? = none := by
  decide +kernel

def LoopValues : Contract := contract!{
  uint checks;
  function early() returns (uint r) { while (checks++ < 9) { return checks; } }
  function bad() returns (bool r) { checks++; revert(); }
  function failLoop() { while (bad()) { checks = 99; } }
  function read() returns (uint r) { return checks; }
}

def effectfulHeads := sol[LoopValues]{
  uint i = 0;
  uint y = 77;
  while ((y = i++) < 3) { if (i == 2) { continue; } }
  assert(i == 4);
  assert(y == 3);
  while (i++ < 9) { break; }
  assert(i == 5);
  while (false && i++ < 99) { assert(false); }
  assert(i == 5);
  uint z = early();
  assert(z == 1);
  assert(checks == 1);
}

theorem effectfulHeads_run :
    (Prog.run (State.ofStorage (Storage.init LoopValues)) effectfulHeads).halt? = none := by
  rcases Prog.runF_approx 8 effectfulHeads (State.ofStorage (Storage.init LoopValues)) with h | h
  · exact absurd (congrArg TRes.halt? h) (by decide +kernel)
  · rw [Prog.run, ← h]
    decide +kernel

def failedHead := sol[LoopValues]{ while (bad()) { assert(false); } }
theorem failedHead_reverts :
    (Prog.run (State.ofStorage (Storage.init LoopValues)) failedHead).halt? = some .revert := by
  rcases Prog.runF_approx 3 failedHead (State.ofStorage (Storage.init LoopValues)) with h | h
  · exact absurd (congrArg TRes.halt? h) (by decide +kernel)
  · rw [Prog.run, ← h]
    decide +kernel

-- Failed condition effects do not commit across API calls.
#eval (do
  let rows : List Frontend.ImportRow := ["failLoop", "read"].map fun name =>
    { name, sourceSignature := name ++ "()", tag := .diamond, params := [],
      status := .elaborated, reason := "" }
  let data ← IO.ofExcept (Lean.Json.parse
    "{\"vectors\":[{\"signature\":\"failLoop()\",\"args\":[],\"failure\":true,\"expected\":[]},{\"signature\":\"read()\",\"args\":[],\"failure\":false,\"expected\":[\"0\"]}]}")
  let report := Tools.Upstream.replay LoopValues rows data
  unless (report.getObjValAs? String "status").toOption == some "working" do
    throw (IO.userError report.pretty) : IO Unit)

open Linear in
theorem hypothesis_projection :
    ((AFml.imp (.and (.eq [1] 0) (.le [0, 1] 7)) (.le [0, 1] 7)).hypVerify?).isSome = true := by
  decide +kernel

open Linear in
theorem false_not_certified : ((AFml.eq [] 1).hypVerify?).isSome = false := by
  decide +kernel

open Linear in
theorem false_still_refuted :
    (match AFml.verify (.eq [] 1) with | .inl _ => false | .inr _ => true) = true := by
  decide +kernel

/-- info: 'Solidity.Upstream.Group05.pointerPanic_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pointerPanic_exact
/-- info: 'Solidity.Upstream.Group05.hypothesis_projection' depends on axioms: [propext] -/
#guard_msgs in #print axioms hypothesis_projection
/-- info: 'Solidity.Upstream.Group05.false_not_certified' depends on axioms: [propext] -/
#guard_msgs in #print axioms false_not_certified
/-- info: 'Solidity.Upstream.Group05.false_still_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms false_still_refuted
/-- info: 'Solidity.Upstream.Group05.memoryAlias_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memoryAlias_run
/-- info: 'Solidity.Upstream.Group05.unassigned_reverts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unassigned_reverts
/-- info: 'Solidity.Upstream.Group05.wrongByte_panics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wrongByte_panics
/-- info: 'Solidity.Upstream.Group05.effectfulHeads_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms effectfulHeads_run
/-- info: 'Solidity.Upstream.Group05.failedHead_reverts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms failedHead_reverts
end Solidity.Upstream.Group05
