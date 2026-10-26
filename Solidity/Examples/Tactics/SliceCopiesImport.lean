import Solidity.Frontend.Testing
import Solidity.Calculus.Surface
import Solidity.Examples.Tactics.SliceCopies

/-! The modern, pinned Solidity 0.8.38 fixture follows the same slice-copy
path as native syntax, while preserving calldata local locations. -/
solc_import "../../../tests/solc/SliceCopies.ast.json" hash 0xec803d395de97787
  as Solkey.Migration.SliceCopies testing

namespace Solidity.Examples.Tactics.SliceCopiesImport
open Semantics
open Solidity.Examples.Tactics.SliceCopies (observe_run_of_fuel)
open scoped Scoped
local instance : InContract := ⟨Solkey.Migration.SliceCopies⟩

private def copiesInput := sol{
  uint[] memory a = new uint[](4); a[0] = 3; a[1] = 5; a[2] = 7; a[3] = 9;
  copies(a);
}
/-- Imported Solidity `memory a = v[0:2]; memory b = v;` has the expected successful execution. -/
theorem copies_run : (Prog.run (State.init Solkey.Migration.SliceCopies) copiesInput).isOk = true := by
  apply observe_run_of_fuel copiesInput (State.init Solkey.Migration.SliceCopies) 8 (fun r => r.isOk) rfl
  decide +kernel

private def passingInput := sol{
  uint[] memory a = new uint[](4); a[0] = 3; a[1] = 5; a[2] = 7; a[3] = 9;
  passing(a);
}
/-- Imported Solidity `read(v); mutate(v); echo(xs);` has the expected successful execution. -/
theorem passing_run : (Prog.run (State.init Solkey.Migration.SliceCopies) passingInput).isOk = true := by
  apply observe_run_of_fuel passingInput (State.init Solkey.Migration.SliceCopies) 8 (fun r => r.isOk) rfl
  decide +kernel

private def storageInput := sol{
  uint[] memory a = new uint[](4); a[0] = 3; a[1] = 5; a[2] = 7; a[3] = 9;
  storageCopy(a);
}
/-- Imported Solidity `stored = v; rows.push(xs[1:3]);` has the expected successful execution. -/
theorem storage_run : (Prog.run (State.init Solkey.Migration.SliceCopies) storageInput).isOk = true := by
  apply observe_run_of_fuel storageInput (State.init Solkey.Migration.SliceCopies) 8 (fun r => r.isOk) rfl
  decide +kernel

private def lazyInput := sol{
  uint[] memory a = new uint[](4); a[0] = 3; a[1] = 5; a[2] = 7; a[3] = 9;
  bool skipped = lazy(a); assert(!skipped);
}
/-- Imported Solidity `false && mutate(xs[9:10]) == 0` has the expected successful execution. -/
theorem lazy_run : (Prog.run (State.init Solkey.Migration.SliceCopies) lazyInput).isOk = true := by
  apply observe_run_of_fuel lazyInput (State.init Solkey.Migration.SliceCopies) 8 (fun r => r.isOk) rfl
  decide +kernel


private def bytesInput := sol{ bytes memory b = hex"0061626300"; hashes(b); }
/-- Imported Solidity slice hashes equal the hashes of `abc`, even after writing its copy. -/
theorem hashes_run : (Prog.run (State.init Solkey.Migration.SliceCopies) bytesInput).isOk = true := by
  apply observe_run_of_fuel bytesInput (State.init Solkey.Migration.SliceCopies) 8 (fun r => r.isOk) rfl
  decide +kernel

private def narrowInput := sol{
  uint8[] memory a = new uint8[](2); a[1] = 255;
  bool[] memory b = new bool[](2); b[1] = true;
  bytes2[] memory c = new bytes2[](2); c[1] = 0x1234; narrow(a, b, c);
}
/-- Imported Solidity primitive slice copies retain their element shape. -/
theorem narrow_run : (Prog.run (State.init Solkey.Migration.SliceCopies) narrowInput).isOk = true := by
  apply observe_run_of_fuel narrowInput (State.init Solkey.Migration.SliceCopies) 8 (fun r => r.isOk) rfl
  decide +kernel

private def invalidBounds := sol{
  uint[] memory a = new uint[](3); uint[] memory b = invalidRange(a);
}
/-- Imported Solidity crossed endpoints produce ordinary revert, not exhaustion or panic. -/
theorem invalidRange_run : (match Prog.run (State.init Solkey.Migration.SliceCopies) invalidBounds with
    | .error .revert => true | _ => false) = true := by
  apply observe_run_of_fuel invalidBounds (State.init Solkey.Migration.SliceCopies) 8
    (fun r => match r with | .error .revert => true | _ => false) rfl
  decide +kernel

private def failedAssertion := sol{
  uint[] memory a = new uint[](3); a[1] = 5; falsePost(a);
}
/-- Imported Solidity assertion `xs[1] == 99` fails after changing only its copy. -/
theorem falsePost_run : (match Prog.run (State.init Solkey.Migration.SliceCopies) failedAssertion with
    | .error .panic => true | _ => false) = true := by
  apply observe_run_of_fuel failedAssertion (State.init Solkey.Migration.SliceCopies) 8
    (fun r => match r with | .error .panic => true | _ => false) rfl
  decide +kernel

private def aliasesInput := sol{
  Pair memory p = Pair(17); uint[2] memory a = [uint(1), 2]; aliases(p, a);
}
/-- Imported Solidity calldata struct/fixed-array aliases retain the pre-existing path. -/
theorem aliases_run : (Prog.run (State.init Solkey.Migration.SliceCopies) aliasesInput).isOk = true := by
  apply observe_run_of_fuel aliasesInput (State.init Solkey.Migration.SliceCopies) 8 (fun r => r.isOk) rfl
  decide +kernel

end Solidity.Examples.Tactics.SliceCopiesImport
