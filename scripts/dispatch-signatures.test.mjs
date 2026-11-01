import {test} from 'node:test';
import {mkdtempSync, writeFileSync, rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {execFileSync} from 'node:child_process';

test('callable signatures preserve nested modes, native keys and boundary refusals', () => {
  const directory = mkdtempSync(join(tmpdir(), 'solidity-dispatch-signature-'));
  try {
    const check = join(directory, 'Check.lean');
    writeFileSync(check, `import Solidity.Frontend.SolcJson.Contract
open Solidity.Frontend.FiniteDispatch

-- Every signature renders exactly as the previous function-type representation.
example (external : Bool) (parameters returns : List Ty) :
    (Signature.mk parameters returns).native external =
      (Ty.function external parameters returns).native := rfl

#eval do
  let parse (text : String) : IO (Bool × Signature) := do
    let some result := parseCallable 32 text
      | throw (IO.userError s!"callable unexpectedly refused: {text}")
    pure result
  let (external, nested) ← parse "function(function(uint) external returns(bool)) internal returns(bytes4)"
  let (otherExternal, otherNested) ← parse "function(function(uint) internal returns(bool)) external returns(bytes4)"
  unless !external && otherExternal && nested != otherNested do
    throw (IO.userError "outer mode erased a nested function's visibility")
  let (internal, address) ← parse "function(address) internal returns(bool)"
  let (external, word) ← parse "function(uint256) external returns(bool)"
  unless !internal && external && address != word && address.native true == word.native true do
    throw (IO.userError "source address/uint identity or native erasure changed")
  for source in ["uint256", "bool", "function(uint[]) internal returns(bool)",
      "function(Missing) external returns(bool)"] do
    unless (parseCallable 32 source).isNone do
      throw (IO.userError s!"unsupported callable admitted: {source}")
  unless (parseCallable 0 "function() internal returns()").isNone do
    throw (IO.userError "callable parsing ignored its fuel bound")
  let (external, bytes) ← parse "function() internal returns(bytes memory)"
  unless !external && bytes.parameters.isEmpty && bytes.returns == [Ty.memoryBytes] do
    throw (IO.userError "memory-byte return location lost")
  let (external, array) ← parse "function(uint256[] memory, address) internal returns(uint256)"
  unless !external && array.parameters == [Ty.memoryArray (.word false ⟨31, by decide⟩), Ty.address] do
    throw (IO.userError "memory-array parameter location lost")
  unless array.native false == "function(uint[]memory,uint)returns(uint)" do
    throw (IO.userError s!"memory-array native key changed: {array.native false}")
  let (_, addresses) ← parse "function(address[] memory) internal returns(uint256)"
  unless addresses != array && (addresses.parameters.map Ty.native) == ["uint[]memory"] do
    throw (IO.userError "memory-array element identity or native erasure changed")
  let (_, storageArray) ← parse "function(uint256[] storage pointer) internal returns(uint256)"
  unless storageArray.parameters == [Ty.storageArray (.word false ⟨31, by decide⟩)] do
    throw (IO.userError "storage-array parameter location lost")
  let (_, memoryStruct) ← parse "function(struct C.P memory) internal returns(uint256)"
  let (_, storageStruct) ← parse "function(struct C.P storage pointer) internal returns(uint256)"
  let (_, otherStruct) ← parse "function(struct C.Q memory) internal returns(uint256)"
  unless memoryStruct.parameters == [Ty.nominal "C.P" false] &&
      storageStruct.parameters == [Ty.nominal "C.P" true] &&
      memoryStruct.native false != otherStruct.native false do
    throw (IO.userError "struct parameters lost their nominal identity or location")
  for source in ["function(uint256[] calldata) internal returns(uint256)",
      "function(struct C.P calldata) internal returns(uint256)",
      "function(bytes1[] memory) internal returns(uint256)",
      "function(uint256[][] memory) internal returns(uint256)",
      "function(function() internal[] memory) internal returns(uint256)"] do
    unless (parseCallable 64 source).isNone do
      throw (IO.userError s!"unsupported reference callable admitted: {source}")
`);
    execFileSync('lake', ['--quiet', '--no-build', 'lean', check, '--', '--tstack=131072'],
      {stdio:'pipe', encoding:'utf8', timeout:60000});
  } finally {
    rmSync(directory, {recursive:true, force:true});
  }
});
