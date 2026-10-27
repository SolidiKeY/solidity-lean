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
`);
    execFileSync('lake', ['--quiet', '--no-build', 'lean', check, '--', '--tstack=131072'],
      {stdio:'pipe', encoding:'utf8', timeout:60000});
  } finally {
    rmSync(directory, {recursive:true, force:true});
  }
});
