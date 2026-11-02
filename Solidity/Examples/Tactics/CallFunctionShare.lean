import Solidity.Tools.CallFunctionShare
import Solidity.Calculus.Closers
namespace Solidity.Examples.Tactics.CallFunctionShare
def Affine : Contract := contract!{
  function f0(uint x) returns (uint r) { r = x * 3 + 1; }
  function f1(uint x) returns (uint r) { r = f0(f0(x)); }
  function f2(uint x) returns (uint r) { r = f1(f1(x)); }
  function f3(uint x) returns (uint r) { r = f2(f2(x)); }
  function f4(uint x) returns (uint r) { r = f3(f3(x)); }
  function f5(uint x) returns (uint r) { r = f4(f4(x)); }
  function f6(uint x) returns (uint r) { r = f5(f5(x)); }
  function f7(uint x) returns (uint r) { r = f6(f6(x)); }
  function f8(uint x) returns (uint r) { r = f7(f7(x)); }
}
local instance : InContract := ⟨Affine⟩
open scoped Solidity.Scoped
/-- Full parsed-source result through the unchanged walk and checked sharing. -/
theorem affineSix : ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f6(a); ⟩ y >= a } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close_call_shared

/-- The same producer at another actual source level. -/
theorem affineSeven : ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f7(a); ⟩ y >= a } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close_call_shared

/-- Successful and failed executions retain the original box observation. -/
theorem affineSixBox : ⊨ᶠ dl!{ [ uint y = f6(a); ] y >= a } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close_call_shared

/-! Original and transformed complete leaves of the same parsed source.
The open count belongs to the original walk, before this optional consumer. -/
/-- info: 5 node(s), 1 branch(es), 0 original open, old largest leaf 26, shared largest leaf 26 term node(s) -/
#guard_msgs in
#proof_share_size dl!{ a < 1000 → ⟨ uint y = f1(a); ⟩ y >= a }

/-- info: 5 node(s), 1 branch(es), 1 original open, old largest leaf 274, shared largest leaf 269 term node(s) -/
#guard_msgs in
#proof_share_size dl!{ a < 1000 → ⟨ uint y = f6(a); ⟩ y >= a }

/-- info: 5 node(s), 1 branch(es), 1 original open, old largest leaf 530, shared largest leaf 302 term node(s) -/
#guard_msgs in
#proof_share_size dl!{ a < 1000 → ⟨ uint y = f7(a); ⟩ y >= a }

/-- error: #proof_share_size: not a closed scoped formula `Fml C Γ` (`cdl!{ … }`, or `dl!{ … }` under `open scoped Solidity.Scoped`) -/
#guard_msgs in
#proof_share_size (7 : Nat)
end Solidity.Examples.Tactics.CallFunctionShare
