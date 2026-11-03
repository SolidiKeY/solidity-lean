import Solidity.Backend.FunctionValues.Interface
import Solidity.Backend.WorldCalls.ExternalCalls

/-! Signature-only G42.05 declared-call boundary. No G42.02 execution,
G42.04 library or G40 decoder producer is supplied. In particular CALL is
not presented as STATICCALL, and no dynamic-function RExpr lowering is inferred. -/
namespace Solidity.Backend.FunctionValues
open Solidity.Source Solidity.Roadmap
open Solidity.Lowering.Readonly

/-- Binding to an existing declared invocation, with the same full function
signature, receiver, mutability and selector prefix. Arbitrary captured
function values need not have such a declaration binding. -/
structure DeclaredBinding (E : Env) (Γ : RCtx) (dn : DeclName)
    (ps rs : List STy) (m : Option Source.Mutability)
    (value : ExternalValue E.layout ps rs m) where
  invocation : InvocationFrame.Invocation E Γ dn ps rs
  receiver : invocation.captured.receiver = value.address
  mutability : invocation.declaration.fnMut = m
  selector : ∃ suffix : List UInt8, invocation.captured.input = value.selector ++ suffix

/-- Unchanged G42.02 interfaces, indexed by the actual bound invocation.
These fields alone assert no coverage, static opcode adequacy, dynamic call
lowering or nonvacuous execution. Consumers must supply a reached Fetched run. -/
structure DeclaredCallBoundary (binding : DeclaredBinding E Γ dn ps rs m value) where
  world : WorldCalls.Premises binding.invocation
  fetched : WorldCalls.FetchedPremises binding.invocation world

end Solidity.Backend.FunctionValues
