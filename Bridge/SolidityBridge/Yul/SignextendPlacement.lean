import SolidityBridge.Yul.BinaryPlacement
import SolidityBridge.Yul.SignedPlacement
import SolidityBridge.RoadmapV15.P10.SignExtensionPositive
/-! Concrete producer bodies for the typed binary placement consumer. Source
indices/full dirty words remain the actual compiler's; no new semantics/state.
No generic-interface hypothesis is counted as final concrete adequacy. -/
namespace SolidityBridge.Yul.SignextendPlacement
open Solidity Solidity.Yul Solidity.Yul.Closed Solidity.Yul.Compilation
open Backend Scalar Solidity.Evm.External EvmYul
open SolidityBridge.RoadmapV15

def expr : Expr [] [] 2 1 :=
  .builtin (.pure .signextend) (Fin.cases (.local 0) (fun _ => .local 1))
def compiled := (PureExpressions.compile 2 expr).get (by rfl)

/-- Real producer proof for every index/value word, including large indices,
negative residues and truncation. Actual emitted compiler code is also proved. -/
def primitive : BinaryPlacement.Primitive .SIGNEXTEND compiled :=
  ⟨rfl,fun site a b tail room gas fuel =>
    (P10.signextend_all_agreement site a b tail room gas fuel).2⟩

/-- Concrete checked instantiation, not an unproved interface parameter. -/
abbrev continuation := BinaryPlacement.continuation primitive

/-- A second real producer demonstrates reuse without changing earlier
signed-quotient contracts or their code. -/
def signedPrimitive : BinaryPlacement.Primitive .SDIV SignedPlacement.sdivCompiled :=
  ⟨rfl,fun site a b tail room gas fuel =>
    (P10.sdiv_agreement site a b tail room gas fuel).2⟩

abbrev signedContinuation := BinaryPlacement.continuation signedPrimitive

#print axioms primitive
#print axioms continuation
#print axioms signedPrimitive
#print axioms signedContinuation
end SolidityBridge.Yul.SignextendPlacement
