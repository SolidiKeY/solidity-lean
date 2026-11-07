import Solidity.Source.Types

/-! ABI head dimensions for the owned calldata aggregate subset. The existing
Source values and judgments are retained. Dynamic or unmodelled shapes use an
offset head; static arrays occupy their complete inline head span. -/
namespace Solidity.Source

/-- Statically encoded words for the represented ABI subset. Zero means a
dynamic or unmodelled head, not an assumption of a zero-sized encoding.
Struct layouts remain outside this producer. -/
def STy.cdStaticWords (τ : STy) : Nat :=
  if τ.oneWord then 1 else match τ with
    | .array _ σ (some length) => length*σ.cdStaticWords
    | _ => 0

/-- A dynamic element occupies one offset word; a represented static array
occupies all its inline words. -/
def STy.cdHeadBytes (τ : STy) : Nat := 32*max 1 τ.cdStaticWords

def STy.cdStride : STy → Nat
  | .bytes _ | .string _ => 1
  | .array _ σ _ => σ.cdHeadBytes
  | _ => 32


end Solidity.Source
