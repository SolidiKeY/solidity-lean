import Solidity.Correctness.Lowering.Total.Decode.Callee.Functions

/-!
# Ordinary function headers from retained source metadata

Source identity is independent of model aliases. This adapter uses the retained
source name, visibility and mutability to call the declaration assembler.
It covers ordinary contract-local functions and selected ABI functions. Free
functions, retained inherited entries, special entries, implementation-only
roles and absent metadata remain unsupported here. Those are implementation
gaps, not new admission conditions or a universal-coverage claim. Full ABI
signature/selector agreement, inheritance and model `payable` agreement remain
separate obligations.
-/
namespace Solidity.Correctness.Lowering.Total.Decode.Callee

/-- Visibility of an ordinary declaration whose role is representable by the
non-virtual contract-function assembler. -/
def ordinaryVisibility : SourceCallable → Option Source.Visibility
  | .local .privateFn => some .priv
  | .local .internalFn => some .internal
  | .abi .publicFn .selected _ => some .pub
  | .abi .externalFn .selected _ => some .external
  | _ => none

/-- Nonpayable has no explicit mutability token; all other retained tokens
are emitted without interpreting the model's separate payable flag. -/
def sourceMutability : SourceMutability → Option Source.Mutability
  | .nonpayable => none
  | .pureFn => some .pure
  | .viewFn => some .view
  | .payable => some .payable

/-- Translate an ordinary declaration using its own retained source header.
No model-name alias or independently supplied header replaces source identity. -/
def fromMetadata (T : Tables) (R : CallSpellExt.Registry) (scope : String)
    (d : FunDecl) : Option Source.Decl := do
  let source ← d.sourceDecl
  let visibility ← ordinaryVisibility source.callable
  functionDecl T R scope source.name (some visibility) (sourceMutability source.mutability) d

/-- The emitted declaration has the retained source identity and header, and
is exactly the existing assembly of the original declaration. This bridge
allows its body/frame certificate to be reused without a second traversal;
it does not prove ABI, inheritance, payable-value or execution agreement. -/
theorem fromMetadata_header {T : Tables} {R : CallSpellExt.Registry}
    {scope : String} {d : FunDecl} {out : Source.Decl}
    (h : fromMetadata T R scope d = some out) :
    ∃ source visibility, d.sourceDecl = some source ∧
      ordinaryVisibility source.callable = some visibility ∧
      functionDecl T R scope source.name (some visibility)
        (sourceMutability source.mutability) d = some out ∧
      out.name = source.name ∧ out.scope = some scope := by
  simp only [fromMetadata, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨source, hs, visibility, hv, hd⟩ := h
  obtain ⟨_, _, _, _, _, _, _, _, he, _⟩ :=
    functionDecl_faithful T R scope source.name (some visibility)
      (sourceMutability source.mutability) d out hd { decls := [] }
  exact ⟨source, visibility, hs, hv, hd, congrArg Source.Decl.name he,
    congrArg Source.Decl.scope he⟩

end Solidity.Correctness.Lowering.Total.Decode.Callee
