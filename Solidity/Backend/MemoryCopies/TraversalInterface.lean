import Solidity.Theory.Typed.Mem

/-! Fresh sibling identities from the existing typed storage-copy traversal.
This describes the actual fold, without another traversal or shape selector. -/
namespace Solidity.Backend.MemoryCopies

/-- Every copied reference sibling is new and appears after its predecessors.
The vector may contain arbitrary existing intrinsic nested reference values.
This is an intrinsic heap obligation, not a storage-layout compiler premise. -/
structure TraversalFreshCertificate {H : HTy} {R : RefTy} {n : Nat}
    (heap : Heap H) (values : SVec (.ref R) n)
    (memory : (Ty.ref R).mapFree = true) : Prop where
  fresh : ∀ identity ∈ (values.copyStToM heap memory).val.1.map (fun reference => reference.id),
    H.length ≤ identity
  ordered : ((values.copyStToM heap memory).val.1.map (fun reference => reference.id)).Pairwise (· < ·)

end Solidity.Backend.MemoryCopies
