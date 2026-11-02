import Solidity.Source.Decls

/-! Decidable identity of intrinsic source declarations for finite call allowlists.
No syntax representation is changed. The derived instances are global: no other
`DecidableEq` or `BEq` for `Syn` or `Decl` exists.
-/
namespace Solidity.Source

deriving instance DecidableEq for Syn
deriving instance DecidableEq for Decl

end Solidity.Source
