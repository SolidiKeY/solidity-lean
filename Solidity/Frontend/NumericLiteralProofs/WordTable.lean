import Solidity.Frontend.NumericLiteralProofs.WordTable.Part29

/-! # Every fixed word is disjoint from numeric tokens -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

theorem solWordTable_no_num (raw : Bytes) (n : NumLit) :
    solWordTable raw ≠ .tok (.num n) := table_prefix_root raw n

end Solidity.Frontend.NumericLiteralProofs
