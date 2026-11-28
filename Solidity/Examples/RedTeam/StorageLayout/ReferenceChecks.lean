import Solidity.Storage.HashedKeccak
import Solidity.ERC7201

/-!
# Independent word-layout and namespace reference vectors

`check-reference.py` computes these with PyCryptodome Keccak-256. The roots
come from `Layout.sol` checked by solc. These are executable checks, not a
universal solc refinement theorem or an external EVM execution. Solc storage
metadata does not itself enumerate hashed entry addresses.
-/
namespace Solidity.Examples.RedTeam.StorageLayout.ReferenceChecks
open Solidity.Storage

-- uint256[] words at slot 7: element 3, stride one.
#guard Loc.word (2 ^ 256) keccakH (.data (.root 7) 3) ==
  0xa66cc928b5edb82af9bd49922954155ab7b0942694bea4ce44661d9a8736c68b

-- wallets at slot 9; Wallet.stash is at member offset 1.
#guard Loc.word (2 ^ 256) keccakH (.hash 9 (.hash 5 (.root 9) 1) 0) ==
  0x24ca46cb27a3a19b4f1680b91a5b967a5f2bbf9ba773a8b64741dc16a52f7a90

-- Solidity bool[] bits at slot 8: element 1 shares the data base at byte 1.
-- The full-word model instead adds one to this base (BoolPacking witness).
#guard Loc.word (2 ^ 256) keccakH (.data (.root 8) 0) ==
  0xf3f7a9fe364faab93b216da50a3214154f22a0a2b415b23a84c8169e8b636ee3

#guard (Solidity.ERC7201.root "example.storage.Layout".toUTF8.toList).val ==
  0x1e0ff7cc49d2ef7d2fd80942c4710ca44af1d633174b1be50f21e91312d81200

end Solidity.Examples.RedTeam.StorageLayout.ReferenceChecks
