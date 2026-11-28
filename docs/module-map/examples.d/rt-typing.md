| `Examples/RedTeam/Typing/AddressRange.lean` | Red team: `address a = 2^200; address b = a + 1;` (both rejected by solc) elaborate and run to an address above `2^160`. |
| `Examples/RedTeam/Typing/BytesIntMix.lean` | Red team: implicit `uint8`↔`bytes1`, a short hex literal at `bytes2` and `bytes1 + bytes1` (all rejected by solc) elaborate and run. |
| `Examples/RedTeam/Typing/ConstantWrite.lean` | Red team: assignments to a `constant` and to an `immutable` outside the constructor (rejected by solc) elaborate and change the values. |
| `Examples/RedTeam/Typing/EnumConversions.lean` | Red team: implicit enum↔`uint` conversions and `E(5)` (rejected by solc) elaborate; the last runs to a panic. |
| `Examples/RedTeam/Typing/Mutability.lean` | Red team: a `view` body writing storage, a `pure` body reading it and `msg.value` in a non-payable function (rejected by solc) elaborate and run. |
| `Examples/RedTeam/Typing/NarrowRootWrite.lean` | Red team: widths live outside `Ty`, so the typed statement `s = 300;` at a `uint8` root is a `Stmt` and its run leaves `s > 255`. |
