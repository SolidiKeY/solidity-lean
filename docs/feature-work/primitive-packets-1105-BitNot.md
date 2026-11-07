# G25 unsigned bitwise NOT packet

`Solidity.Backend.PrimitivePackets.BitNot` connects actual Source local evaluation to the public memory value compiler and selected model execution for every unsigned byte width from 8 through 256. It reuses the published `UnsignedComplement` laws and the original Source, intrinsic `Val`, compiler and machine; CheckedAdd and producer files are unchanged.

`masked_value` proves the canonical numeric result is `2^bits - 1 - x`. `source_success` preserves the exact Source state and works with either checked setting. `selected` is extracted from the actual `Memory.compileVal` result after proving it succeeds. `public_selection`, `compiled_code`, `narrow_code` and `full_code` expose that selection: widths below 256 use the existing full-word NOT followed by modulo `2^bits` narrowing, while uint256 retains NOT alone. No new AND-based selector or calling convention is substituted.

`target_success` derives the actual run from the existing compiled-value certificate. `success` joins public selection, Source evaluation, value correspondence and target execution. Its premises are a valid unsigned width, canonical Source local read, initial `IntegerLocalFamily` (including index/alias coherence), and the existing full `StateRepr`. No compiled value, desired run, output word or poststate is supplied by the caller. The complete Source state and all target fields below the pushed result are preserved, including arbitrary saved stacks and populated caller memory/aliases/frame.

The Controls fixture proves representation rather than assuming it. A generic exact-word run covers all valid widths and operands. Concrete cases include uint8 zero/maximum/regular values, uint16 `0x1234 -> 0xedcb`, and uint256 zero/maximum. `joint8` quantifies over both pipelines and both checked modes. Negative controls reject incorrect initial values/indices, inadequate Source fuel, invalid width proofs and noncanonical uint8 inputs. Actual unmasked code produces `2^256-6` for input 5, and cannot produce the required uint8 result 250. Protected populated memory cells remain exact.

Modules for coordinator registration:

- `Solidity.Backend.PrimitivePackets.BitNot.Source`
- `Solidity.Backend.PrimitivePackets.BitNot.Selected`
- `Solidity.Backend.PrimitivePackets.BitNot.Target`
- `Solidity.Backend.PrimitivePackets.BitNot.Agreement`
- `Solidity.Backend.PrimitivePackets.BitNot.Controls`

The signature consumer is `tests/primitive-packets-1105/BitNot/Signatures.lean`. Roots, global pins and module-map changes remain coordinator-owned. Validation commands, timings, actual gate outcomes, raw failures and separate finder/skeptic reviews are recorded in the sealed handoff. This packet proves local-expression leaves under its explicit initial representation premises; it does not supply frontend admission/origin, a general G24 producer, native EVM/charged/capacity adequacy, or completion of the original VY3 assignment.
