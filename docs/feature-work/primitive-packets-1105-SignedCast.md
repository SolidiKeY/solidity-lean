# Signed narrowing and widening cast packet

The modules under `Solidity/Backend/PrimitivePackets/SignedCast/` connect the existing signed-width Source conversion to public memory-compiler selection and the intrinsic instruction interpreter. Every approved source and destination byte width (8 through 256 bits) is covered. Selection is proved total for those widths; callers supply neither selected certificates nor desired runs.

`source_success` retains the exact Source state and explicit conversion behavior, independently of checked arithmetic mode. `selection_exists` and `public_selection` discharge selection. `target_success` and `success` preserve the full target machine below the result word and an arbitrary saved stack, given the existing initial local family and full `StateRepr`. Those initial representation premises are not physical-input-origin proofs.

`signextend_source` separately proves that actual scalar `SIGNEXTEND` execution gives the encoding of the same Source wrapped integer. The public memory compiler uses the existing typed conditional/modulo/subtraction expansion; this packet does not claim it emits `SIGNEXTEND` or replace its code with that opcode.

Controls instantiate the agreement in both Source pipelines and include int16-to-int8 negative truncation, the positive-to-negative boundary, int16-to-int256 widening, populated memory, arbitrary caller tails, wrong signedness/width/byte index and operand shortage. A complete model frame equality is stronger than the finite ordered-memory sample. The supplied caller fixture has an empty typed heap and populated physical memory; general agreement permits every state with the stated representation.

These are kernel model proofs, not fetched Osaka execution, external compiler/EVM tests, arbitrary CALL/world or transaction correspondence. No Source implementation, compiler, reserved adapter, budget, premise or exclusion is changed. Registration, module-map and axiom-pin updates are left to the coordinator as assigned.
