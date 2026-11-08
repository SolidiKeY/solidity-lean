# Assembler boundary

[Authoritative source](../../Solidity/Backend).

Emitted code observations must distinguish instruction-list execution from byte fetching. Jump relocation, PUSH widths and complete code-image provenance must hold for the actual emitted bytes. Agreement for individual encoding vectors does not identify an arbitrary physical byte array with an assembler output.
