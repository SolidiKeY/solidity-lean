# Scalar lowering

[Authoritative source](../../Solidity/Backend/Scalar).

Arithmetic agreement must use the actual Solidity width, signedness and checked/unchecked mode. A word-level identity does not by itself justify source casts or overflow behavior. External opcode execution and source-evaluation order require their own correspondence, beyond symbolic stack arithmetic.
