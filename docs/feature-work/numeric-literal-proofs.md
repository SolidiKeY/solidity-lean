# Literal correctness boundary

[Authoritative source](../../Solidity/Frontend/NumericLiteralProofs); keep [original acceptance](../../scripts/check-sol-numeric-literals.py) and [H296 integrated acceptance](../../scripts/check-sol-numeric-literals-integrated.py) distinct (`--help` describes the integrated modes).

Accepted spelling, exact numerical interpretation, source typing and emitted machine-width behavior are distinct obligations. A host parser or byte-vector regression is not a kernel proof of the source interpretation. Preserve the pinned compiler/grammar and the intrinsic width/scale constraints.
