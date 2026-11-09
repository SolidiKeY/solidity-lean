# Checked frontend trust boundary

[Authoritative source](../../Solidity/Frontend/Checked).

The independent checked frontend targets the pinned Solidity grammar. An untrusted proposer is acceptable only where its certificate is checked against that grammar. Solc JSON import and the independent parser are distinct trust paths; successful importer regression tests do not prove lexer/parser completeness or exact source provenance.

<a id="g08-checked-lexical-analysis"></a>

<a id="g09-type-and-declaration-syntax"></a>

<a id="g10-expressions"></a>

<a id="g11-statements-definitions-and-whole-units"></a>
