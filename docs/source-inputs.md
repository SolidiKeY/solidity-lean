# Source obligation input premises

`Frontend/Problems.lean` builds plain imported source obligations over the
model's typed states. Their premises describe the initial domain of a Solidity
execution: parameter and array-element ABI bounds, nonpayable value rejection,
and the documented ether-supply bound where applicable.

Every such source obligation also assumes `address(this) < 2^160`, including
constructor obligations. EVM addresses occupy 160 bits; this is an environment
input condition, not a property proved from the function body or an ABI decoder
check. The lower bound is already supplied by the unsigned native word type.
The premise is unconditional so an address read inside an inlined helper,
resolved external self call, getter or synthesized finite-dispatch branch is
covered without relying on a syntactic read detector.

The native `TTx.selfAddress` field remains a 256-bit word. Native
`Calculus.Problem.fml`, direct `Problem.callPre` callers using its default
arguments, ordinary native formulas, and the specified-function pipeline are
unchanged. This source premise does not establish a general compiler/EVM
simulation theorem or impose new constraints on `msg.sender`.

Actual source address casts retain their meaning. In particular, projecting a
stored external function value's address and converting it to `address` still
cleans to 160 bits. With native `selfAddress = 2^200`, the packed value fits in
256 bits, but this cleaned projection differs from the broader native
`address(this)`. The concrete projection control panics there, demonstrating
why a source proof must state its EVM input domain rather than erase the cast.
The maximum EVM address has a separate successful projection control.

`--self-address A` and Lean `solc_scoped_problems N self A` optionally pin the
deployment address. They reject `A >= 2^160` before generating obligations;
otherwise the explicit equality could contradict the canonical premise and
allow a vacuous result. Address zero and `2^160 - 1` remain in the input domain.
`SourceAdmissionImport` pins both endpoints, the first rejected word, a much
wider native countermodel, and premise inclusion even without a direct read.
The CLI regression rejects decimal and hexadecimal out-of-range inputs before
starting compiler or proof jobs.

The source `FunctionTypes.sol` positive `externalValue` verdict remains
`proved`; its assertions and expected status are not weakened. Combined
validation of these changes is **in progress** in
[feature-work/integration.md](feature-work/integration.md).

The source problem printer evaluates the imported contract and formula only to
render their typed data. These two metaprogramming sites replace the former
string-evaluation site in the trust inventory; they neither create proofs nor
decide whether an obligation holds.

`#solkey_problem` preserves the source premises in its displayed obligation:
each implication is shown before the named call, with nested quantified
premises rendered by the existing typed formula printer in the surrounding
parameter names. Constructor deployment updates remain visible. Primitive
parameters keep KeY sort names; reference parameters use an explicit
`bind[box]` or `bind[diamond]` label with the model type. Those labels are a
source-output extension, not newly supported KeY input sorts. The native
`Problem.parts` and `Problem.text` APIs remain unchanged. The source command
fails explicitly on a shape it cannot describe; it does not print a weaker
obligation or silently drop input conditions.
