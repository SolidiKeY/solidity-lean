# Compiler verification

The verified Solidity → EVM compiler (`Solidity/Evm/`: a stack machine, a
compiler from the untyped AST, a uint256-bounded interpreter and a Leroy-style
forward simulation) was written against the untyped syntax and removed when
the core became typed (commit `9721af1` is the last one that has it, with this
document in full).

**To port:** mini-solkey's `Ch08_EVM`, `Ch09_Compiler` and `Ch10_Correctness`
are the model — a compiler over `Stmt C` and a simulation against
`Stmt.run` — scaled up from mini-solkey's storage fragment to memory, arrays
and `transfer`.
