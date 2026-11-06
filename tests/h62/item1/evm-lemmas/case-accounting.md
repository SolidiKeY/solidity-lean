# H70 exact case accounting at c6f550e

This is source accounting, not a Lean proof, extraction, or performance gate.
The H70 router accepted an owner ticket for solidity-v12-v17-20261031/v14-payments-bytecode; it grants no file edit permission. The relay is host-only.

## First-statement revert

All seven private declarations have identical statements and proof bodies. Each derives `(Prog.cons s P).run σ = .error .revert` from `s.run σ = .error .revert`. Each is used once, paired with `run_append_revert hc`. The distinct successful-first-statement / reverting-tail arm uses `by rw [ho']; rfl`; preserve it and the successful tail case.

| File | Declaration | First-statement revert | Tail revert |
|---|---:|---:|---:|
| `Solidity/Evm/MemoryCompile.lean` | 861 | 914 | 913 |
| `Solidity/Evm/MemoryFixedCompile.lean` | 145 | 169 | 168 |
| `Solidity/Evm/MemoryObjectCompile.lean` | 104 | 126 | 125 |
| `Solidity/Evm/MemoryObjectConstructionCompile.lean` | 320 | 357 | 356 |
| `Solidity/Evm/MemoryRefArrayCompile.lean` | 83 | 104 | 103 |
| `Solidity/Evm/MemoryStorageConstructionCompile.lean` | 66 | 112 | 111 |
| `Solidity/Evm/MemoryStorageCopyCompile.lean` | 722 | 780 | 779 |

`Solidity/Evm/Correct.lean:894` proves the general error version with the same proof. A syntactic import traversal by the finder found no transitive import of Correct by these consumers. Import or extraction needs owner agreement, acyclic dependency verification, registration and measured before/after checking.

## Storage location cases

These are symbolic `Solidity.Storage.Loc` inequalities, not EVM `Slot`. Some uses need the reverse orientation.

| File | Case and use |
|---|---|
| `Solidity/Backend/StorageOps/NestedPopTransport.lean` | child :40 and grandchild :45; query cases :65,67 and reverse orientations :161–163 |
| `Solidity/Backend/StorageOps/NestedClearFrames.lean` | inline child :82 and grandchild :87, separate query cases |
| `Solidity/Backend/StorageOps/PushTransport.lean` | child :38, use :82 |
| `Solidity/Backend/StorageOps/PrimitivePop.lean` | child :58, use :97; sibling inequality :102 uses constructor injectivity |
| `Solidity/Backend/StorageOps/TargetClearRepresentation.lean` | child :116, uses :155,165; sibling inequality :62 |
| `Solidity/Backend/StorageOps/TargetPrimitivePop.lean` | child :44, both orientations in write commutation :55 onward |
| `Solidity/Backend/StorageOps/FreshArrayHistory.lean` | inline child :62, used in representation proof |
| `Solidity/Backend/StorageOps/TargetArrayWrite.lean` | inline reverse child :91–96 |
| `Solidity/Lowering/StorageOps/SourceTwoArrayDeleteNumeric.lean` | child :11, use :22 |

Concrete word inequalities additionally require covered locations and `FiniteRun.word_inj`: `Solidity/Backend/StorageOps/LifecycleNumeric.lean:101–109`, `Solidity/Backend/StorageOps/PrimitiveCycleNumeric.lean:92–97`, and `Solidity/Backend/StorageOps/NumericRetainedCycle.lean:110–119` (including a grandchild). Symbolic inequality alone does not supply those premises. `Solidity/Backend/StorageOps/OperationDepth.lean` uses depth for monotonicity. This manually reviewed census covers occurrences of `Loc.depth` in Backend/StorageOps and Lowering/StorageOps at the pinned base; it does not claim every semantically equivalent proof in the repository.

## Owner requests and remaining work

Request exact-file agreement for the seven EVM files above and the nine symbolic-case files above, plus the three concrete-word files if those sites are to consume a shared symbolic lemma. Shared module registration needs its owner or coordinator. The allocation and indexed-fragment checkpoints retain their existing reductions and types. No extraction, full validation, timing delta, or Lean proof is claimed here.

Independent read-only finder and skeptic reviewed the source cases without a Lean server. Their findings prompted inclusion of tail-revert, inline nested and concrete-word cases. Post-change independent read-only reviews found no material error in the ledger; neither reviewer used a Lean server. Other nested Evm.Slot proofs are distinct and are not covered by this literal Loc.depth census.
