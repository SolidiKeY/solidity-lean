# VA2 PARALLEL-INTERFACE: joined walks and context updates

Producer source checkpoint: `04da7063854f2bb719e2bed9ab52c306279da4ee`.
Frozen base: `8bd8742ad987d566f7ba7624372cec1c020be07c`.
Branch: `codex/solidity-automation-20261031/va2-sharing`.
Repository: `/workspace/va2-sharing`.

This is an incremental concrete producer interface, not completion of AU03/AU04 or final combined-tree validation. The accompanying committed bundle and source archive identify immutable inputs. Module hashes and verbatim source declarations are exported alongside this document; consume those declarations, not an assumed future Residue theorem.

## Ready modules and signatures

* `Solidity.Calculus.JoinSequence`: `LocalWrites C Γ` is a list of dependent triples `(p : PrimTy) × Idx Γ (.val p) × Val C Γ p`. `LocalWrites.program` preserves assignment order and RHS syntax. `LocalWrites.guarded` shifts each original target/RHS past a fresh Boolean head and guards each write; the snapshot survives writes to the original condition. `Prog.localWrites?_reconstruct` proves successful decoding preserves the entire indexed program and output context. `Prog.localWrites?_wk` commutes with `Thin` weakening on the complete decoded write data.
* `Solidity.Calculus.Sound.JoinSequence`: `State.setLocal_push_snapshot` transports a primitive local write past the snapshot. `LocalWrites.captured_drop_runSt` equates the actual captured block, with its head popped, to the original conditional typed run in every state. `LocalWrites.captured_sound` and `LocalWrites.joinPlan_sound` establish `Premise.Runs` for either modality. The latter requires the actual query equation `Upd.ifJoin? c.lower thn els = some (.inr body)`; it does not assume arbitrary branches are eligible. There are no added validity, arithmetic, or totality premises.
* `Solidity.Calculus.JoinSequenceSize`: `LocalWrites.captured_size` counts the actual capture declaration, block, both guarded branches and all RHS syntax. Its result is original conditional size plus `3 * (thn.length + els.length) + 1`. `LocalWrites.joinPlan_size_le`, under the same concrete query equation, bounds emitted capture program size by `4 * originalConditional.size + 1`. These are program-size laws, not bounds on walked leaves or call-family expansion.

Freshness is intrinsic and positional: old locals shift through `.there`, and the snapshot is `.here`. Display names do not establish freshness. The existing dispatcher supplies its name budget. Exact state equality after dropping the head preserves all global, heap and frame observations; no new hash or validity premises are introduced.

## Nontrivial witnessed clients

`Solidity.Examples.Tactics.JoinSequence.capturedChangedGuardDependent` executes the actual capture block: the selected branch changes the source guard to false, writes one, then reads the predecessor and produces two; the unselected branch divides by zero. `capturedSelectedFailure` selects that failing branch and observes failure. `actualMixedPlan` checks that the real dispatcher emits the sequence plan; `capturedEmittedSize` checks its actual size is 34. Boolean dependency, canonical short-circuit refusal and singleton-plan controls remain in the same module.

Existing per-file diagnostics, compiled axiom audits, affected builds and independent reviews are recorded in [the VA2 handoff](after-roadmap-va2.md). Kernel-checked theorems establish the stated Lean semantic laws; diagnostics and measurements alone are not semantic proofs. No external EVM equivalence result is claimed.

## Client obligations and pending producer facts

Clients must use the intrinsic context indices, the concrete successful query equation when selecting a plan, and the existing typed run/modality semantics. Canonical short-circuit boundaries remain split. No VA1 whole-lane theorem is needed to use these ready declarations.

AU04 fresh-local call-result sharing, function-family leaf bounds, post-anon loop cost repair, the forced signed sequential closer fixture, and final full combined-tree gates remain open. This package does not supply those missing facts and must not be used as a completion certificate. A staged consumer must record the exact producer head and module hashes and validate its concrete combined tree before integration.


## Subsequent independent AU04 prerequisite

The next VA2 checkpoint adds `Solidity.Calculus.CallResultCapture`: `capture_applyV`, `restore_locals`, `restore_state`, `target_fresh`, `restore_applyV`, `capture_exh`, `sound`, `complete`, `holds_iff`, and `leaf_size`. The generic equivalence covers all primitive result terms and both modalities with no extra premise. It is independently usable before VA1 Residue, but does not compress a recursively expanded term. Its exact committed producer head is resolved by the accompanying checkpoint revision manifest; consume that concrete commit, not this paragraph as an assumed theorem. The ready walk source checkpoint above remains immutable.
