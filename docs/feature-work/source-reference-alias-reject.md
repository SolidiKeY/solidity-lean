# Late bounds rejection through a reached reference local

`SourceBoolRefsAt.computed_alias_delete_reject` in
`Backend/MemoryOps/SourceReferenceAliasReject.lean` derives three linked stages:
actual computed `dst[i] = src[j]`, actual local alias selection from the reached
parent slot, then indexed deletion at an out-of-bounds child index. All suffix
alignment, length and independent Source observer facts come from INITIAL
correspondence and the real two-operation prefix. No reached relation or run is
an input. The failing suffix writes nothing, so it needs no selected-child
address-separation footprint.

The first two Source statements execute at `fuel+6` and `fuel+5`; the failing
expression and statement use `fuel+3` and `fuel+4`. One three-statement RItems
execution at `fuel+7` keeps ORIGINAL Source context length nps. It returns the
exact index panic and the actual reached globals. The prefix local frame is
proved separately; the enclosing error result does not return those locals.
Intrinsic Prog and the whole existing word append reject after their actual
successful prefixes, without returning a target machine. No transaction rollback,
post-revert machine or target panic-byte equivalence is claimed.

Both pipelines and same/distinct parent cases are independently inhabited.
A represented scalar3 and old alias LEFT are added using existing context/state
relations, not a declaration execution. The new alias occupies cell7, which held
99 in the earlier fixture; guard99 preservation is not claimed for this new
initial context. Every earlier fixture body/vector/guard is preserved.
All five INITIAL/reached Source objects, five intrinsic objects and every cell of
three complete 24-word prefix vectors are observed. The parent and local change
to RIGHT; the child endpoint3 then rejects without clearing RIGHT[1]. Actual
initial alias LEFT[0]=true and reached alias RIGHT[0]=false distinguish a stale
pointer; equal child lengths do not imply different endpoint rejection verdicts.
Retained LEFT[0] and RIGHT[1] stay true. Reached expression horizon2 actually times
out. Skipped alias/incorrect clear negatives are vector comparisons, not executed
reordered Source programs.

The three headline guards measure exactly propext, Classical.choice and Quot.sound.
This is kernel/typed/symbolic-word evidence, not physical-byte instruction execution,
compiler/EVM adequacy, general recursive graphs, ABI/storage/deepcopy, all-profile
allocation failure or complete Source/V10/target closure. Original queues remain open.
