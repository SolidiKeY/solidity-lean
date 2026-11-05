# Computed reference replacement and reached local alias

`Solidity.Backend.MemoryOps.SourceBoolRefsAt.computed_reference_alias_sequence`
in `SourceReferenceAliasSequence` connects two existing operations, not two
independently initial-state runs. INITIAL src[j] computes the child; actual
replacement supplies reached dst[i], observer, alignment, MemOK and full
RefArrayStateRepr to the published selected_alias_word producer. Source Items,
intrinsic Prog and whole symbolic-word append execute through that same output.

Premises: INITIAL source/destination Boolean-child reference-array observers,
root/index Source/native alignment, both initial parent bounds, Source MemOK and
full RefArrayStateRepr. The alias local is overwritten, so no selected-child
local/value or desired postcondition is supplied. No selected-footprint or
global injection premise is needed for the local-only suffix. Contexts stay
unchanged; Source horizons fuel+5/fuel+4 combine to fuel+6 at ORIGINAL Γ.length
nps. Initial Source alias value need not agree with the target alias value for
this overwrite-only theorem; the controls independently align both to LEFT.
This is a finite operation component, not a general Source state representation.

Final Source locals are the INITIAL locals with only the alias updated; native
setLocal and target local-cell write are explicit. Source/global/native heap
frames, primitive child contents/observers, strong representation and allocator
transport are derived. Allocator transport keeps positive-base and initial
live-parent/cursor premises. No object is allocated/copied; no child length cap.

Both pipelines and distinct/same parent cases are inhabited in
computed_reference_alias_client. An independently represented INITIAL LEFT
child local uses Source cons/intrinsic push; this is not a declaration execution.
Actual source[1]=RIGHT replaces parent[0], then the local selects reached RIGHT.
Complete five-object Source/native tables and all24 initial/intermediate/final
word cells retain parents/shared LEFT references, children, empty parent, headers,
root/alias/scalar locals, guard99, free pointer48 and saved stack42. Parent slot
33 (or37) changes16->24, then alias cell6 changes16->24. Source indexed reads
are true before replacement, still true after replacement if selection is
omitted, and false after actual selection. The omitted-selection Source Items
program is executed explicitly. Native value read returns false; published readLocalCode
pushes word0 on the saved tail. Those final read
expressions are separate from the TWO-statement Source program; no three-
statement Source program or automatic discarded-result compiler claim follows.
Vector comparisons additionally distinguish omitted/early selection; no actual
reversed-order Source program is asserted. Earlier failures/controls stay intact.

Three measured exact guards record standard propext/Classical.choice/Quot.sound.
Failed draft parse/rewrite/opaque projection/index reductions are retained;
no statement/premise/expected-vector weakening or raised budget is used. Raw
strictdocs/inventory and frozen comparisons remain failing separately from
complete public zero-new. Full private/default/TestSuite/strict/corpus closure
and source-keyed cold timing obligations remain open. Kernel/symbolic-word
checking is not physical-byte, general graph/deep-copy, ABI/storage, external
compiler/EVM or final Source/V10 adequacy. Original queues remain unfinished.
