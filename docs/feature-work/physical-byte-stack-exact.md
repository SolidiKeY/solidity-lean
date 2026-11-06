# Exact materializer stack classification

PhysicalByteStackExact proves the actual stackSafe equation for the existing nonempty Environment.materialize prefix: its two transient slots must fit, and the suffix guard runs on the actual reached byte memory. materialize_checked_suffix_exact proves full checked execution equals suffix checked execution on that reached memory when space exists, and None otherwise. No successful suffix, assumed guard result or desired final state is a premise.

For a live REVERT suffix, materialize_checked_revert_exact classifies every runtime caller stack: offset/length plus the materializer's two transient slots must fit the existing1024-word bound. It returns the complete reached byte payload and caller tail exactly in that branch, otherwise None. No guard, evaluator, gas policy or Source admission rule changes. Nonempty is a supported operation shape; previous empty-materializer laws remain separate and unchanged.

The new inhabited client quantifies over every caller list using the existing populated fixture. It proves the None iff classification and complete returned-machine stack/byte/protected-word observations only when a machine is actually returned. Earlier finite capacity, empty and overlap controls and all vectors are byte-preserved. The failed decision on an unreduced projection is retained and repaired by an explicit projection reduction, without changing the claim or limits.

These are exact local byte-slice guard laws, not Source/world/compiler, gas, allocation, physical numeric-load or concrete ByteWorld producer closure. Exact standard pins and focused validation are component evidence; original full-lane gates and obligations remain open.
