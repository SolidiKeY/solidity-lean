# Actual dynamic entry guard followed by Boolean copy

SourceRawBoolEntry composes the existing Source.cdTail at stride32 with Source.cdToMem for the dynamic Boolean memory type. The first guard checks the length-word span, the second rejects length at least2^64, and the third checks the full element span. source_raw_bool_entry_refused derives early empty-data revert and unchanged state from those actual refusal conditions. This is not a standalone-copy refusal theorem.

source_raw_bool_entry_success uses initial bounds and raw canonical argument words, under the explicit four-byte selector/frame binding, to derive guard success, the actual returned offset/length and the byte-derived allocation. raw_bool_frame_word proves the offset alignment. No desired successful run, decoded payload or reached representation is assumed. This is a composition of existing Source operations, not a new evaluator, ABI encoder or Source AST.

Controls execute complete valid entry plus copy, a passed entry guard followed by an invalid second Boolean, truncated-entry refusal versus successful standalone padding for the same bytes, and exact-end zero-length success. They reuse unchanged populated object/local/world observations. Failed recursion-limited automation is retained and repaired by explicit header/length/span facts without increasing limits. These APIs have no pipeline or horizon parameter. No Source Items, intrinsic/native writer, MemOK/allocator, full ABI admission, physical/compiler/EVM or transaction closure is claimed.

The help branch adopts published master9c44a2f9 while preserving frozen ancestry and all earlier component seals. Full private-lane gates remain open. New baseline comparisons bind that exact public tree separately from historical findings.
