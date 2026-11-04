# Prepared owned cache handoff — not yet delivered

Archive: owned-cache.tar.gz; SHA256083d6bf7f5702b4dad1ac8b250452f9b7f7913d4a7278e695bc317741916258a; size294765 bytes.

The manifest binds four source modules, four Lake trace depHashes and12 content-addressed artifacts. Archive members are artifacts/<name>, traces/<module>.trace.json, inputs.solidity-lean.jsonl and artifacts.SHA256SUMS. Read-back verification and both independent reviews matched all bytes against the actual VM cache.

Recipient: verify the supplement checksum manifest, unpack to a separate staging directory, and verify artifacts.SHA256SUMS from the staged artifacts directory. Use the coordinator's existing supported cache-import procedure; retain Lake's own mapping-file lock and never overwrite existing content-addressed artifacts. This worker has not imported anything into another machine and does not prescribe an unverified new transfer protocol.

Return an actual recipient receipt naming the source head, pack SHA256, verified artifact count and imported mappings. Until then cache-receipt.json remains a blocked local attempt receipt. Dependency caches and complete import closure are not asserted transferred.
