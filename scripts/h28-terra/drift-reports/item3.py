#!/usr/bin/env python3
"""Classify the frozen retained sort diagnostic multiset and source identity."""
import collections
import json
import sys

EXPECTED_DIAGNOSTICS = ['solkeycheck: READ DRIFT: storageRootWriteCopySource: file has [storage/value/fixed Struct], table has '
 '[storage/value/fixed StValue]',
 'solkeycheck: READ DRIFT: storageFieldWriteCopySource: file has [storage/value/fixed Struct], table has '
 '[storage/value/fixed StValue]',
 'solkeycheck: READ DRIFT: storageFieldReadStoreRoot: file has [storage/value/fixed Struct], table has '
 '[storage/value/fixed StValue]',
 'solkeycheck: READ DRIFT: storageIndexReadMappingStoreRoot: file has [storage/value/fixed Struct], table '
 'has [storage/value/fixed StValue]',
 'solkeycheck: READ DRIFT: storageIndexWriteMappingCopySource: file has [storage/value/fixed Struct], table '
 'has [storage/value/fixed StValue]',
 'solkeycheck: READ DRIFT: storageIndexReadArrayStoreRoot: file has [storage/length/fixed int, '
 'storage/value/fixed Struct, storage/length/fixed int], table has [storage/length/fixed int, '
 'storage/value/fixed StValue, storage/length/fixed int]',
 'solkeycheck: READ DRIFT: storageIndexWriteArrayCopySource: file has [storage/length/fixed int, '
 'storage/value/fixed Struct, storage/length/fixed int], table has [storage/length/fixed int, '
 'storage/value/fixed StValue, storage/length/fixed int]',
 'solkeycheck: READ DRIFT: storagePushValueCopySource: file has [storage/length/fixed int, '
 'storage/value/fixed Struct, storage/length/fixed int], table has [storage/length/fixed int, '
 'storage/value/fixed StValue, storage/length/fixed int]',
 'solkeycheck: UNKNOWN TOKEN: memoryReferenceDeclFreshAlloc: typedId<[alphaType<[..]>',
 'solkeycheck: UNKNOWN TOKEN: memoryReferenceDeclFreshAlloc: typedId<[alphaType<[..]>',
 'solkeycheck: UNKNOWN TOKEN: memoryReferenceDeclFreshAlloc: typedId<[alphaType<[..]>',
 'solkeycheck: UNKNOWN TOKEN: memoryRootDeleteFreshRebind: typedId<[alphaType<[..]>',
 'solkeycheck: UNKNOWN TOKEN: memoryRootDeleteFreshRebind: typedId<[alphaType<[..]>',
 'solkeycheck: UNKNOWN TOKEN: memoryRootDeleteFreshRebind: typedId<[alphaType<[..]>',
 'solkeycheck: UNKNOWN TOKEN: memoryArrayFreshAlloc: typedId<[alphaType<[..]>',
 'solkeycheck: UNKNOWN TOKEN: memoryArrayFreshAlloc: typedId<[alphaType<[..]>',
 'solkeycheck: UNKNOWN TOKEN: memoryArrayFreshAlloc: typedId<[alphaType<[..]>',
 'solkeycheck: UNKNOWN TOKEN: memoryArrayFreshAlloc: typedId<[alphaType<[..]>',
 'solkeycheck: UNKNOWN TOKEN: memoryStorageCopy: typedId<[alphaType<[..]>',
 'solkeycheck: UNKNOWN TOKEN: memoryStorageCopy: typedId<[alphaType<[..]>',
 'solkeycheck: UNKNOWN TOKEN: memoryStorageCopy: typedId<[alphaType<[..]>',
 'solkeycheck: UNKNOWN TOKEN: memoryStorageCopy: typedId<[alphaType<[..]>',
 'solkeycheck: UNKNOWN TOKEN: memoryFieldDeleteReference: typedId<[alphaType<[..]>',
 'solkeycheck: UNKNOWN TOKEN: memoryFieldDeleteReference: typedId<[alphaType<[..]>',
 'solkeycheck: UNKNOWN TOKEN: memoryFieldDeleteReference: typedId<[alphaType<[..]>',
 'solkeycheck: UNKNOWN TOKEN: memoryIndexDeleteReference: typedId<[alphaType<[..]>',
 'solkeycheck: UNKNOWN TOKEN: memoryIndexDeleteReference: typedId<[alphaType<[..]>',
 'solkeycheck: UNKNOWN TOKEN: memoryIndexDeleteReference: typedId<[alphaType<[..]>',
 'solkeycheck: UNANNOTATED READS: storageRootWriteCopySourcePrim: taclet reads 1 value(s) but has no '
 'annotation-table row',
 'solkeycheck: UNANNOTATED READS: storageFieldWriteCopySourcePrim: taclet reads 1 value(s) but has no '
 'annotation-table row',
 'solkeycheck: UNANNOTATED READS: storageIndexReadMappingStoreRootPrim: taclet reads 1 value(s) but has no '
 'annotation-table row',
 'solkeycheck: UNANNOTATED READS: storageIndexWriteMappingCopySourcePrim: taclet reads 1 value(s) but has no '
 'annotation-table row',
 'solkeycheck: UNANNOTATED READS: storageIndexReadArrayStoreRootPrim: taclet reads 3 value(s) but has no '
 'annotation-table row',
 'solkeycheck: UNANNOTATED READS: storageIndexWriteArrayCopySourcePrim: taclet reads 3 value(s) but has no '
 'annotation-table row',
 'solkeycheck: UNANNOTATED READS: storagePushValueCopySourcePrim: taclet reads 3 value(s) but has no '
 'annotation-table row',
 'solkeycheck: UNANNOTATED READS: localValueDelete: taclet reads 1 value(s) but has no annotation-table row',
 'solkeycheck: UNANNOTATED READS: storageFieldReadStoreRootPrim: taclet reads 1 value(s) but has no '
 'annotation-table row',
 'solkeycheck: 37 mismatch(es); run with --list to inspect the parsed reads',
 'solkeycheck: parsed 389 taclets, 140 read-bearing, table covers 131']
EXPECTED_SOURCE_IDENTITY = '7afc53773d5b3bdf586b564e9919a74101eda203b863cd72ca13837f2ed1c6a0:ded1d0661919b11930e38048a876962423631c09b0f0167cb110c3b5de388f3f:114f3a4e901fc282cec56d9e210fcffb2776e0cd'

def report(data):
    files = data.get("files", [])
    if (not isinstance(files, list) or any(
        not isinstance(f, dict) or not isinstance(f.get("path"), str)
        or not isinstance(f.get("text"), str) for f in files
    ) or len({f["path"] for f in files}) != len(files)):
        return {"error": "invalid-or-duplicate-files"}
    lines = data.get("diagnostics", [])
    counts = collections.Counter(lines)
    categories = collections.Counter()
    for line in lines:
        for kind in ["READ DRIFT", "UNKNOWN TOKEN", "UNANNOTATED READS"]:
            if line.startswith("solkeycheck: " + kind + ":"):
                categories[kind] += 1
    identity = data.get("sourceIdentity") == EXPECTED_SOURCE_IDENTITY
    exact = counts == collections.Counter(EXPECTED_DIAGNOSTICS)
    return {"multiplicities": dict(sorted(counts.items())),
            "categories": dict(sorted(categories.items())),
            "complete37": identity and exact and dict(categories) == {
                "READ DRIFT": 8, "UNKNOWN TOKEN": 20, "UNANNOTATED READS": 9},
            "sourceIdentity": data.get("sourceIdentity"), "sourceIdentityOk": identity,
            "exactRetainedMultiset": exact}


if __name__ == "__main__":
    json.dump(report(json.load(sys.stdin)), sys.stdout)
    print()
