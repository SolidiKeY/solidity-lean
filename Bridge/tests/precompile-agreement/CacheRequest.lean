import Cache.Hashing

/-! Environment tooling only. Uses the pinned cache hasher; no theorem or trust claim. -/
open Cache Cache.IO Cache.Hashing

def main (args : List String) : IO Unit := CacheM.run do
  let roots ← parseArgs ("lookup" :: args)
  let memo ← getHashMemo roots
  let hashes ← memo.filterByRootModules roots.keys
  for (mod, hash) in hashes.toArray do
    IO.println s!"{mod}\t{hash.asLTar}"
