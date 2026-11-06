import Solidity.Yul.Views.RecursiveRootCompatibility

namespace Solidity.Yul.Views

/-- All original root certificates embed, not only the new concrete fixtures.
No legacy guard or coordinate is changed. Header traces for the existing
one-level API are proved equal separately in RecursiveRootCompatibility. -/
def StorageDeclarations.recursiveRoots {E ds} (d : StorageDeclarations E ds) : RecursiveRootDeclarations E ds :=
  d.memberRoots.recursiveRoots

theorem StorageDeclarations.recursiveRoots_pack {E ds} (d : StorageDeclarations E ds) : d.recursiveRoots.pack = d.pack :=
  d.memberRoots.recursiveRoots_pack.trans d.memberRoots_pack

theorem StorageDeclarations.recursiveRoots_paths {E ds} (d : StorageDeclarations E ds) : d.recursiveRoots.paths = d.paths :=
  d.memberRoots.recursiveRoots_paths.trans d.memberRoots_paths

end Solidity.Yul.Views
