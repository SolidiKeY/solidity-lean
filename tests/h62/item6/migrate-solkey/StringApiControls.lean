import Solidity.KeySort

/-! Isolated case controls for the external Raw String-API blocker. These use
only the dependency-free sort prerequisite and standard strings. They neither
replace Raw's parser nor prove its general correctness. Check each unchanged
statement independently on the two official toolchains. No raised budget. -/
namespace H62.MigrateSolkey.StringApiControls

theorem hashKeccakDrop : ("#keccak256".drop 1).toString = "keccak256" := by
  decide +kernel

theorem hashShaDrop : ("#sha256".drop 1).toString = "sha256" := by
  decide +kernel

theorem unicodeDrop : ("κλx".drop 1).toString = "λx" := by
  decide +kernel

theorem functionPrefixDrop :
    ("function(uint256,address)".drop 9).toString.toList = "uint256,address)".toList := by
  decide +kernel

theorem returnsPrefixAndSuffix :
    ("returns(uint256)".drop 8).toString.toList.dropLast = "uint256".toList := by
  decide +kernel

theorem locationSuffixEta :
    ["[]memory", "[]storage"].find? (fun suffix : String => "uint256[]memory".endsWith suffix)
      = some "[]memory" := by
  decide +kernel

theorem absentLocationSuffix :
    ["[]memory", "[]storage"].find? (fun suffix : String => "uint256".endsWith suffix)
      = none := by
  decide +kernel

theorem locationSuffixCharacterBoundary :
    "uint256[]memory".toList.take ("uint256[]memory".length - "[]memory".length)
      = "uint256".toList := by
  decide +kernel

#print axioms hashKeccakDrop
#print axioms hashShaDrop
#print axioms unicodeDrop
#print axioms functionPrefixDrop
#print axioms returnsPrefixAndSuffix
#print axioms locationSuffixEta
#print axioms absentLocationSuffix
#print axioms locationSuffixCharacterBoundary

end H62.MigrateSolkey.StringApiControls
