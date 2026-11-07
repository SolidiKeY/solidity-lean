import Solidity.KeySort
#eval if Solidity.KeySort.le .identity .memValue &&
    !(Solidity.KeySort.le .identity .stValue) then
  IO.println "KeySort runtime: PASS (existing lattice, identity/memory boundary)"
else throw (IO.userError "KeySort runtime failed")
