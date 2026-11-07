import SolidityBridge.PrecompileAgreement.Controls
open SolidityBridge.PrecompileAgreement.Controls Solidity.Precompiles Solidity.Roadmap.Evm
def modHeader (b e m : Nat) : Bytes := word b ++ word e ++ word m
open EvmYul in
#guard (Ξ_EXPMOD default (UInt256.ofNat 1000) default
  (input (array (modHeader 33 1 1 ++ [1] ++ zeros 31 ++ [1,1,3])))).2.2.2.2 == array [1]
