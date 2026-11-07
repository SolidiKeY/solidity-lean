import Solidity.Precompiles.Field
import Solidity.Precompiles.Basic
import Solidity.Precompiles.Modexp
import Solidity.Precompiles.Bn254
import Solidity.Precompiles.Blake2f
import Solidity.Precompiles.P256

set_option pp.all true

#check @Solidity.Precompiles.readPad_length
#check @Solidity.Precompiles.toBE_length
#check @Solidity.Precompiles.mapM_eq_none_iff
#check @Solidity.Precompiles.ecrecover_isSome
#check @Solidity.Precompiles.sha256_isSome
#check @Solidity.Precompiles.ripemd160_isSome
#check @Solidity.Precompiles.identity_eq
#check @Solidity.Precompiles.words_mono
#check @Solidity.Precompiles.sha256Gas_mono
#check @Solidity.Precompiles.ripemd160Gas_mono
#check @Solidity.Precompiles.identityGas_mono
#check @Solidity.Precompiles.Modexp.modexp_eq_none_iff
#check @Solidity.Precompiles.Modexp.modexp_length
#check @Solidity.Precompiles.Modexp.gas_ge
#check @Solidity.Precompiles.Bn254.add_eq_none_iff
#check @Solidity.Precompiles.Bn254.mul_eq_none_iff
#check @Solidity.Precompiles.Bn254.onCurve_aff
#check @Solidity.Precompiles.Bn254.decodeG1_eq_none_iff
#check @Solidity.Precompiles.Bn254.pairing_eq_none_iff
#check @Solidity.Precompiles.Blake2f.compress_size
#check @Solidity.Precompiles.Blake2f.flatMap_length
#check @Solidity.Precompiles.Blake2f.blake2f_eq_none_iff
#check @Solidity.Precompiles.Blake2f.blake2f_length
#check @Solidity.Precompiles.P256.p256Verify_isSome
