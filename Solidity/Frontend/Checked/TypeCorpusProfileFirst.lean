import Solidity.Frontend.Checked.TypeCorpusObservations

/-! One original G09 corpus member and its unchanged profile observation. -/

namespace Solidity.Frontend.Checked.TypeCorpusCertificates

open Solidity.Source

theorem first_profile :
    profileObservation declCorpus[0]! = true := by
  decide +kernel

end Solidity.Frontend.Checked.TypeCorpusCertificates
