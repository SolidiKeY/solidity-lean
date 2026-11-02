import Solidity.Frontend.Checked.TypeCorpusObservations

/-! One original G09 corpus member and its unchanged roundtrip observation. -/

namespace Solidity.Frontend.Checked.TypeCorpusCertificates

open Solidity.Source

theorem first_roundtrip :
    roundtripObservation declCorpus[0]! = true := by
  decide +kernel

end Solidity.Frontend.Checked.TypeCorpusCertificates
