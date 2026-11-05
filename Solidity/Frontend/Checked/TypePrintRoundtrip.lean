import Solidity.Frontend.Checked.TypeCorpusMembers
import Solidity.Frontend.Checked.TypeCorpusRoundtripFirst
import Solidity.Frontend.Checked.TypeCorpusRoundtripSecond

/-! Isolated unchanged G09 kernel control, for bounded performance checking. -/

namespace Solidity.Frontend.Checked

open Solidity.Source

/-- **Round trip**: the printed text parses to a tree with the same nodes
and tokens. -/
theorem print_roundtrip :
    declCorpus.all (fun s => reprintFingerprint s == fingerprint (parseWithLayout (ascii s)) &&
      (reprintFingerprint s).isSome) = true := by
  change declCorpus.all TypeCorpusCertificates.roundtripObservation = true
  rw [TypeCorpusCertificates.members]
  simp only [List.all_cons, List.all_nil, TypeCorpusCertificates.first_roundtrip,
    TypeCorpusCertificates.second_roundtrip, Bool.and_self]

end Solidity.Frontend.Checked
