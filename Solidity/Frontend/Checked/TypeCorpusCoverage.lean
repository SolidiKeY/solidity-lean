import Solidity.Frontend.Checked.TypeCorpusFirst
import Solidity.Frontend.Checked.TypeCorpusSecond

/-! Isolated unchanged G09 kernel control, for bounded performance checking. -/

namespace Solidity.Frontend.Checked

open Solidity.Source

/-- **Acceptance coverage (G09)**: every type and declaration constructor is
produced by an accepted program of the corpus. -/
theorem declCtors_covered :
    declCtors.all (fun c => declCorpus.any fun s => (ctorsOf s).contains c) = true := by
  change declCtors.all (fun c => (ctorsOf declCorpus[0]!).contains c ||
    ((ctorsOf declCorpus[1]!).contains c || false)) = true
  rw [TypeCorpusCertificates.first_ctors, TypeCorpusCertificates.second_ctors]
  rfl

end Solidity.Frontend.Checked
