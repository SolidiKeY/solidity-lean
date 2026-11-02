import Solidity.Frontend.Checked.TypeCorpusFirst
import Solidity.Frontend.Checked.TypeCorpusSecond

/-! Isolated unchanged G09 kernel control, for bounded performance checking. -/

namespace Solidity.Frontend.Checked

open Solidity.Source

theorem declCorpus_accepted : declCorpus.all (fun s => !(ctorsOf s).isEmpty) = true := by
  change (!(ctorsOf declCorpus[0]!).isEmpty &&
    (!(ctorsOf declCorpus[1]!).isEmpty && true)) = true
  rw [TypeCorpusCertificates.first_ctors, TypeCorpusCertificates.second_ctors]
  rfl

end Solidity.Frontend.Checked
