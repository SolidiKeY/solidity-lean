import Solidity.Frontend.Checked.TypeCorpusMembers
import Solidity.Frontend.Checked.TypeCorpusProfileFirst
import Solidity.Frontend.Checked.TypeCorpusProfileSecond

/-! Isolated unchanged G09 kernel control, for bounded performance checking. -/

namespace Solidity.Frontend.Checked

open Solidity.Source

/-- The corpus is in the profile: no syntax-level rejection. -/
theorem declCorpus_in_profile :
    declCorpus.all (fun s => match parse (ascii s) with
      | .ok u => u.rejections.isEmpty | .error _ => false) = true := by
  change declCorpus.all TypeCorpusCertificates.profileObservation = true
  rw [TypeCorpusCertificates.members]
  simp only [List.all_cons, List.all_nil, TypeCorpusCertificates.first_profile,
    TypeCorpusCertificates.second_profile, Bool.and_self]

end Solidity.Frontend.Checked
