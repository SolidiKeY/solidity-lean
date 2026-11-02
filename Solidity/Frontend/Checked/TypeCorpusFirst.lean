import Solidity.Frontend.Checked.TypeExampleCore

/-! Exact kernel-certified constructor list for one original G09 corpus member.
The external list observation is only staging; the theorem below checks the actual parser. -/

namespace Solidity.Frontend.Checked.TypeCorpusCertificates

open Solidity.Source

def firstCtors : List Ctor :=
  [.unit, .cons, .topPart, .struct, .structMember, .elem, .cons, .structMember, .array, .userType, .none, .cons, .structMember, .mapping, .userType, .nil, .cons, .topPart, .enum, .cons, .topPart, .udvt, .cons, .topPart, .constant, .elem, .lit, .cons, .topPart, .error, .cons, .errorParam, .elem, .cons, .errorParam, .elem, .nil, .cons, .topPart, .event, .cons, .eventParam, .elem, .cons, .eventParam, .elem, .nil, .cons, .topPart, .usingPart, .usingPath, .some, .userType, .cons, .topPart, .usingPart, .usingAliases, .usingAlias, .cons, .usingAlias, .nil, .some, .userType, .cons, .topPart, .usingPart, .usingPath, .none, .nil]

theorem first_ctors : ctorsOf declCorpus[0]! = firstCtors := by
  decide +kernel

end Solidity.Frontend.Checked.TypeCorpusCertificates
