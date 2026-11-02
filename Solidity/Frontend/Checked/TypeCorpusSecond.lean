import Solidity.Frontend.Checked.TypeExampleCore

/-! Exact kernel-certified constructor list for one original G09 corpus member.
The external list observation is only staging; the theorem below checks the actual parser. -/

namespace Solidity.Frontend.Checked.TypeCorpusCertificates

open Solidity.Source

def secondCtors : List Ctor :=
  [.unit, .cons, .contract, .none, .nil, .cons, .stateVar, .elem, .some, .lit, .cons, .stateVar, .elem, .none, .cons, .stateVar, .mapping, .elem, .none, .cons, .stateVar, .elem, .none, .cons, .stateVar, .fnType, .cons, .param, .elem, .nil, .cons, .param, .elem, .nil, .none, .cons, .stateVar, .array, .elem, .none, .none, .cons, .struct, .structMember, .elem, .nil, .cons, .event, .nil, .cons, .error, .nil, .cons, .stateVar, .fnType, .cons, .param, .elem, .nil, .nil, .none, .cons, .stateVar, .fnType, .nil, .nil, .none, .cons, .stateVar, .mapping, .userType, .none, .cons, .function, .cons, .param, .array, .elem, .none, .cons, .param, .userType, .cons, .param, .elem, .nil, .nil, .nil, .some, .block, .nil, .nil, .nil]

theorem second_ctors : ctorsOf declCorpus[1]! = secondCtors := by
  decide +kernel

end Solidity.Frontend.Checked.TypeCorpusCertificates
