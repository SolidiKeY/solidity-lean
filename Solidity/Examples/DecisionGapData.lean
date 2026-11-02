import Solidity.Syntax.Contract

/-! Original decision-fixture contract, independently of its regression chain. -/
namespace Solidity.Examples.Decision

/-- The roots the shapes read. -/
def Gaps : Contract := contract!{
  struct Acc { uint v; bool live; }
  mapping(uint => mapping(uint => uint)) allow;
  mapping(uint => uint) balances;
  mapping(int => uint) ibal;
  mapping(bool => uint) flags;
  mapping(uint => Acc) accs;
  uint[] arr;
  uint[3] fixedArr;
}

end Solidity.Examples.Decision
