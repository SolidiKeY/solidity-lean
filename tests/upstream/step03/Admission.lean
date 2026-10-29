import Solidity.Syntax.Splice
open Solidity
private def SliceBaseline : Contract := contract!{}
#eval match elabProgS SliceBaseline (sol_raw!{
  uint[2][] memory xs = new uint[2][](2);
  uint[2][] memory m = xs[:];
}) with
| .ok _ => "admitted"
| .error e => e
#eval match elabProgS SliceBaseline (sol_raw!{
  uint[] memory xs = new uint[](2);
  uint[] memory m = xs[:];
}) with
| .ok _ => "admitted"
| .error e => e
