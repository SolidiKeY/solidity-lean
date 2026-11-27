import Solidity.Solkey.TestSuite
import Solidity.Frontend.Problems



/--
info: \programVariables {
    int x;
    int y;
}

\problem {
    (self < 1461501637330902918203684832716283019655932542976) -> (wt(storage)) -> \[{ additionStorageWrite(x, y)@TestSuite; }\](true)
}
-/
#guard_msgs in
#solkey_problem Solkey.TestSuite.additionStorageWrite

/--
info: \programVariables {
    bool b;
}

\problem {
    (self < 1461501637330902918203684832716283019655932542976) -> (wt(storage)) -> \<{ boolIsTrueOrFalse(b)@TestSuite; }\>(true)
}
-/
#guard_msgs in
#solkey_problem Solkey.TestSuite.boolIsTrueOrFalse

open Solidity in
theorem Solkey.TestSuite.initState_wt :
    holds (State.init Solkey.TestSuite) (Fml.wt Solkey.TestSuite) :=
  initStorage_wt
