import Solidity.Solkey.TestSuite
import Solidity.Frontend.Problems

/-!
# solkey's `TestSuite` obligations

One statement per function the import elaborated (`solc_problems`,
`Frontend/Problems.lean`): `Solkey.TestSuite.f.problem`, the obligation as
solkey's `SolidityProblemSynthesizer` states it, the modality the
function's tag, `∀` over its parameters, a diamond under `wt(storage)`
(`Calculus/Problem.lean`).  The theorems are in the `Derived*` modules
beside this one; `Report.lean` counts them.
-/

solc_problems Solkey.TestSuite

/-! Two statements as solkey prints them: a box and a diamond, each with
parameters. -/

/--
info: \programVariables {
    int x;
    int y;
}

\problem {
    \[{ additionStorageWrite(x, y)@TestSuite; }\](true)
}
-/
#guard_msgs in
#solkey_problem Solkey.TestSuite.additionStorageWrite

/--
info: \programVariables {
    bool b;
}

\problem {
    wt(storage) -> \<{ boolIsTrueOrFalse(b)@TestSuite; }\>(true)
}
-/
#guard_msgs in
#solkey_problem Solkey.TestSuite.boolIsTrueOrFalse

open Solidity in
/-- The diamond's premise is satisfiable: the storage `TestSuite` starts in
is well-formed (`initStorage_wt`: the empty program reaches it). -/
theorem Solkey.TestSuite.initState_wt :
    holds Solkey.TestSuite.initState (Fml.wt Solkey.TestSuite) :=
  initStorage_wt (by decide +kernel) (by decide +kernel)
