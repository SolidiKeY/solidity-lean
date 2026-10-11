import Solidity.Solkey.TestSuite
import Solidity.Frontend.Problems

/-!
# solkey's `TestSuite` obligations, in solkey's syntax

One statement per public or external function the import elaborated; an
internal helper has none, as solkey inlines it at its calls: the
obligation as solkey's `SolidityProblemSynthesizer` states it, the
modality the function's tag, `∀` over its parameters, under `wt(storage)`
(`Calculus/Problem.lean`), on the scoped program `Solkey.TestSuite.f`.
They are declared in `ScopedProblems.lean`, `Solkey.TestSuite.f.problem`
(`solc_scoped_problems`, `Frontend/Problems.lean`); `#solkey_problem` here
prints the statement it would declare.  The theorems are in the `Derived*`
modules; `Report.lean` counts them.  The suggestions `#solkey_derive?` prints are pinned in
`Suggestions.lean`, which no `Derived` module imports, so that its
searches stay off their path.
-/

/-! Two statements as solkey prints them: a box and a diamond, each with
parameters. -/

/--
info: \programVariables {
    int x;
    int y;
}

\problem {
    wt(storage) -> \[{ additionStorageWrite(x, y)@TestSuite; }\](true)
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
/-- The premise is satisfiable: the storage `TestSuite` starts in is
well-formed (`initStorage_wt`: the empty program reaches it, and its words
are defaults). -/
theorem Solkey.TestSuite.initState_wt :
    NFml.holds Solkey.TestSuite.initState (NFml.wt Solkey.TestSuite) :=
  initStorage_wt (by decide +kernel) (by decide +kernel)
