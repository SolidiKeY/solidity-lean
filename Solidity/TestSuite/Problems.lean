import Solidity.Solkey.TestSuite
import Solidity.Frontend.Problems

/-!
# solkey's `TestSuite` obligations, as `Update.lean`'s formulas

One statement per public or external function the import elaborated
(`solc_problems`, `Frontend/Problems.lean`); an internal helper has none,
as solkey inlines it at its calls: the obligation as solkey's
`SolidityProblemSynthesizer` states it, the modality the function's tag,
`∀` over its parameters, under `wt(storage)` (`Calculus/Problem.lean`).
Declared `Solkey.TestSuite.f.problem.legacy` and not compiled (`legacy`):
the statement proved is the scoped `Solkey.TestSuite.f.problem` of
`CoreProblems.lean`, checked to erase to this one, and `#solkey_problem`
prints this one.  The theorems are in the `Derived*` modules; `Report.lean`
counts them.  The suggestions `#solkey_derive?` prints are pinned in
`Suggestions.lean`, which no `Derived` module imports, so that its
searches stay off their path.
-/

solc_problems Solkey.TestSuite legacy

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
    holds Solkey.TestSuite.initState (NFml.wt Solkey.TestSuite) :=
  initStorage_wt (by decide +kernel) (by decide +kernel)
