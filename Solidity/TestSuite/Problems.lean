import Solidity.Solkey.TestSuite
import Solidity.Frontend.Problems

/-!
# solkey's `TestSuite` obligations

One statement per function the import elaborated (`solc_problems`,
`Frontend/Problems.lean`): `Solkey.TestSuite.f.problem`, the obligation as
solkey's `SolidityProblemSynthesizer` states it, the modality the
function's tag, `∀` over its parameters, under `wt(storage)`
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
    holds Solkey.TestSuite.initState (Fml.wt Solkey.TestSuite) :=
  initStorage_wt (by decide +kernel) (by decide +kernel)

/-! The suggestion `#solkey_derive?` prints, pinned: a statement the
closer proves in the residue is `sol_prove` alone; a leaf it leaves (an
array written past a `push`, outside its fragment) is closed with the `wt`
premise set aside (`Derive.searchLeaf`), and several leaves each go under
their `case`. -/

/--
info: theorem Solkey.TestSuite.additionStorageWrite.proved : ⊢ Solkey.TestSuite.additionStorageWrite.problem := by
  sol_prove

additionStorageWrite: derived
-/
#guard_msgs in
#solkey_derive? Solkey.TestSuite from 0 count 1

/--
info: theorem Solkey.TestSuite.testStorageArrayReadWrite.proved : ⊢ Solkey.TestSuite.testStorageArrayReadWrite.problem := by
  sol_prove
  case leaf1 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close
  case leaf2 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close

testStorageArrayReadWrite: derived
-/
#guard_msgs in
#solkey_derive? Solkey.TestSuite from 222 count 1
