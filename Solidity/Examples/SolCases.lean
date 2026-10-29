import Solidity.Tools.SolCases
import Solidity.Syntax.Splice

/-! Concrete kernel parser/printer round trips for the admitted source grammar.
The external harness compiles every generated source with solc as well. -/
namespace Solidity.Tools.SolCases

def roundTrip : Prog caseContract [] [] := sol[caseContract]{ x = y; }
theorem roundTrip_exact : roundTrip = sequence [.assign x (.val (.read y))] := by rfl
#print axioms roundTrip_exact
#guard (program roundTrip).toOption == some "x = y; "

def literals : Prog caseContract [] [] := sequence [.assign x (.val
  (.binop (p := .uint) .div (by rfl) (by rfl)
    (.simple (.lit 5 (by decide))) (.simple (.lit 2 (by decide)))))]
#guard (program literals).toOption == some "x = (uint256(5) / uint256(2)); "
theorem literal_division_exact : ((Prog.run (State.init caseContract) literals.withPanics).toOption.bind
    (fun o => fmtRoot o.st.storage "x")) = some "2" := by decide +kernel
#print axioms literal_division_exact

/-- An unrepresentable model-only statement is explicitly refused. -/
theorem refuse_assumption : statement (Stmt.assumeFalse : Stmt caseContract [] []) =
    .error "solcases.statement.unsupported" := rfl
#print axioms refuse_assumption
end Solidity.Tools.SolCases
