import Solidity.Tools.SourceCounterexample
import Solidity.Calculus.Spec

/-!
# Exact-goal source counterexample certificates

The report's Boolean argument is read back from the same candidate quotation in
the returned proof. Successful examples retain a theorem at the exact original
goal's negation. True, vacuous, ill-matched and open goals create no refutation.
Large numeric values stay decimal strings rather than JSON floating-point data.
-/

namespace Solidity.Examples.SourceCounterexample

def Model : Contract := contract!{
  uint count;

  ensures \result == flag;
  function bad(bool flag) public pure returns (bool) { return true; }

  ensures \result == flag;
  function good(bool flag) public pure returns (bool) { return flag; }

  requires amount < 0;
  ensures false;
  function vacuous(uint amount) public pure {}

  requires amount > 9007199254740991;
  ensures \result == amount;
  function wide(uint amount) public pure returns (uint) { return 0; }
}

def badSpec : Fml Model [] := cspec[Model]{bad}
def goodSpec : Fml Model [] := cspec[Model]{good}
def vacuousSpec : Fml Model [] := cspec[Model]{vacuous}
def wideSpec : Fml Model [] := cspec[Model]{wide}

def Other : Contract := contract!{ bool other; }

def References : Contract := contract!{
  uint[] entries;
  ensures false;
  function bad() public pure {}
}

def referenceSpec : Fml References [] := cspec[References]{bad}

open Lean Elab Command Meta in
run_cmd liftTermElabM do
  let φ := mkConst ``badSpec
  let goal ← mkAppM ``Fml.Valid #[φ]
  let some evidence ← Tools.refuteSource? goal 16
    | throwError "the false Boolean specification needs a certified counterexample"
  unless ← isDefEq (← inferType evidence.proof) (mkNot goal) do
    throwError "the certificate does not negate the exact tested goal"
  let (head, proofArgs) := evidence.proof.consumeMData.getAppFnArgs
  unless head == ``Fml.not_valid_of_eval3Peel && proofArgs.size == 6 do
    throwError "the certificate must expose the candidate's bound argument quotation"
  let quotedValues ← unsafe evalExpr (List (Var × Semantics.CallValue))
    (← inferType proofArgs[2]!) proofArgs[2]!
  let .ok arguments := evidence.report.getObjValAs? (Array Json) "arguments"
    | throwError "the counterexample must retain typed arguments"
  unless arguments.size == 1 do throwError "unexpected source argument count"
  match quotedValues with
  | [(.user name, .bool value)] =>
    unless (arguments[0]!.getObjValAs? String "modelName").toOption == some name &&
        (arguments[0]!.getObjValAs? String "type").toOption == some "bool" &&
        (arguments[0]!.getObjValAs? Bool "value").toOption == some value && !value do
      throwError "the displayed argument differs from the certificate's candidate"
  | _ => throwError "the witness must bind the Boolean source argument"
  let name := `Solidity.Examples.SourceCounterexample.badRefuted
  addDecl <| .thmDecl {name, levelParams := [], type := mkNot goal, value := evidence.proof}
  unless (← collectAxioms name).all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "the source refutation uses a nonstandard dependency"

example : ¬ Fml.Valid badSpec := badRefuted

open Lean Elab Command Meta in
run_cmd liftTermElabM do
  for name in [``goodSpec, ``vacuousSpec, ``referenceSpec] do
    let goal ← mkAppM ``Fml.Valid #[mkConst name]
    if (← Tools.refuteSource? goal 16).isSome then
      throwError "a true, vacuous or unsupported specification must not be refuted"
  let φ := mkConst ``badSpec
  let goal ← mkAppM ``Fml.Valid #[φ]
  if (← Tools.refuteSource? goal 0).isSome then throwError "budget zero must do no search"
  if (← Tools.refuteSource? (mkConst ``True) 16).isSome then
    throwError "an unrelated proposition is not a source formula validity goal"
  if (← Tools.refuteSource? (mkNot goal) 16).isSome then
    throwError "an already negated goal must not be treated as formula validity"
  let mismatch := mkApp2 (mkConst ``Fml.Valid) (mkConst ``Other) φ
  if (← Tools.refuteSource? mismatch 16).isSome then
    throwError "the contract and formula must have the same type index"
  let formulaType ← inferType φ
  withLocalDeclD `freeFormula formulaType fun free => do
    let openGoal ← mkAppM ``Fml.Valid #[free]
    if (← Tools.refuteSource? openGoal 16).isSome then
      throwError "an open formula must not produce a source certificate"
  let unresolved ← mkFreshExprMVar formulaType
  let unresolvedGoal ← mkAppM ``Fml.Valid #[unresolved]
  if (← Tools.refuteSource? unresolvedGoal 16).isSome then
    throwError "an unresolved formula must not produce a source certificate"

open Lean Elab Command Meta in
run_cmd liftTermElabM do
  let goal ← mkAppM ``Fml.Valid #[mkConst ``wideSpec]
  let some evidence ← Tools.refuteSource? goal 16
    | throwError "the wide unsigned argument needs a source witness"
  let .ok arguments := evidence.report.getObjValAs? (Array Json) "arguments"
    | throwError "the wide witness must retain its argument"
  let .ok value := arguments[0]!.getObjValAs? String "value"
    | throwError "large numbers must be decimal JSON strings"
  unless value == "115792089237316195423570985008687907853269984665640564039457584007913129639935" do
    throwError "the certified wide argument lost precision"
  addDecl <| .thmDecl {
    name := `Solidity.Examples.SourceCounterexample.wideRefuted,
    levelParams := [], type := mkNot goal, value := evidence.proof}

example : ¬ Fml.Valid wideSpec := wideRefuted

#guard ((Tools.sourceArgumentJson "wide" (.uint (PrimTy.ofIntD .uint ((2 : Int)^256 - 1)))).getObjValAs? String "value").toOption ==
  some "115792089237316195423570985008687907853269984665640564039457584007913129639935"
#guard ((Tools.sourceArgumentJson "signed" (.int (PrimTy.ofIntD .int (-((2 : Int)^255))))).getObjValAs? String "value").toOption ==
  some "-57896044618658097711785492504343953926634992332820282019728792003956564819968"
#guard ((Tools.sourceArgumentJson "$flag" (.bool false)).getObjValAs? Bool "value").toOption == some false
#guard ((Tools.sourceArgumentJson "$flag" (.bool false)).getObjValAs? String "modelName").toOption == some "$flag"

/-- info: 'Solidity.Examples.SourceCounterexample.badRefuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms badRefuted
/-- info: 'Solidity.Examples.SourceCounterexample.wideRefuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wideRefuted

end Solidity.Examples.SourceCounterexample
