import Solidity.Yul.DirectUpdates
import Solidity.Yul.Checks.DirectWords
namespace Solidity.Yul.Checks.DirectUpdates
open Closed
open Solidity.Yul.Checks.DirectWords
def control : Control := ⟨false,false⟩
structure Case where
  name : String
  results : Nat
  targets : Fin results → Target types 1
  rhs : Expr [] types 1 results
  policy : Policy.StmtP .A (Stmt.assign (c := control) targets rhs)
def one (target : Target types 1) : Fin 1 → Target types 1 := Fin.cases target Fin.elim0
def fixtures : List Case :=
  [⟨"localFromSmall",1,one (.local 0),narrow,by apply (Policy.stmt_iff .A _).mp; rfl⟩,
   ⟨"boolFromSmall",1,one (.external flag.writeRef),narrow,by apply (Policy.stmt_iff .A _).mp; rfl⟩,
   ⟨"smallFromSelector",1,one (.external small.writeRef),selector,by apply (Policy.stmt_iff .A _).mp; rfl⟩,
   ⟨"addressFromSmall",1,one (.external (WordCell.address function).writeRef),narrow,by apply (Policy.stmt_iff .A _).mp; rfl⟩,
   ⟨"selectorFromAddress",1,one (.external (WordCell.selector function).writeRef),address,by apply (Policy.stmt_iff .A _).mp; rfl⟩,
   ⟨"sum",1,one (.external small.writeRef),bin .add narrow boolean,by apply (Policy.stmt_iff .A _).mp; rfl⟩,
   ⟨"divZero",1,one (.external small.writeRef),division,by apply (Policy.stmt_iff .A _).mp; rfl⟩,
   ⟨"mulDiv",1,one (.external small.writeRef),mulDiv,by apply (Policy.stmt_iff .A _).mp; rfl⟩,
   ⟨"discardPop",0,Fin.elim0,popped,by apply (Policy.stmt_iff .A _).mp; rfl⟩]
def snapshot (s : WordState types 1) : List Nat :=
  [(s.locals 0).val,(s.cells small).val,(s.cells flag).val,
    (s.cells (.address function)).val,(s.cells (.selector function)).val]
def observe (index fuel : Nat) : Option (List Nat) :=
  (fixtures[index]?).bind (fun c =>
    (Solidity.Yul.DirectUpdates.assign fuel c.targets c.rhs c.policy state).map snapshot)
example : observe 0 0 = none := by decide
example : observe 0 1 = none := by decide
example : observe 0 2 = some [257,257,2,2^256-1,2^32+1] := by decide
example : observe 1 2 = some [7,257,257,2^256-1,2^32+1] := by decide
example : observe 2 2 = some [7,2^32+1,2,2^256-1,2^32+1] := by decide
example : observe 3 2 = some [7,257,2,257,2^32+1] := by decide
example : observe 4 2 = some [7,257,2,2^256-1,2^256-1] := by decide
example : observe 5 2 = none := by decide
example : observe 5 3 = some [7,259,2,2^256-1,2^32+1] := by decide
example : observe 6 3 = some [7,0,2,2^256-1,2^32+1] := by decide
example : observe 7 3 = none := by decide
example : observe 7 4 = some [7,330,2,2^256-1,2^32+1] := by decide
example : observe 8 3 = none := by decide
example : observe 8 4 = some [7,257,2,2^256-1,2^32+1] := by decide

/-- Primitive alias-order regression only: no claim that source assignment
admission accepts duplicate targets. The lowest source index writes last. -/
def duplicateTargets : Fin 3 → Target types 1 :=
  Fin.cases (.external small.writeRef)
    (Fin.cases (.external flag.writeRef) (Fin.cases (.external small.writeRef) Fin.elim0))
def duplicatePolicy : ∀ i, Policy.TargetP .A (duplicateTargets i) :=
  Fin.cases True.intro (Fin.cases True.intro (Fin.cases True.intro (fun i => Fin.elim0 i)))
def duplicateValues : Values 3 := Fin.cases (word 1) (Fin.cases (word 257) (Fin.cases (word 511) Fin.elim0))
example : snapshot (Solidity.Yul.DirectUpdates.writeValues 3 duplicateTargets duplicatePolicy duplicateValues state) =
    [7,1,257,2^256-1,2^32+1] := by decide
example : (Solidity.Yul.DirectUpdates.writeValues 3 duplicateTargets duplicatePolicy duplicateValues state).pack =
    Closed.writeValues 3
      (fun i => WordAdapter.target (duplicateTargets i) (duplicatePolicy i)
        (Fin.castAdd (wordCellCount types)) (fun cell => Fin.natAdd 1 cell.slot)) duplicateValues state.pack :=
  Solidity.Yul.DirectUpdates.pack_writeValues 3 duplicateTargets duplicatePolicy duplicateValues state
example : ¬ Policy.TargetP .A
    (Target.external (X := [.memory]) (n := 1) ⟨.here,.plain,.memoryWrite⟩) := by intro h; cases h
example (index : Fin 0) : False := Nat.not_lt_zero index.val index.isLt
def witness : Nonempty Case := ⟨fixtures[7]⟩
def dirtyWitness : ∃ s : WordState types 1,
    snapshot s = [7,257,257,2^256-1,2^32+1] :=
  ⟨Solidity.Yul.DirectUpdates.write (.external flag.writeRef) True.intro (word 257) state,by decide⟩
/-- info: DIRECT_UPDATES_COMPILED_PASS:81 actual direct/packed assignment comparisons including full state and normal-flow observation; not EVM -/
#guard_msgs in
#eval do
  let mut count := 0
  for c in fixtures do
    let lowered := WordAdapter.statement (Stmt.assign (c := control) c.targets c.rhs) c.policy
      (Fin.castAdd (wordCellCount types)) (fun cell => Fin.natAdd 1 cell.slot)
    for fuel in List.range 9 do
      let direct := (Solidity.Yul.DirectUpdates.assign fuel c.targets c.rhs c.policy state).map
        (fun s : WordState types 1 => (s.pack |> List.ofFn |> List.map Fin.val,true))
      let reference := (evalStmt fuel .nil True.intro lowered.code lowered.words state.pack).map
        (fun outcome : Outcome control (1+wordCellCount types) => (outcome.vars |> List.ofFn |> List.map Fin.val,outcome.flow.isNormal))
      unless direct == reference do
        throw (IO.userError ("direct assignment full-result agreement failed: " ++ c.name))
      count := count+1
  unless count == 81 do throw (IO.userError "assignment matrix incomplete")
  IO.println "DIRECT_UPDATES_COMPILED_PASS:81 actual direct/packed assignment comparisons including full state and normal-flow observation; not EVM"
#check @Solidity.Yul.DirectUpdates.assign_agrees
#print axioms Solidity.Yul.DirectUpdates.pack_write
#print axioms Solidity.Yul.DirectUpdates.assign_agrees
end Solidity.Yul.Checks.DirectUpdates
