import Solidity.Yul.OpenScoped
import Solidity.Yul.OpenLocal
import Solidity.Yul.Checks.WordAdapterCode
import Solidity.Yul.Checks.RawDivergence
import Solidity.Yul.Checks.LocalBlock
namespace Solidity.Yul.Checks.OpenRun
open Closed
open Solidity.Source (Syn)
namespace Fixture
export Solidity.Yul.Checks.WordAdapter
  (types x scope outside localNames initial snapshot prepare prepared dirty bound mulDiv recursive looping pair switched division crossed never
   mulDivPrepared recursivePrepared loopingPrepared mulDivCode recursiveCode loopingCode
   mulDiv_lowered recursive_lowered looping_lowered observe observe_cache)
end Fixture
structure Case where
  name : String
  body : List (Syn .yulStmt)
  checked : ScopedSyntax.Prepared Fixture.scope .A Fixture.outside Fixture.localNames
    (Solidity.Yul.Checks.BlockTyping.list body)
def cases : List Case :=
  [⟨"dirty",Fixture.dirty,(Fixture.prepare Fixture.dirty).toOption.get (by decide)⟩,
   ⟨"bound",Fixture.bound,(Fixture.prepare Fixture.bound).toOption.get (by decide)⟩,
   ⟨"mulDiv",Fixture.mulDiv,Fixture.mulDivPrepared⟩,
   ⟨"recursive",Fixture.recursive,Fixture.recursivePrepared⟩,
   ⟨"looping",Fixture.looping,Fixture.loopingPrepared⟩,
   ⟨"pair",Fixture.pair,(Fixture.prepare Fixture.pair).toOption.get (by decide)⟩,
   ⟨"switch",Fixture.switched,(Fixture.prepare Fixture.switched).toOption.get (by decide)⟩,
   ⟨"zero-div",Fixture.division,(Fixture.prepare Fixture.division).toOption.get (by decide)⟩,
   ⟨"fields",Fixture.crossed,(Fixture.prepare Fixture.crossed).toOption.get (by decide)⟩,
   ⟨"loop-diverge",Fixture.never,(Fixture.prepare Fixture.never).toOption.get (by decide)⟩,
   ⟨"recursive-diverge",Solidity.Yul.Checks.RawDivergence.source,Solidity.Yul.Checks.RawDivergence.prepared⟩]
def snapshot {c} (result : WordAdapter.Outcome Fixture.types c 0) : List Nat × Bool :=
  (Fixture.snapshot result.state.cells,result.flow.isNormal)
def observe (c : Case) (fuel : Nat) : Option (List Nat × Bool) :=
  (c.checked.openRun fuel Fixture.initial).map snapshot
example (fuel : Nat) (cells : WordCells Fixture.types) :
    Solidity.Yul.Checks.RawDivergence.prepared.openRun fuel cells = none := by
  rw [ScopedSyntax.Prepared.openRun_eq_rawRun]
  exact Solidity.Yul.Checks.RawDivergence.run_none fuel cells

example : (Fixture.mulDivPrepared.openRun 32 Fixture.initial).map
    (fun result => Fixture.snapshot result.state.cells) = some [599,2,0,0] := by
  rw [ScopedSyntax.Prepared.openRun_eq_rawRun]
  change Fixture.observe Fixture.mulDiv 32 = _
  rw [Fixture.observe_cache Fixture.mulDiv Fixture.mulDivPrepared 32 Fixture.mulDivCode Fixture.mulDiv_lowered]
  decide
example : (Fixture.recursivePrepared.openRun 32 Fixture.initial).map
    (fun result => Fixture.snapshot result.state.cells) = some [13,2,0,0] := by
  rw [ScopedSyntax.Prepared.openRun_eq_rawRun]
  change Fixture.observe Fixture.recursive 32 = _
  rw [Fixture.observe_cache Fixture.recursive Fixture.recursivePrepared 32 Fixture.recursiveCode Fixture.recursive_lowered]
  decide
example : (Fixture.loopingPrepared.openRun 32 Fixture.initial).map
    (fun result => Fixture.snapshot result.state.cells) = some [259,2,0,3] := by
  rw [ScopedSyntax.Prepared.openRun_eq_rawRun]
  change Fixture.observe Fixture.looping 32 = _
  rw [Fixture.observe_cache Fixture.looping Fixture.loopingPrepared 32 Fixture.loopingCode Fixture.looping_lowered]
  decide

def signature : Sig := ⟨1,1⟩
def constantContext : List ExternalType := [.value (.unsigned 0),.constant (word 9)]
def constantBody : Stmt [signature] (globals constantContext) ⟨true,false⟩ 2 :=
  .assign (Fin.cases (.local 1) Fin.elim0)
    (.builtin (.pure .add) (Fin.cases (.local 0)
      (Fin.cases (.external ⟨.here,.plain,.constantRead⟩) Fin.elim0)))
def constantPolicy : Policy.StmtP .A constantBody := (Policy.stmt_iff .A _).mp rfl
def constantBodies : Bodies [signature] (globals constantContext) [signature] := .cons constantBody .nil
def constantEnvironment : OpenFunctions.PureEnvironment [signature] :=
  .group [signature] .nil constantBodies ⟨constantPolicy,True.intro⟩
def call : Expr [signature] [] 0 1 := .call .here (Fin.cases (.literal (word 257)) Fin.elim0)
def callPolicy : Policy.ExprP .A call := (Policy.expr_iff .A _).mp rfl
def empty : WordState [] 0 := ⟨Fin.elim0,OpenFunctions.globalCells []⟩
example : (Solidity.Yul.OpenRun.expression 8 constantEnvironment call callPolicy empty).map
    (fun values => (values 0).val) = some 266 := by decide
example (index : WordCell (globals constantContext)) : False := index.not_globals
example : OpenFunctions.lookup constantEnvironment (.here : Member [signature] signature) =
    ⟨[signature],constantContext,constantEnvironment,constantBody,constantPolicy⟩ := rfl
example : Closed.lookup (OpenFunctions.lower constantEnvironment) (.here : Member [signature] signature) =
    OpenFunctions.lowerClosure (OpenFunctions.lookup constantEnvironment .here) :=
  OpenFunctions.lookup_lower constantEnvironment .here

def laterSignature : Sig := ⟨0,1⟩
def laterBody : Stmt [laterSignature,signature] [] ⟨true,false⟩ 1 :=
  .assign (Fin.cases (.local 0) Fin.elim0) (.literal (word 99))
def laterBodies : Bodies [laterSignature,signature] (globals []) [laterSignature] := .cons laterBody .nil
def laterPolicy : Policy.BodiesP .A laterBodies := (Policy.bodies_iff .A _).mp rfl
def laterEnvironment : OpenFunctions.PureEnvironment [laterSignature,signature] :=
  .group [laterSignature] constantEnvironment laterBodies laterPolicy
def oldCall : Expr [laterSignature,signature] [] 0 1 :=
  .call (.there .here) (Fin.cases (.literal (word 257)) Fin.elim0)
def laterCall : Expr [laterSignature,signature] [] 0 1 := .call .here Fin.elim0
example : OpenFunctions.lookup laterEnvironment (.there .here : Member [laterSignature,signature] signature) =
    OpenFunctions.lookup constantEnvironment .here :=
  OpenFunctions.lookup_old (X := []) (signatures := [laterSignature]) constantEnvironment laterBodies laterPolicy .here
example : (Solidity.Yul.OpenRun.expression 8 laterEnvironment oldCall
    ((Policy.expr_iff .A _).mp rfl) empty).map (fun values => (values 0).val) = some 266 := by decide
example : (Solidity.Yul.OpenRun.expression 8 laterEnvironment laterCall
    ((Policy.expr_iff .A _).mp rfl) empty).map (fun values => (values 0).val) = some 99 := by decide

/-- Generic tier data is available without claiming physical execution. -/
def memoryBody : Stmt [laterSignature] [] ⟨true,false⟩ 1 :=
  .assign (Fin.cases (.local 0) Fin.elim0)
    (.builtin .mload (Fin.cases (.literal (word 0)) Fin.elim0))
def memoryBodies : Bodies [laterSignature] (globals []) [laterSignature] := .cons memoryBody .nil
def memoryPolicy : Policy.BodiesP .B memoryBodies := (Policy.bodies_iff .B _).mp rfl
def memoryEnvironment : OpenFunctions.Environment .B [laterSignature] :=
  .group [laterSignature] .nil memoryBodies memoryPolicy
example : ¬ Policy.BodiesP .A memoryBodies := by
  intro admitted
  have builtin : Policy.BuiltinP .A .mload := admitted.1.2.1
  cases builtin.2
example : ¬ Nonempty (Member [] signature) := by rintro ⟨index⟩; cases index
example : Fixture.prepared [Solidity.Yul.Checks.BlockTyping.fn "bad" [] ["r"]
    [Solidity.Yul.Checks.BlockTyping.assign "r" (Solidity.Yul.Checks.BlockTyping.varExpr "x")]] = false := by decide
example : Fixture.prepared [Solidity.Yul.Checks.BlockTyping.assign "x"
    (Solidity.Yul.Checks.BlockTyping.call "mulDiv" [Solidity.Yul.Checks.BlockTyping.lit 1]),
    Solidity.Yul.Checks.BlockTyping.fn "mulDiv" ["a","b"] ["r"] []] = false := by decide
example : Fixture.prepared [Solidity.Yul.Checks.BlockTyping.fn "unused" [] ["r"]
    [Solidity.Yul.Checks.BlockTyping.assign "r" (Solidity.Yul.Checks.BlockTyping.call "gas" [])]] = false := by decide
example (fuel : Nat) :
    Solidity.Yul.OpenRun.localBlock Solidity.Yul.Checks.LocalBlock.ctx
      Solidity.Yul.Checks.LocalBlock.code Solidity.Yul.Checks.LocalBlock.policy fuel
        Solidity.Yul.Checks.LocalBlock.initial =
    runLocalBlock Solidity.Yul.Checks.LocalBlock.ctx Solidity.Yul.Checks.LocalBlock.code
      Solidity.Yul.Checks.LocalBlock.policy fuel Solidity.Yul.Checks.LocalBlock.initial :=
  Solidity.Yul.OpenRun.localBlock_eq _ _ _ _ _
example (cells : WordCells Fixture.types) :
    Solidity.Yul.OpenRun.holds .box Solidity.Yul.Checks.RawDivergence.prepared.typing.code
      Solidity.Yul.Checks.RawDivergence.prepared.policy (fun _ => False) ⟨Fin.elim0,cells⟩ := by
  intro fuel result done
  change Solidity.Yul.Checks.RawDivergence.prepared.openRun fuel cells = some result at done
  rw [ScopedSyntax.Prepared.openRun_eq_rawRun,Solidity.Yul.Checks.RawDivergence.run_none] at done
  cases done
example (cells : WordCells Fixture.types) :
    ¬ Solidity.Yul.OpenRun.holds .diamond Solidity.Yul.Checks.RawDivergence.prepared.typing.code
      Solidity.Yul.Checks.RawDivergence.prepared.policy (fun _ => True) ⟨Fin.elim0,cells⟩ := by
  rintro ⟨fuel,result,done,_⟩
  change Solidity.Yul.Checks.RawDivergence.prepared.openRun fuel cells = some result at done
  rw [ScopedSyntax.Prepared.openRun_eq_rawRun,Solidity.Yul.Checks.RawDivergence.run_none] at done
  cases done
def environmentWitness : Nonempty (OpenFunctions.PureEnvironment [signature]) := ⟨constantEnvironment⟩
def physicalDataWitness : Nonempty (OpenFunctions.Environment .B [laterSignature]) := ⟨memoryEnvironment⟩
def parsedWitness : Nonempty (ScopedSyntax.Prepared Fixture.scope .A Fixture.outside Fixture.localNames
    (Solidity.Yul.Checks.BlockTyping.list Fixture.recursive)) := ⟨Fixture.recursivePrepared⟩
example (mode : Solidity.Modality) :
    ∃ premise : Logic.Fml (0+wordCellCount Fixture.types), ∀ cells : WordCells Fixture.types,
      Solidity.Yul.OpenRun.holds mode Fixture.recursivePrepared.typing.code Fixture.recursivePrepared.policy
        (fun result => (result.state.cells Fixture.x).val = 13) ⟨Fin.elim0,cells⟩ ↔
          premise.holds (WordState.pack (X := Fixture.types) (n := 0) ⟨Fin.elim0,cells⟩) :=
  Fixture.recursivePrepared.openState_rule_sound mode _
/-- info: OPEN_RUN_COMPILED_PASS:88 actual checked-source direct/packed complete-state-flow comparisons; not EVM -/
#guard_msgs in
#eval do
  let mut count := 0
  for c in cases do
    for fuel in [0,1,2,3,4,8,16,32] do
      let direct := (c.checked.openRun fuel Fixture.initial).map snapshot
      let reference := (c.checked.rawRun fuel Fixture.initial).map snapshot
      unless direct == reference do throw (IO.userError ("full direct AST agreement failed: " ++ c.name))
      count := count+1
  unless count == 88 do throw (IO.userError "full direct AST matrix incomplete")
  unless observe cases[2] 32 == some ([599,2,0,0],true) &&
      observe cases[3] 32 == some ([13,2,0,0],true) &&
      observe cases[4] 32 == some ([259,2,0,3],true) &&
      observe cases[5] 32 == some ([2,257,0,0],true) do
    throw (IO.userError "full direct AST nontrivial function/loop/multi-return witness failed")
  IO.println "OPEN_RUN_COMPILED_PASS:88 actual checked-source direct/packed complete-state-flow comparisons; not EVM"
#check @Solidity.Yul.OpenRun.run_agrees
#check @Solidity.Yul.OpenRun.rule_sound
#print axioms Solidity.Yul.OpenRun.agreement
#print axioms Solidity.Yul.OpenRun.run_agrees
#print axioms Solidity.Yul.OpenRun.rule_sound
end Solidity.Yul.Checks.OpenRun
