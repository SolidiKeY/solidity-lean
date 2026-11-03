import Solidity.Yul.DirectBindings
import Solidity.Yul.Checks.DirectControl
set_option Elab.async false
namespace Solidity.Yul.Checks.DirectBindings
open Closed
open Solidity.Yul.DirectBindings
open Solidity.Yul.Checks.DirectWords
def arg2 {n} (a b : Expr [] types n 1) : Fin 2 → Expr [] types n 1 :=
  Fin.cases a (Fin.cases b Fin.elim0)
def bin {n} (op : Pure 2) (a b : Expr [] types n 1) : Expr [] types n 1 :=
  .builtin (.pure op) (arg2 a b)
def set {c n} (target : Target types n) (rhs : Expr [] types n 1) : Stmt [] types c n :=
  .assign (Fin.cases target Fin.elim0) rhs
def setProof {c n} (target : Target types n) (rhs : Expr [] types n 1) :
    Supported types (set (c := c) target rhs) := .base (.assign _ _)
def rawBind {c : Control} : Stmt [] types c 1 :=
  .let_ 1 narrow (.seq (set (.external flag.writeRef) (.local 0))
    (set (.local 1) (bin .add (.local 0) (.local 1))))
def rawBindProof {c : Control} : Supported types (rawBind (c := c)) :=
  .let_ _ (.seq (setProof _ _) (setProof _ _))
def zeroBind : Stmt [] types ⟨false,false⟩ 1 :=
  .zero 2 (.seq (set (.external flag.writeRef) (.local 0))
    (set (.local 2) (bin .add (.local 1) (.local 2))))
def zeroProof : Supported types zeroBind :=
  .zero 2 (.seq (setProof _ _) (setProof _ _))
def nested : Stmt [] types ⟨false,false⟩ 1 :=
  .let_ 1 selector (.zero 1 (.seq (set (.external (WordCell.address function).writeRef) (.local 1))
    (set (.local 2) (bin .add (.local 0) (.local 2)))))
def nestedProof : Supported types nested :=
  .let_ _ (.zero 1 (.seq (setProof _ _) (setProof _ _)))
def guardBind (initial : Expr [] types 1 1) : Stmt [] types ⟨false,false⟩ 1 :=
  .let_ 1 initial (.if_ (.local 0) (set (.external flag.writeRef) (.local 0)))
def guardProof (initial : Expr [] types 1 1) : Supported types (guardBind initial) :=
  .let_ _ (.if_ _ (setProof _ _))
def leaveBind : Stmt [] types ⟨true,false⟩ 1 :=
  .let_ 1 selector (.seq (set (.external flag.writeRef) (.local 0))
    (.seq .leave (set (.local 1) (.literal (word 999)))))
def leaveProof : Supported types leaveBind :=
  .let_ _ (.seq (setProof _ _) (.seq (.base .leave) (setProof _ _)))
def breakBind : Stmt [] types ⟨false,true⟩ 1 :=
  .zero 2 (.seq (set (.local 0) (.literal (word 511)))
    (.seq (set (.external flag.writeRef) (.local 0)) .break_))
def breakProof : Supported types breakBind :=
  .zero 2 (.seq (setProof _ _) (.seq (setProof _ _) (.base .break_)))
def continueBind : Stmt [] types ⟨false,true⟩ 1 :=
  .zero 2 (.seq (set (.local 0) (.literal (word 511)))
    (.seq (set (.external flag.writeRef) (.local 0)) .continue_))
def continueProof : Supported types continueBind :=
  .zero 2 (.seq (setProof _ _) (.seq (setProof _ _) (.base .continue_)))
def afterBind : Stmt [] types ⟨false,false⟩ 1 :=
  .seq rawBind (set (.external small.writeRef) (bin .add (.local 0) boolean))
def afterProof : Supported types afterBind := .seq rawBindProof (setProof _ _)
structure Case where
  name : String
  control : Control
  code : Stmt [] types control 1
  proof : Supported types code
  policy : Policy.StmtP .A code
def fixtures : List Case :=
  [⟨"raw-bind",⟨false,false⟩,rawBind,rawBindProof,by apply (Policy.stmt_iff .A _).mp; rfl⟩,
   ⟨"zero-bind",⟨false,false⟩,zeroBind,zeroProof,by apply (Policy.stmt_iff .A _).mp; rfl⟩,
   ⟨"nested-fields",⟨false,false⟩,nested,nestedProof,by apply (Policy.stmt_iff .A _).mp; rfl⟩,
   ⟨"dirty-guard",⟨false,false⟩,guardBind narrow,guardProof _,by apply (Policy.stmt_iff .A _).mp; rfl⟩,
   ⟨"zero-guard",⟨false,false⟩,guardBind (.literal (word 0)),guardProof _,by apply (Policy.stmt_iff .A _).mp; rfl⟩,
   ⟨"leave-drops",⟨true,false⟩,leaveBind,leaveProof,by apply (Policy.stmt_iff .A _).mp; rfl⟩,
   ⟨"break-drops",⟨false,true⟩,breakBind,breakProof,by apply (Policy.stmt_iff .A _).mp; rfl⟩,
   ⟨"continue-drops",⟨false,true⟩,continueBind,continueProof,by apply (Policy.stmt_iff .A _).mp; rfl⟩,
   ⟨"after-bind",⟨false,false⟩,afterBind,afterProof,by apply (Policy.stmt_iff .A _).mp; rfl⟩,
   ⟨"zero-arity",⟨false,false⟩,.zero 0 .skip,.zero 0 (.base .skip),True.intro⟩,
   ⟨"zero-result-let",⟨false,false⟩,.let_ 0 popped (set (.external flag.writeRef) narrow),
     .let_ _ (setProof _ _),by apply (Policy.stmt_iff .A _).mp; rfl⟩]
def snapshot {c} (outcome : WordAdapter.Outcome types c 1) : List Nat × String :=
  (Solidity.Yul.Checks.DirectUpdates.snapshot outcome.state,
    Solidity.Yul.Checks.DirectControl.flowTag outcome.flow)
def observe (index fuel : Nat) : Option (List Nat × String) :=
  (fixtures[index]?).bind (fun c => (eval fuel c.proof c.policy state).map snapshot)
example : observe 0 0 = none := by decide
example : observe 0 4 = none := by decide
example : observe 0 5 = some ([264,257,257,2^256-1,2^32+1],"normal") := by decide
example : observe 1 4 = none := by decide
example : observe 1 5 = some ([7,257,0,2^256-1,2^32+1],"normal") := by decide
example : observe 2 5 = none := by decide
example : observe 2 6 = some ([7,257,2,2^32+1,2^32+1],"normal") := by decide
example : observe 3 3 = none := by decide
example : observe 3 4 = some ([7,257,257,2^256-1,2^32+1],"normal") := by decide
example : observe 4 3 = some ([7,257,2,2^256-1,2^32+1],"normal") := by decide
example : observe 5 3 = none := by decide
example : observe 5 4 = some ([7,257,2^32+1,2^256-1,2^32+1],"leave") := by decide
example : observe 6 5 = some ([7,257,511,2^256-1,2^32+1],"break") := by decide
example : observe 7 5 = some ([7,257,511,2^256-1,2^32+1],"continue") := by decide
example : observe 8 5 = none := by decide
example : observe 8 6 = some ([264,521,257,2^256-1,2^32+1],"normal") := by decide
example : observe 9 1 = none := by decide
example : observe 9 2 = some ([7,257,2,2^256-1,2^32+1],"normal") := by decide

example : observe 10 3 = none := by decide
example : observe 10 4 = some ([7,257,257,2^256-1,2^32+1],"normal") := by decide

def coordinates := (Coordinates.canonical types 1).prepend 2
def front : Values 2 := Fin.cases (word 511) (Fin.cases (word 0) Fin.elim0)
example : (List.ofFn (coordinates.pack (state.extend front))).map Fin.val =
    [511,0,7,257,2,2^256-1,2^32+1] := by decide
example : (List.ofFn ((coordinates.prepend 1).pack ((state.extend front).extend (fun _ => word 9)))).map Fin.val =
    [9,511,0,7,257,2,2^256-1,2^32+1] := by decide
example (index : Fin 3) (cell : WordCell types) : coordinates.locals index ≠ coordinates.cells cell :=
  coordinates.disjoint index cell
example (s : WordState types 3) :
    (Coordinates.canonical types 1).pack (s.drop 2) =
      Closed.dropValues 2 (coordinates.pack s) := Coordinates.pack_drop (r := 2) (Coordinates.canonical types 1) s

def oldCode := Solidity.Yul.Checks.DirectControl.ordered (c := ⟨false,false⟩)
def old : Supported types oldCode := .base Solidity.Yul.Checks.DirectControl.orderedProof
def expanded : Supported types oldCode :=
  .seq (.base Solidity.Yul.Checks.DirectControl.mutateProof) (.base Solidity.Yul.Checks.DirectControl.copyProof)
example : old ≠ expanded := by intro same; cases same
example (fuel : Nat) (s : WordState types 1) :
    eval fuel old ((Policy.stmt_iff .A _).mp rfl) s =
      eval fuel expanded ((Policy.stmt_iff .A _).mp rfl) s :=
  evidence_independent old expanded _ fuel s
/-- Frontiers only, not source-admission verdicts. Old Basic binder refusal remains. -/
example : ¬ Nonempty (DirectControl.Basic types (rawBind (c := ⟨false,false⟩))) := by rintro ⟨p⟩; cases p
example : ¬ Nonempty (Supported types
    (Stmt.functions (F := []) (c := ⟨false,false⟩) (n := 1) [] .nil .skip)) := by
  rintro ⟨p⟩
  cases p with
  | base p => cases p
example : ¬ Nonempty (Coordinates [] 0 1) := by
  rintro ⟨c⟩
  cases c.origin 0 with
  | inl i => exact Fin.elim0 i
  | inr cell =>
    cases cell with
    | scalar ref => cases ref.index
    | address index => cases index
    | selector index => cases index
def witness : Nonempty Case := ⟨fixtures[0]⟩
def dirtyWitness : ∃ s : WordState types 3,
    (List.ofFn (coordinates.pack s)).map Fin.val = [511,0,7,257,2,2^256-1,2^32+1] :=
  ⟨state.extend front,by decide⟩
#eval do
  let mut count := 0
  for c in fixtures do
    for fuel in [0,1,2,3,4,5,6,8,12] do
      let direct := (eval fuel c.proof c.policy state).map snapshot
      let reference := (WordAdapter.run c.code c.policy fuel state).map snapshot
      unless direct == reference do throw (IO.userError ("direct binder agreement failed: " ++ c.name))
      count := count+1
  unless count == 99 do throw (IO.userError "binder matrix incomplete")
  IO.println "DIRECT_BINDINGS_COMPILED_PASS:99 actual direct/packed nested-binder full-state-flow comparisons; not EVM"
#check @Solidity.Yul.Coordinates
#check @Solidity.Yul.Coordinates.prepend
#check @Solidity.Yul.DirectBindings.agrees
#check @Solidity.Yul.DirectBindings.run_agrees
#print axioms Solidity.Yul.Coordinates.pack_prefix
#print axioms Solidity.Yul.DirectBindings.run_agrees
#print axioms Solidity.Yul.DirectBindings.evidence_independent
end Solidity.Yul.Checks.DirectBindings
