import Solidity.Yul.DirectControl
import Solidity.Yul.Checks.DirectUpdates
set_option Elab.async false
namespace Solidity.Yul.Checks.DirectControl
open Closed
open Solidity.Yul.Checks.DirectWords
open Solidity.Yul.DirectControl
def mutate {c : Control} : Stmt [] types c 1 :=
  .assign (Fin.cases (.external flag.writeRef) Fin.elim0) narrow
def mutateProof {c : Control} : Basic types (mutate (c := c)) :=
  .assign _ _
def copyFlag {c : Control} : Stmt [] types c 1 :=
  .assign (Fin.cases (.local 0) Fin.elim0) boolean
def copyProof {c : Control} : Basic types (copyFlag (c := c)) := .assign _ _
def ordered {c : Control} : Stmt [] types c 1 := .seq mutate copyFlag
def orderedProof {c : Control} : Basic types (ordered (c := c)) :=
  .seq mutateProof copyProof
def trueGuard : Stmt [] types ⟨false,false⟩ 1 := .if_ boolean mutate
def falseGuard : Stmt [] types ⟨false,false⟩ 1 := .if_ (.literal (word 0)) ordered
def earlyLeave : Stmt [] types ⟨true,false⟩ 1 := .seq mutate (.seq .leave copyFlag)
def earlyBreak : Stmt [] types ⟨false,true⟩ 1 := .seq mutate (.seq .break_ copyFlag)
def earlyContinue : Stmt [] types ⟨false,true⟩ 1 := .seq mutate (.seq .continue_ copyFlag)
def skippedBreak : Stmt [] types ⟨false,true⟩ 1 := .seq .break_ mutate
def guardedLeave : Stmt [] types ⟨true,false⟩ 1 := .seq (.if_ boolean .leave) mutate
def discardThenWrite : Stmt [] types ⟨false,false⟩ 1 := .seq (.discard popped) mutate
structure Case where
  name : String
  control : Control
  code : Stmt [] types control 1
  proof : Basic types code
  policy : Policy.StmtP .A code
def fixtures : List Case :=
  [⟨"ordered",⟨false,false⟩,ordered,orderedProof,by apply (Policy.stmt_iff .A _).mp; rfl⟩,
   ⟨"dirty-true",⟨false,false⟩,trueGuard,.if_ _ mutateProof,by apply (Policy.stmt_iff .A _).mp; rfl⟩,
   ⟨"false-skips",⟨false,false⟩,falseGuard,.if_ _ orderedProof,by apply (Policy.stmt_iff .A _).mp; rfl⟩,
   ⟨"early-leave",⟨true,false⟩,earlyLeave,.seq mutateProof (.seq .leave copyProof),by apply (Policy.stmt_iff .A _).mp; rfl⟩,
   ⟨"early-break",⟨false,true⟩,earlyBreak,.seq mutateProof (.seq .break_ copyProof),by apply (Policy.stmt_iff .A _).mp; rfl⟩,
   ⟨"early-continue",⟨false,true⟩,earlyContinue,.seq mutateProof (.seq .continue_ copyProof),by apply (Policy.stmt_iff .A _).mp; rfl⟩,
   ⟨"break-skips",⟨false,true⟩,skippedBreak,.seq .break_ mutateProof,by apply (Policy.stmt_iff .A _).mp; rfl⟩,
   ⟨"guarded-leave",⟨true,false⟩,guardedLeave,.seq (.if_ _ .leave) mutateProof,by apply (Policy.stmt_iff .A _).mp; rfl⟩,
   ⟨"discard-before-write",⟨false,false⟩,discardThenWrite,.seq (.discard _) mutateProof,by apply (Policy.stmt_iff .A _).mp; rfl⟩,
   ⟨"skip",⟨false,false⟩,.skip,.skip,True.intro⟩]
def flowTag {c} : Flow c → String
  | .normal => "normal"
  | .leave_ _ => "leave"
  | .break_ _ => "break"
  | .continue_ _ => "continue"
def snapshot {c} (outcome : WordAdapter.Outcome types c 1) : List Nat × String :=
  (Solidity.Yul.Checks.DirectUpdates.snapshot outcome.state,flowTag outcome.flow)
def observe (index fuel : Nat) : Option (List Nat × String) :=
  (fixtures[index]?).bind (fun c => (eval fuel c.proof c.policy state).map snapshot)

example : observe 0 0 = none := by decide
example : observe 0 2 = none := by decide
example : observe 0 3 = some ([257,257,257,2^256-1,2^32+1],"normal") := by decide
example : observe 1 2 = none := by decide
example : observe 1 3 = some ([7,257,257,2^256-1,2^32+1],"normal") := by decide
example : observe 2 1 = none := by decide
example : observe 2 2 = some ([7,257,2,2^256-1,2^32+1],"normal") := by decide
example : observe 3 2 = none := by decide
example : observe 3 3 = some ([7,257,257,2^256-1,2^32+1],"leave") := by decide
example : observe 4 3 = some ([7,257,257,2^256-1,2^32+1],"break") := by decide
example : observe 5 3 = some ([7,257,257,2^256-1,2^32+1],"continue") := by decide
example : observe 6 2 = some ([7,257,2,2^256-1,2^32+1],"break") := by decide
example : observe 7 2 = none := by decide
example : observe 7 3 = some ([7,257,2,2^256-1,2^32+1],"leave") := by decide
example : observe 8 4 = none := by decide
example : observe 8 5 = some ([7,257,257,2^256-1,2^32+1],"normal") := by decide
example : observe 9 0 = none := by decide
example : observe 9 1 = some ([7,257,2,2^256-1,2^32+1],"normal") := by decide

/-- Explicit family frontier, not a source admission refusal. -/
example : ¬ Nonempty (Basic types (Stmt.zero (c := ⟨false,false⟩) (n := 1) 1 .skip)) := by
  rintro ⟨proof⟩
  cases proof
example : ¬ Nonempty (Basic types
    (Stmt.functions (F := []) (c := ⟨false,false⟩) (n := 1) [] .nil .skip)) := by
  rintro ⟨proof⟩
  cases proof
example : ¬ Policy.StmtP .A
    (Stmt.discard (F := []) (X := types) (c := ⟨false,false⟩) (n := 1)
      (.builtin .stop Fin.elim0)) := by
  intro policy
  cases policy.1.2

def witness : Nonempty Case := ⟨fixtures[3]⟩
def doneWitness : ∃ outcome : WordAdapter.Outcome types ⟨true,false⟩ 1,
    eval 3 (.seq mutateProof (.seq .leave copyProof))
      (show Policy.StmtP .A earlyLeave from (Policy.stmt_iff .A _).mp rfl) state = some outcome ∧
      snapshot outcome = ([7,257,257,2^256-1,2^32+1],"leave") :=
  ⟨⟨Solidity.Yul.DirectUpdates.write (.external flag.writeRef) True.intro (word 257) state,.leave_ rfl⟩,
    rfl,by decide⟩
example (fuel : Nat) : eval fuel orderedProof
    ((Policy.stmt_iff .A _).mp (show Policy.checkStmt .A (ordered (c := ⟨false,false⟩)) = .ok () from rfl)) state =
    WordAdapter.run ordered ((Policy.stmt_iff .A _).mp rfl) fuel state :=
  run_agrees fuel orderedProof _ state

#eval do
  let mut count := 0
  for c in fixtures do
    for fuel in List.range 9 do
      let direct := (eval fuel c.proof c.policy state).map snapshot
      let reference := (WordAdapter.run c.code c.policy fuel state).map snapshot
      unless direct == reference do throw (IO.userError ("direct control agreement failed: " ++ c.name))
      count := count+1
  unless count == 90 do throw (IO.userError "direct control matrix incomplete")
  IO.println "DIRECT_CONTROL_COMPILED_PASS:90 direct/actual raw-run full state/flow comparisons; not EVM tests"
#check @Solidity.Yul.DirectControl.agrees
#check @Solidity.Yul.DirectControl.run_agrees
#print axioms Solidity.Yul.DirectControl.run_agrees
#print axioms Solidity.Yul.DirectControl.stable
#print axioms Solidity.Yul.DirectControl.evidence_independent
end Solidity.Yul.Checks.DirectControl
