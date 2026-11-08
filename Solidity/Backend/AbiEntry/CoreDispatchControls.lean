import Solidity.Backend.AbiEntry.CoreDispatch
import Solidity.Backend.AbiEntry.CoreJoinControls

/-! Actual first/middle/missing selector outcomes and terminal collision
failure, with heterogeneous intrinsic body outputs and inhabited input Sim. -/
namespace Solidity.Backend.AbiEntry.CoreDispatchControls
open Solidity.Evm
open Interface (DispatchBody DispatchRow dispatchTarget)
private def C : Contract := {vars := []}
private abbrev Γ : Ctx := [.val .uint]
private def state : State C Γ := (freshT C 0 W_pos (wmod 0)).push (t := .val .uint) ⟨5,by decide⟩
private def machine : Machine :=
  {Machine.init with
    mem := fun address => if address=0 then .val (wmod 5) else .val (wmod 0)
    stack := [.val (wmod 258),.val (wmod 513)]}
private theorem represented : Sim C 1 0 (Frag.init Γ) state machine := CoreJoinControls.initial_representation
private abbrev Target := DispatchBody C Γ (Frag.init Γ)
private abbrev Row := DispatchRow C Γ (Frag.init Γ)
private def alpha : Target :=
  {outCtx := .val .bool::Γ
   program := .cons (.declLocal .bool (.user "matched") (some
     (.binop .eqB rfl rfl (.simple (.local .here)) (.simple (.lit 5 (by decide)))))) .nil
   outFrag := Frag.init (.val .bool::Γ)
   admitted := by rfl}
private def beta : Target :=
  {outCtx := Γ,program := .cons (.assignLocal .here (.simple (.lit 22 (by decide)))) .nil
   outFrag := Frag.init Γ,admitted := by rfl}
private def fallback : Target :=
  {outCtx := Γ,program := ValueGateBody.guard false (.cons (.assignLocal .here (.simple (.lit 77 (by decide)))) .nil)
   outFrag := Frag.init Γ,admitted := by rfl}
private def rejecting : Target :=
  {outCtx := Γ,program := .cons .revert .nil,outFrag := Frag.init Γ,admitted := by rfl}
private def firstRows : List Row := [⟨wmod 5,alpha⟩,⟨wmod 5,beta⟩,⟨wmod 6,beta⟩]
private def laterRows : List Row := [⟨wmod 6,alpha⟩,⟨wmod 5,beta⟩]
private def missRows : List Row := [⟨wmod 6,alpha⟩,⟨wmod 7,beta⟩]
private def rejectRows : List Row := [⟨wmod 5,rejecting⟩,⟨wmod 5,beta⟩]
private def compiled (rows : List Row) := CoreDispatch.compiled 0 (Frag.init Γ) .here rows fallback
private def alphaOut : Machine := {machine with mem := upd machine.mem 1 (.val (bword true))}
private def betaOut : Machine := {machine with mem := upd machine.mem 0 (.val (wmod 22))}
private def fallbackOut : Machine := {machine with mem := upd machine.mem 0 (.val (wmod 77))}
private theorem actual (rows : List Row) (room : ∀ row ∈ rows,1+Prog.pushes row.target.program≤Lmax) :
    run (compiled rows).code machine=run (compileProg 0 (dispatchTarget rows fallback (wmod 5)).program) machine :=
  CoreDispatch.executed 1 0 (Frag.init Γ) .here rows fallback (compiled rows)
    (CoreDispatch.selected 0 (Frag.init Γ) .here rows fallback) state machine represented room (wmod 5) rfl
private theorem firstRoom : ∀ row ∈ firstRows,1+Prog.pushes row.target.program≤Lmax := by
  intro row member
  simp only [firstRows,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> decide
private theorem laterRoom : ∀ row ∈ laterRows,1+Prog.pushes row.target.program≤Lmax := by
  intro row member
  simp only [laterRows,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> decide
private theorem missRoom : ∀ row ∈ missRows,1+Prog.pushes row.target.program≤Lmax := by
  intro row member
  simp only [missRows,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> decide
private theorem rejectRoom : ∀ row ∈ rejectRows,1+Prog.pushes row.target.program≤Lmax := by
  intro row member
  simp only [rejectRows,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> decide

theorem public_selections :
    Compiler.compile 0 (Frag.init Γ) (CoreDispatch.route (Frag.init Γ) .here firstRows fallback)=some (compiled firstRows) ∧
    Compiler.compile 0 (Frag.init Γ) alpha.program=some (CoreDispatch.bodyCompiled 0 (Frag.init Γ) alpha) ∧
    Compiler.compile 0 (Frag.init Γ) beta.program=some (CoreDispatch.bodyCompiled 0 (Frag.init Γ) beta) :=
  ⟨CoreDispatch.selected 0 (Frag.init Γ) .here firstRows fallback,
    CoreDispatch.body_selected 0 (Frag.init Γ) alpha,CoreDispatch.body_selected 0 (Frag.init Γ) beta⟩

theorem first_match_wins_collision : run (compiled firstRows).code machine=.ok alphaOut 0 := by
  rw [actual firstRows firstRoom]
  rfl

theorem later_match_executes : run (compiled laterRows).code machine=.ok betaOut 0 := by
  rw [actual laterRows laterRoom]
  rfl

theorem no_match_executes_fallback : run (compiled missRows).code machine=.ok fallbackOut 0 := by
  rw [actual missRows missRoom]
  rfl

/-- A rejected first match cannot fall through to a colliding successful body. -/
theorem collision_failure_terminal :
    run (compiled rejectRows).code machine=.revert ∧
    run (CoreDispatch.bodyCompiled 0 (Frag.init Γ) beta).code machine=.ok betaOut 0 := by
  constructor
  · rw [actual rejectRows rejectRoom]
    rfl
  · rfl

theorem empty_table_executes_default : run (compiled []).code machine=.ok fallbackOut 0 := by
  rw [actual [] (fun _ member => False.elim (List.not_mem_nil member))]
  rfl

theorem default_can_revert :
    run (CoreDispatch.compiled 0 (Frag.init Γ) .here [] rejecting).code machine=.revert := by
  rw [CoreDispatch.executed 1 0 (Frag.init Γ) .here [] rejecting _
    (CoreDispatch.selected 0 (Frag.init Γ) .here [] rejecting) state machine represented
    (fun _ member => False.elim (List.not_mem_nil member)) (wmod 5) rfl]
  rfl

theorem heterogeneous_outputs : alpha.outCtx=.val .bool::Γ ∧ beta.outCtx=Γ ∧
    alphaOut.mem 0=.val (wmod 5) ∧ alphaOut.mem 1=.val (bword true) ∧ betaOut.mem 0=.val (wmod 22) :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem protected_and_saved :
    alphaOut.mem 2=.val (wmod 0) ∧ alphaOut.stack=[.val (wmod 258),.val (wmod 513)] ∧
    alphaOut.store=machine.store ∧ alphaOut.bal=machine.bal ∧ alphaOut.callvalue=machine.callvalue ∧
    betaOut.stack=machine.stack ∧ fallbackOut.stack=machine.stack := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.AbiEntry.CoreDispatchControls.public_selections' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms public_selections
/-- info: 'Solidity.Backend.AbiEntry.CoreDispatchControls.first_match_wins_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms first_match_wins_collision
/-- info: 'Solidity.Backend.AbiEntry.CoreDispatchControls.later_match_executes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms later_match_executes
/-- info: 'Solidity.Backend.AbiEntry.CoreDispatchControls.no_match_executes_fallback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_match_executes_fallback
/-- info: 'Solidity.Backend.AbiEntry.CoreDispatchControls.collision_failure_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms collision_failure_terminal
/-- info: 'Solidity.Backend.AbiEntry.CoreDispatchControls.empty_table_executes_default' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_table_executes_default
/-- info: 'Solidity.Backend.AbiEntry.CoreDispatchControls.default_can_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms default_can_revert
/-- info: 'Solidity.Backend.AbiEntry.CoreDispatchControls.heterogeneous_outputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms heterogeneous_outputs
/-- info: 'Solidity.Backend.AbiEntry.CoreDispatchControls.protected_and_saved' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
end Solidity.Backend.AbiEntry.CoreDispatchControls
