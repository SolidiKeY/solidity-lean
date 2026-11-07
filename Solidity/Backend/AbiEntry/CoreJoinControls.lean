import Solidity.Backend.AbiEntry.CoreJoin

/-! Inhabited typed input, actual selected returning/reverting/looping bodies,
and a raw escaping-jump counterexample. No execution is supplied as a premise. -/
namespace Solidity.Backend.AbiEntry.CoreJoinControls
open Solidity.Evm
private def C : Contract := {vars := []}
private abbrev Γ : Ctx := [.val .uint]
private def state : State C Γ := (freshT C 0 W_pos (wmod 0)).push (t := .val .uint) ⟨5,by decide⟩
private def machine : Machine :=
  {Machine.init with
    mem := fun address => if address=0 then .val (wmod 5) else .val (wmod 0)
    stack := [.val (wmod 258),.val (wmod 513)]}

theorem initial_representation : Sim C 1 0 (Frag.init Γ) state machine := by
  have fresh : Sim C 1 0 (Frag.init []) (freshT C 0 W_pos (wmod 0)) (Machine.init (fun _ => 0) (wmod 0)) :=
    Sim.init C 0 W_pos (fun _ => 0) (wmod 0) rfl
  refine ⟨fresh.store,?_,?_,fresh.net,fresh.netSelf,fresh.bound,?_,fresh.env,fresh.funds,fresh.oracle⟩
  · intro p index
    cases index with
    | here => exact ReprV.uint_of rfl
    | there index => nomatch index
  · intro R index
    cases index with | there index => nomatch index
  · intro R index
    cases index with | there index => nomatch index

private def BodyCtx : Ctx := .val .bool :: Γ
private def yes : Prog C Γ BodyCtx :=
  .cons (.declLocal .bool (.user "matched") (some
    (.binop .eqB rfl rfl (.simple (.local .here)) (.simple (.lit 5 (by decide)))))) .nil
private def no : Prog C Γ Γ := .cons (.assignLocal .here (.simple (.lit 77 (by decide)))) .nil
private theorem yesCore : inFragP (Frag.init Γ) yes=some (Frag.init BodyCtx) := by rfl
private theorem noCore : inFragP (Frag.init Γ) no=some (Frag.init Γ) := by rfl
private def left := CoreJoin.compiled 0 (Frag.init Γ) yes _ yesCore
private def right := CoreJoin.compiled 0 (Frag.init Γ) no _ noCore
private def whole (tag : Fin W) := SelectorBranches.selectedWhole 0 (Frag.init Γ) .here tag yes no _ _ yesCore noCore
private def matched : Machine := {machine with mem := upd machine.mem 1 (.val (bword true))}
private def missed : Machine := {machine with mem := upd machine.mem 0 (.val (wmod 77))}
private def tailCode : List Evm.Instr := [.push (.val (wmod 77)),.mstore 0]

theorem returning_body_join :
    Compiler.compile 0 (Frag.init Γ) yes=some left ∧
    run (left.code++[.jump tailCode.length]++tailCode) machine=.ok matched 0 := by
  refine ⟨CoreJoin.selected 0 (Frag.init Γ) yes _ yesCore,?_⟩
  rw [CoreJoin.joined 1 0 (Frag.init Γ) yes _ yesCore left
    (CoreJoin.selected 0 (Frag.init Γ) yes _ yesCore) state machine initial_representation (by decide) tailCode]
  rfl

private theorem branches (tag : Fin W) :
    run (whole tag).code machine=if tag.val=(wmod 5).val then run left.code machine else run right.code machine :=
  CoreJoin.branch_outcome 1 0 (Frag.init Γ) .here tag yes no _ _ yesCore noCore
    (whole tag) left right (SelectorBranches.whole_selected 0 (Frag.init Γ) .here tag yes no _ _ yesCore noCore)
    (CoreJoin.selected 0 (Frag.init Γ) yes _ yesCore) (CoreJoin.selected 0 (Frag.init Γ) no _ noCore)
    state machine initial_representation (by decide) (wmod 5) rfl

theorem represented_branch_outcomes :
    run (whole (wmod 5)).code machine=.ok matched 0 ∧ run (whole (wmod 6)).code machine=.ok missed 0 := by
  constructor
  · rw [branches,if_pos (rfl : (wmod 5).val=(wmod 5).val)]
    rfl
  · rw [branches,if_neg (by decide : (wmod 6).val≠(wmod 5).val)]
    rfl

private def reverting : Prog C Γ Γ := .cons .revert .nil
private theorem revertingCore : inFragP (Frag.init Γ) reverting=some (Frag.init Γ) := by rfl
private def revertingCompiled := CoreJoin.compiled 0 (Frag.init Γ) reverting _ revertingCore

theorem reverting_body_join :
    Compiler.compile 0 (Frag.init Γ) reverting=some revertingCompiled ∧
    run (revertingCompiled.code++[.jump tailCode.length]++tailCode) machine=.revert := by
  refine ⟨CoreJoin.selected 0 (Frag.init Γ) reverting _ revertingCore,?_⟩
  rw [CoreJoin.joined 1 0 (Frag.init Γ) reverting _ revertingCore revertingCompiled
    (CoreJoin.selected 0 (Frag.init Γ) reverting _ revertingCore) state machine initial_representation (by decide) tailCode]
  rfl

private def forever : Prog C Γ Γ := .cons (.loop .auto (.simple (.bool true)) .nil) .nil
private theorem foreverCore : inFragP (Frag.init Γ) forever=some (Frag.init Γ) := by rfl
private def foreverCompiled := CoreJoin.compiled 0 (Frag.init Γ) forever _ foreverCore
private theorem forever_fault : run foreverCompiled.code machine=.fault := by
  have turns : ∀ n, loopIterN (fun next => exec [.push (.val (wmod 1))] 0 next)
      (fun next => exec [] 0 next) n machine=.inl machine := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => exact ih
  have divergent : loopRun (fun next => exec [.push (.val (wmod 1))] 0 next)
      (fun next => exec [] 0 next) machine=.fault := loopRun_of_forall (fun n => ⟨machine,turns n⟩)
  change (loopRun (fun next => exec [.push (.val (wmod 1))] 0 next)
    (fun next => exec [] 0 next) machine).bind (fun next skip => exec [] skip next)=.fault
  rw [divergent]
  rfl

theorem divergent_body_join :
    Compiler.compile 0 (Frag.init Γ) forever=some foreverCompiled ∧
    run foreverCompiled.code machine=.fault ∧
    run (foreverCompiled.code++[.jump tailCode.length]++tailCode) machine=.fault := by
  refine ⟨CoreJoin.selected 0 (Frag.init Γ) forever _ foreverCore,forever_fault,?_⟩
  rw [CoreJoin.joined 1 0 (Frag.init Γ) forever _ foreverCore foreverCompiled
    (CoreJoin.selected 0 (Frag.init Γ) forever _ foreverCore) state machine initial_representation (by decide) tailCode]
  exact forever_fault

/-- Raw escaping jumps do not satisfy arbitrary join removal. -/
theorem escaping_raw_counterexample :
    run [.jump 1] machine=.ok machine 1 ∧
    run ([.jump 1]++[.jump tailCode.length]++tailCode) machine=.ok missed 0 ∧
    run ([.jump 1]++[.jump tailCode.length]++tailCode) machine≠run [.jump 1] machine := by
  refine ⟨rfl,rfl,?_⟩
  change Out.ok missed 0≠Out.ok machine 1
  intro impossible
  exact Nat.noConfusion (Out.ok.inj impossible).2

theorem protected_and_saved :
    matched.mem 0=.val (wmod 5) ∧ matched.mem 1=.val (bword true) ∧ matched.mem 2=.val (wmod 0) ∧
    matched.stack=[.val (wmod 258),.val (wmod 513)] ∧ matched.store=machine.store ∧
    matched.bal=machine.bal ∧ matched.callvalue=machine.callvalue := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.AbiEntry.CoreJoinControls.initial_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms initial_representation
/-- info: 'Solidity.Backend.AbiEntry.CoreJoinControls.returning_body_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms returning_body_join
/-- info: 'Solidity.Backend.AbiEntry.CoreJoinControls.represented_branch_outcomes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms represented_branch_outcomes
/-- info: 'Solidity.Backend.AbiEntry.CoreJoinControls.reverting_body_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reverting_body_join
/-- info: 'Solidity.Backend.AbiEntry.CoreJoinControls.divergent_body_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms divergent_body_join
/-- info: 'Solidity.Backend.AbiEntry.CoreJoinControls.escaping_raw_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms escaping_raw_counterexample
/-- info: 'Solidity.Backend.AbiEntry.CoreJoinControls.protected_and_saved' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
end Solidity.Backend.AbiEntry.CoreJoinControls
