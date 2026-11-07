import Solidity.Backend.AbiEntry.SizeBranches

/-! Actual typed short/full bodies, represented input, strict size boundary,
terminal failure and raw escaping-skip controls. Native size binding is separate. -/
namespace Solidity.Backend.AbiEntry.SizeBranchesControls
open Solidity.Evm
private def C : Contract := {vars := []}
private abbrev Γ : Ctx := [.val .uint]
private def state (size : Fin W) : State C Γ :=
  (freshT C 0 W_pos (wmod 0)).push (t := .val .uint)
    ⟨(size.val : Int),PrimTy.inRange_uint_of_lt size.isLt⟩
private def machine (size : Fin W) : Machine :=
  {Machine.init with
    mem := fun address => if address=0 then .val size else .val (wmod 71)
    stack := [.val (wmod 258),.val (wmod 513)]}
private theorem represented (size : Fin W) : Sim C 1 0 (Frag.init Γ) (state size) (machine size) := by
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
private def yes : Prog C Γ Γ :=
  .cons (.assignLocal .here (.simple (.lit 11 (by decide)))) .nil
private def no : Prog C Γ (.val .bool::Γ) :=
  .cons (.declLocal .bool (.user "sizeIsFour") (some
    (.binop .eqB rfl rfl (.simple (.local .here)) (.simple (.lit 4 (by decide)))))) .nil
private def failing : Prog C Γ Γ := .cons .revert .nil
private theorem yesCore : inFragP (Frag.init Γ) yes=some (Frag.init Γ) := rfl
private theorem noCore : inFragP (Frag.init Γ) no=some (Frag.init (.val .bool::Γ)) := rfl
private theorem failCore : inFragP (Frag.init Γ) failing=some (Frag.init Γ) := rfl
private def left := SizeBranches.selectedBranch 0 (Frag.init Γ) yes _ yesCore
private def right := SizeBranches.selectedBranch 0 (Frag.init Γ) no _ noCore
private def whole := SizeBranches.selectedWhole 0 (Frag.init Γ) .here yes no _ _ yesCore noCore
private def wholeFail := SizeBranches.selectedWhole 0 (Frag.init Γ) .here failing no _ _ failCore noCore
private def shortOut (size : Fin W) : Machine := {machine size with mem := upd (machine size).mem 0 (.val (wmod 11))}
private def fullOut (size : Fin W) : Machine := {machine size with mem := upd (machine size).mem 1 (.val (bword (decide (4=size.val))))}
private theorem room : 1+Prog.pushes yes≤Lmax := by decide
private theorem actual (size : Fin W) : run whole.code (machine size)=
    if size.val<4 then run left.code (machine size) else run right.code (machine size) :=
  SizeBranches.branch_outcome 1 0 (Frag.init Γ) .here yes no _ _ yesCore noCore whole left right
    (SizeBranches.whole_selected 0 (Frag.init Γ) .here yes no _ _ yesCore noCore)
    (SizeBranches.branch_selected 0 (Frag.init Γ) yes _ yesCore)
    (SizeBranches.branch_selected 0 (Frag.init Γ) no _ noCore)
    (state size) (machine size) (represented size) room size rfl

theorem public_selection :
    Compiler.compile 0 (Frag.init Γ) (SizeBranches.program .here yes no)=some whole :=
  SizeBranches.whole_selected 0 (Frag.init Γ) .here yes no _ _ yesCore noCore

theorem short (size : Fin W) (small : size.val<4) :
    run whole.code (machine size)=.ok (shortOut size) 0 := by
  rw [actual,if_pos small]
  change run [.push (.val (wmod 11)),.mstore 0] (machine size)=_
  rfl

theorem full (size : Fin W) (long : 4≤size.val) :
    run whole.code (machine size)=.ok (fullOut size) 0 := by
  rw [actual,if_neg (Nat.not_lt_of_ge long)]
  change run [.mload 0,.push (.val (wmod 4)),.eq,.mstore 1] (machine size)=_
  have initial : (machine size).mem 0=.val size := rfl
  have four : (wmod 4).val=4 := rfl
  simp only [run,exec_cons_zero,Instr.step,Machine.next,Out.bind,initial,four]
  rfl

theorem boundaries :
    run whole.code (machine (wmod 0))=.ok (shortOut (wmod 0)) 0 ∧
    run whole.code (machine (wmod 3))=.ok (shortOut (wmod 3)) 0 ∧
    run whole.code (machine (wmod 4))=.ok (fullOut (wmod 4)) 0 ∧
    run whole.code (machine (wmod (W-1)))=.ok (fullOut (wmod (W-1))) 0 :=
  ⟨short _ (by decide),short _ (by decide),full _ (by decide),full _ (by decide)⟩

theorem short_revert_is_terminal : run wholeFail.code (machine (wmod 0))=.revert := by
  have outcome : run wholeFail.code (machine (wmod 0))=
      if (wmod 0).val<4 then run (SizeBranches.selectedBranch 0 (Frag.init Γ) failing _ failCore).code (machine (wmod 0))
      else run right.code (machine (wmod 0)) :=
    SizeBranches.branch_outcome 1 0 (Frag.init Γ) .here failing no _ _ failCore noCore wholeFail
      (SizeBranches.selectedBranch 0 (Frag.init Γ) failing _ failCore) right
      (SizeBranches.whole_selected 0 (Frag.init Γ) .here failing no _ _ failCore noCore)
      (SizeBranches.branch_selected 0 (Frag.init Γ) failing _ failCore)
      (SizeBranches.branch_selected 0 (Frag.init Γ) no _ noCore)
      (state (wmod 0)) (machine (wmod 0)) (represented (wmod 0)) (by decide) (wmod 0) rfl
  rw [if_pos (by decide)] at outcome
  exact outcome.trans rfl

private theorem whole_code : whole.code=
    [.mload 0,.push (.val (wmod 4)),.gt,.iszero,.jumpi 3,.push (.val (wmod 11)),.mstore 0,
      .jump 4,.mload 0,.push (.val (wmod 4)),.eq,.mstore 1] := rfl

theorem malformed_size_faults :
    run whole.code {machine (wmod 0) with mem := fun _ => .slot (.root 0)}=.fault := by
  rw [whole_code]
  simp only [run,exec,Instr.step,Machine.next,Out.bind]

theorem escaping_raw_skip_retained :
    run ([.mload 0,.push (.val (wmod 4)),.gt,.iszero,.jumpi 2]++[.jump 9]++[.jump 1]++[.revert])
      (machine (wmod 0))=.ok (machine (wmod 0)) 7 := by
  have front : run ([.mload 0,.push (.val (wmod 4)),.gt,.iszero,.jumpi 2]++[.jump 9]++[.jump 1]++[.revert])
      (machine (wmod 0))=if (wmod 0).val<4 then run ([.jump 9]++[.jump 1]++[.revert]) (machine (wmod 0))
      else run [.revert] (machine (wmod 0)) :=
    SizeBranches.test_run 0 (wmod 0) [.jump 9] [.revert] (machine (wmod 0)) rfl
  rw [if_pos (by decide)] at front
  exact front.trans rfl

theorem protected_state :
    (fullOut (wmod 4)).mem 0=.val (wmod 4) ∧ (fullOut (wmod 4)).mem 1=.val (bword true) ∧
    (fullOut (wmod 4)).mem 2=.val (wmod 71) ∧
    (fullOut (wmod 4)).stack=[.val (wmod 258),.val (wmod 513)] ∧
    (fullOut (wmod 4)).store=(machine (wmod 4)).store ∧
    (fullOut (wmod 4)).bal=(machine (wmod 4)).bal := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.AbiEntry.SizeBranchesControls.public_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms public_selection
/-- info: 'Solidity.Backend.AbiEntry.SizeBranchesControls.short' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short
/-- info: 'Solidity.Backend.AbiEntry.SizeBranchesControls.full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms full
/-- info: 'Solidity.Backend.AbiEntry.SizeBranchesControls.boundaries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boundaries
/-- info: 'Solidity.Backend.AbiEntry.SizeBranchesControls.short_revert_is_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_revert_is_terminal
/-- info: 'Solidity.Backend.AbiEntry.SizeBranchesControls.malformed_size_faults' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms malformed_size_faults
/-- info: 'Solidity.Backend.AbiEntry.SizeBranchesControls.escaping_raw_skip_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms escaping_raw_skip_retained
/-- info: 'Solidity.Backend.AbiEntry.SizeBranchesControls.protected_state' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms protected_state
end Solidity.Backend.AbiEntry.SizeBranchesControls
