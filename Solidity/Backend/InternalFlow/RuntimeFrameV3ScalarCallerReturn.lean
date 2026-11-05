import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarUnwindEndpoint
import Solidity.Backend.InternalFlow.RuntimeFrameV3CallerReframe
import Solidity.Backend.InternalFlow.RuntimeFrameResult

/-! A populated scalar caller saves its old scalar before argument setup and
recovers it after the actual three-parent return. The handwritten countdown
image and compiler-generated checked increments are explicit; no general
public recursive selector or profile instance is claimed. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarCallerReturn
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource CountdownWitness
abbrev Γ : Ctx := .val .uint :: CallerReframe.Checks.Γ
abbrev F := CallerReframe.Checks.F.push (.val .uint) .ok
def caller := CallerReframe.Checks.caller.push (t:=.val .uint) (countValue 77 (by decide))
def before := writeMachine (writeMachine CallerReframe.Checks.before 7 w[0]) 4 w[77]
def entryCode : List Instr := [.mload 3,.mstore 6,.push w[3],.mstore 3,.push w[0],.mstore 4]
def suffix : List Instr := [.mload 6,.mstore 3,.mload 4,.mstore 4]
def args : Args P.C Γ (Parameters A) :=
 .snoc (.snocMemory .nil A (.user "alias") (.var (.there (.there .here)) rfl)) .uint (.user "count") (.simple (.lit 3 rfl))
def invoke (depth : Nat) : Stmt P.C Γ Γ :=
 InterfaceV1.recursiveSource "scalarCountdown" args (.val .uint (.user "result") (some .here)) (step A rfl) depth

theorem initial : StateRepr 1 1 16 F caller P.base before :=
 (reserved_write CallerReframe.Checks.initial 7 (by decide) (by decide) w[0]).consVal
   (countValue 77 (by decide)) w[77] (ReprV.uint_of rfl) (by decide)

theorem arguments : args.evalT caller=.ok (countValue 3 (by decide),(some P.r0,())) := rfl

theorem source (depth : Nat) (enough : 3<depth) :
 (invoke depth).run caller=.ok ⟨caller.setLocal .here (countValue 3 (by decide)),List.prefix_refl _⟩ := by
 simpa only [if_pos enough] using call_all_horizons rfl "scalarCountdown" args .here depth caller 3 (by decide) P.r0 arguments

theorem entered : run entryCode before=.ok ScalarUnwind.Client.entered 0 := by
 change (.ok (writeMachine (writeMachine (writeMachine before 6 w[2]) 3 w[3]) 4 w[0]) 0 : Evm.Out)=_
 apply congrArg (fun memory => Evm.Out.ok {AllocatorReturn.Checks.input with mem:=memory} 0)
 funext x
 by_cases h4 : x=4
 · subst x;rfl
 by_cases h3 : x=3
 · subst x;rfl
 by_cases h6 : x=6
 · subst x;rfl
 by_cases h7 : x=7
 · subst x;rfl
 simp only [before,CallerReframe.Checks.before,ParentPrefixes.Checks.input,
   ScalarUnwind.Client.before,writeMachine,upd,if_neg h4,if_neg h3,if_neg h6,if_neg h7]

def tailCode : List Instr :=
 RecursiveActivation.descentCode (C:=P.C) 2 CountdownWitness.F 8 ++
 ([.push w[0],.mstore 4] ++ ScalarUnwind.Client.unwindCode)
def image := entryCode ++ (tailCode ++ suffix)

theorem endpoint : ∃ (last : Machine) (addresses : Nat → Fin W),
 run image before=.ok last 0 ∧
 StateRepr 1 1 16 F (caller.setLocal .here (countValue 3 (by decide))) addresses last ∧
 last.stack=[w[77]] ∧ last.mem 3=w[2] ∧ last.mem 4=w[3] ∧
 last.mem 1=w[16] ∧ last.mem 2=w[16] ∧ last.mem 6=w[2] ∧ last.mem 8=w[10] ∧
 StructAllocatorRepr caller.heap addresses 16 ⟨22,by decide⟩ last ∧
 BaseExtends caller.H P.base addresses ∧
 (∀ x,16≤x → last.mem x=before.mem x) ∧
 (∀ x,x<10 → x≠3 → x≠4 → x≠6 → x≠8 → last.mem x=before.mem x) ∧
 (∀ j,j<3 → last.mem (10+2*j)=w[16] ∧ last.mem (10+2*j+1)=.val (wmod (3-j))) := by
 obtain ⟨down,addresses,executed,represented,stack,cursor,alias,count,result,owner,extended,outside,payload⟩ := ScalarUnwind.Client.endpoint
 have body : run tailCode ScalarUnwind.Client.entered=.ok down 0 := by
   unfold ScalarUnwind.Client.image at executed
   rw [run_append_ok ScalarUnwind.Client.entry_run] at executed
   exact executed
 have saved : down.mem 6=w[2] := outside 6 (by decide) (by decide) (by decide) (by decide) (.inl (by decide))
 let mid := writeMachine down 3 w[2]
 let last := writeMachine mid 4 w[3]
 have exitRun : run suffix down=.ok last 0 := by
   change (.ok (writeMachine (writeMachine down 3 (down.mem 6)) 4 (down.mem 4)) 0 : Evm.Out)=_
   rw [saved,result]
 have after : StateRepr 1 2 16 ScalarUnwind.Client.F
     ((ScalarUnwind.Client.state 3 (by decide)).setLocal (.there .here) (countValue 2 (by decide))) addresses last :=
   (represented.setVal (.there .here) (countValue 2 (by decide)) w[2] (ReprV.uint_of rfl)).setVal
     .here (countValue 3 (by decide)) w[3] (ReprV.uint_of rfl)
 have initialResult := initial.setVal .here (countValue 3 (by decide)) w[3] (ReprV.uint_of rfl)
 have alias1 : last.mem 1=w[16] := by
   change upd (upd down.mem 3 w[2]) 4 w[3] 1=_
   simpa only [upd,if_neg (by decide : (1:Nat)≠4),if_neg (by decide : (1:Nat)≠3)] using
     outside 1 (by decide) (by decide) (by decide) (by decide) (.inl (by decide))
 have alias2 : last.mem 2=w[16] := (upd_other mid.mem w[3] (by decide : (2:Nat)≠4)).trans
   ((upd_other down.mem w[2] (by decide : (2:Nat)≠3)).trans alias)
 have words : ∀ {t : LTy} (index : Idx Γ t),
     last.mem (cellOf 1 index)=(writeMachine before 4 w[3]).mem (cellOf 1 index) := by
   intro t index
   cases index with
   | here => rfl
   | there index => cases index with
     | here => rfl
     | there index => cases index with
       | here => exact alias2
       | there index => cases index with
         | here => exact alias1
         | there index => cases index
 have framed := CallerReframe.reframe (caller.setLocal .here (countValue 3 (by decide)))
   ((ScalarUnwind.Client.state 3 (by decide)).setLocal (.there .here) (countValue 2 (by decide)))
   (List.prefix_refl _) P.base addresses (writeMachine before 4 w[3]) last initialResult after extended words (by
     intro R index
     cases index with | there index => cases index with | there index => cases index with | there index => cases index with | there index => cases index)
 have owned : StructAllocatorRepr caller.heap addresses 16 ⟨22,by decide⟩ last :=
   (owner.localWrite 3 (by decide) (by decide) w[2]).localWrite 4 (by decide) (by decide) w[3]
 refine ⟨last,addresses,?_,framed,stack,rfl,rfl,alias1,alias2,?_,?_,owned,extended,?_,?_,?_⟩
 · unfold image
   rw [run_append_ok entered,run_append_ok body]
   exact exitRun
 · exact (upd_other mid.mem w[3] (by decide : (6:Nat)≠4)).trans
     ((upd_other down.mem w[2] (by decide : (6:Nat)≠3)).trans saved)
 · exact (upd_other mid.mem w[3] (by decide : (8:Nat)≠4)).trans
     ((upd_other down.mem w[2] (by decide : (8:Nat)≠3)).trans cursor)
 · intro x high
   have old := outside x (by omega) (by omega) (by omega) (by omega) (.inr high)
   have new : last.mem x=ScalarUnwind.Client.before.mem x :=
     (upd_other mid.mem w[3] (by omega)).trans ((upd_other down.mem w[2] (by omega)).trans old)
   exact new.trans (by
     simp only [ScalarUnwind.Client.before,before,CallerReframe.Checks.before,ParentPrefixes.Checks.input,writeMachine,upd,
       if_neg (show x≠3 from by omega),if_neg (show x≠4 from by omega),
       if_neg (show x≠6 from by omega),if_neg (show x≠7 from by omega)])

 · intro x low hc hv hs hp
   by_cases hr : x=2
   · subst x;exact alias2
   have old := outside x hp hr hc hv (.inl low)
   have new : last.mem x=ScalarUnwind.Client.before.mem x :=
     (upd_other mid.mem w[3] hv).trans ((upd_other down.mem w[2] hc).trans old)
   exact new.trans (by
     by_cases h7 : x=7
     · subst x;rfl
     simp only [ScalarUnwind.Client.before,before,CallerReframe.Checks.before,ParentPrefixes.Checks.input,writeMachine,upd,
       if_neg hc,if_neg hv,if_neg hs,if_neg h7])
 · intro j small
   exact ⟨(upd_other mid.mem w[3] (by omega)).trans
      ((upd_other down.mem w[2] (by omega)).trans (payload j small).1),
     (upd_other mid.mem w[3] (by omega)).trans
      ((upd_other down.mem w[2] (by omega)).trans (payload j small).2)⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarCallerReturn
