import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarParentRestore

/-! Checked scalar-result propagation after actual paired parent restoration.
Uses the published expression compiler, and writes only the live result cell.
No arbitrary recursive compiler selector or profile witness is supplied. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarUnwind
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

def rhs {C : Contract} {R : RefTy} : Val C (Frame R) .uint :=
 .binop .add rfl rfl (.simple (.local .here)) (.simple (.lit 1 rfl))
def value {C : Contract} {R : RefTy} (b : Nat) (F : Frag (Frame R)) :=
 (Memory.compileVal (C:=C) b F (rhs (R:=R))).get (by rfl)
def advanceCode {C : Contract} {R : RefTy} (b : Nat) (F : Frag (Frame R)) :=
 (value (C:=C) b F).code ++ [.mstore (b+2)]

theorem selected {C : Contract} {R : RefTy} (b : Nat) (F : Frag (Frame R)) :
 Memory.compileVal (C:=C) b F (rhs (R:=R))=some (value b F) := by rfl

theorem advance {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Frame R)}
 (σ : State C (Frame R)) (base : Nat → Fin W) (after : Machine)
 (repr : StateRepr L b frame F σ base after) (n : Nat) (bound : n+1<W)
 (result : TEnv.get (.here : Idx (Frame R) (.val .uint)) σ.env=countValue n (by omega)) :
 run (advanceCode (C:=C) b F) after=.ok (writeMachine after (b+2) (.val (wmod (n+1)))) 0 ∧
 StateRepr L b frame F (finished σ (n+1) bound) base
   (writeMachine after (b+2) (.val (wmod (n+1)))) := by
 have numeric : (TEnv.get (.here : Idx (Frame R) (.val .uint)) σ.env).val=(n:Int) :=
   congrArg (fun x : PrimTy.uint.Denote => x.val) result
 have eval : rhs.evalT σ=.ok (countValue (n+1) bound) := by
   change TRes.ofOpt (PrimTy.ofInt? .uint ((TEnv.get (.here : Idx (Frame R) (.val .uint)) σ.env).val+1))=_
   rw [numeric,successor_ofInt n bound]
   rfl
 have actual := (value (C:=C) b F).cert.correct repr
 rcases actual with ⟨v,w,source,word,executed⟩ | ⟨source,executed⟩
 · have same : v=countValue (n+1) bound := Except.ok.inj (source.symm.trans eval)
   subst v
   have encoded : ReprV .uint (countValue (n+1) bound) (.val (wmod (n+1))) := by
     have exactWord : wmod (n+1)=(⟨n+1,bound⟩ : Fin W) := Fin.ext (Nat.mod_eq_of_lt bound)
     rw [exactWord]
     exact ReprV.uint_of rfl
   have unique : w=.val (wmod (n+1)) := Restored.value_unique word encoded
   subst w
   refine ⟨?_,?_⟩
   · unfold advanceCode
     rw [run_append_ok executed]
     rfl
   · exact repr.setVal .here _ _ encoded
 · rw [eval] at source
   cases source

def code {C : Contract} {R : RefTy} (b pointer : Nat) (F : Frag (Frame R)) :=
 Restore.restoreCells pointer (Restore.contextCells b (Parameters R)) ++ advanceCode (C:=C) b F

/-- One actual parent return, with the child scalar kept live through restore
and consumed by the checked addition. The source states are typed updates,
not whole-loop preservation assumptions. -/
theorem step {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Frame R)}
 (σ : State C (Frame R)) (base : Nat → Fin W) (after : Machine)
 (repr : StateRepr L b frame F σ base after)
 (n : Nat) (bound : n+1<W)
 (result : TEnv.get (.here : Idx (Frame R) (.val .uint)) σ.env=countValue n (by omega))
 (lo pointer start : Nat)
 (locals : b+3≤lo) (above : lo≤pointer) (below : pointer<frame)
 (payload : lo≤start) (separate : pointer<start) (fits : start+2<W)
 (current : after.mem pointer=.val (wmod (start+2)))
 (reference : after.mem start=after.mem b)
 (counter : after.mem (start+1)=.val (wmod (n+1))) :
 ∃ last,
 run (code (C:=C) b pointer F) after=.ok last 0 ∧
 StateRepr L b frame F (finished (σ.setLocal (.there .here) (countValue (n+1) bound)) (n+1) bound) base last ∧
 last.stack=after.stack ∧ last.mem pointer=.val (wmod start) ∧
 last.mem b=after.mem b ∧ last.mem (b+1)=.val (wmod (n+1)) ∧
 last.mem (b+2)=.val (wmod (n+1)) ∧
 GrowsAllocator b frame 0 σ base after
   (finished (σ.setLocal (.there .here) (countValue (n+1) bound)) (n+1) bound) base last ∧
 (∀ x, x≠pointer → x≠b → x≠b+1 → x≠b+2 → last.mem x=after.mem x) := by
 obtain ⟨mid,executed,represented,stack,cursor,alias,count,live,growth,outside⟩ :=
   ScalarParentRestore.restore σ base after repr (n+1) bound lo pointer start locals above below payload separate fits current reference counter
 have advanced := advance (σ.setLocal (.there .here) (countValue (n+1) bound)) base mid represented n bound result
 let last := writeMachine mid (b+2) (.val (wmod (n+1)))
 have unchanged : ∀ x, x≠b+2 → last.mem x=mid.mem x := fun x different => upd_other _ _ different
 refine ⟨last,?_,advanced.2,stack,?_,?_,?_,?_,?_,?_⟩
 · unfold code
   rw [run_append_ok executed]
   exact advanced.1
 · exact (unchanged pointer (by omega)).trans cursor
 · exact (unchanged b (by omega)).trans alias
 · exact (unchanged (b+1) (by omega)).trans count
 · exact upd_same _ _ _
 · intro allocation positive initial space
   have owned := growth allocation positive initial space
   simpa only [Nat.add_zero] using owned.localWrite (b+2) (by omega) (by have h:=repr.locals;change b+3≤frame at h;omega) (.val (wmod (n+1)))
 · intro x hp hr hc hv
   exact (unchanged x hv).trans (outside x hp hr hc)

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarUnwind

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ScalarUnwind.rhs' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarUnwind.rhs

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ScalarUnwind.value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarUnwind.value

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ScalarUnwind.advanceCode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarUnwind.advanceCode

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ScalarUnwind.selected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarUnwind.selected

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ScalarUnwind.advance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarUnwind.advance

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ScalarUnwind.code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarUnwind.code

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ScalarUnwind.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarUnwind.step
