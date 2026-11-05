import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarRecursiveSource
import Solidity.Backend.InternalFlow.RuntimeFrameContext

/-! Actual scalar child entry after scoped allocation. This consumes the
reached representation and allocator, captures the full parent context, and
executes the public value compiler. No recursive body compiler is asserted. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarEntry
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

def decrement {C : Contract} {R : RefTy} : Val C (Frame R) .uint :=
 .binop .sub rfl rfl (.simple (.local (.there .here))) (.simple (.lit 1 rfl))
def compiled {C : Contract} {R : RefTy} (b : Nat) (F : Frag (Frame R)) :
 CompiledVal b F (decrement (C:=C) (R:=R)) :=
 ⟨_,.binary .sub rfl rfl _ _ _ _ (.core _ rfl) (.core _ rfl)⟩
theorem public_selection {C : Contract} {R : RefTy} (b : Nat) (F : Frag (Frame R)) :
 Memory.compileVal b F decrement=some (compiled (C:=C) b F) := by rfl

def childMachine {R : RefTy} (b : Nat) (m : Machine) (n : Nat) (fit : n<W) :=
 writeMachine (writeMachine m (cellOf b (.there .here : Idx (Frame R) (.val .uint))) (.val ⟨n,fit⟩))
  (cellOf b (.here : Idx (Frame R) (.val .uint))) w[0]
def code {C : Contract} {R : RefTy} (b : Nat) (F : Frag (Frame R)) : List Instr :=
 (compiled (C:=C) b F).code ++ [.mstore (cellOf b (.there .here : Idx (Frame R) (.val .uint))),
 .push w[0],.mstore (cellOf b (.here : Idx (Frame R) (.val .uint)))]

theorem entry_state {C : Contract} {R : RefTy} (σ : State C (Frame R)) (n : Nat) (fit : n<W)
 (ref : HRef σ.H R) (alias : TEnv.get (.there (.there .here) : Idx (Frame R) (.mem R)) σ.env=some ref) :
 (σ.setLocal (.there .here) (countValue n fit)).setLocal .here (PrimTy.dflt .uint)=entered σ n fit ref := by
 have tail : σ.env.2.2=(some ref,()) := Prod.ext alias (by cases σ.env.2.2.2;rfl)
 change σ.withEnv (Δ:=Frame R) (PrimTy.dflt .uint,(countValue n fit,σ.env.2.2))=_
 rw [tail]
 rfl

theorem decrement_eval {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (σ : State C (Frame R)) (n : Nat) (fit : n+1<W) (ref : HRef σ.H R)
 (counter : TEnv.get (.there .here : Idx (Frame R) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame R) (.mem R)) σ.env=some ref) :
 decrement.evalT σ=.ok (countValue n (by omega)) := by
 have evaluated := ScalarRecursiveSource.next_eval hm σ n fit ref counter alias
 change (do
   let args ← (Args.snocMemory Args.nil R (.user "alias") (.var (.there (.there .here)) hm)).evalT σ
   let value ← decrement.evalT σ
   pure (value,args))=_ at evaluated
 simp only [Args.evalT,MPath.mvalT,alias,ok_bind] at evaluated
 cases actual : decrement.evalT σ with
 | error halt => simp only [actual,error_bind] at evaluated;cases evaluated
 | ok v =>
   simp only [actual,ok_bind] at evaluated
   exact congrArg Except.ok (congrArg Prod.fst (Except.ok.inj evaluated))

theorem entry {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Frame R)}
 (hm : (Ty.ref R).mapFree=true) (σ : State C (Frame R)) (n : Nat) (fit : n+1<W)
 (ref : HRef σ.H R)
 (counter : TEnv.get (.there .here : Idx (Frame R) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame R) (.mem R)) σ.env=some ref)
 (base : Nat → Fin W) (m : Machine) (repr : StateRepr L b frame F σ base m) :
 run (code (C:=C) b F) m=.ok (childMachine (R:=R) b m n (by omega)) 0 ∧
 StateRepr L b frame F (entered σ n (by omega) ref) base (childMachine (R:=R) b m n (by omega)) ∧
 (next R hm).evalT σ=.ok (countValue n (by omega),(some ref,())) ∧
 ((result R).enterT (σ.withEnv (Δ:=Parameters R) (countValue n (by omega),(some ref,())))).st=entered σ n (by omega) ref := by
 have source := decrement_eval hm σ n fit ref counter alias
 have executed : run (compiled (C:=C) b F).code m=.ok (m.push (.val ⟨n,by omega⟩)) 0 := by
   rcases (compiled (C:=C) b F).cert.correct repr with ⟨v,w,evaluated,represented,actual⟩ | ⟨evaluated,actual⟩
   · have same : v=countValue n (by omega) := Except.ok.inj (evaluated.symm.trans source)
     subst v
     have word : w=.val ⟨n,by omega⟩ := Restore.uint_unique represented (ReprV.uint_of rfl)
     rw [word] at actual
     exact actual
   · rw [source] at evaluated
     cases evaluated
 have represented := (repr.setVal (.there .here) (countValue n (by omega)) (.val ⟨n,by omega⟩)
   (ReprV.uint_of rfl)).setVal .here (PrimTy.dflt .uint) w[0] (ReprV.dflt_zero .uint)
 rw [entry_state σ n (by omega) ref alias] at represented
 refine ⟨?_,represented,ScalarRecursiveSource.next_eval hm σ n fit ref counter alias,rfl⟩
 change run ((compiled (C:=C) b F).code ++ _) m=_
 rw [run_append_ok executed]
 rfl

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarEntry

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarEntry.public_selection' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarEntry.public_selection

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarEntry.entry_state' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarEntry.entry_state

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarEntry.decrement_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarEntry.decrement_eval

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarEntry.entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarEntry.entry
