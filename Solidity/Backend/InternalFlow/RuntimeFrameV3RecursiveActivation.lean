import Solidity.Backend.InternalFlow.RuntimeFrameV3RecursiveSource
import Solidity.Backend.InternalFlow.RuntimeFrameCallAgreement

/-! Actual recursive parameter entry from reached caller representation.
Only existing StateRepr, Args/CallRet and checked capture/value instructions are
used. This is one activation bridge, not a recursive target compiler. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveActivation
open Evm Evm.Memory
open RecursiveSource

theorem parameter_projection {C : Contract} {R : RefTy} {tail : Ctx} {L b frame : Nat}
 {F : Frag (Parameters R ++ tail)} {σ : State C (Parameters R ++ tail)}
 {base : Nat → Fin W} {m : Machine} (repr : StateRepr L b frame F σ base m) :
 StateRepr L (b+tail.length) frame (Frag.init (Parameters R))
 (σ.withEnv (TEnv.take (Parameters R) σ.env)) base m := by
 have scalarAddress : lvl (b+tail.length) (.here : Idx (Parameters R) (.val .uint))=
     lvl b (.here : Idx (Parameters R ++ tail) (.val .uint)) := by
   change (b+tail.length)+1=b+(tail.length+1)
   omega
 have pointerAddress : cellOf (b+tail.length) (.there .here : Idx (Parameters R) (.mem R))=
     cellOf b (.there .here : Idx (Parameters R ++ tail) (.mem R)) := by
   change b+tail.length=b+((tail.length+1+1)-1-1)
   omega
 refine ⟨⟨repr.core.store,?_,?_,repr.core.net,repr.core.netSelf,repr.core.bound,?_,
   repr.core.env,repr.core.funds,repr.core.oracle⟩,repr.heap,?_,?_,repr.structs,repr.separated,repr.refs⟩
 · intro p index
   cases index with
   | here =>
     change ReprV .uint σ.env.1 (m.memAt (lvl (b+tail.length) (.here : Idx (Parameters R) (.val .uint))))
     rw [scalarAddress]
     exact repr.core.vals (.here : Idx (Parameters R ++ tail) (.val .uint))
   | there i => cases i with | there i => cases i
 · intro R index flag
   cases index with | there i => cases i with | there i => cases i
 · intro R index flag
   cases index with | there i => cases i with | there i => cases i
 · intro R index
   cases index with
   | there i => cases i with
     | here =>
       obtain ⟨ref,value,word⟩ := repr.pointers (.there .here : Idx (Parameters R ++ tail) (.mem R))
       refine ⟨ref,value,?_⟩
       rw [pointerAddress]
       exact word
     | there i => cases i
 · have room := repr.locals
   change b+((Parameters R)++tail).length≤frame at room
   simp only [Parameters,List.length_append,List.length_cons,List.length_nil] at room ⊢
   omega

def decrement {C : Contract} {R : RefTy} : Val C (Parameters R) .uint :=
 .binop .sub rfl rfl (.simple (.local .here)) (.simple (.lit 1 rfl))

def compiled (b : Nat) {C : Contract} {R : RefTy} (F : Frag (Parameters R)) :
 CompiledVal b F (decrement (C:=C) (R:=R)) :=
 ⟨_,.binary .sub rfl rfl _ _ _ _ (.core _ rfl) (.core _ rfl)⟩

theorem public_selection (b : Nat) {C : Contract} {R : RefTy} (F : Frag (Parameters R)) :
 compileVal b F (decrement (C:=C) (R:=R))=some (compiled b F) := rfl

def selected (b : Nat) {C : Contract} {R : RefTy} (F : Frag (Parameters R)) :
 Composition.Program (C:=C) b F (.cons (.assignLocal .here decrement) .nil) :=
 Composition.cons (Composition.assign F .here decrement (compiled b F)) (Composition.nil b F)

theorem selected_need (b : Nat) {C : Contract} {R : RefTy} (F : Frag (Parameters R)) :
 (selected (C:=C) b F).checked.need=2 := rfl
theorem selected_cost (b : Nat) {C : Contract} {R : RefTy} (F : Frag (Parameters R)) (σ : State C (Parameters R)) :
 (selected b F).checked.cost σ=0 := rfl
theorem selected_frag (b : Nat) {C : Contract} {R : RefTy} (F : Frag (Parameters R)) :
 (selected (C:=C) b F).checked.frag=F := rfl

theorem decrement_eval {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (σ : State C (Parameters R)) (n : Nat) (bound : n+1<W) (ref : HRef σ.H R)
 (counter : TEnv.get (.here : Idx (Parameters R) (.val .uint)) σ.env=countValue (n+1) bound)
 (alias : TEnv.get (.there .here : Idx (Parameters R) (.mem R)) σ.env=some ref) :
 (decrement (C:=C) (R:=R)).evalT σ=.ok (countValue n (by omega)) := by
 have evaluated := next_eval hm σ n bound ref counter alias
 change (do
   let args ← (Args.snocMemory Args.nil R (.user "alias") (.var (.there .here) hm)).evalT σ
   let value ← (decrement (C:=C) (R:=R)).evalT σ
   pure (value,args)) = _ at evaluated
 simp only [Args.evalT,MPath.mvalT,alias,ok_bind] at evaluated
 cases actual : (decrement (C:=C) (R:=R)).evalT σ with
 | error halt => simp only [actual,error_bind] at evaluated;cases evaluated
 | ok v =>
   simp only [actual,ok_bind] at evaluated
   exact congrArg Except.ok (congrArg Prod.fst (Except.ok.inj evaluated))

/-- The compiled local update is EXACTLY the next native call's entered
parameter state, not an unrelated supplied intermediate representation. -/
theorem source_activation {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (σ : State C (Parameters R)) (n : Nat) (bound : n+1<W) (ref : HRef σ.H R)
 (counter : TEnv.get (.here : Idx (Parameters R) (.val .uint)) σ.env=countValue (n+1) bound)
 (alias : TEnv.get (.there .here : Idx (Parameters R) (.mem R)) σ.env=some ref) :
 let child : State C (Parameters R) := σ.withEnv (countValue n (by omega),(some ref,()))
 (nextArgs R hm).evalT σ=.ok child.env ∧
 (.cons (.assignLocal .here decrement) .nil : Prog C (Parameters R) (Parameters R)).run σ=
 .ok ⟨child,List.prefix_refl _⟩ := by
 have evaluated := next_eval hm σ n bound ref counter alias
 have value := decrement_eval hm σ n bound ref counter alias
 have tail : σ.env.2=(some ref,()) := Prod.ext alias (by cases σ.env.2.2;rfl)
 refine ⟨evaluated,?_⟩
 change TRun.seq (TRun.assignLocal .here decrement) TRun.nil σ = _
 simp only [TRun.seq,TRun.assignLocal,value,ok_bind,TRun.nil,Except.map]
 change Except.ok (⟨{σ with env := (countValue n (by omega),σ.env.2)},List.prefix_refl _⟩ : Solidity.Out C σ.H (Parameters R))=_
 rw [tail]
 rfl

def activationCode {C : Contract} {R : RefTy} (b : Nat) (F : Frag (Parameters R)) (pointer : Nat) : List Instr :=
 Restore.saveCells pointer (Restore.contextCells b (Parameters R)) ++ (selected (C:=C) b F).checked.code

/-- Real capture followed by the actual checked decrement implements ONE
native recursive activation. Arguments, entered child representation, frame
payload and allocator transport are derived, not supplied as a simulation. -/
theorem activation {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Parameters R)}
 (hm : (Ty.ref R).mapFree=true) (σ : State C (Parameters R))
 (n : Nat) (bound : n+1<W) (ref : HRef σ.H R)
 (counter : TEnv.get (.here : Idx (Parameters R) (.val .uint)) σ.env=countValue (n+1) bound)
 (alias : TEnv.get (.there .here : Idx (Parameters R) (.mem R)) σ.env=some ref)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F σ base before)
 (lo pointer start : Nat) (localBound : b+2≤lo) (pointerAbove : lo≤pointer)
 (pointerBelow : pointer<frame) (payloadAbove : lo≤start) (payloadBelow : start+2≤frame)
 (separate : pointer<start ∨ start+2≤pointer) (fits : start+2<W)
 (current : before.mem pointer=.val (wmod start)) :
 let child : State C (Parameters R) := σ.withEnv (countValue n (by omega),(some ref,()))
 ∃ saved after addresses,
 (nextArgs R hm).evalT σ=.ok child.env ∧
 ((CallRet.none : CallRet (Parameters R) [] (Parameters R)).enterT (σ.withEnv child.env)).st=child ∧
 run (Restore.saveCells pointer (Restore.contextCells b (Parameters R))) before=.ok saved 0 ∧
 run (selected (C:=C) b F).checked.code saved=.ok after 0 ∧
 run (activationCode (C:=C) b F pointer) before=.ok after 0 ∧
 StateRepr L b frame F child addresses after ∧ after.stack=before.stack ∧
 BaseExtends σ.H base addresses ∧
 GrowsAllocator b frame 0 σ base before child addresses after ∧
 after.mem pointer=.val (wmod (start+2)) ∧
 (∀ i, i<2 → after.mem (start+i)=before.mem (b+i)) := by
 let child : State C (Parameters R) := σ.withEnv (countValue n (by omega),(some ref,()))
 have source := source_activation hm σ n bound ref counter alias
 obtain ⟨saved,captureRun,captured,captureRepr,captureGrowth⟩ :=
   Context.capture_context before lo pointer start repr localBound pointerAbove pointerBelow
     payloadAbove payloadBelow separate fits current
 have input : AllocationInput b frame ((selected b F).checked.cost σ) σ base saved :=
   .inl (selected_cost b F σ)
 obtain ⟨after,addresses,bodyRun,bodyRepr,stack,extended,growth,words⟩ :=
   Composition.endpoint (selected b F) captureRepr (by simpa only [selected_need] using localBound)
     (by omega) input (⟨child,List.prefix_refl _⟩ : Solidity.Out C σ.H (Parameters R)) source.2
 have count : (Restore.contextCells b (Parameters R)).length=2 := by
   simp only [Restore.contextCells,List.length_map,List.length_range,Parameters,List.length_cons,List.length_nil]
 have cursor : after.mem pointer=.val (wmod (start+2)) := by
   rw [words pointer pointerAbove pointerBelow,captured.cursor,count]
 have payload : ∀ i, i<2 → after.mem (start+i)=before.mem (b+i) := by
   intro i small
   rw [words (start+i) (by omega) (by omega)]
   have old := captured.payload i (by simpa only [count] using small)
   simpa only [Restore.contextCells,List.getElem_map,List.getElem_range] using old
 refine ⟨saved,after,addresses,source.1,rfl,captureRun,bodyRun,?_,?_,
   stack.trans captured.stack,extended,?_,cursor,payload⟩
 · exact Evm.run_append_ok captureRun |>.trans bodyRun
 · simpa only [selected_frag] using bodyRepr
 · have combined := captureGrowth.comp growth
   simpa only [selected_cost,Nat.zero_add] using combined

/-- Exact machine result of the public value compiler and checked local
store. Expression evaluation itself preserves EVERY machine field; only the
actual counter destination is written by the store. -/
theorem decrement_run {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Parameters R)}
 (hm : (Ty.ref R).mapFree=true) (σ : State C (Parameters R))
 (n : Nat) (bound : n+1<W) (ref : HRef σ.H R)
 (counter : TEnv.get (.here : Idx (Parameters R) (.val .uint)) σ.env=countValue (n+1) bound)
 (alias : TEnv.get (.there .here : Idx (Parameters R) (.mem R)) σ.env=some ref)
 (base : Nat → Fin W) (m : Machine) (repr : StateRepr L b frame F σ base m) :
 run (selected (C:=C) b F).checked.code m=
 .ok (writeMachine m (cellOf b (.here : Idx (Parameters R) (.val .uint))) (.val ⟨n,by omega⟩)) 0 := by
 have source := decrement_eval hm σ n bound ref counter alias
 rcases (compiled b F).cert.correct repr with ⟨v,w,evaluated,represented,actual⟩ | ⟨evaluated,actual⟩
 · have same : v=countValue n (by omega) := Except.ok.inj (evaluated.symm.trans source)
   subst v
   have word : w=.val ⟨n,by omega⟩ := Restore.uint_unique represented (ReprV.uint_of rfl)
   rw [word] at actual
   change run (((compiled b F).code ++ [.mstore (cellOf b (.here : Idx (Parameters R) (.val .uint)))]) ++ []) m = _
   rw [List.append_nil,Evm.run_append_ok actual]
   rfl
 · rw [source] at evaluated
   cases evaluated

def guardCompiled (b : Nat) {C : Contract} {R : RefTy} (F : Frag (Parameters R)) :
 CompiledVal b F (nonzero (C:=C) (R:=R)) :=
 ⟨_,.binary .gt rfl rfl _ _ _ _ (.core _ rfl) (.core _ rfl)⟩

theorem public_guard_selection (b : Nat) {C : Contract} {R : RefTy} (F : Frag (Parameters R)) :
 compileVal b F (nonzero (C:=C) (R:=R))=some (guardCompiled b F) := rfl

def descentCode {C : Contract} {R : RefTy} (b : Nat) (F : Frag (Parameters R)) (pointer : Nat) : List Instr :=
 [.loop (guardCompiled (C:=C) b F).code (activationCode (C:=C) b F pointer)]

/-- The actual public guard code reads the SAME represented counter as the
native recursive branch and leaves every field unchanged below its Boolean. -/
theorem guard_run {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Parameters R)}
 (σ : State C (Parameters R)) (n : Nat) (bound : n<W)
 (counter : TEnv.get (.here : Idx (Parameters R) (.val .uint)) σ.env=countValue n bound)
 (base : Nat → Fin W) (m : Machine) (repr : StateRepr L b frame F σ base m) :
 run (guardCompiled (C:=C) b F).code m=
 .ok (m.push (.val (bword (decide (0<n))))) 0 := by
 have source := guard_eval σ n (congrArg (fun v : PrimTy.uint.Denote => v.val) counter)
 rcases (guardCompiled b F).cert.correct repr with ⟨v,w,evaluated,represented,actual⟩ | ⟨evaluated,actual⟩
 · have same : v=decide (0<n) := Except.ok.inj (evaluated.symm.trans source)
   subst v
   change w=.val (bword (decide (0<n))) at represented
   simpa only [represented] using actual
 · rw [source] at evaluated
   cases evaluated

/-- Opaque composition boundary for the existing loop turn. The condition
is DERIVED from the same represented source counter; the body premise is an
actual run of the fixed activation code, supplied by activation above. -/
theorem positive_turn {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Parameters R)}
 (σ : State C (Parameters R)) (n : Nat) (bound : n+1<W)
 (counter : TEnv.get (.here : Idx (Parameters R) (.val .uint)) σ.env=countValue (n+1) bound)
 (base : Nat → Fin W) (m next : Machine) (repr : StateRepr L b frame F σ base m)
 (pointer : Nat) (executed : run (activationCode (C:=C) b F pointer) m=.ok next 0) :
 loopTurn (run (guardCompiled (C:=C) b F).code) (run (activationCode (C:=C) b F pointer)) m=.inl next := by
 have guard := guard_run σ (n+1) bound counter base m repr
 have positive : decide (0<n+1)=true := decide_eq_true (by omega)
 simp only [loopTurn,guard,positive,Machine.push,bword,if_true,Nat.one_ne_zero,if_false,executed]

/-- False guard skips activation even when its decrement leaf would revert. -/
theorem zero_turn {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Parameters R)}
 (σ : State C (Parameters R))
 (counter : TEnv.get (.here : Idx (Parameters R) (.val .uint)) σ.env=countValue 0 W_pos)
 (base : Nat → Fin W) (m : Machine) (repr : StateRepr L b frame F σ base m) (pointer : Nat) :
 loopTurn (run (guardCompiled (C:=C) b F).code) (run (activationCode (C:=C) b F pointer)) m=.inr (.ok m 0) := by
 have guard := guard_run σ 0 W_pos counter base m repr
 simp only [loopTurn,guard,show decide (0<(0:Nat))=false from rfl,Machine.push,bword,Bool.false_eq_true,if_false,if_true]

theorem decrement_failure {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Parameters R)}
 (σ : State C (Parameters R)) (base : Nat → Fin W) (m : Machine)
 (repr : StateRepr L b frame F σ base m) (source : (decrement (C:=C) (R:=R)).evalT σ=.error .revert) :
 run (selected (C:=C) b F).checked.code m=.revert := by
 rcases (compiled b F).cert.correct repr with ⟨v,w,evaluated,represented,actual⟩ | ⟨evaluated,actual⟩
 · rw [source] at evaluated
   cases evaluated
 · change run (((compiled b F).code ++ [.mstore (cellOf b (.here : Idx (Parameters R) (.val .uint)))]) ++ []) m = _
   rw [List.append_nil,Evm.run_append_revert actual]

end Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveActivation
