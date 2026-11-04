import Solidity.Backend.MemoryOps.SourceRhsAssignment

/-! Result-producing adapter for the supported actual memory-writing RHS.
A final existing local read is justified by the reached state, not an assumed
expression result or a replacement compiler. General emission selection is open. -/
namespace Solidity.Backend.MemoryOps

/-- Ordinary composition of the TWO existing writes and existing scalar read.
This is a certified concrete adapter, not a general Source expression compiler. -/
def rhsAssignValueCode {C : Contract} {Δ : Ctx} (b : Nat)
    (root : Idx Δ (.mem (.array (.prim .bool)))) (outer inner : Idx Δ (.val .uint))
    (rhs : Idx Δ (.val .bool)) : List Evm.Instr :=
  (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local inner)) (.simple (.local rhs)) ++
    Evm.Memory.writeLocalCode (C := C) b root (.simple (.local outer)) (.simple (.local rhs))) ++
      Evm.compileVal b (.simple (.local rhs) : Val C Δ .bool)

/-- Derive the emitted Bool result from the actual reached heap/state/local,
retaining both write executions, source result, heap observers and stack tail. -/
theorem rhs_assign_value_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (fuel : Nat) (σ : State C Δ) (r : HRef σ.H (.array (.prim .bool)))
    (hr : SourceBoolMemoryAt y address σ.heap r .dyn)
    (sroot : Source.Idx Γ (.array .memory .bool none)) (outer inner : Source.Idx Γ (.int .u256))
    (srhs : Source.Idx Γ .bool) (root : Idx Δ (.mem (.array (.prim .bool))))
    (oi ii : Idx Δ (.val .uint)) (rhs : Idx Δ (.val .bool)) (k l : PrimTy.uint.Denote) (v : Bool)
    (hsroot : y.1.get sroot=.memRef rfl address) (houter : y.1.get outer=sourceUint k)
    (hinner : y.1.get inner=sourceUint l) (hvalue : y.1.get srhs=.bool v)
    (htroot : TEnv.get root σ.env=some r) (hto : TEnv.get oi σ.env=k)
    (hti : TEnv.get ii σ.env=l) (htv : TEnv.get rhs σ.env=v)
    (inside : l.1.toNat<σ.heap.len r .dyn) (outerInside : k.1.toNat<σ.heap.len r .dyn)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) (SH : Source.HeapTy) (memOK : Source.MemOK E SH y) :
    ∃ (mid out : Heap σ.H) (ym z : Source.EMState E Γ) (mm target : Evm.Machine),
      σ.heap.writeAddr (.index r .dyn l) v=some mid ∧ mid.writeAddr (.index r .dyn k) v=some out ∧
      (Source.evalE G Fsrc (fuel+3) (sourceIndexedAssign sroot inner srhs)).run y=(.ok (.val (.bool v)),ym) ∧
      (Source.evalE G Fsrc (fuel+4) (sourceRhsAssign sroot outer inner srhs)).run y=(.ok (.val (.bool v)),z) ∧
      Prog.run σ (.cons (.assignMem (.index .dyn (.var root rfl) (.simple (.local ii))) (.val (.simple (.local rhs))))
        (.cons (.assignMem (.index .dyn (.var root rfl) (.simple (.local oi))) (.val (.simple (.local rhs)))) .nil))=
          .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      (Val.simple (.local rhs) : Val C Δ .bool).evalT (σ.withHeap out)=.ok v ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local ii)) (.simple (.local rhs))) m=.ok mm 0 ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local oi)) (.simple (.local rhs))) mm=.ok target 0 ∧
      Evm.run (Evm.compileVal b (.simple (.local rhs) : Val C Δ .bool)) target=
        .ok (target.push (.val (Evm.bword v))) 0 ∧
      Evm.run (rhsAssignValueCode (C := C) b root oi ii rhs) m=.ok (target.push (.val (Evm.bword v))) 0 ∧
      SourceBoolMemoryAt ym address mid r .dyn ∧ SourceBoolMemoryAt z address out r .dyn ∧
      Source.MemOK E SH z ∧ Evm.Memory.StateRepr L b frame F (σ.withHeap out) base (target.push (.val (Evm.bword v))) ∧
      z.1=y.1 ∧ MObj.elems .dyn (out.get r)=((MObj.elems .dyn (σ.heap.get r)).set l.1.toNat v).set k.1.toNat v ∧
      (∀ {Q : RefTy} (q : HRef σ.H Q),r.id≠q.id → out.get q=σ.heap.get q) ∧
      (∀ a,a≠address → z.2.heap.get a=y.2.heap.get a) ∧ z.2.heap.next=y.2.heap.next ∧
      (z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals) ∧
      (target.push (.val (Evm.bword v))).stack=.val (Evm.bword v)::m.stack ∧
      (target.push (.val (Evm.bword v))).mem=target.mem ∧
      Evm.ReprV .bool v (.val (Evm.bword v)) ∧
      Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out) (target.push (.val (Evm.bword v))) := by
  first
  | solve | rfl | simp only [] | omega
  | obtain ⟨mid,out,ym,z,mm,target,hw₁,hw₂,innerRun,expr,stmt,native,word₁,word₂,word,hr₁,hr₂,mok₁,mok₂,hm₁,hm₂,
      locals₁,locals₂,elems,other,addrs,next,effects,stack,alloc⟩ :=
      rhs_assign_success_word G Fsrc fuel σ r hr sroot outer inner srhs root oi ii rhs k l v
        hsroot houter hinner hvalue htroot hto hti htv inside outerInside hm SH memOK
    have aligned : TEnv.get rhs (σ.withHeap out).env=v := htv
    obtain ⟨w,rep,read⟩ := Evm.simple_sim hm₂.core (.local rhs) rfl
    change Evm.ReprV .bool (TEnv.get rhs (σ.withHeap out).env) w at rep
    rw [aligned] at rep
    rw [rep.bool_inv] at read
    have reload : Evm.run (Evm.compileVal b (.simple (.local rhs) : Val C Δ .bool)) target=
        .ok (target.push (.val (Evm.bword v))) 0 := read
    refine ⟨mid,out,ym,z,mm,target,hw₁,hw₂,innerRun,expr,native,?_,word₁,word₂,reload,?_,hr₁,hr₂,mok₂,
      hm₂.push _,locals₂,elems,other,addrs,next,effects,?_,rfl,rfl,?_⟩
    · simp only [Val.evalT,Simple.evalT,aligned]
    · rw [rhsAssignValueCode,Evm.run_append_ok word];exact reload
    · change .val (Evm.bword v)::target.stack=.val (Evm.bword v)::m.stack
      rw [stack]
    · intro cursor hb ha;exact (alloc cursor hb ha).stack _

/-- A real late lvalue rejection stops before the emitted result reload.
Only the successful RHS prefix is observed; no post-revert machine is invented. -/
theorem rhs_assign_value_bounds_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (fuel : Nat) (σ : State C Δ) (r : HRef σ.H (.array (.prim .bool)))
    (hr : SourceBoolMemoryAt y address σ.heap r .dyn)
    (sroot : Source.Idx Γ (.array .memory .bool none)) (outer inner : Source.Idx Γ (.int .u256))
    (srhs : Source.Idx Γ .bool) (root : Idx Δ (.mem (.array (.prim .bool))))
    (oi ii : Idx Δ (.val .uint)) (rhs : Idx Δ (.val .bool)) (k l : PrimTy.uint.Denote) (v : Bool)
    (hsroot : y.1.get sroot=.memRef rfl address) (houter : y.1.get outer=sourceUint k)
    (hinner : y.1.get inner=sourceUint l) (hvalue : y.1.get srhs=.bool v)
    (htroot : TEnv.get root σ.env=some r) (hto : TEnv.get oi σ.env=k)
    (hti : TEnv.get ii σ.env=l) (htv : TEnv.get rhs σ.env=v)
    (inside : l.1.toNat<σ.heap.len r .dyn) (outside : σ.heap.len r .dyn≤k.1.toNat)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) (SH : Source.HeapTy) (memOK : Source.MemOK E SH y) :
    ∃ (mid : Heap σ.H) (ym : Source.EMState E Γ) (mm : Evm.Machine),
      σ.heap.writeAddr (.index r .dyn l) v=some mid ∧
      (Source.evalE G Fsrc (fuel+3) (sourceIndexedAssign sroot inner srhs)).run y=(.ok (.val (.bool v)),ym) ∧
      (Source.evalE G Fsrc (fuel+4) (sourceRhsAssign sroot outer inner srhs)).run y=
        (.error (.revert (Source.panicData .index)),ym) ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local ii)) (.simple (.local rhs))) m=.ok mm 0 ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local oi)) (.simple (.local rhs))) mm=.revert ∧
      Evm.run (rhsAssignValueCode (C := C) b root oi ii rhs) m=.revert ∧
      (∀ suffix,Evm.run (rhsAssignValueCode (C := C) b root oi ii rhs ++ suffix) m=.revert) ∧
      SourceBoolMemoryAt ym address mid r .dyn ∧ Source.MemOK E SH ym ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap mid) base mm ∧ ym.1=y.1 ∧
      MObj.elems .dyn (mid.get r)=(MObj.elems .dyn (σ.heap.get r)).set l.1.toNat v ∧
      (∀ a,a≠address → ym.2.heap.get a=y.2.heap.get a) ∧ ym.2.heap.next=y.2.heap.next ∧
      (ym.2.ex=y.2.ex ∧ ym.2.events=y.2.events ∧ ym.2.logs=y.2.logs ∧ ym.2.fnLocals=y.2.fnLocals) ∧
      mm.stack=m.stack ∧ Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap mid) mm := by
  first
  | solve | rfl | simp only [] | omega
  | obtain ⟨mid,ym,mm,hw,innerRun,expr,stmt,native₁,native₂,native,word₁,word₂,word,hr₁,mok₁,hm₁,
      locals,elems,other,addrs,next,effects,stack,alloc⟩ :=
      rhs_assign_late_bounds_word G Fsrc fuel σ r hr sroot outer inner srhs root oi ii rhs k l v
        hsroot houter hinner hvalue htroot hto hti htv inside outside hm SH memOK
    have stopped : Evm.run (rhsAssignValueCode (C := C) b root oi ii rhs) m=.revert := by
      unfold rhsAssignValueCode
      exact Evm.run_append_revert word
    exact ⟨mid,ym,mm,hw,innerRun,expr,word₁,word₂,stopped,fun _ => Evm.run_append_revert stopped,
      hr₁,mok₁,hm₁,locals,elems,addrs,next,effects,stack,alloc⟩

/-- info: 'Solidity.Backend.MemoryOps.rhs_assign_value_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rhs_assign_value_word
/-- info: 'Solidity.Backend.MemoryOps.rhs_assign_value_bounds_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rhs_assign_value_bounds_word
end Solidity.Backend.MemoryOps
