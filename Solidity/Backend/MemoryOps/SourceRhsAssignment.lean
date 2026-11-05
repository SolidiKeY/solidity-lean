import Solidity.Backend.MemoryOps.SourceSequence

/-! Actual side-effectful assignment RHS, then the reached outer lvalue.
The word append certifies the discarded-result statement only, not an emitted
assignment-expression result or a new compiler/evaluator. -/
namespace Solidity.Backend.MemoryOps

def sourceRhsAssign {E : Source.Env} {Γ : Source.RCtx}
    (root : Source.Idx Γ (.array .memory .bool none))
    (outer inner : Source.Idx Γ (.int .u256)) (rhs : Source.Idx Γ .bool) : Source.RExpr E Γ .bool :=
  .assign (.indexArray (.local root) (by decide) (.local outer) rfl) (sourceIndexedAssign root inner rhs)

/-- Substitute an ACTUALLY executed RHS for the unchanged local that returns
its value in the reached state. The outer location is resolved only afterwards. -/
theorem source_assign_rhs_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (y mid out : Source.EMState E Γ)
    (loc : Source.RLVal E Γ .bool) (rhs : Source.RExpr E Γ .bool) (srhs : Source.Idx Γ .bool)
    (v : Bool) (result : Except Source.Halt (Source.RVal E.layout .bool))
    (first : (Source.evalE G F (fuel+1) rhs).run y=(.ok (.val (.bool v)),mid))
    (aligned : mid.1.get srhs=.bool v)
    (second : (Source.evalE G F (fuel+2) (.assign loc (.local srhs))).run mid=(result,out)) :
    (Source.evalE G F (fuel+2) (.assign loc rhs)).run y=(result,out) := by
  first
  | solve | rfl | simp only [] | omega
  | rw [Source.evalE,Source.Hoare.run_bind,first]
    rw [Source.evalE,Source.Hoare.run_bind,source_local_value_run G F fuel mid srhs (.bool v) aligned] at second
    exact second

/-- Recover the exact heap effect of a real primitive assignment from the
independent initial observer and producer, including arbitrary other addresses. -/
theorem SourceBoolMemoryAt.assign_state {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y z : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (.array (.prim .bool))}
    (hr : SourceBoolMemoryAt y a hp r .dyn) (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (root : Source.Idx Γ (.array .memory .bool none)) (idx : Source.Idx Γ (.int .u256)) (rhs : Source.Idx Γ .bool)
    (k : PrimTy.uint.Denote) (v : Bool) (hroot : y.1.get root=.memRef rfl a)
    (hidx : y.1.get idx=sourceUint k) (hrhs : y.1.get rhs=.bool v) (hk : k.1.toNat<hp.len r .dyn)
    (run : (Source.evalE G F (fuel+3) (sourceIndexedAssign root idx rhs)).run y=(.ok (.val (.bool v)),z)) :
    ∃ (ht : y.2.heap.ty a=some (.array .memory .bool none)),
      z=(y.1,{y.2 with heap := y.2.heap.write a (sourceBoolMemory ((MObj.elems .dyn (hp.get r)).set k.1.toNat v)) ht}) := by
  first
  | solve | rfl | simp only [] | omega
  | obtain ⟨ht,write⟩ := source_bool_write y a (MObj.elems .dyn (hp.get r)) hr k.1.toNat hk v
    have known := hr.eval_assign_of_run G F fuel root idx rhs k v hroot hidx hrhs hk write
    exact ⟨ht,congrArg Prod.snd (run.symm.trans known)⟩

/-- An actual successful RHS write precedes the failing OUTER lvalue.
Initial bounds/alignment supply every reached premise. Source retains that RHS
state; native/word errors expose no invented post-revert state. -/
theorem rhs_assign_late_bounds_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
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
      (Source.execS G Fsrc (fuel+5) Γ.length none
        (.expr (sourceRhsAssign sroot outer inner srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.error (.revert (Source.panicData .index)),(.nil,ym.2)) ∧
      Stmt.run σ (.assignMem (.index .dyn (.var root rfl) (.simple (.local ii))) (.val (.simple (.local rhs))))=
        .ok ⟨σ.withHeap mid,List.prefix_refl _⟩ ∧
      Stmt.run (σ.withHeap mid) (.assignMem (.index .dyn (.var root rfl) (.simple (.local oi))) (.val (.simple (.local rhs))))=.error .revert ∧
      Prog.run σ (.cons (.assignMem (.index .dyn (.var root rfl) (.simple (.local ii))) (.val (.simple (.local rhs))))
        (.cons (.assignMem (.index .dyn (.var root rfl) (.simple (.local oi))) (.val (.simple (.local rhs)))) .nil))=.error .revert ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local ii)) (.simple (.local rhs))) m=.ok mm 0 ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local oi)) (.simple (.local rhs))) mm=.revert ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local ii)) (.simple (.local rhs)) ++
        Evm.Memory.writeLocalCode (C := C) b root (.simple (.local oi)) (.simple (.local rhs))) m=.revert ∧
      SourceBoolMemoryAt ym address mid r .dyn ∧ Source.MemOK E SH ym ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap mid) base mm ∧ ym.1=y.1 ∧
      MObj.elems .dyn (mid.get r)=(MObj.elems .dyn (σ.heap.get r)).set l.1.toNat v ∧
      (∀ {Q : RefTy} (q : HRef σ.H Q),r.id≠q.id → mid.get q=σ.heap.get q) ∧
      (∀ a,a≠address → ym.2.heap.get a=y.2.heap.get a) ∧ ym.2.heap.next=y.2.heap.next ∧
      (ym.2.ex=y.2.ex ∧ ym.2.events=y.2.events ∧ ym.2.logs=y.2.logs ∧ ym.2.fnLocals=y.2.fnLocals) ∧
      mm.stack=m.stack ∧ Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap mid) mm := by
  first
  | solve | rfl | simp only [] | omega
  | obtain ⟨mid,ym,mm,hw,expr₁,stmt₁,native₁,word₁,hr₁,hm₁,mok₁,locals,stack,alloc⟩ :=
      resolved_assign_word G Fsrc fuel σ r hr sroot inner srhs root ii rhs l v hsroot hinner hvalue htroot hti htv inside hm SH memOK
    have elems := indexedWrite_elems σ.heap mid r .dyn l v hw
    have bound : mid.len r .dyn≤k.1.toNat := by
      change (MObj.elems .dyn (mid.get r)).length≤k.1.toNat
      rw [elems,List.length_set];exact outside
    obtain ⟨expr₂,word₂⟩ := resolved_assign_word_bounds G Fsrc (fuel+1) (σ.withHeap mid) r hr₁ sroot outer srhs root oi rhs k v
      (by rw [locals];exact hsroot) (by rw [locals];exact houter) (by rw [locals];exact hvalue) htroot hto htv bound hm₁
    have expr := source_assign_rhs_run G Fsrc (fuel+2) y ym ym
      (.indexArray (.local sroot) (by decide) (.local outer) rfl) (sourceIndexedAssign sroot inner srhs) srhs v _
      expr₁ (by rw [locals];exact hvalue) expr₂
    have stmt := source_expr_statement_error G Fsrc (fuel+4) Γ.length _ y ym _ expr
    have none : mid.writeAddr (.index r .dyn k) v=none := by
      simp only [Heap.writeAddr,Heap.setIndex,show ¬k.1.toNat<(MObj.elems .dyn (mid.get r)).length from Nat.not_lt.mpr bound,↓reduceIte]
    have native₂ : Stmt.run (σ.withHeap mid) (.assignMem (.index .dyn (.var root rfl) (.simple (.local oi))) (.val (.simple (.local rhs))))=.error .revert := by
      have tr : TEnv.get root (σ.withHeap mid).env=some r := htroot
      have ti : TEnv.get oi (σ.withHeap mid).env=k := hto
      have tv : TEnv.get rhs (σ.withHeap mid).env=v := htv
      have nw : (σ.withHeap mid).heap.writeAddr (.index r .dyn k) v=Option.none := none
      change TRun.assignMem _ _ (σ.withHeap mid)=_
      simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,tr,ti,tv,
        nw,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    obtain ⟨ht,reached⟩ := hr.assign_state G Fsrc fuel sroot inner srhs l v hsroot hinner hvalue inside expr₁
    refine ⟨mid,ym,mm,hw,expr₁,expr,stmt,native₁,native₂,intrinsic_heap_pair_error σ _ _ mid .revert native₁ native₂,
      word₁,word₂,?_,hr₁,mok₁,hm₁,locals,elems,?_,?_,?_,?_,stack,alloc⟩
    · rw [Evm.run_append_ok word₁];exact word₂
    · intro Q q hn;exact indexedWrite_frame σ.heap mid r .dyn l v hw q hn
    · intro a hn;rw [reached];exact Source.Heap.write_other y.2.heap hn _ ht
    · rw [reached];rfl
    · rw [reached];exact ⟨rfl,rfl,rfl,rfl⟩

theorem rhs_assign_success_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
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
      (Source.execS G Fsrc (fuel+5) Γ.length none
        (.expr (sourceRhsAssign sroot outer inner srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      Prog.run σ (.cons (.assignMem (.index .dyn (.var root rfl) (.simple (.local ii))) (.val (.simple (.local rhs))))
        (.cons (.assignMem (.index .dyn (.var root rfl) (.simple (.local oi))) (.val (.simple (.local rhs)))) .nil))=
          .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local ii)) (.simple (.local rhs))) m=.ok mm 0 ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local oi)) (.simple (.local rhs))) mm=.ok target 0 ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local ii)) (.simple (.local rhs)) ++
        Evm.Memory.writeLocalCode (C := C) b root (.simple (.local oi)) (.simple (.local rhs))) m=.ok target 0 ∧
      SourceBoolMemoryAt ym address mid r .dyn ∧ SourceBoolMemoryAt z address out r .dyn ∧
      Source.MemOK E SH ym ∧ Source.MemOK E SH z ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap mid) base mm ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap out) base target ∧ ym.1=y.1 ∧ z.1=y.1 ∧
      MObj.elems .dyn (out.get r)=((MObj.elems .dyn (σ.heap.get r)).set l.1.toNat v).set k.1.toNat v ∧
      (∀ {Q : RefTy} (q : HRef σ.H Q),r.id≠q.id → out.get q=σ.heap.get q) ∧
      (∀ a,a≠address → z.2.heap.get a=y.2.heap.get a) ∧ z.2.heap.next=y.2.heap.next ∧
      (z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals) ∧
      target.stack=m.stack ∧ Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out) target := by
  first
  | solve | rfl | simp only [] | omega
  | obtain ⟨mid,ym,mm,hw₁,expr₁,stmt₁,native₁,word₁,hr₁,hm₁,mok₁,locals₁,stack₁,alloc₁⟩ :=
      resolved_assign_word G Fsrc fuel σ r hr sroot inner srhs root ii rhs l v hsroot hinner hvalue htroot hti htv inside hm SH memOK
    have elems₁ := indexedWrite_elems σ.heap mid r .dyn l v hw₁
    have bound : k.1.toNat<mid.len r .dyn := by
      change k.1.toNat<(MObj.elems .dyn (mid.get r)).length
      rw [elems₁,List.length_set];exact outerInside
    obtain ⟨out,z,target,hw₂,expr₂,stmt₂,native₂,word₂,hr₂,hm₂,mok₂,locals₂,stack₂,alloc₂⟩ :=
      resolved_assign_word G Fsrc (fuel+1) (σ.withHeap mid) r hr₁ sroot outer srhs root oi rhs k v
        (by rw [locals₁];exact hsroot) (by rw [locals₁];exact houter) (by rw [locals₁];exact hvalue)
        htroot hto htv bound hm₁ SH mok₁
    have expr := source_assign_rhs_run G Fsrc (fuel+2) y ym z
      (.indexArray (.local sroot) (by decide) (.local outer) rfl) (sourceIndexedAssign sroot inner srhs) srhs v _
      expr₁ (by rw [locals₁];exact hvalue) expr₂
    have stmt := source_expr_statement_run G Fsrc (fuel+4) Γ.length _ y z (.val (.bool v)) expr
    obtain ⟨ht₁,reached₁⟩ := hr.assign_state G Fsrc fuel sroot inner srhs l v hsroot hinner hvalue inside expr₁
    obtain ⟨ht₂,reached₂⟩ := hr₁.assign_state G Fsrc (fuel+1) sroot outer srhs k v
      (by rw [locals₁];exact hsroot) (by rw [locals₁];exact houter) (by rw [locals₁];exact hvalue) bound expr₂
    refine ⟨mid,out,ym,z,mm,target,hw₁,hw₂,expr₁,expr,stmt,intrinsic_heap_pair_run σ _ _ mid out native₁ native₂,
      word₁,word₂,?_,hr₁,hr₂,mok₁,mok₂,hm₁,hm₂,locals₁,locals₂.trans locals₁,?_,?_,?_,?_,?_,stack₂.trans stack₁,?_⟩
    · rw [Evm.run_append_ok word₁];exact word₂
    · rw [indexedWrite_elems mid out r .dyn k v hw₂,elems₁]
    · intro Q q hn
      rw [indexedWrite_frame mid out r .dyn k v hw₂ q hn,indexedWrite_frame σ.heap mid r .dyn l v hw₁ q hn]
    · intro a hn
      rw [reached₂,Source.Heap.write_other ym.2.heap hn _ ht₂,reached₁,Source.Heap.write_other y.2.heap hn _ ht₁]
    · rw [reached₂];change ym.2.heap.next=y.2.heap.next;rw [reached₁];rfl
    · rw [reached₂];change ym.2.ex=y.2.ex ∧ ym.2.events=y.2.events ∧ ym.2.logs=y.2.logs ∧ ym.2.fnLocals=y.2.fnLocals
      rw [reached₁];exact ⟨rfl,rfl,rfl,rfl⟩
    · intro cursor hb ha;exact alloc₂ cursor hb (alloc₁ cursor hb ha)

/-- info: 'Solidity.Backend.MemoryOps.rhs_assign_success_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rhs_assign_success_word

/-- info: 'Solidity.Backend.MemoryOps.source_assign_rhs_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_assign_rhs_run
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.assign_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolMemoryAt.assign_state
/-- info: 'Solidity.Backend.MemoryOps.rhs_assign_late_bounds_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rhs_assign_late_bounds_word
end Solidity.Backend.MemoryOps
