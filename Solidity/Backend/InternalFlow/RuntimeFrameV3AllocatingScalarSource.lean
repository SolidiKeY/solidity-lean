import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarRecursiveSource
import Solidity.Backend.InternalFlow.RuntimeFrameV3DomainTransport

/-! Native allocating scalar recursion over the existing intrinsic recUnroll,
callRec, scoped allocation and primitive-return semantics. This is source
execution evidence, not a target recursive compiler or approved-domain instance. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

def size : Fin W := ⟨3,by decide⟩
def lengthExpr {C : Contract} {R : RefTy} : Simple C (Frame R) .uint := .lit 3 rfl
def allocate {C : Contract} {R : RefTy} : Stmt C (Frame R) (Frame R) :=
 .block (.cons (.declMem (.array (.prim .bool)) (.user "private")
   (some (.newArr lengthExpr rfl)) rfl rfl) .nil)
def allocated {C : Contract} {R : RefTy} (σ : State C (Frame R)) :=
 (σ.alloc (defaultArray .bool size)).1
def extension {C : Contract} {R : RefTy} (σ : State C (Frame R)) : σ.H <+: (allocated σ).H := List.prefix_append _ _
def continuation {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) (depth : Nat)
 (back : Unit → Prog C (Frame R) (Frame R)) : Prog C (Frame R) (Frame R) :=
 .cons (.callRec "allocatingScalar" depth (next R hm) (result R) back) (.cons increment .nil)
def step {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) (depth : Nat)
 (back : Unit → Prog C (Frame R) (Frame R)) : Prog C (Frame R) (Frame R) :=
 .cons (.ite guard (.cons allocate (continuation R hm depth back)) (.cons zero .nil)) .nil
def body {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) (depth : Nat) : Prog C (Frame R) (Frame R) :=
 recUnroll Prog.recBase (step R hm) depth

theorem scoped_allocation {C : Contract} {R : RefTy} (σ : State C (Frame R)) :
 allocate.run σ=.ok ⟨allocated σ,extension σ⟩ := by
 have declared := newArray_decl σ .bool lengthExpr size rfl
 change TRun.block (.push .refl)
  (TRun.seq (TRun.declMem (.array (.prim .bool)) (some (.newArr lengthExpr rfl)) rfl) TRun.nil) σ=_
 simp only [TRun.block,TRun.seq,declared,TRun.nil,Except.map]
 rfl

theorem allocated_parameters {C : Contract} {R : RefTy} (σ : State C (Frame R))
 (n : Nat) (bound : n+1<W) (ref : HRef σ.H R)
 (counter : TEnv.get (.there .here : Idx (Frame R) (.val .uint)) σ.env=countValue (n+1) bound)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame R) (.mem R)) σ.env=some ref) :
 TEnv.get (.there .here : Idx (Frame R) (.val .uint)) (allocated σ).env=countValue (n+1) bound ∧
 TEnv.get (.there (.there .here) : Idx (Frame R) (.mem R)) (allocated σ).env=some (ref.wk (extension σ)) := by
 constructor
 · exact counter
 · change (TEnv.get (.there (.there .here) : Idx (Frame R) (.mem R)) σ.env).map (HRef.wk (extension σ))=_
   rw [alias]
   rfl

theorem source_positive {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (σ : State C (Frame R)) (depth n : Nat) (bound : n+1<W)
 (counter : TEnv.get (.there .here : Idx (Frame R) (.val .uint)) σ.env=countValue (n+1) bound) :
 (body R hm (depth+1)).run σ=
 ((continuation R hm depth (fun _ => body R hm depth)).run (allocated σ)).map
  (fun out => (⟨out.st,(extension σ).trans out.ext⟩ : Solidity.Out C σ.H (Frame R))) := by
 have guarded := guard_eval σ (n+1) (congrArg (fun v : PrimTy.uint.Denote => v.val) counter)
 have positive : decide (0<n+1)=true := decide_eq_true (by omega)
 have source := scoped_allocation σ
 let rest : TStep C (Frame R) (Frame R) := (continuation R hm depth (fun _ => body R hm depth)).runR
 change TRun.seq (TRun.ite guard .refl (TRun.seq allocate.runR rest)
  .refl (TRun.seq zero.runR TRun.nil)) TRun.nil σ=_
 change allocate.runR σ=.ok ⟨allocated σ,extension σ⟩ at source
 change _=(rest (allocated σ)).map _
 simp only [TRun.seq,TRun.ite,guarded,positive,boolT,source,Except.map,ok_bind,if_true]
 cases actual : rest (allocated σ) with
 | error halt => rfl
 | ok out => simp only [TRun.nil];cases out;rfl

theorem source_zero {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (σ : State C (Frame R)) (depth : Nat)
 (counter : TEnv.get (.there .here : Idx (Frame R) (.val .uint)) σ.env=countValue 0 W_pos) :
 (body R hm (depth+1)).run σ=.ok ⟨finished σ 0 W_pos,List.prefix_refl _⟩ := by
 have guarded := guard_eval σ 0 (congrArg (fun v : PrimTy.uint.Denote => v.val) counter)
 change TRun.seq (TRun.ite guard .refl
  (TRun.seq allocate.runR (continuation R hm depth (fun _ => body R hm depth)).runR)
  .refl (TRun.seq zero.runR TRun.nil)) TRun.nil σ=_
 simp only [TRun.seq,TRun.ite,guarded,boolT,TRun.nil,Except.map]
 rfl


theorem success {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (depth : Nat) (σ : State C (Frame R)) (count : Nat) (bound : count<W) (ref : HRef σ.H R)
 (counter : TEnv.get (.there .here : Idx (Frame R) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame R) (.mem R)) σ.env=some ref)
 (enough : count<depth) :
 ∃ out, (body R hm depth).run σ=.ok out ∧
 out.st.H.length=σ.H.length+count ∧
 out.st.env=TEnv.set (.here : Idx (Frame R) (.val .uint)) (countValue count bound)
   (TEnv.wk out.ext (Frame R) σ.env) ∧
 Heap.Keeps out.ext σ.heap out.st.heap := by
 induction count generalizing depth σ with
 | zero =>
   cases depth with
   | zero => omega
   | succ depth =>
     refine ⟨⟨finished σ 0 W_pos,List.prefix_refl _⟩,source_zero hm σ depth counter,?_,?_,Heap.Keeps.refl σ.heap⟩
     · change σ.H.length=σ.H.length+0
       omega
     · change TEnv.set .here (countValue 0 W_pos) σ.env=TEnv.set .here (countValue 0 W_pos)
         (TEnv.wk (List.prefix_refl _) (Frame R) σ.env)
       rw [TEnv.wk_self]
 | succ count ih =>
   cases depth with
   | zero => omega
   | succ depth =>
     let parent := allocated σ
     let e := extension σ
     let inherited := ref.wk e
     let arguments : TEnv C parent.H (Parameters R) := (countValue count (by omega),(some inherited,()))
     let child := entered parent count (by omega) inherited
     have parameters := allocated_parameters σ count bound ref counter alias
     have kept : Heap.Keeps e σ.heap parent.heap := Heap.keeps_alloc σ.heap (defaultArray .bool size)
     obtain ⟨out,runChild,grown,locals,contents⟩ := ih depth child (by omega) inherited rfl rfl (by omega)
     have args := next_eval hm parent count bound inherited parameters.1 parameters.2
     have native := call_return (next R hm) (result R) .refl (body R hm depth).runR
      parent arguments args out runChild
     let returned := exported (result R) Ext.refl parent arguments out
     have call : (.callRec "allocatingScalar" depth (next R hm) (result R) (fun _ => body R hm depth) :
       Stmt C (Frame R) (Frame R)).run parent=.ok returned := by
       change TRun.call (next R hm) (result R) (body R hm depth).ext (body R hm depth).runR parent=_
       have scope : (body (C:=C) R hm depth).ext=Ext.refl := Subsingleton.elim _ _
       rw [scope]
       exact native
     have childValue : TEnv.get (.here : Idx (Frame R) (.val .uint)) out.st.env=countValue count (by omega) := by
       rw [locals,TEnv.get_set]
     have returnedEnv : returned.st.env=TEnv.set (.here : Idx (Frame R) (.val .uint))
       (countValue count (by omega)) (TEnv.wk returned.ext (Frame R) parent.env) := by
       change TEnv.set .here (TEnv.get (.here : Idx (Frame R) (.val .uint)) out.st.env)
         (TEnv.wk returned.ext (Frame R) parent.env)=_
       rw [childValue]
     have value : TEnv.get (.here : Idx (Frame R) (.val .uint)) returned.st.env=countValue count (by omega) := by
       rw [returnedEnv,TEnv.get_set]
     have advanced := increment_run returned.st count bound value
     have continued : (continuation R hm depth (fun _ => body R hm depth)).run parent=
       .ok ⟨finished returned.st (count+1) bound,returned.ext⟩ := by
       rw [continuation,Prog.run_cons_ok call,Prog.run_cons_ok advanced,Prog.run_nil]
       rfl
     let final : Solidity.Out C σ.H (Frame R) :=
       ⟨finished returned.st (count+1) bound,e.trans returned.ext⟩
     refine ⟨final,?_,?_,?_,?_⟩
     · rw [source_positive hm σ depth count bound counter,continued]
       rfl
     · change out.st.H.length=σ.H.length+(count+1)
       change out.st.H.length=(σ.H++([.array (.prim .bool)] : HTy)).length+count at grown
       simpa only [List.length_append,List.length_singleton,Nat.add_assoc,Nat.add_comm 1 count] using grown
     · change TEnv.set .here (countValue (count+1) bound) returned.st.env=
         TEnv.set .here (countValue (count+1) bound) (TEnv.wk (e.trans returned.ext) (Frame R) σ.env)
       rw [returnedEnv]
       change (countValue (count+1) bound,(TEnv.wk returned.ext (Frame R) parent.env).2)=
         (countValue (count+1) bound,(TEnv.wk (e.trans returned.ext) (Frame R) σ.env).2)
       have transport := TEnv.wk_trans e returned.ext (Frame R) σ.env
       exact congrArg (fun env : TEnv C out.st.H (Frame R) =>
         (countValue (count+1) bound,env.2)) transport
     · exact kept.trans contents

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.scoped_allocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.scoped_allocation

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.allocated_parameters' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.allocated_parameters

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.source_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.source_positive

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.source_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.source_zero

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.success
