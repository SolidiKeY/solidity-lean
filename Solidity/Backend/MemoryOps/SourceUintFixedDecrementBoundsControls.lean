import Solidity.Backend.MemoryOps.SourceUintFixedDecrementBounds
import Solidity.Backend.MemoryOps.SourceUintFixedDeclareAliasControls
import Solidity.Evm.Correct
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.MemoryOps.SourceUintFixedDecrementBoundsControls
open Evm Evm.Memory
open Source.SemanticsExamples (E0 F0 s0)
private def C : Contract := {vars := []}
private abbrev A : RefTy := .fixed (.prim .uint) 3
private abbrev N : RefTy := .fixed (.prim .uint) 2
private abbrev H : HTy := [A,A,N]
private abbrev Δ : Ctx := [.val .uint,.val .uint,.mem A,.mem A,.mem A,.mem N]
private abbrev SA := Source.STy.array .memory (.int .u256) (some 3)
private abbrev SN := Source.STy.array .memory (.int .u256) (some 2)
private abbrev Γ : Source.RCtx := [.int .u256,.int .u256,SA,SA,SA,SN]
private def u (v : Nat) : PrimTy.uint.Denote := indexValue (wmod v)
private def left : HRef H A := ⟨0,rfl⟩
private def right : HRef H A := ⟨1,rfl⟩
private def neighbor : HRef H N := ⟨2,rfl⟩
private def hp : Heap H := (⟨[u 1,u 8,u 1],rfl⟩,⟨[u 9,u 10,u 9],rfl⟩,⟨[u 11,u 12],rfl⟩,())
private def state (k v : Nat) : State C Δ := {storage := Storage.init C,H := H,heap := hp,env := (u k,u v,some right,some left,some left,some neighbor,())}
private def base (i : Nat) : Fin W := if i=0 then wmod 16 else if i=1 then wmod 24 else wmod 32
private def machine (k v : Nat) : Machine := {Machine.init with stack := [w[77],w[88]],mem := fun a =>
  if a=0 then w[40] else if a=1 then w[32] else if a=2 then w[16] else if a=3 then w[16] else if a=4 then w[24]
  else if a=5 then (Word.val (wmod v)) else if a=6 then (Word.val (wmod k)) else if a=15 then w[99]
  else if a=16 then w[1] else if a=17 then w[8] else if a=18 then w[1]
  else if a=24 then w[9] else if a=25 then w[10] else if a=26 then w[9]
  else if a=32 then w[11] else if a=33 then w[12] else w[0]}
private theorem refs {R : RefTy} (q : HRef H R) :
    (R=A ∧ (HEq q left ∨ HEq q right)) ∨ (R=N ∧ HEq q neighbor) := by
  rcases q with ⟨i,hi⟩
  cases i with
  | zero => cases hi;exact .inl ⟨rfl,.inl HEq.rfl⟩
  | succ i => cases i with
    | zero => cases hi;exact .inl ⟨rfl,.inr HEq.rfl⟩
    | succ i => cases i with
      | zero => cases hi;exact .inr ⟨rfl,HEq.rfl⟩
      | succ i => cases hi
private theorem no_struct {s : Name} (q : HRef H (.struct s)) : False := by
  rcases refs q with ⟨ht,_⟩ | ⟨ht,_⟩ <;> cases ht
private theorem heap_repr (k v : Nat) : Objects.HeapRepr hp base 8 (machine k v) := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
  · intro R q
    rcases refs q with ⟨rfl,hq|hq⟩ | ⟨rfl,hq⟩ <;> cases hq <;> decide
  · intro R q
    rcases refs q with ⟨rfl,hq|hq⟩ | ⟨rfl,hq⟩ <;> cases hq <;> decide
  · intro R Q q r hn
    rcases refs q with ⟨rfl,hq|hq⟩ | ⟨rfl,hq⟩ <;> cases hq
      <;> rcases refs r with ⟨rfl,hr|hr⟩ | ⟨rfl,hr⟩ <;> cases hr
      <;> first | exact (hn rfl).elim | decide
  · intro A E a r
    rcases refs r with ⟨rfl,hr|hr⟩ | ⟨rfl,hr⟩ <;> cases hr <;> cases a
    all_goals
      refine ⟨by decide,?_,?_⟩
      · intro hh
        cases (by simpa only [Objects.header] using hh : (0 : Nat)=1)
      · intro i v hv
        simp only [Heap.get,Objs.get,hp,left,right,neighbor,MObj.elems_fixed] at hv
        cases i with
        | zero => cases Option.some.inj hv;exact ReprV.uint_of rfl
        | succ i => cases i with
          | zero => cases Option.some.inj hv;exact ReprV.uint_of rfl
          | succ i => cases i with
            | zero => first | (cases Option.some.inj hv;exact ReprV.uint_of rfl) | cases hv
            | succ i => cases hv
  · intro s r
    exact (no_struct r).elim
  · intro s f R r hf
    exact (no_struct r).elim
private theorem initial_repr (k v : Nat) : Objects.StateRepr 1 1 8 (Frag.init Δ) (state k v) base (machine k v) := by
  have hc : Sim C 1 0 (Frag.init []) (freshT C 0 W_pos ⟨0,W_pos⟩) Machine.init := Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨?_,heap_repr k v,?_,by decide⟩
  · refine ⟨hc.store,?_,?_,hc.net,hc.netSelf,hc.bound,?_,hc.env,hc.funds,hc.oracle⟩
    · intro p i
      cases i with
      | here => exact ReprV.uint_of rfl
      | there i => cases i with
        | here => exact ReprV.uint_of rfl
        | there i => cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
    · intro R i hi
      cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
    · intro R i hi
      cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
  · intro R i
    cases i with | there i => cases i with
      | there i => cases i with
        | here => exact ⟨right,rfl,rfl⟩
        | there i => cases i with
          | here => exact ⟨left,rfl,rfl⟩
          | there i => cases i with
            | here => exact ⟨left,rfl,rfl⟩
            | there i => cases i with
              | here => exact ⟨neighbor,rfl,rfl⟩
              | there i => nomatch i
private theorem initial_allocator (k v : Nat) : Objects.AllocatorRepr hp base 8 ⟨40,by decide⟩ (machine k v) := by
  refine ⟨heap_repr k v,⟨by decide,by decide,rfl,?_⟩,?_⟩
  · intro a ha
    change 40≤a at ha
    simp only [machine,if_neg (show a≠0 by omega),if_neg (show a≠1 by omega),if_neg (show a≠2 by omega),
      if_neg (show a≠3 by omega),if_neg (show a≠4 by omega),if_neg (show a≠5 by omega),if_neg (show a≠6 by omega),
      if_neg (show a≠15 by omega),if_neg (show a≠16 by omega),if_neg (show a≠17 by omega),if_neg (show a≠18 by omega),
      if_neg (show a≠24 by omega),if_neg (show a≠25 by omega),if_neg (show a≠26 by omega),if_neg (show a≠32 by omega),if_neg (show a≠33 by omega)]
  · intro R q
    rcases refs q with ⟨rfl,hq|hq⟩ | ⟨rfl,hq⟩ <;> cases hq <;> decide
private def source3 (a b : PrimTy.uint.Denote) : Source.Data E0.layout SA :=
  .array 3 (fun _ h => by cases h;rfl) (fun i => .val (sourceUint (if i.val=1 then b else a)))
private def source2 : Source.Data E0.layout SN :=
  .array 2 (fun _ h => by cases h;rfl) (fun i => .val (sourceUint (if i.val=0 then u 11 else u 12)))
private theorem three_conversion {K : HTy} (a b : PrimTy.uint.Denote) :
    sourceUintFixedObject (D := E0.layout) (⟨[a,b,a],rfl⟩ : MObj K A)=source3 a b := by
  unfold sourceUintFixedObject source3
  congr 1
  funext i
  rcases i with ⟨i,hi⟩
  cases i with
  | zero => rfl
  | succ i => cases i with
    | zero => rfl
    | succ i => cases i with
      | zero => rfl
      | succ i => omega
private theorem two_conversion {K : HTy} :
    sourceUintFixedObject (D := E0.layout) (⟨[u 11,u 12],rfl⟩ : MObj K N)=source2 := by
  unfold sourceUintFixedObject source2
  congr 1
  funext i
  rcases i with ⟨i,hi⟩
  cases i with
  | zero => rfl
  | succ i => cases i with
    | zero => rfl
    | succ i => omega
private def y0 : Source.EMState E0 [] := (.nil,s0)
private def y1 : Source.EMState E0 [] := ((Source.allocRef (source3 (u 1) (u 8))).run y0).2
private def y2 : Source.EMState E0 [] := ((Source.allocRef (source3 (u 9) (u 10))).run y1).2
private def y3 : Source.EMState E0 [] := ((Source.allocRef source2).run y2).2
private def sy (k v : Nat) : Source.EMState E0 Γ :=
  (.cons (sourceUint (u k)) (.cons (sourceUint (u v)) (.cons (.memRef rfl 1) (.cons (.memRef rfl 0)
    (.cons (.memRef rfl 0) (.cons (.memRef rfl 2) .nil))))),y3.2)
private abbrev SH := (Source.Heap.empty (D := E0.layout)).ty
private def si : Source.Idx Γ (.int .u256) := .here
private def sv : Source.Idx Γ (.int .u256) := .there .here
private def ss : Source.Idx Γ SA := .there (.there .here)
private def sd : Source.Idx Γ SA := .there (.there (.there .here))
private def sa : Source.Idx Γ SA := .there (.there (.there (.there .here)))
private def ti : Idx Δ (.val .uint) := .here
private def tv : Idx Δ (.val .uint) := .there .here
private def ts : Idx Δ (.mem A) := .there (.there .here)
private def td : Idx Δ (.mem A) := .there (.there (.there .here))
private def ta : Idx Δ (.mem A) := .there (.there (.there (.there .here)))
private theorem represented_left (k v : Nat) : SourceUintFixedAt (sy k v) 0 hp left := by
  unfold SourceUintFixedAt
  change (sy k v).2.heap.get 0=some ⟨SA,sourceUintFixedObject (D := E0.layout) (⟨[u 1,u 8,u 1],rfl⟩ : MObj H A)⟩
  rw [three_conversion];rfl
private theorem represented_right (k v : Nat) : SourceUintFixedAt (sy k v) 1 hp right := by
  unfold SourceUintFixedAt
  change (sy k v).2.heap.get 1=some ⟨SA,sourceUintFixedObject (D := E0.layout) (⟨[u 9,u 10,u 9],rfl⟩ : MObj H A)⟩
  rw [three_conversion];rfl
private theorem represented_neighbor (k v : Nat) : SourceUintFixedAt (sy k v) 2 hp neighbor := by
  unfold SourceUintFixedAt
  change (sy k v).2.heap.get 2=some ⟨SN,sourceUintFixedObject (D := E0.layout) (⟨[u 11,u 12],rfl⟩ : MObj H N)⟩
  rw [two_conversion];rfl
private theorem source_memOK (k v : Nat) : Source.MemOK E0 SH (sy k v) := by
  have h0 : Source.MemOK E0 SH y0 :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have h1 : (match (Source.allocRef (sourceUintFixedObject (⟨[u 1,u 8,u 1],rfl⟩ : MObj H A))).run y0 with
      | (.ok value,y) => Source.MemOK E0 SH y ∧ Source.Val.RefOK E0 y.2.heap.ty value
      | (.error _,y) => Source.MemOK E0 SH y) := source_uint_fixed_alloc_memOK (E := E0) (Γ := []) SH (⟨[u 1,u 8,u 1],rfl⟩ : MObj H A) y0 h0
  rw [three_conversion] at h1
  change Source.MemOK E0 SH y1 ∧ _ at h1
  have h2 : (match (Source.allocRef (sourceUintFixedObject (⟨[u 9,u 10,u 9],rfl⟩ : MObj H A))).run y1 with
      | (.ok value,y) => Source.MemOK E0 SH y ∧ Source.Val.RefOK E0 y.2.heap.ty value
      | (.error _,y) => Source.MemOK E0 SH y) := source_uint_fixed_alloc_memOK (E := E0) (Γ := []) SH (⟨[u 9,u 10,u 9],rfl⟩ : MObj H A) y1 h1.1
  rw [three_conversion] at h2
  change Source.MemOK E0 SH y2 ∧ _ at h2
  have h3 : (match (Source.allocRef (sourceUintFixedObject (⟨[u 11,u 12],rfl⟩ : MObj H N))).run y2 with
      | (.ok value,y) => Source.MemOK E0 SH y ∧ Source.Val.RefOK E0 y.2.heap.ty value
      | (.error _,y) => Source.MemOK E0 SH y) := source_uint_fixed_alloc_memOK (E := E0) (Γ := []) SH (⟨[u 11,u 12],rfl⟩ : MObj H N) y2 h2.1
  rw [two_conversion] at h3
  change Source.MemOK E0 SH y3 ∧ _ at h3
  exact ⟨⟨h3.1.1.1,⟨trivial,⟨trivial,⟨⟨SA,rfl,rfl⟩,⟨⟨SA,rfl,rfl⟩,⟨⟨SA,rfl,rfl⟩,⟨⟨SN,rfl,rfl⟩,trivial⟩⟩⟩⟩⟩⟩⟩,h3.1.2⟩


private def code : List Instr := fixedUintDecrementCode (C := C) 1 td ti


/-! Fixed-array bounds controls. Populated1,8,1 array, separate9,10,9 child and11,12
neighbor; typed/source local aliases and full initial word state unchanged. -/
theorem exact_endpoint_rejection (p : Roadmap.Pipeline) (pre : Bool) :
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintFixedDecrement pre sd si)).run (sy 3 42)=
      (.error (.revert (Source.panicData .index)),sy 3 42) ∧
    (Source.execS (Source.SemanticsExamples.G0 p) F0 4 Γ.length none
      (.expr (sourceUintFixedDecrement pre sd si) : Source.RStmt E0 [] false .body Γ Γ) (sy 3 42).1).run (.nil,(sy 3 42).2)=
      (.error (.revert (Source.panicData .index)),(.nil,(sy 3 42).2)) ∧
    TRun.incDec (fixedUintDecrementOp pre) (.mindex .fixed (.var td rfl) (.local ti)) (state 3 42)=.error .revert ∧
    run code (machine 3 42)=.revert :=
  resolved_uint_fixed_decrement_bounds_word (Source.SemanticsExamples.G0 p) F0 0 pre (state 3 42) left
    (represented_left 3 42) sd si td ti (u 3) rfl rfl rfl rfl (by decide) (initial_repr 3 42)

theorem valid_index_changes_selected (p : Roadmap.Pipeline) (pre : Bool) :
    ∃ (out : Heap H) (z : Source.EMState E0 Γ) (target : Machine),
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintFixedDecrement pre sd si)).run (sy 0 42)=
        (.ok (.val (sourceUint (if pre then u 0 else u 1))),z) ∧
      run code (machine 0 42)=.ok target 0 ∧
      [(hp.get left).1,(hp.get right).1,(hp.get neighbor).1,
       (out.get left).1,(out.get right).1,(out.get neighbor).1]=
        [[u 1,u 8,u 1],[u 9,u 10,u 9],[u 11,u 12],
         [u 0,u 8,u 1],[u 9,u 10,u 9],[u 11,u 12]] ∧
      SourceUintFixedAt z 0 out left ∧ z.1=(sy 0 42).1 ∧
      (∀ a,a≠0 → z.2.heap.get a=(sy 0 42).2.heap.get a) ∧
      target.stack=[w[77],w[88]] ∧
      Objects.StateRepr 1 1 8 (Frag.init Δ) ((state 0 42).withHeap out) base target ∧
      z.2.ex=(sy 0 42).2.ex ∧ z.2.events=(sy 0 42).2.events ∧
      z.2.logs=(sy 0 42).2.logs ∧ z.2.fnLocals=(sy 0 42).2.fnLocals := by
  obtain ⟨out,z,target,hw,hs,he,hstmt,hi,hc,hr,hm,hmok,hl,hstack,keep,hobj,haddr,hex,hev,hlog,hfn⟩ :=
    resolved_uint_fixed_decrement_word (Source.SemanticsExamples.G0 p) F0 0 pre (state 0 42) left (represented_left 0 42)
      sd si td ti (u 0) rfl rfl rfl rfl (by simp only [Heap.len,MObj.elems_fixed];decide)
      (by simp only [MObj.elems_fixed];decide) SH (source_memOK 0 42) (initial_repr 0 42)
  simp only [MObj.elems_fixed] at hw
  change hp.writeAddr (.index left .fixed (u 0)) (u 0)=some out at hw
  have hv : MObj.elems .fixed (out.get left)=
      (MObj.elems .fixed (hp.get left)).set (u 0).val.toNat (u 0) :=
    indexedWrite_elems hp out left .fixed (u 0) (u 0) hw
  simp only [MObj.elems_fixed] at hv
  have hvec : [(hp.get left).1,(hp.get right).1,(hp.get neighbor).1,
      (out.get left).1,(out.get right).1,(out.get neighbor).1]=
      [[u 1,u 8,u 1],[u 9,u 10,u 9],[u 11,u 12],[u 0,u 8,u 1],[u 9,u 10,u 9],[u 11,u 12]] := by
    rw [hv,hobj right (by decide),hobj neighbor (by decide)];rfl
  refine ⟨out,z,target,?_,hc,hvec,hr,hl,haddr,hstack,hm,hex,hev,hlog,hfn⟩
  simpa only [MObj.elems_fixed] using he

/-- Rejecting the wrong original index0 is contradicted by actual success,
while actual endpoint3 is rejected. No post-revert target machine is asserted. -/
theorem stale_valid_index_is_not_endpoint_failure (p : Roadmap.Pipeline) (pre : Bool) :
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintFixedDecrement pre sd si)).run (sy 0 42)≠
      (.error (.revert (Source.panicData .index)),sy 0 42) := by
  obtain ⟨out,z,target,he,_⟩ := valid_index_changes_selected p pre
  rw [he];intro h;cases h

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDecrementBoundsControls.exact_endpoint_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exact_endpoint_rejection
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDecrementBoundsControls.valid_index_changes_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms valid_index_changes_selected
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDecrementBoundsControls.stale_valid_index_is_not_endpoint_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stale_valid_index_is_not_endpoint_failure
end Solidity.Backend.MemoryOps.SourceUintFixedDecrementBoundsControls
