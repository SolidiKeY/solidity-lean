import Solidity.Backend.MemoryOps.SourceUintFixedAliasFailure
import Solidity.Backend.MemoryOps.SourceUintFixedDeclaration
import Solidity.Evm.Correct
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.MemoryOps.SourceUintFixedAliasControls
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
private def hp : Heap H := (⟨[u 7,u 8,u 7],rfl⟩,⟨[u 9,u 10,u 9],rfl⟩,⟨[u 11,u 12],rfl⟩,())
private def state (k v : Nat) : State C Δ := {storage := Storage.init C,H := H,heap := hp,env := (u k,u v,some right,some left,some left,some neighbor,())}
private def base (i : Nat) : Fin W := if i=0 then wmod 16 else if i=1 then wmod 24 else wmod 32
private def machine (k v : Nat) : Machine := {Machine.init with stack := [w[77],w[88]],mem := fun a =>
  if a=0 then w[40] else if a=1 then w[32] else if a=2 then w[16] else if a=3 then w[16] else if a=4 then w[24]
  else if a=5 then (Word.val (wmod v)) else if a=6 then (Word.val (wmod k)) else if a=15 then w[99]
  else if a=16 then w[7] else if a=17 then w[8] else if a=18 then w[7]
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
  have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
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
private def y1 : Source.EMState E0 [] := ((Source.allocRef (source3 (u 7) (u 8))).run y0).2
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
  change (sy k v).2.heap.get 0=some ⟨SA,sourceUintFixedObject (D := E0.layout) (⟨[u 7,u 8,u 7],rfl⟩ : MObj H A)⟩
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
  have h1 := source_uint_fixed_alloc_memOK (E := E0) (Γ := []) SH (⟨[u 7,u 8,u 7],rfl⟩ : MObj H A) y0 h0
  rw [three_conversion] at h1
  change Source.MemOK E0 SH y1 ∧ _ at h1
  have h2 := source_uint_fixed_alloc_memOK (E := E0) (Γ := []) SH (⟨[u 9,u 10,u 9],rfl⟩ : MObj H A) y1 h1.1
  rw [three_conversion] at h2
  change Source.MemOK E0 SH y2 ∧ _ at h2
  have h3 := source_uint_fixed_alloc_memOK (E := E0) (Γ := []) SH (⟨[u 11,u 12],rfl⟩ : MObj H N) y2 h2.1
  rw [two_conversion] at h3
  change Source.MemOK E0 SH y3 ∧ _ at h3
  exact ⟨⟨h3.1.1.1,⟨trivial,⟨trivial,⟨⟨SA,rfl,rfl⟩,⟨⟨SA,rfl,rfl⟩,⟨⟨SA,rfl,rfl⟩,⟨⟨SN,rfl,rfl⟩,trivial⟩⟩⟩⟩⟩⟩⟩,h3.1.2⟩

/-- Initial objects and Source table are independently inhabited. -/
theorem initial_views (k v : Nat) : Source.MemOK E0 SH (sy k v) ∧
    SourceUintFixedAt (sy k v) 0 hp left ∧ SourceUintFixedAt (sy k v) 1 hp right ∧
    SourceUintFixedAt (sy k v) 2 hp neighbor ∧
    Objects.StateRepr 1 1 8 (Frag.init Δ) (state k v) base (machine k v) ∧
    Objects.AllocatorRepr hp base 8 ⟨40,by decide⟩ (machine k v) :=
  ⟨source_memOK k v,represented_left k v,represented_right k v,represented_neighbor k v,initial_repr k v,initial_allocator k v⟩

private def rebound (k v : Nat) : Source.EMState E0 Γ := ((sy k v).1.set sd (.memRef rfl 1),(sy k v).2)
private def reboundState (k v : Nat) := (state k v).setLocal td (some right)
private def reboundWord (k v : Nat) := writeMachine (machine k v) 3 w[24]
private def writeCode : List Instr :=
  Evm.compileVal 1 (.simple (.local tv) : Val C Δ .uint) ++ [.mload (Evm.cellOf 1 td)] ++
    Evm.compileVal 1 (.simple (.local ti) : Val C Δ .uint) ++ Objects.writeCode (.fixed : ArrTy A (.prim .uint))
private def clearCode : List Instr :=
  Evm.compileVal 1 (deleteDefaultValue .uint : Val C Δ .uint) ++ [.mload (Evm.cellOf 1 td)] ++
    Evm.compileVal 1 (.simple (.local ti) : Val C Δ .uint) ++ Objects.writeCode (.fixed : ArrTy A (.prim .uint))

/-- Distinct bindings, same-identity alias and self-rebinding are actual Source,
intrinsic and word executions; no object is copied. -/
theorem alias_cases (p : Roadmap.Pipeline) (k v : Nat) :
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (sourceLocalAlias sd ss)).run (sy k v)=
      (.ok (.val (.memRef rfl 1)),rebound k v) ∧
    Stmt.run (state k v) (.rebindMem td (.alias (.var ts rfl)))=.ok ⟨reboundState k v,List.prefix_refl _⟩ ∧
    run (aliasLocalCode 1 td ts) (machine k v)=.ok (reboundWord k v) 0 ∧
    (rebound k v).1.get sd=.memRef rfl 1 ∧ (rebound k v).1.get sa=.memRef rfl 0 ∧
    TEnv.get td (reboundState k v).env=some right ∧ TEnv.get ta (reboundState k v).env=some left ∧
    (rebound k v).2=(sy k v).2 ∧ (reboundState k v).heap=hp ∧
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (sourceLocalAlias sd sa)).run (sy k v)=
      (.ok (.val (.memRef rfl 0)),sy k v) ∧
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (sourceLocalAlias ss ss)).run (sy k v)=
      (.ok (.val (.memRef rfl 1)),sy k v) := by
  have h := source_uint_fixed_alias_word (Source.SemanticsExamples.G0 p) F0 0 (sy k v) sd ss 1 rfl SH (source_memOK k v)
    (state k v) td ts right rfl (represented_right k v) (initial_repr k v) (initial_allocator k v) (by decide)
  have hsame := source_local_alias_run (Source.SemanticsExamples.G0 p) F0 0 (sy k v) sd sa (.memRef rfl 0) rfl
  have hself := source_local_alias_run (Source.SemanticsExamples.G0 p) F0 0 (sy k v) ss ss (.memRef rfl 1) rfl
  exact ⟨h.1,h.2.2.1,h.2.2.2.1,rfl,rfl,rfl,rfl,rfl,rfl,hsame,hself⟩

/-- Runtime index/value execution. The retained LEFT alias and neighbour frame
through the actual RIGHT write/delete, and the entire Source object table is
observed at both changed heaps. -/
theorem reached_program (p : Roadmap.Pipeline) (k v : Nat) (hk : k<3) :
    ∃ (out1 out2 : Heap H) (z1 z2 : Source.EMState E0 Γ) (m1 m2 : Machine),
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 7 Γ.length none
        (sourceUintFixedAliasProgram sd ss si sv) (sy k v).1).run (.nil,(sy k v).2)=
        (.ok (.normal z2.1),(.nil,z2.2)) ∧
      Prog.run (state k v) (intrinsicUintFixedAliasProgram td ts ti tv)=.ok ⟨(reboundState k v).withHeap out2,List.prefix_refl _⟩ ∧
      run writeCode (reboundWord k v)=.ok m1 0 ∧ run clearCode m1=.ok m2 0 ∧
      run (aliasLocalCode 1 td ts ++ writeCode ++ clearCode) (machine k v)=.ok m2 0 ∧
      [(out1.get left).1,(out1.get right).1,(out1.get neighbor).1,
       (out2.get left).1,(out2.get right).1,(out2.get neighbor).1]=
        [[u 7,u 8,u 7],[u 9,u 10,u 9].set k (u v),[u 11,u 12],
         [u 7,u 8,u 7],[u 9,u 10,u 9].set k (PrimTy.dflt .uint),[u 11,u 12]] ∧
      [z1.2.heap.get 0,z1.2.heap.get 1,z1.2.heap.get 2,z2.2.heap.get 0,z2.2.heap.get 1,z2.2.heap.get 2]=
        [(sy k v).2.heap.get 0,some ⟨SA,sourceUintFixedObject (out1.get right)⟩,(sy k v).2.heap.get 2,
         (sy k v).2.heap.get 0,some ⟨SA,sourceUintFixedObject (out2.get right)⟩,(sy k v).2.heap.get 2] ∧
      SourceUintFixedAt z2 0 out2 left ∧ SourceUintFixedAt z2 1 out2 right ∧ SourceUintFixedAt z2 2 out2 neighbor ∧
      [z2.1.get sd,z2.1.get sa,z2.1.get ss]=[.memRef rfl 1,.memRef rfl 0,.memRef rfl 1] ∧
      [TEnv.get td ((reboundState k v).withHeap out2).env,TEnv.get ta ((reboundState k v).withHeap out2).env]=[some right,some left] ∧
      Objects.StateRepr 1 1 8 (Frag.init Δ) ((reboundState k v).withHeap out2) base m2 ∧
      Objects.AllocatorRepr out2 base 8 ⟨40,by decide⟩ m2 ∧ Source.MemOK E0 SH z1 ∧ Source.MemOK E0 SH z2 ∧
      m2.stack=[w[77],w[88]] ∧ m2.mem 0=w[40] ∧
      z2.2.ex=(sy k v).2.ex ∧ z2.2.events=(sy k v).2.events ∧ z2.2.logs=(sy k v).2.logs ∧ z2.2.fnLocals=(sy k v).2.fnLocals := by
  have hkw : k<W := Nat.lt_trans hk (by decide : 3<W)
  have hki : (u k).1.toNat=k := by change (wmod k).val=k;exact Nat.mod_eq_of_lt hkw
  obtain ⟨o1,o2,z1,z2,m1,m2,hsA,hs1,hs2,hitems,hprog,hw1,hw2,hrA,hr1,hr2,hcA,hc1,hc2,hwhole,hm2,ha2,hmok1,hmok2,hl1,hl2,hrootS,hrootT,hsloc,htloc,hstack,hfree,hobj,haddr,hex,hev,hlog,hfn,hviews,he1,he2,hwrite,hdelete,haddr1,hobj1⟩ :=
    source_uint_fixed_alias_program_word (Source.SemanticsExamples.G0 p) F0 0 (sy k v) sd ss si sv 1 (state k v) td ts ti tv right (u k) (u v)
      rfl rfl rfl rfl rfl rfl (represented_right k v) (by rw [hki];exact hk) SH (source_memOK k v)
      (initial_repr k v) (initial_allocator k v) (by decide)
  change hp.writeAddr (.index right .fixed (u k)) (u v)=some o1 at hw1
  change o1.writeAddr (.index right .fixed (u k)) (PrimTy.dflt .uint)=some o2 at hw2
  have ho1 : o1=hp.set right (MObj.setElem .fixed (hp.get right) k (u v)) := by
    simpa only [Heap.writeAddr,Heap.setIndex,MObj.elems_fixed,hki,(hp.get right).2,if_pos hk,Option.some.injEq] using hw1.symm
  have ho2 : o2=o1.set right (MObj.setElem .fixed (o1.get right) k (PrimTy.dflt .uint)) := by
    simpa only [Heap.writeAddr,Heap.setIndex,MObj.elems_fixed,hki,(o1.get right).2,if_pos hk,Option.some.injEq] using hw2.symm
  have hv1 : (o1.get right).1=[u 9,u 10,u 9].set k (u v) := by rw [ho1,Heap.get_set_same,MObj.setElem_fixed];rfl
  have hv2 : (o2.get right).1=[u 9,u 10,u 9].set k (PrimTy.dflt .uint) := by
    rw [ho2,Heap.get_set_same,MObj.setElem_fixed]
    change (o1.get right).1.set k (PrimTy.dflt .uint)=_
    rw [hv1,List.set_set]
  have h1l := hobj1 left (by change (1 : Nat)≠0;decide)
  have h1n := hobj1 neighbor (by change (1 : Nat)≠2;decide)
  have h2l := hobj left (by change (1 : Nat)≠0;decide)
  have h2n := hobj neighbor (by change (1 : Nat)≠2;decide)
  have hleft := hviews left 0 (by change (1 : Nat)≠0;decide) (by decide) (represented_left k v)
  have hneighbor := hviews neighbor 2 (by change (1 : Nat)≠2;decide) (by decide) (represented_neighbor k v)
  refine ⟨o1,o2,z1,z2,m1,m2,hitems,hprog,hc1,hc2,hwhole,?_,?_,hleft,hr2,hneighbor,?_,rfl,hm2,ha2,hmok1,hmok2,?_,hfree,hex,hev,hlog,hfn⟩
  · rw [h1l,h1n,h2l,h2n,hv1,hv2];rfl
  · rw [haddr1 0 (by decide),haddr1 2 (by decide),haddr 0 (by decide),haddr 2 (by decide),hr1,hr2]
  · rw [hl2];rfl
  · exact hstack

private def cells (m : Machine) : List Word :=
  [m.mem 0,m.mem 1,m.mem 2,m.mem 3,m.mem 4,m.mem 5,m.mem 6,m.mem 15,
   m.mem 16,m.mem 17,m.mem 18,m.mem 24,m.mem 25,m.mem 26,m.mem 32,m.mem 33]
private def observed (code : List Instr) (m : Machine) : Option (List Word × List Word) :=
  match run code m with | .ok out 0 => some (cells out,out.stack) | _ => none
private theorem observed_ok {code : List Instr} {m out : Machine} (h : run code m=.ok out 0) :
    observed code m=some (cells out,out.stack) := by unfold observed;rw [h]
private theorem update_run (m : Machine) (a k v : Nat) (hk : k<3) (hkw : k<W) (ha : a+k<W) (hb : a<W)
    (h5 : m.mem 5=Word.val (wmod v)) (h3 : m.mem 3=Word.val (wmod a)) (h6 : m.mem 6=Word.val (wmod k)) :
    run writeCode m=.ok (writeMachine m (a+k) (.val (wmod v))) 0 := by
  change run ([.mload 5,.mload 3,.mload 6] ++ Objects.fixedAddrCode 3 ++ [.mstoreAt]) m=_
  have hp : run [.mload 5,.mload 3,.mload 6] m=
      .ok (((m.push (.val (wmod v))).push (.val (wmod a))).push (.val (wmod k))) 0 := by
    simp only [run,exec_cons_zero,Instr.step,Machine.next,Machine.push,Out.ok_bind,exec_nil,h5,h3,h6]
  have hc := Objects.fixedAddr_run (m.push (.val (wmod v))) ⟨a,hb⟩ (wmod k) 3
  rw [if_pos (by simpa only [wmod_of_lt hkw] using hk)] at hc
  rw [List.append_assoc,run_append_ok hp]
  rw [show wmod a=⟨a,hb⟩ from Fin.ext (Nat.mod_eq_of_lt hb)]
  change run (Objects.fixedAddrCode 3 ++ [.mstoreAt])
    (((m.push (.val (wmod v))).push (.val ⟨a,hb⟩)).push (.val (wmod k)))=_
  rw [run_append_ok hc]
  simp only [run,Machine.push,exec_cons_zero,Instr.step,Out.ok_bind,exec_nil,wmod_of_lt hkw,wmod_of_lt ha,writeMachine]
private theorem clear_run (m : Machine) (a k : Nat) (hk : k<3) (hkw : k<W) (ha : a+k<W) (hb : a<W)
    (h3 : m.mem 3=Word.val (wmod a)) (h6 : m.mem 6=Word.val (wmod k)) :
    run clearCode m=.ok (writeMachine m (a+k) w[0]) 0 := by
  change run ([.push w[0],.mload 3,.mload 6] ++ Objects.fixedAddrCode 3 ++ [.mstoreAt]) m=_
  have hp : run [.push w[0],.mload 3,.mload 6] m=
      .ok (((m.push w[0]).push (.val (wmod a))).push (.val (wmod k))) 0 := by
    simp only [run,exec_cons_zero,Instr.step,Machine.next,Machine.push,Out.ok_bind,exec_nil,h3,h6]
  have hc := Objects.fixedAddr_run (m.push w[0]) ⟨a,hb⟩ (wmod k) 3
  rw [if_pos (by simpa only [wmod_of_lt hkw] using hk)] at hc
  rw [List.append_assoc,run_append_ok hp]
  rw [show wmod a=⟨a,hb⟩ from Fin.ext (Nat.mod_eq_of_lt hb)]
  change run (Objects.fixedAddrCode 3 ++ [.mstoreAt]) (((m.push w[0]).push (.val ⟨a,hb⟩)).push (.val (wmod k)))=_
  rw [run_append_ok hc]
  simp only [run,Machine.push,exec_cons_zero,Instr.step,Out.ok_bind,exec_nil,wmod_of_lt hkw,wmod_of_lt ha,writeMachine]

/-- Complete16word observations. Wrong order writes LEFT before redirecting;
after RIGHT deletion the retained LEFT alias still discriminates the two runs. -/
theorem word_vectors :
    cells (machine 2 42)=[w[40],w[32],w[16],w[16],w[24],w[42],w[2],w[99],w[7],w[8],w[7],w[9],w[10],w[9],w[11],w[12]] ∧
    observed (aliasLocalCode 1 td ts) (machine 2 42)=some
      ([w[40],w[32],w[16],w[24],w[24],w[42],w[2],w[99],w[7],w[8],w[7],w[9],w[10],w[9],w[11],w[12]],[w[77],w[88]]) ∧
    observed (aliasLocalCode 1 td ts ++ writeCode) (machine 2 42)=some
      ([w[40],w[32],w[16],w[24],w[24],w[42],w[2],w[99],w[7],w[8],w[7],w[9],w[10],w[42],w[11],w[12]],[w[77],w[88]]) ∧
    observed (aliasLocalCode 1 td ts ++ writeCode ++ clearCode) (machine 2 42)=some
      ([w[40],w[32],w[16],w[24],w[24],w[42],w[2],w[99],w[7],w[8],w[7],w[9],w[10],w[0],w[11],w[12]],[w[77],w[88]]) ∧
    observed (writeCode ++ aliasLocalCode 1 td ts ++ clearCode) (machine 2 42)=some
      ([w[40],w[32],w[16],w[24],w[24],w[42],w[2],w[99],w[7],w[8],w[42],w[9],w[10],w[0],w[11],w[12]],[w[77],w[88]]) ∧
    observed (aliasLocalCode 1 td ta ++ writeCode ++ clearCode) (machine 2 42)=some
      ([w[40],w[32],w[16],w[16],w[24],w[42],w[2],w[99],w[7],w[8],w[0],w[9],w[10],w[9],w[11],w[12]],[w[77],w[88]]) := by
  have hA : run (aliasLocalCode 1 td ts) (machine 2 42)=.ok (reboundWord 2 42) 0 := by rfl
  have hW := update_run (reboundWord 2 42) 24 2 42 (by decide) (by decide) (by decide) (by decide) rfl rfl rfl
  have hD := clear_run (writeMachine (reboundWord 2 42) 26 w[42]) 24 2 (by decide) (by decide) (by decide) (by decide) rfl rfl
  have hAW : run (aliasLocalCode 1 td ts ++ writeCode) (machine 2 42)=.ok (writeMachine (reboundWord 2 42) 26 w[42]) 0 := by
    rw [run_append_ok hA];exact hW
  have hAWD : run (aliasLocalCode 1 td ts ++ writeCode ++ clearCode) (machine 2 42)=.ok (writeMachine (writeMachine (reboundWord 2 42) 26 w[42]) 26 w[0]) 0 := by
    rw [run_append_ok hAW];exact hD
  have hOld := update_run (machine 2 42) 16 2 42 (by decide) (by decide) (by decide) (by decide) rfl rfl rfl
  have hOldCanonical : run writeCode (machine 2 42)=.ok (writeMachine (machine 2 42) 18 w[42]) 0 := by
    simpa only [wmod_of_lt (by decide : 42<W)] using hOld
  have hOldA : run (aliasLocalCode 1 td ts) (writeMachine (machine 2 42) 18 w[42])=
      .ok (writeMachine (writeMachine (machine 2 42) 18 w[42]) 3 w[24]) 0 := by rfl
  have hOldD := clear_run (writeMachine (writeMachine (machine 2 42) 18 w[42]) 3 w[24]) 24 2
    (by decide) (by decide) (by decide) (by decide) rfl rfl
  have hwrong : run (writeCode ++ aliasLocalCode 1 td ts ++ clearCode) (machine 2 42)=
      .ok (writeMachine (writeMachine (writeMachine (machine 2 42) 18 w[42]) 3 w[24]) 26 w[0]) 0 := by
    rw [List.append_assoc,run_append_ok hOldCanonical,run_append_ok hOldA];exact hOldD
  have hSame : run (aliasLocalCode 1 td ta) (machine 2 42)=.ok (writeMachine (machine 2 42) 3 w[16]) 0 := by rfl
  have hSameW := update_run (writeMachine (machine 2 42) 3 w[16]) 16 2 42 (by decide) (by decide) (by decide) (by decide) rfl rfl rfl
  have hSameD := clear_run (writeMachine (writeMachine (machine 2 42) 3 w[16]) 18 w[42]) 16 2 (by decide) (by decide) (by decide) (by decide) rfl rfl
  have hs : run (aliasLocalCode 1 td ta ++ writeCode ++ clearCode) (machine 2 42)=
      .ok (writeMachine (writeMachine (writeMachine (machine 2 42) 3 w[16]) 18 w[42]) 18 w[0]) 0 := by
    rw [List.append_assoc,run_append_ok hSame,run_append_ok hSameW];exact hSameD
  exact ⟨rfl,observed_ok hA,observed_ok hAW,observed_ok hAWD,observed_ok hwrong,observed_ok hs⟩

/-- True endpoint rejection occurs after the successful reference-local prefix.
Only that prefix machine is exposed; there is no post-revert machine. -/
theorem endpoint (p : Roadmap.Pipeline) :
    (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 Γ.length none
      (sourceUintFixedAliasReject sd ss si sv) (sy 3 42).1).run (.nil,(sy 3 42).2)=
        (.error (.revert (Source.panicData .index)),(.nil,(sy 3 42).2)) ∧
    Prog.run (state 3 42) (intrinsicUintFixedAliasReject td ts ti tv)=.error .revert ∧
    run (aliasLocalCode 1 td ts) (machine 3 42)=.ok (reboundWord 3 42) 0 ∧
    run (aliasLocalCode 1 td ts ++ writeCode) (machine 3 42)=.revert ∧
    (rebound 3 42).1.get sd=.memRef rfl 1 ∧ (rebound 3 42).1.get sa=.memRef rfl 0 ∧
    cells (reboundWord 3 42)=[w[40],w[32],w[16],w[24],w[24],w[42],w[3],w[99],w[7],w[8],w[7],w[9],w[10],w[9],w[11],w[12]] := by
  have h := source_uint_fixed_alias_reject (Source.SemanticsExamples.G0 p) F0 0 (sy 3 42) sd ss si sv 1
    (state 3 42) td ts ti tv right (u 3) (u 42) rfl rfl rfl rfl rfl rfl (represented_right 3 42)
    (by decide) SH (source_memOK 3 42) (initial_repr 3 42) (initial_allocator 3 42) (by decide)
  exact ⟨h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.2.1,rfl,rfl,rfl⟩

/-- At horizon6 the rebinding and material42 write really execute before the
third Source expression times out. The returned globals retain the changed
RIGHT object; this is not a transaction rollback theorem. -/
theorem late_timeout (p : Roadmap.Pipeline) :
    ∃ (out : Heap H) (z : Source.EMState E0 Γ) (mm : Machine),
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 Γ.length none
        (sourceUintFixedAliasProgram sd ss si sv) (sy 2 42).1).run (.nil,(sy 2 42).2)=
          (.error .timeout,(.nil,z.2)) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintFixedIndexedAssign sd si sv)).run (rebound 2 42)=
        (.ok (.val (sourceUint (u 42))),z) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (sourceUintFixedIndexedDelete sd si)).run z=(.error .timeout,z) ∧
      SourceUintFixedAt z 1 out right ∧
      [(out.get left).1,(out.get right).1,(out.get neighbor).1]=[[u 7,u 8,u 7],[u 9,u 10,u 42],[u 11,u 12]] ∧
      [z.2.heap.get 0,z.2.heap.get 1,z.2.heap.get 2]=
        [(sy 2 42).2.heap.get 0,some ⟨SA,sourceUintFixedObject (out.get right)⟩,(sy 2 42).2.heap.get 2] ∧
      run (aliasLocalCode 1 td ts ++ writeCode) (machine 2 42)=.ok mm 0 ∧
      Objects.StateRepr 1 1 8 (Frag.init Δ) ((reboundState 2 42).withHeap out) base mm ∧ Source.MemOK E0 SH z := by
  have ha := source_uint_fixed_alias_word (Source.SemanticsExamples.G0 p) F0 2 (sy 2 42) sd ss 1 rfl SH (source_memOK 2 42)
    (state 2 42) td ts right rfl (represented_right 2 42) (initial_repr 2 42) (initial_allocator 2 42) (by decide)
  obtain ⟨out,z,mm,hw,hs,he,hstmt,hi,hc,hr,hm,hmok,hl,hstack,hkeep⟩ :=
    resolved_uint_fixed_assign_word (Source.SemanticsExamples.G0 p) F0 0 (reboundState 2 42) right ha.2.2.2.2.1
      sd si sv td ti tv (u 2) (u 42) rfl rfl rfl rfl rfl rfl (by decide) ha.2.2.2.2.2.2.1 SH ha.2.2.2.2.2.1
  have hd : (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (sourceUintFixedIndexedDelete sd si)).run z=(.error .timeout,z) := by rfl
  have hds := source_expr_statement_error (Source.SemanticsExamples.G0 p) F0 2 Γ.length _ z z .timeout hd
  have hstmt' : (Source.execS (Source.SemanticsExamples.G0 p) F0 4 Γ.length none
      (.expr (sourceUintFixedIndexedAssign sd si sv) : Source.RStmt E0 [] false .body Γ Γ) (rebound 2 42).1).run (.nil,(rebound 2 42).2)=
        (.ok (.normal z.1),(.nil,z.2)) := by simpa only [hl] using hstmt
  have htail : (Source.execItems (Source.SemanticsExamples.G0 p) F0 5 Γ.length none
      (.stmt (.expr (sourceUintFixedIndexedAssign sd si sv)) (.stmt (.expr (sourceUintFixedIndexedDelete sd si)) .nil) : Source.RItems E0 [] false .body Γ Γ)
      (rebound 2 42).1).run (.nil,(rebound 2 42).2)=(.error .timeout,(.nil,z.2)) := by
    rw [Source.execItems,Source.Hoare.run_bind,hstmt']
    change (Source.execItems (Source.SemanticsExamples.G0 p) F0 4 Γ.length none
      (.stmt (.expr (sourceUintFixedIndexedDelete sd si)) .nil : Source.RItems E0 [] false .body Γ Γ) z.1 >>=
        fun o => Source.EM.lift (o.up Γ)).run (.nil,z.2)=_
    rw [Source.Hoare.run_bind,Source.execItems,Source.Hoare.run_bind,hds]
  have hwhole : (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 Γ.length none
      (sourceUintFixedAliasProgram sd ss si sv) (sy 2 42).1).run (.nil,(sy 2 42).2)=(.error .timeout,(.nil,z.2)) := by
    rw [sourceUintFixedAliasProgram,Source.execItems,Source.Hoare.run_bind,ha.2.1]
    change (Source.execItems (Source.SemanticsExamples.G0 p) F0 5 Γ.length none
      (.stmt (.expr (sourceUintFixedIndexedAssign sd si sv)) (.stmt (.expr (sourceUintFixedIndexedDelete sd si)) .nil) : Source.RItems E0 [] false .body Γ Γ)
      (rebound 2 42).1 >>= fun o => Source.EM.lift (o.up Γ)).run (.nil,(rebound 2 42).2)=_
    rw [Source.Hoare.run_bind,htail]
  have hv := indexedWrite_elems _ _ right .fixed (u 2) (u 42) hw
  have hf := ha.2.2.2.2.1.write_frames F0 2 (u 2) (u 42) (by decide) hw hs
  refine ⟨out,z,mm,hwhole,he,hd,hr,?_,?_,?_,hm,hmok⟩
  · rw [hf.2.1 left (by change (1 : Nat)≠0;decide),hf.2.1 neighbor (by change (1 : Nat)≠2;decide)]
    simp only [MObj.elems_fixed] at hv
    rw [hv];rfl
  · rw [hf.2.2.1 0 (by decide),hf.2.2.1 2 (by decide),hr]
  · rw [run_append_ok ha.2.2.2.1];exact hc

/-- Reusing the OLD pointer before redirecting materially writes LEFT, whereas
the reached program writes RIGHT. This is an actual Source/intrinsic/word
prefix counterexample, not a hypothetical corrupted output relation. -/
theorem stale_prefix (p : Roadmap.Pipeline) :
    ∃ (out : Heap H) (z : Source.EMState E0 Γ) (mm : Machine),
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintFixedIndexedAssign sd si sv)).run (sy 2 42)=
        (.ok (.val (sourceUint (u 42))),z) ∧
      Stmt.run (state 2 42) (.assignMem (.index .fixed (.var td rfl) (.simple (.local ti))) (.val (.simple (.local tv))))=
        .ok ⟨(state 2 42).withHeap out,List.prefix_refl _⟩ ∧
      run writeCode (machine 2 42)=.ok mm 0 ∧
      [(out.get left).1,(out.get right).1,(out.get neighbor).1]=[[u 7,u 8,u 42],[u 9,u 10,u 9],[u 11,u 12]] ∧
      SourceUintFixedAt z 0 out left ∧ z.1.get sa=.memRef rfl 0 ∧
      z.2.heap.get 1=(sy 2 42).2.heap.get 1 := by
  obtain ⟨out,z,mm,hw,hs,he,hstmt,hi,hc,hr,hm,hmok,hl,hstack,hkeep⟩ :=
    resolved_uint_fixed_assign_word (Source.SemanticsExamples.G0 p) F0 0 (state 2 42) left (represented_left 2 42)
      sd si sv td ti tv (u 2) (u 42) rfl rfl rfl rfl rfl rfl (by decide) (initial_repr 2 42) SH (source_memOK 2 42)
  have hv := indexedWrite_elems _ _ left .fixed (u 2) (u 42) hw
  have hf := (represented_left 2 42).write_frames F0 2 (u 2) (u 42) (by decide) hw hs
  refine ⟨out,z,mm,he,hi,hc,?_,hr,?_,hf.2.2.1 1 (by decide)⟩
  · rw [hf.2.1 right (by change (0 : Nat)≠1;decide),hf.2.1 neighbor (by change (0 : Nat)≠2;decide)]
    simp only [MObj.elems_fixed] at hv
    rw [hv];rfl
  · rw [hl];rfl

/-- Actual indexed reads discriminate the rebound local from the retained
OLD alias in both independent Source pipeline configurations. -/
theorem selected_reads (p : Roadmap.Pipeline) :
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local sd) (.local si) rfl)).run (sy 2 42)=
      (.ok (.val (sourceUint (u 7))),sy 2 42) ∧
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local sd) (.local si) rfl)).run (rebound 2 42)=
      (.ok (.val (sourceUint (u 9))),rebound 2 42) ∧
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local sa) (.local si) rfl)).run (rebound 2 42)=
      (.ok (.val (sourceUint (u 7))),rebound 2 42) ∧
    (u 7)≠u 9 ∧ left.id≠right.id := by
  have hr : SourceUintFixedAt (rebound 2 42) 1 hp right := represented_right 2 42
  have hl : SourceUintFixedAt (rebound 2 42) 0 hp left := represented_left 2 42
  exact ⟨(represented_left 2 42).eval_index (Source.SemanticsExamples.G0 p) F0 0 sd si (u 2) rfl rfl (by decide),
    hr.eval_index (Source.SemanticsExamples.G0 p) F0 0 sd si (u 2) rfl rfl (by decide),
    hl.eval_index (Source.SemanticsExamples.G0 p) F0 0 sa si (u 2) rfl rfl (by decide),by decide,by decide⟩

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedAliasControls.selected_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected_reads
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedAliasControls.initial_views' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms initial_views
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedAliasControls.alias_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms alias_cases
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedAliasControls.reached_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reached_program
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedAliasControls.word_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_vectors
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedAliasControls.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms endpoint
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedAliasControls.late_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms late_timeout
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedAliasControls.stale_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stale_prefix
end Solidity.Backend.MemoryOps.SourceUintFixedAliasControls
