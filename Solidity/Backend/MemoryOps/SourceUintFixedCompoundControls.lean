import Solidity.Backend.MemoryOps.SourceUintFixedCompoundSequence
import Solidity.Backend.MemoryOps.SourceUintFixedFuel
import Solidity.Backend.MemoryOps.SourceUintFixedCompoundBounds
import Solidity.Backend.MemoryOps.SourceUintFixedDeclaration
import Solidity.Evm.Correct
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.MemoryOps.SourceUintFixedCompoundControls
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

private def ay (k v : Nat) : Source.EMState E0 Γ := ((sy k v).1.set sd (.memRef rfl 1),(sy k v).2)
private def ast (k v : Nat) := (state k v).setLocal td (some right)
private def aw (k v : Nat) := writeMachine (machine k v) 3 w[24]
private def ac : List Instr := aliasLocalCode 1 td ts
private def addCode : List Instr := fixedUintAddCode (C := C) 1 td ti tv
private def aliasAdds : Source.RItems E0 [] false .body Γ Γ :=
  .stmt (.expr (sourceLocalAlias sd ss)) (sourceUintFixedAddTwice sd si sv)
private def typedAliasAdds : Prog C Δ Δ :=
  .cons (.rebindMem td (.alias (.var ts rfl))) (intrinsicUintFixedAddTwice td ti tv)

/-- Real rebound RIGHT9→51→93, not frozen9→51→51. The Source table, retained
LEFT and neighbour, full Objects allocator and word execution are derived. -/
theorem alias_updates (p : Roadmap.Pipeline) :
    ∃ (out1 out2 : Heap H) (z1 z2 : Source.EMState E0 Γ) (m1 m2 : Machine),
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 7 Γ.length none aliasAdds (sy 2 42).1).run (.nil,(sy 2 42).2)=
        (.ok (.normal z2.1),(.nil,z2.2)) ∧
      Prog.run (state 2 42) typedAliasAdds=.ok ⟨(ast 2 42).withHeap out2,List.prefix_refl _⟩ ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 4 (sourceUintFixedIndexedAdd sd si sv)).run (ay 2 42)=
        (.ok (.val (sourceUint (u 51))),z1) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintFixedIndexedAdd sd si sv)).run z1=
        (.ok (.val (sourceUint (u 93))),z2) ∧
      [(out1.get left).1,(out1.get right).1,(out1.get neighbor).1,(out2.get left).1,(out2.get right).1,(out2.get neighbor).1]=
        [[u 7,u 8,u 7],[u 9,u 10,u 51],[u 11,u 12],[u 7,u 8,u 7],[u 9,u 10,u 93],[u 11,u 12]] ∧
      [z1.2.heap.get 0,z1.2.heap.get 1,z1.2.heap.get 2,z2.2.heap.get 0,z2.2.heap.get 1,z2.2.heap.get 2]=
        [(sy 2 42).2.heap.get 0,some ⟨SA,sourceUintFixedObject (out1.get right)⟩,(sy 2 42).2.heap.get 2,
         (sy 2 42).2.heap.get 0,some ⟨SA,sourceUintFixedObject (out2.get right)⟩,(sy 2 42).2.heap.get 2] ∧
      SourceUintFixedAt z1 1 out1 right ∧ SourceUintFixedAt z2 1 out2 right ∧ z2.1=(ay 2 42).1 ∧
      [z2.1.get sd,z2.1.get sa,z2.1.get ss]=[.memRef rfl 1,.memRef rfl 0,.memRef rfl 1] ∧
      run addCode (aw 2 42)=.ok m1 0 ∧ run addCode m1=.ok m2 0 ∧
      run (ac ++ addCode ++ addCode) (machine 2 42)=.ok m2 0 ∧
      Objects.StateRepr 1 1 8 (Frag.init Δ) ((ast 2 42).withHeap out2) base m2 ∧
      Objects.AllocatorRepr out2 base 8 ⟨40,by decide⟩ m2 ∧ Source.MemOK E0 SH z1 ∧ Source.MemOK E0 SH z2 ∧
      m2.stack=[w[77],w[88]] ∧ m2.mem 0=w[40] ∧
      z2.2.ex=(sy 2 42).2.ex ∧ z2.2.events=(sy 2 42).2.events ∧ z2.2.logs=(sy 2 42).2.logs ∧ z2.2.fnLocals=(sy 2 42).2.fnLocals := by
  have hA := source_uint_fixed_alias_word (Source.SemanticsExamples.G0 p) F0 3 (sy 2 42) sd ss 1 rfl SH (source_memOK 2 42)
    (state 2 42) td ts right rfl (represented_right 2 42) (initial_repr 2 42) (initial_allocator 2 42) (by decide)
  obtain ⟨o1,o2,z1,z2,m1,m2,he1,he2,hitems,hprog,hw1,hw2,hc1,hc2,hwhole,hr1,hr2,hm2,ha2,hmok1,hmok2,hl1,hl2,hstack,hfree,hobj,haddr,hex,hev,hlog,hfn,hsource1⟩ :=
    resolved_uint_fixed_add_twice_word (Source.SemanticsExamples.G0 p) F0 0 Γ.length (ast 2 42) right hA.2.2.2.2.1
      sd si sv td ti tv (u 2) (u 42) rfl rfl rfl rfl rfl rfl
      (by simp only [Heap.len,MObj.elems_fixed];decide)
      (by simp only [MObj.elems_fixed];decide) (by simp only [MObj.elems_fixed];decide)
      SH hA.2.2.2.2.2.1 hA.2.2.2.2.2.2.1 hA.2.2.2.2.2.2.2.1 (by decide)
  have hsrc := source_items_cons_run (Source.SemanticsExamples.G0 p) F0 6 Γ.length _ _ (sy 2 42) (ay 2 42) z2 hA.2.1 hitems
  have htyped : Prog.run (state 2 42) typedAliasAdds=.ok ⟨(ast 2 42).withHeap o2,List.prefix_refl _⟩ := by
    rw [typedAliasAdds,Prog.run_cons_ok hA.2.2.1]
    change Except.map _ (Prog.run (ast 2 42) (intrinsicUintFixedAddTwice td ti tv))=_
    rw [hprog]
    rfl
  simp only [MObj.elems_fixed] at hw1 hw2 he1 he2
  change hp.writeAddr (.index right .fixed (u 2)) (u 51)=some o1 at hw1
  change o1.writeAddr (.index right .fixed (u 2)) (u 93)=some o2 at hw2
  have hv1 := indexedWrite_elems hp o1 right .fixed (u 2) (u 51) hw1
  have hv2 := indexedWrite_elems o1 o2 right .fixed (u 2) (u 93) hw2
  simp only [MObj.elems_fixed] at hv1 hv2
  have hout1 : (o1.get right).1=[u 9,u 10,u 51] := hv1
  have hout2 : (o2.get right).1=[u 9,u 10,u 93] := by rw [hv2,hout1];rfl
  have hframe1l := indexedWrite_frame hp o1 right .fixed (u 2) (u 51) hw1 left (by change (1 : Nat)≠0;decide)
  have hframe1n := indexedWrite_frame hp o1 right .fixed (u 2) (u 51) hw1 neighbor (by change (1 : Nat)≠2;decide)
  have hVec : [(o1.get left).1,(o1.get right).1,(o1.get neighbor).1,(o2.get left).1,(o2.get right).1,(o2.get neighbor).1]=
      [[u 7,u 8,u 7],[u 9,u 10,u 51],[u 11,u 12],[u 7,u 8,u 7],[u 9,u 10,u 93],[u 11,u 12]] := by
    rw [hframe1l,hframe1n,hobj left (by change (1 : Nat)≠0;decide),hobj neighbor (by change (1 : Nat)≠2;decide),hout1,hout2]
    rfl
  have hTable : [z1.2.heap.get 0,z1.2.heap.get 1,z1.2.heap.get 2,z2.2.heap.get 0,z2.2.heap.get 1,z2.2.heap.get 2]=
      [(sy 2 42).2.heap.get 0,some ⟨SA,sourceUintFixedObject (o1.get right)⟩,(sy 2 42).2.heap.get 2,
       (sy 2 42).2.heap.get 0,some ⟨SA,sourceUintFixedObject (o2.get right)⟩,(sy 2 42).2.heap.get 2] := by
    rw [hsource1 0 (by decide),hsource1 2 (by decide),haddr 0 (by decide),haddr 2 (by decide),hr1,hr2]
  have hLoc : [z2.1.get sd,z2.1.get sa,z2.1.get ss]=[.memRef rfl 1,.memRef rfl 0,.memRef rfl 1] := by rw [hl2];rfl
  have hWord : run (ac ++ addCode ++ addCode) (machine 2 42)=.ok m2 0 := by
    rw [List.append_assoc]
    change run (aliasLocalCode 1 td ts ++ (addCode ++ addCode)) (machine 2 42)=_
    rw [run_append_ok hA.2.2.2.1]
    exact hwhole
  exact ⟨o1,o2,z1,z2,m1,m2,hsrc,htyped,he1,he2,hVec,hTable,hr1,hr2,hl2,hLoc,hc1,hc2,hWord,hm2,ha2,hmok1,hmok2,hstack,hfree,hex,hev,hlog,hfn⟩

private def delta : Nat := W-10
private def maximum : PrimTy.uint.Denote := u (W-1)

/-- Material first update9+(W-10)=max, then ACTUAL reached max+(W-10)
overflows. Reusing initial9 would incorrectly succeed again. No suffix state is
claimed for typed/word errors; Source retains the actual max prefix globals. -/
theorem late_overflow (p : Roadmap.Pipeline) :
    ∃ (out : Heap H) (z : Source.EMState E0 Γ) (m1 : Machine),
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 7 Γ.length none aliasAdds (sy 2 delta).1).run (.nil,(sy 2 delta).2)=
        (.error (.revert (Source.panicData .arithmetic)),(.nil,z.2)) ∧
      Prog.run (state 2 delta) typedAliasAdds=.error .revert ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 4 (sourceUintFixedIndexedAdd sd si sv)).run (ay 2 delta)=
        (.ok (.val (sourceUint maximum)),z) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintFixedIndexedAdd sd si sv)).run z=
        (.error (.revert (Source.panicData .arithmetic)),z) ∧
      [(out.get left).1,(out.get right).1,(out.get neighbor).1]=[[u 7,u 8,u 7],[u 9,u 10,maximum],[u 11,u 12]] ∧
      [z.2.heap.get 0,z.2.heap.get 1,z.2.heap.get 2]=
        [(sy 2 delta).2.heap.get 0,some ⟨SA,sourceUintFixedObject (out.get right)⟩,(sy 2 delta).2.heap.get 2] ∧
      SourceUintFixedAt z 1 out right ∧ Source.MemOK E0 SH z ∧ z.1=(ay 2 delta).1 ∧
      run (ac ++ addCode) (machine 2 delta)=.ok m1 0 ∧ run addCode m1=.revert ∧
      run (ac ++ addCode ++ addCode) (machine 2 delta)=.revert ∧
      Objects.StateRepr 1 1 8 (Frag.init Δ) ((ast 2 delta).withHeap out) base m1 ∧
      Objects.AllocatorRepr out base 8 ⟨40,by decide⟩ m1 ∧ m1.stack=[w[77],w[88]] ∧ m1.mem 0=w[40] ∧
      z.2.ex=(sy 2 delta).2.ex ∧ z.2.events=(sy 2 delta).2.events ∧ z.2.logs=(sy 2 delta).2.logs ∧ z.2.fnLocals=(sy 2 delta).2.fnLocals ∧
      (u 9).1+(u delta).1=maximum.1 ∧ PrimTy.uint.inRange (maximum.1+(u delta).1)≠true ∧ maximum≠u 9 := by
  have hA := source_uint_fixed_alias_word (Source.SemanticsExamples.G0 p) F0 3 (sy 2 delta) sd ss 1 rfl SH (source_memOK 2 delta)
    (state 2 delta) td ts right rfl (represented_right 2 delta) (initial_repr 2 delta) (initial_allocator 2 delta) (by decide)
  obtain ⟨o1,z1,m1,he1,he2,hitems,hprog,hw1,hc1,hc2,hwhole,hr1,hm1,ha1,hmok1,hl1,hstack,hfree,hobj,haddr,hex,hev,hlog,hfn⟩ :=
    resolved_uint_fixed_add_late_overflow_word (Source.SemanticsExamples.G0 p) F0 0 Γ.length (by rfl) (ast 2 delta) right hA.2.2.2.2.1
      sd si sv td ti tv (u 2) (u delta) rfl rfl rfl rfl rfl rfl
      (by simp only [Heap.len,MObj.elems_fixed];decide)
      (by simp only [MObj.elems_fixed];decide) (by simp only [MObj.elems_fixed];decide)
      SH hA.2.2.2.2.2.1 hA.2.2.2.2.2.2.1 hA.2.2.2.2.2.2.2.1 (by decide)
  change (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 Γ.length none (sourceUintFixedAddTwice sd si sv) (ay 2 delta).1).run (.nil,(ay 2 delta).2)=
    (.error (.revert (Source.panicData .arithmetic)),(.nil,z1.2)) at hitems
  have hsrc : (Source.execItems (Source.SemanticsExamples.G0 p) F0 7 Γ.length none aliasAdds (sy 2 delta).1).run (.nil,(sy 2 delta).2)=
      (.error (.revert (Source.panicData .arithmetic)),(.nil,z1.2)) := by
    rw [aliasAdds,Source.execItems,Source.Hoare.run_bind,hA.2.1]
    change (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 Γ.length none (sourceUintFixedAddTwice sd si sv) (ay 2 delta).1 >>=
      fun o => Source.EM.lift (o.up Γ)).run (.nil,(ay 2 delta).2)=_
    rw [Source.Hoare.run_bind,hitems]
  have htyped : Prog.run (state 2 delta) typedAliasAdds=.error .revert := by
    rw [typedAliasAdds,Prog.run_cons_ok hA.2.2.1]
    change Except.map _ (Prog.run (ast 2 delta) (intrinsicUintFixedAddTwice td ti tv))=_
    rw [hprog];rfl
  simp only [MObj.elems_fixed] at hw1 he1
  change hp.writeAddr (.index right .fixed (u 2)) maximum=some o1 at hw1
  have hv := indexedWrite_elems hp o1 right .fixed (u 2) maximum hw1
  simp only [MObj.elems_fixed] at hv
  have hout : (o1.get right).1=[u 9,u 10,maximum] := hv
  have hVec : [(o1.get left).1,(o1.get right).1,(o1.get neighbor).1]=[[u 7,u 8,u 7],[u 9,u 10,maximum],[u 11,u 12]] := by
    rw [hobj left (by change (1 : Nat)≠0;decide),hobj neighbor (by change (1 : Nat)≠2;decide),hout];rfl
  have hTable : [z1.2.heap.get 0,z1.2.heap.get 1,z1.2.heap.get 2]=
      [(sy 2 delta).2.heap.get 0,some ⟨SA,sourceUintFixedObject (o1.get right)⟩,(sy 2 delta).2.heap.get 2] := by
    rw [haddr 0 (by decide),haddr 2 (by decide),hr1]
  have hPrefix : run (ac ++ addCode) (machine 2 delta)=.ok m1 0 := by
    change run (aliasLocalCode 1 td ts ++ addCode) (machine 2 delta)=_
    rw [run_append_ok hA.2.2.2.1];exact hc1
  have hWord : run (ac ++ addCode ++ addCode) (machine 2 delta)=.revert := by
    rw [run_append_ok hPrefix];exact hc2
  exact ⟨o1,z1,m1,hsrc,htyped,he1,he2,hVec,hTable,hr1,hmok1,hl1,hPrefix,hc2,hWord,hm1,ha1,hstack,hfree,hex,hev,hlog,hfn,by decide,by decide,by decide⟩

/-- Endpoint Source panic, intrinsic failure and whole target revert are derived
from the actual fixed bound; the insufficient Source horizon is distinct. -/
theorem bounds_timeout (p : Roadmap.Pipeline) :
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintFixedIndexedAdd sd si sv)).run (sy 3 42)=
      (.error (.revert (Source.panicData .index)),sy 3 42) ∧
    Stmt.run (state 3 42) (.opAssign .add rfl rfl (.mindex .fixed (.var td rfl) (.local ti)) (.simple (.local tv)))=.error .revert ∧
    run addCode (machine 3 42)=.revert ∧
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (sourceUintFixedIndexedAdd sd si sv)).run (sy 2 42)=
      (.error .timeout,sy 2 42) := by
  have h := resolved_uint_fixed_add_bounds_word (Source.SemanticsExamples.G0 p) F0 0 (state 3 42) left (represented_left 3 42)
    sd si sv td ti tv (u 3) (u 42) rfl rfl rfl rfl rfl rfl (by decide) (initial_repr 3 42)
  exact ⟨h.1,h.2.1,h.2.2,source_uint_fixed_add_timeout (Source.SemanticsExamples.G0 p) F0 (sy 2 42) sd si sv⟩

private def cells (m : Machine) : List Word :=
  [m.mem 0,m.mem 1,m.mem 2,m.mem 3,m.mem 4,m.mem 5,m.mem 6,m.mem 15,
   m.mem 16,m.mem 17,m.mem 18,m.mem 24,m.mem 25,m.mem 26,m.mem 32,m.mem 33,m.mem 7,m.mem 40,m.mem 41,m.mem 42]
private def observed (code : List Instr) (m : Machine) : Option (List Word × List Word) :=
  match run code m with | .ok out 0 => some (cells out,out.stack) | _ => none
private theorem observed_ok {code : List Instr} {m out : Machine} (h : run code m=.ok out 0) :
    observed code m=some (cells out,out.stack) := by unfold observed;rw [h]
private def rd : List Instr := [.mload 3] ++ [.mload 6] ++ Objects.readCode (.fixed : ArrTy A (.prim .uint))
private theorem read_run (m : Machine) (a k old : Fin W) (hk : k.val<3) (hs : a.val+k.val<W)
    (hp : m.mem 3=.val a) (hi : m.mem 6=.val k) (hc : m.mem (a.val+k.val)=.val old) :
    run rd m=.ok (m.push (.val old)) 0 := by
  change run ([.mload 3] ++ ([.mload 6] ++ Objects.readCode (.fixed : ArrTy A (.prim .uint)))) m=_
  rw [run_append_ok (show run [.mload 3] m=.ok (m.push (.val a)) 0 from by change Out.ok (m.push (m.mem 3)) 0=_;rw [hp])]
  rw [run_append_ok (show run [.mload 6] (m.push (.val a))=.ok ((m.push (.val a)).push (.val k)) 0 from by change Out.ok ((m.push (.val a)).push (m.mem 6)) 0=_;rw [hi])]
  have ha := Objects.fixedAddr_run m a k 3
  rw [if_pos hk] at ha
  change run (Objects.fixedAddrCode 3 ++ [.mloadAt]) ((m.push (.val a)).push (.val k))=_
  rw [run_append_ok ha]
  simp only [run,Machine.push,exec_cons_zero,Instr.step,wmod_of_lt hs,Out.ok_bind,exec_nil,hc,Machine.next]
private theorem add_run (m : Machine) (a k old v : Fin W) (hk : k.val<3) (hs : a.val+k.val<W)
    (hp : m.mem 3=.val a) (hi : m.mem 6=.val k) (hv : m.mem 5=.val v) (hc : m.mem (a.val+k.val)=.val old)
    (hadd : old.val+v.val<W) :
    run addCode m=.ok (writeMachine m (a.val+k.val) (.val ⟨old.val+v.val,hadd⟩)) 0 := by
  have hr := read_run m a k old hk hs hp hi hc
  have hvalue : run (binaryCode .uint .add rd [.mload 5]) m=.ok (m.push (.val ⟨old.val+v.val,hadd⟩)) 0 := by
    change run (rd ++ ([.mload 5] ++ uTail .add)) m=_
    rw [run_append_ok hr]
    rw [run_append_ok (show run [.mload 5] (m.push (.val old))=.ok ((m.push (.val old)).push (.val v)) 0 from by change Out.ok ((m.push (.val old)).push (m.mem 5)) 0=_;rw [hv])]
    exact (add_tail m m.stack old.isLt v.isLt).trans (by rw [dif_pos hadd];rfl)
  change run ((binaryCode .uint .add rd [.mload 5]) ++ ([.mload 3] ++ ([.mload 6] ++ Objects.writeCode (.fixed : ArrTy A (.prim .uint))))) m=_
  rw [run_append_ok hvalue]
  rw [run_append_ok (show run [.mload 3] (m.push (.val ⟨old.val+v.val,hadd⟩))=.ok ((m.push (.val ⟨old.val+v.val,hadd⟩)).push (.val a)) 0 from by change Out.ok ((m.push (.val ⟨old.val+v.val,hadd⟩)).push (m.mem 3)) 0=_;rw [hp])]
  rw [run_append_ok (show run [.mload 6] ((m.push (.val ⟨old.val+v.val,hadd⟩)).push (.val a))=.ok (((m.push (.val ⟨old.val+v.val,hadd⟩)).push (.val a)).push (.val k)) 0 from by change Out.ok (((m.push (.val ⟨old.val+v.val,hadd⟩)).push (.val a)).push (m.mem 6)) 0=_;rw [hi])]
  have ha := Objects.fixedAddr_run (m.push (.val ⟨old.val+v.val,hadd⟩)) a k 3
  rw [if_pos hk] at ha
  change run (Objects.fixedAddrCode 3 ++ [.mstoreAt]) (((m.push (.val ⟨old.val+v.val,hadd⟩)).push (.val a)).push (.val k))=_
  rw [run_append_ok ha]
  simp only [run,Machine.push,exec_cons_zero,Instr.step,wmod_of_lt hs,Out.ok_bind,exec_nil,writeMachine]
private theorem add_reject (m : Machine) (a k old v : Fin W) (hk : k.val<3) (hs : a.val+k.val<W)
    (hp : m.mem 3=.val a) (hi : m.mem 6=.val k) (hv : m.mem 5=.val v) (hc : m.mem (a.val+k.val)=.val old)
    (hadd : ¬old.val+v.val<W) : run addCode m=.revert := by
  have hr := read_run m a k old hk hs hp hi hc
  have hvalue : run (binaryCode .uint .add rd [.mload 5]) m=.revert := by
    change run (rd ++ ([.mload 5] ++ uTail .add)) m=_
    rw [run_append_ok hr]
    rw [run_append_ok (show run [.mload 5] (m.push (.val old))=.ok ((m.push (.val old)).push (.val v)) 0 from by change Out.ok ((m.push (.val old)).push (m.mem 5)) 0=_;rw [hv])]
    exact (add_tail m m.stack old.isLt v.isLt).trans (by rw [dif_neg hadd])
  change run ((binaryCode .uint .add rd [.mload 5]) ++ ([.mload 3] ++ ([.mload 6] ++ Objects.writeCode (.fixed : ArrTy A (.prim .uint))))) m=_
  exact run_append_revert hvalue

/-- Complete20word prefix/final vectors from ACTUAL whole word executions.
Skipping the alias targets LEFT7→49→91, rather than selected RIGHT9→51→93. -/
theorem word_vectors :
    observed (ac ++ addCode) (machine 2 42)=some
      ([w[40],w[32],w[16],w[24],w[24],w[42],w[2],w[99],w[7],w[8],w[7],w[9],w[10],w[51],w[11],w[12],w[0],w[0],w[0],w[0]],[w[77],w[88]]) ∧
    observed (ac ++ addCode ++ addCode) (machine 2 42)=some
      ([w[40],w[32],w[16],w[24],w[24],w[42],w[2],w[99],w[7],w[8],w[7],w[9],w[10],w[93],w[11],w[12],w[0],w[0],w[0],w[0]],[w[77],w[88]]) ∧
    observed (addCode ++ addCode) (machine 2 42)=some
      ([w[40],w[32],w[16],w[16],w[24],w[42],w[2],w[99],w[7],w[8],w[91],w[9],w[10],w[9],w[11],w[12],w[0],w[0],w[0],w[0]],[w[77],w[88]]) ∧
    observed (ac ++ addCode) (machine 2 delta)=some
      ([w[40],w[32],w[16],w[24],w[24],.val (wmod delta),w[2],w[99],w[7],w[8],w[7],w[9],w[10],.val (wmod (W-1)),w[11],w[12],w[0],w[0],w[0],w[0]],[w[77],w[88]]) ∧
    run (ac ++ addCode ++ addCode) (machine 2 delta)=.revert ∧
    (u 93)≠u 51 := by
  have hA : run ac (machine 2 42)=.ok (aw 2 42) 0 := by rfl
  have h1 := add_run (aw 2 42) ⟨24,by decide⟩ ⟨2,by decide⟩ ⟨9,by decide⟩ ⟨42,by decide⟩ (by decide) (by decide) rfl rfl rfl rfl (by decide)
  have h2 := add_run (writeMachine (aw 2 42) 26 w[51]) ⟨24,by decide⟩ ⟨2,by decide⟩ ⟨51,by decide⟩ ⟨42,by decide⟩ (by decide) (by decide) rfl rfl rfl rfl (by decide)
  have hA1 : run (ac ++ addCode) (machine 2 42)=.ok (writeMachine (aw 2 42) 26 w[51]) 0 := by rw [run_append_ok hA];exact h1
  have hA12 : run (ac ++ addCode ++ addCode) (machine 2 42)=.ok (writeMachine (writeMachine (aw 2 42) 26 w[51]) 26 w[93]) 0 := by rw [run_append_ok hA1];exact h2
  have hskip1 := add_run (machine 2 42) ⟨16,by decide⟩ ⟨2,by decide⟩ ⟨7,by decide⟩ ⟨42,by decide⟩ (by decide) (by decide) rfl rfl rfl rfl (by decide)
  have hskip2 := add_run (writeMachine (machine 2 42) 18 w[49]) ⟨16,by decide⟩ ⟨2,by decide⟩ ⟨49,by decide⟩ ⟨42,by decide⟩ (by decide) (by decide) rfl rfl rfl rfl (by decide)
  have hskip : run (addCode ++ addCode) (machine 2 42)=.ok (writeMachine (writeMachine (machine 2 42) 18 w[49]) 18 w[91]) 0 := by rw [run_append_ok hskip1];exact hskip2
  have hD : run ac (machine 2 delta)=.ok (aw 2 delta) 0 := by rfl
  have hmax1 := add_run (aw 2 delta) ⟨24,by decide⟩ ⟨2,by decide⟩ ⟨9,by decide⟩ ⟨delta,by decide⟩ (by decide) (by decide) rfl rfl rfl rfl (by decide)
  have hmax : run (ac ++ addCode) (machine 2 delta)=.ok (writeMachine (aw 2 delta) 26 (.val (wmod (W-1)))) 0 := by
    rw [run_append_ok hD]
    exact hmax1
  have hfail := add_reject (writeMachine (aw 2 delta) 26 (.val (wmod (W-1)))) ⟨24,by decide⟩ ⟨2,by decide⟩ ⟨W-1,by decide⟩ ⟨delta,by decide⟩ (by decide) (by decide) rfl rfl rfl rfl (by decide)
  have hWordFail : run (ac ++ addCode ++ addCode) (machine 2 delta)=.revert := by rw [run_append_ok hmax];exact hfail
  exact ⟨observed_ok hA1,observed_ok hA12,observed_ok hskip,observed_ok hmax,hWordFail,by decide⟩

private def cg (n : Nat) := hp.allocDefault (.fixed (.prim .uint) n) rfl
private def cf (n : Nat) := (cg n).val
private def cs (n k : Nat) := ((state k 42).adopt (cg n)).1.push (t := .mem (.fixed (.prim .uint) n)) (some (cf n))
private def cy (n k : Nat) : Source.EMState E0 ((.array .memory (.int .u256) (some n))::Γ) :=
  (.cons (.memRef rfl 3) (sy k 42).1,{(sy k 42).2 with heap := ((sy k 42).2.heap.alloc ⟨.array .memory (.int .u256) (some n),sourceUintFixedZero n⟩).1})
private def declAdds (n : Nat) : Source.RItems E0 [] false .body Γ ((.array .memory (.int .u256) (some n))::Γ) :=
  .stmt (.declVar (.array .memory (.int .u256) (some n))) (sourceUintFixedAddTwice .here (.there si) (.there sv))
private def typedDeclAdds (n : Nat) : Prog C Δ (.mem (.fixed (.prim .uint) n)::Δ) :=
  .cons (.declMem (.fixed (.prim .uint) n) (.user "fixedCompoundFresh") none rfl rfl)
    (intrinsicUintFixedAddTwice .here (.there ti) (.there tv))
private def cc (n : Nat) : List Instr := Objects.defaultDeclareCode (Γ := Δ) (Objects.DefaultBuilder.fixedPrimitive .uint n).code 1
private def ca (n : Nat) : List Instr := fixedUintAddCode (C := C) 1 (.here : Idx (.mem (.fixed (.prim .uint) n)::Δ) (.mem (.fixed (.prim .uint) n))) (.there ti) (.there tv)

/-- REAL positive fixed default declaration followed by reached0→42→84.
Runtime n/k are unrestricted beyond the existing valid length/index/space facts;
Source cons, typed weakening/push and ORIGINAL parameter count are all derived. -/
theorem declared_updates (p : Roadmap.Pipeline) (n k : Nat) (hn : 0<n) (hk : k<n) (hs : 40+max 1 n<W) :
    ∃ (base' : Nat → Fin W) (m0 m1 m2 : Machine) (o1 o2 : Heap (cg n).H')
      (z1 z2 : Source.EMState E0 ((.array .memory (.int .u256) (some n))::Γ)),
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 (n+7) Γ.length none (declAdds n) (sy k 42).1).run (.nil,(sy k 42).2)=
        (.ok (.normal z2.1),(.nil,z2.2)) ∧
      Prog.run (state k 42) (typedDeclAdds n)=.ok ⟨(cs n k).withHeap o2,(cg n).ext⟩ ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 (n+4) (sourceUintFixedIndexedAdd .here (.there si) (.there sv))).run (cy n k)=
        (.ok (.val (sourceUint (u 42))),z1) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 (n+3) (sourceUintFixedIndexedAdd .here (.there si) (.there sv))).run z1=
        (.ok (.val (sourceUint (u 84))),z2) ∧
      [(o1.get (cf n)).1,(o2.get (cf n)).1]=[(List.replicate n (PrimTy.dflt .uint)).set k (u 42),(List.replicate n (PrimTy.dflt .uint)).set k (u 84)] ∧
      [(o2.get (left.wk (cg n).ext)).1,(o2.get (right.wk (cg n).ext)).1,(o2.get (neighbor.wk (cg n).ext)).1]=
        [[u 7,u 8,u 7],[u 9,u 10,u 9],[u 11,u 12]] ∧
      [z1.2.heap.get 0,z1.2.heap.get 1,z1.2.heap.get 2,z2.2.heap.get 0,z2.2.heap.get 1,z2.2.heap.get 2]=
        [(sy k 42).2.heap.get 0,(sy k 42).2.heap.get 1,(sy k 42).2.heap.get 2,(sy k 42).2.heap.get 0,(sy k 42).2.heap.get 1,(sy k 42).2.heap.get 2] ∧
      SourceUintFixedAt z1 3 o1 (cf n) ∧ SourceUintFixedAt z2 3 o2 (cf n) ∧
      z2.1=(cy n k).1 ∧ z2.1.get .here=.memRef rfl 3 ∧
      [z2.1.get (.there sd),z2.1.get (.there sa)]=[.memRef rfl 0,.memRef rfl 0] ∧
      (cf n).id=3 ∧ (cf n).id≠(left.wk (cg n).ext).id ∧
      run (cc n) (machine k 42)=.ok m0 0 ∧ run (ca n) m0=.ok m1 0 ∧ run (ca n) m1=.ok m2 0 ∧
      run (cc n ++ ca n ++ ca n) (machine k 42)=.ok m2 0 ∧
      Objects.StateRepr 1 1 8 ((Frag.init Δ).push (.mem (.fixed (.prim .uint) n)) .ok) ((cs n k).withHeap o2) base' m2 ∧
      Objects.AllocatorRepr o2 base' 8 ⟨40+max 1 n,hs⟩ m2 ∧ Source.MemOK E0 SH z1 ∧ Source.MemOK E0 SH z2 ∧
      m2.stack=[w[77],w[88]] ∧ m2.mem 0=.val ⟨40+max 1 n,hs⟩ ∧
      z2.2.ex=(sy k 42).2.ex ∧ z2.2.events=(sy k 42).2.events ∧ z2.2.logs=(sy k 42).2.logs ∧ z2.2.fnLocals=(sy k 42).2.fnLocals := by
  have hkw : k<W := by have hn' := Nat.le_max_right 1 n;omega
  have hki : (u k).1.toNat=k := by change (wmod k).val=k;exact Nat.mod_eq_of_lt hkw
  obtain ⟨base',m0,hd0,ht0,hc0,hr0,hmok0,hm0,ha0,hbase,hstack0,hid,hne,hsource0⟩ :=
    source_uint_fixed_declaration_word (Source.SemanticsExamples.G0 p) F0 (sy k 42) (state k 42) n hn SH (source_memOK k 42)
      (initial_repr k 42) (initial_allocator k 42) (by decide) hs (by decide)
  have hz := (source_uint_fixed_intrinsic (sy k 42) hp n hn).2.1
  change MObj.elems .fixed ((cg n).heap.get (cf n))=List.replicate n (PrimTy.dflt .uint) at hz
  have hbound : (u k).1.toNat<(cg n).heap.len (cf n) .fixed := by
    change (u k).1.toNat<(MObj.elems .fixed ((cg n).heap.get (cf n))).length
    rw [hz,List.length_replicate,hki];exact hk
  have hlookup : (MObj.elems .fixed ((cg n).heap.get (cf n)))[(u k).1.toNat]?=some (PrimTy.dflt .uint) := by
    rw [hz]
    exact List.getElem?_replicate_of_lt (by rw [hki];exact hk)
  have hold : (MObj.elems .fixed ((cg n).heap.get (cf n)))[(u k).1.toNat]=PrimTy.dflt .uint :=
    Option.some.inj ((List.getElem?_eq_getElem hbound).symm.trans hlookup)
  have hadd : PrimTy.uint.inRange ((MObj.elems .fixed ((cg n).heap.get (cf n)))[(u k).1.toNat].1+(u 42).1)=true := by rw [hold];decide
  have htwo : PrimTy.uint.inRange (((MObj.elems .fixed ((cg n).heap.get (cf n)))[(u k).1.toNat].1+(u 42).1)+(u 42).1)=true := by rw [hold];decide
  have hit : TEnv.get (.there ti) (cs n k).env=u k := by
    change TEnv.get ti (TEnv.wk (cg n).ext Δ (state k 42).env)=_
    rw [TEnv.get_wk];rfl
  have hvt : TEnv.get (.there tv) (cs n k).env=u 42 := by
    change TEnv.get tv (TEnv.wk (cg n).ext Δ (state k 42).env)=_
    rw [TEnv.get_wk];rfl
  obtain ⟨o1,o2,z1,z2,m1,m2,he1,he2,hitems,hprog,hw1,hw2,hc1,hc2,hwhole,hr1,hr2,hm2,ha2,hmok1,hmok2,hl1,hl2,hstack,hfree,hobj,haddr,hex,hev,hlog,hfn,haddr1⟩ :=
    resolved_uint_fixed_add_twice_word (Source.SemanticsExamples.G0 p) F0 n Γ.length (cs n k) (cf n) hr0
      .here (.there si) (.there sv) .here (.there ti) (.there tv) (u k) (u 42)
      rfl rfl rfl rfl hit hvt hbound hadd htwo SH hmok0 hm0 ha0 (by decide)
  have hone : (⟨(MObj.elems .fixed ((cg n).heap.get (cf n)))[(u k).1.toNat].1+(u 42).1,hadd⟩ : PrimTy.uint.Denote)=u 42 := by
    apply Subtype.ext
    change (MObj.elems .fixed ((cg n).heap.get (cf n)))[(u k).1.toNat].1+(u 42).1=(u 42).1
    rw [hold];rfl
  have hsecond : (⟨((MObj.elems .fixed ((cg n).heap.get (cf n)))[(u k).1.toNat].1+(u 42).1)+(u 42).1,htwo⟩ : PrimTy.uint.Denote)=u 84 := by
    apply Subtype.ext
    change ((MObj.elems .fixed ((cg n).heap.get (cf n)))[(u k).1.toNat].1+(u 42).1)+(u 42).1=(u 84).1
    rw [hold];rfl
  dsimp only [cs,State.push,State.adopt] at hw1 hw2 he1 he2
  rw [hone] at hw1 he1
  rw [hsecond] at hw2 he2
  have hd := source_decl_statement_run (Source.SemanticsExamples.G0 p) F0 (n+5) Γ.length (sy k 42)
    ((sy k 42).1,{(sy k 42).2 with heap := ((sy k 42).2.heap.alloc ⟨.array .memory (.int .u256) (some n),sourceUintFixedZero n⟩).1})
    (.memRef rfl 3) (source_uint_fixed_zeroVal_slack (sy k 42) n 2)
  change (Source.execItems (Source.SemanticsExamples.G0 p) F0 (n+6) Γ.length none (sourceUintFixedAddTwice .here (.there si) (.there sv)) (cy n k).1).run (.nil,(cy n k).2)=
    (.ok (.normal z2.1),(.nil,z2.2)) at hitems
  have hsrc : (Source.execItems (Source.SemanticsExamples.G0 p) F0 (n+7) Γ.length none (declAdds n) (sy k 42).1).run (.nil,(sy k 42).2)=
      (.ok (.normal z2.1),(.nil,z2.2)) := by
    rw [declAdds,Source.execItems,Source.Hoare.run_bind,hd]
    change (Source.execItems (Source.SemanticsExamples.G0 p) F0 (n+6) Γ.length none (sourceUintFixedAddTwice .here (.there si) (.there sv)) (cy n k).1 >>= fun o => Source.EM.lift (o.up Γ)).run (.nil,(cy n k).2)=_
    rw [Source.Hoare.run_bind,hitems];rfl
  have htyped : Prog.run (state k 42) (typedDeclAdds n)=.ok ⟨(cs n k).withHeap o2,(cg n).ext⟩ := by
    have ht : Stmt.run (state k 42) (.declMem (.fixed (.prim .uint) n) (.user "fixedCompoundFresh") none rfl rfl)=.ok ⟨cs n k,(cg n).ext⟩ := ht0
    rw [typedDeclAdds,Prog.run_cons_ok ht]
    change Except.map _ (Prog.run (cs n k) (intrinsicUintFixedAddTwice .here (.there ti) (.there tv)))=_
    rw [hprog];rfl
  have hv1 := indexedWrite_elems (cg n).heap o1 (cf n) .fixed (u k) (u 42) hw1
  have hv2 := indexedWrite_elems o1 o2 (cf n) .fixed (u k) (u 84) hw2
  have hVec1 : (o1.get (cf n)).1=(List.replicate n (PrimTy.dflt .uint)).set k (u 42) := by
    simpa only [MObj.elems_fixed,hz,hki] using hv1
  have hVec2 : (o2.get (cf n)).1=(List.replicate n (PrimTy.dflt .uint)).set k (u 84) := by
    simp only [MObj.elems_fixed] at hv2
    rw [hv2,hVec1,hki,List.set_set]
  have hg : Heap.Keeps (cg n).ext hp (cg n).heap := (source_uint_fixed_intrinsic (sy k 42) hp n hn).2.2.1
  have hOld : [(o2.get (left.wk (cg n).ext)).1,(o2.get (right.wk (cg n).ext)).1,(o2.get (neighbor.wk (cg n).ext)).1]=
      [[u 7,u 8,u 7],[u 9,u 10,u 9],[u 11,u 12]] := by
    rw [hobj (left.wk (cg n).ext) (hne left),hobj (right.wk (cg n).ext) (hne right),hobj (neighbor.wk (cg n).ext) (hne neighbor)]
    change [((cg n).heap.get (left.wk (cg n).ext)).1,((cg n).heap.get (right.wk (cg n).ext)).1,((cg n).heap.get (neighbor.wk (cg n).ext)).1]=_
    rw [hg left,hg right,hg neighbor];rfl
  have hgetL : (sy k 42).2.heap.get 0≠none := by rw [represented_left k 42];exact Option.some_ne_none _
  have hgetR : (sy k 42).2.heap.get 1≠none := by rw [represented_right k 42];exact Option.some_ne_none _
  have hgetN : (sy k 42).2.heap.get 2≠none := by rw [represented_neighbor k 42];exact Option.some_ne_none _
  have hs1 : ∀ a,(sy k 42).2.heap.get a≠none → z1.2.heap.get a=(sy k 42).2.heap.get a := by
    intro a ha
    exact (haddr1 a (Ne.symm (hsource0 a ha).1)).trans (hsource0 a ha).2
  have hs2 : ∀ a,(sy k 42).2.heap.get a≠none → z2.2.heap.get a=(sy k 42).2.heap.get a := by
    intro a ha
    exact (haddr a (Ne.symm (hsource0 a ha).1)).trans (hsource0 a ha).2
  have hTable : [z1.2.heap.get 0,z1.2.heap.get 1,z1.2.heap.get 2,z2.2.heap.get 0,z2.2.heap.get 1,z2.2.heap.get 2]=
      [(sy k 42).2.heap.get 0,(sy k 42).2.heap.get 1,(sy k 42).2.heap.get 2,(sy k 42).2.heap.get 0,(sy k 42).2.heap.get 1,(sy k 42).2.heap.get 2] := by
    rw [hs1 0 hgetL,hs1 1 hgetR,hs1 2 hgetN,hs2 0 hgetL,hs2 1 hgetR,hs2 2 hgetN]
  have hNewLocal : z2.1.get .here=.memRef rfl 3 := by rw [hl2];rfl
  have hLoc : [z2.1.get (.there sd),z2.1.get (.there sa)]=[.memRef rfl 0,.memRef rfl 0] := by rw [hl2];rfl
  have hWord : run (cc n ++ ca n ++ ca n) (machine k 42)=.ok m2 0 := by
    rw [List.append_assoc,cc,run_append_ok hc0]
    exact hwhole
  exact ⟨base',m0,m1,m2,o1,o2,z1,z2,hsrc,htyped,he1,he2,by rw [hVec1,hVec2],hOld,hTable,hr1,hr2,hl2,hNewLocal,hLoc,hid,hne left,hc0,hc1,hc2,hWord,hm2,ha2,hmok1,hmok2,hstack.trans hstack0,ha2.free.cell,hex,hev,hlog,hfn⟩

/-- Length33/index32 actually updates the last fresh cell. Every target payload
word is observed in order via Fin33; endpoint33 and stale old-length3 local fail
at the reached state. Logical indices are not a physical-byte encoding claim. -/
theorem boundary_reads (p : Roadmap.Pipeline) :
    ∃ (base' : Nat → Fin W) (m2 : Machine) (o1 o2 : Heap (cg 33).H')
      (z1 z2 : Source.EMState E0 ((.array .memory (.int .u256) (some 33))::Γ)),
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 40 Γ.length none (declAdds 33) (sy 32 42).1).run (.nil,(sy 32 42).2)=
        (.ok (.normal z2.1),(.nil,z2.2)) ∧
      SourceUintFixedAt z1 3 o1 (cf 33) ∧ SourceUintFixedAt z2 3 o2 (cf 33) ∧
      (Source.memElem (E := E0) (Γ := (.array .memory (.int .u256) (some 33))::Γ) 3 32 (.int .u256)).run z1=(.ok (sourceUint (u 42)),z1) ∧
      (Source.memElem (E := E0) (Γ := (.array .memory (.int .u256) (some 33))::Γ) 3 32 (.int .u256)).run z2=(.ok (sourceUint (u 84)),z2) ∧
      (Source.memElem (E := E0) (Γ := (.array .memory (.int .u256) (some 33))::Γ) 3 33 (.int .u256)).run z2=
        (.error (.revert (Source.panicData .index)),z2) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintFixedIndexedAdd (.there sd) (.there si) (.there sv))).run z2=
        (.error (.revert (Source.panicData .index)),z2) ∧
      (∀ j : Fin 33,m2.mem ((base' (cf 33).id).val+j.val)=if j.val=32 then w[84] else w[0]) ∧
      Objects.StateRepr 1 1 8 ((Frag.init Δ).push (.mem (.fixed (.prim .uint) 33)) .ok) ((cs 33 32).withHeap o2) base' m2 := by
  obtain ⟨base',m0,m1,m2,o1,o2,z1,z2,hsrc,hprog,he1,he2,hvec,hold,htab,hr1,hr2,hl2,hNewLocal,hLoc,hid,hne,hc0,hc1,hc2,hWord,hm2,ha2,hmok1,hmok2,hstack,hfree,hex,hev,hlog,hfn⟩ := declared_updates p 33 32 (by decide) (by decide) (by decide)
  have hv1 : (o1.get (cf 33)).1=(List.replicate 33 (PrimTy.dflt .uint)).set 32 (u 42) := by
    have h := congrArg (fun xs => xs[0]?) hvec
    simpa only [List.getElem?_cons_zero,Option.some.injEq] using h
  have hv2 : (o2.get (cf 33)).1=(List.replicate 33 (PrimTy.dflt .uint)).set 32 (u 84) := by
    have h := congrArg (fun xs => xs[1]?) hvec
    simpa only [List.getElem?_cons_zero,List.getElem?_cons_succ,Option.some.injEq] using h
  have h0 : z2.2.heap.get 0=(sy 32 42).2.heap.get 0 := by
    have h := congrArg (fun xs => xs[3]?) htab
    simpa only [List.getElem?_cons_zero,List.getElem?_cons_succ,Option.some.injEq] using h
  have hOld : SourceUintFixedAt z2 0 hp left := by unfold SourceUintFixedAt;rw [h0];exact represented_left 32 42
  have hRead1 := hr1.read 32 (by decide)
  have hRead2 := hr2.read 32 (by decide)
  simp only [hv1,List.getElem_set_self] at hRead1
  simp only [hv2,List.getElem_set_self] at hRead2
  have hBad := hOld.compound_add_bounds (Source.SemanticsExamples.G0 p) F0 0 (.there sd) (.there si) (.there sv) (u 32) (u 42)
    (by rw [hl2];rfl) (by rw [hl2];rfl) (by rw [hl2];rfl) (by decide)
  have hWords : ∀ j : Fin 33,m2.mem ((base' (cf 33).id).val+j.val)=if j.val=32 then w[84] else w[0] := by
    intro j
    have hj : j.val<(MObj.elems .fixed (o2.get (cf 33))).length := by simp only [MObj.elems_fixed,(o2.get (cf 33)).2];exact j.isLt
    have hget : (MObj.elems .fixed (o2.get (cf 33)))[j.val]?=some (if j.val=32 then u 84 else PrimTy.dflt .uint) := by
      simp only [MObj.elems_fixed,hv2,List.getElem?_set]
      by_cases he : j.val=32
      · simp only [he,List.length_replicate,show (32 : Nat)<33 from by decide,↓reduceIte]
      · simp only [he,Ne.symm he,↓reduceIte,List.getElem?_replicate_of_lt j.isLt]
    have hw := (hm2.heap.arrays (.fixed : ArrTy (.fixed (.prim .uint) 33) (.prim .uint)) (cf 33)).elements j.val _ hget
    obtain ⟨v,hv,hInt,hW⟩ := hw.uint_inv
    have hW' : m2.mem ((base' (cf 33).id).val+j.val)=.val ⟨v,hv⟩ := by simpa only [Objects.header,Nat.add_zero] using hW
    by_cases he : j.val=32
    · simp only [he,↓reduceIte] at hInt ⊢
      have heq : v=84 := by change (84 : Int)=v at hInt;omega
      simpa only [he,heq] using hW'
    · simp only [he,↓reduceIte] at hInt ⊢
      have heq : v=0 := by change (0 : Int)=v at hInt;omega
      simpa only [heq] using hW'
  exact ⟨base',m2,o1,o2,z1,z2,hsrc,hr1,hr2,hRead1,hRead2,hr2.bounds 33 (by decide),hBad,hWords,hm2⟩

private abbrev EH : HTy := [.fixed (.prim .uint) 0]
private def er : HRef EH (.fixed (.prim .uint) 0) := ⟨0,rfl⟩
private def eh : Heap EH := (⟨[],rfl⟩,())
private abbrev EG : Source.RCtx := [.array .memory (.int .u256) (some 0),.int .u256,.int .u256]
private def ey : Source.EMState E0 EG :=
  (.cons (.memRef rfl 0) (.cons (sourceUint (u 0)) (.cons (sourceUint (u 1)) .nil)),
    ((Source.allocRef (E := E0) (Γ := []) (sourceUintFixedObject (D := E0.layout) (⟨[],rfl⟩ : MObj EH (.fixed (.prim .uint) 0)))).run y0).2.2)
/-- Raw kernel empty object, not a zero-length admitted Source profile. Existing
zero-size padding/refusal fixtures remain untouched; no successful update exists. -/
theorem empty_kernel_only (p : Roadmap.Pipeline) :
    SourceUintFixedAt ey 0 eh er ∧
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 3
      (sourceUintFixedIndexedAdd (.here : Source.Idx EG _) (.there .here) (.there (.there .here)))).run ey=
        (.error (.revert (Source.panicData .index)),ey) ∧
    eh.readAddr (.index er .fixed (u 0))=none := by
  have hr : SourceUintFixedAt ey 0 eh er := by rfl
  exact ⟨hr,hr.compound_add_bounds (Source.SemanticsExamples.G0 p) F0 0 .here (.there .here) (.there (.there .here))
    (u 0) (u 1) rfl rfl rfl (by decide),by simp only [Heap.readAddr,Heap.index,MObj.elems_fixed];rfl⟩

private def frd : List Instr := [.mload 7] ++ [.mload 6] ++ Objects.readCode (.fixed : ArrTy A (.prim .uint))
private theorem fresh_read_run (m : Machine) (a k old : Fin W) (hk : k.val<3) (hs : a.val+k.val<W)
    (hp : m.mem 7=.val a) (hi : m.mem 6=.val k) (hc : m.mem (a.val+k.val)=.val old) :
    run frd m=.ok (m.push (.val old)) 0 := by
  change run ([.mload 7] ++ ([.mload 6] ++ Objects.readCode (.fixed : ArrTy A (.prim .uint)))) m=_
  rw [run_append_ok (show run [.mload 7] m=.ok (m.push (.val a)) 0 from by change Out.ok (m.push (m.mem 7)) 0=_;rw [hp])]
  rw [run_append_ok (show run [.mload 6] (m.push (.val a))=.ok ((m.push (.val a)).push (.val k)) 0 from by change Out.ok ((m.push (.val a)).push (m.mem 6)) 0=_;rw [hi])]
  have ha := Objects.fixedAddr_run m a k 3
  rw [if_pos hk] at ha
  change run (Objects.fixedAddrCode 3 ++ [.mloadAt]) ((m.push (.val a)).push (.val k))=_
  rw [run_append_ok ha]
  simp only [run,Machine.push,exec_cons_zero,Instr.step,wmod_of_lt hs,Out.ok_bind,exec_nil,hc,Machine.next]
private theorem fresh_add_run (m : Machine) (a k old v : Fin W) (hk : k.val<3) (hs : a.val+k.val<W)
    (hp : m.mem 7=.val a) (hi : m.mem 6=.val k) (hv : m.mem 5=.val v) (hc : m.mem (a.val+k.val)=.val old)
    (hadd : old.val+v.val<W) :
    run (ca 3) m=.ok (writeMachine m (a.val+k.val) (.val ⟨old.val+v.val,hadd⟩)) 0 := by
  have hr := fresh_read_run m a k old hk hs hp hi hc
  have hvalue : run (binaryCode .uint .add frd [.mload 5]) m=.ok (m.push (.val ⟨old.val+v.val,hadd⟩)) 0 := by
    change run (frd ++ ([.mload 5] ++ uTail .add)) m=_
    rw [run_append_ok hr]
    rw [run_append_ok (show run [.mload 5] (m.push (.val old))=.ok ((m.push (.val old)).push (.val v)) 0 from by change Out.ok ((m.push (.val old)).push (m.mem 5)) 0=_;rw [hv])]
    exact (add_tail m m.stack old.isLt v.isLt).trans (by rw [dif_pos hadd];rfl)
  change run ((binaryCode .uint .add frd [.mload 5]) ++ ([.mload 7] ++ ([.mload 6] ++ Objects.writeCode (.fixed : ArrTy A (.prim .uint))))) m=_
  rw [run_append_ok hvalue]
  rw [run_append_ok (show run [.mload 7] (m.push (.val ⟨old.val+v.val,hadd⟩))=.ok ((m.push (.val ⟨old.val+v.val,hadd⟩)).push (.val a)) 0 from by change Out.ok ((m.push (.val ⟨old.val+v.val,hadd⟩)).push (m.mem 7)) 0=_;rw [hp])]
  rw [run_append_ok (show run [.mload 6] ((m.push (.val ⟨old.val+v.val,hadd⟩)).push (.val a))=.ok (((m.push (.val ⟨old.val+v.val,hadd⟩)).push (.val a)).push (.val k)) 0 from by change Out.ok (((m.push (.val ⟨old.val+v.val,hadd⟩)).push (.val a)).push (m.mem 6)) 0=_;rw [hi])]
  have ha := Objects.fixedAddr_run (m.push (.val ⟨old.val+v.val,hadd⟩)) a k 3
  rw [if_pos hk] at ha
  change run (Objects.fixedAddrCode 3 ++ [.mstoreAt]) (((m.push (.val ⟨old.val+v.val,hadd⟩)).push (.val a)).push (.val k))=_
  rw [run_append_ok ha]
  simp only [run,Machine.push,exec_cons_zero,Instr.step,wmod_of_lt hs,Out.ok_bind,exec_nil,writeMachine]
private def postWord (n k : Nat) := writeMachine (allocateStructMachine (machine k 42) ⟨40,by decide⟩ (max 1 n)) 7 w[40]
private theorem declare_run (n k : Nat) : run (cc n) (machine k 42)=.ok (postWord n k) 0 := by
  change run (allocateStructCode (max 1 n) ++ [.mstore 7]) (machine k 42)=_
  rw [run_append_ok (allocateStruct_run (machine k 42) ⟨40,by decide⟩ (max 1 n) rfl)];rfl

/-- Complete20word observations for the SAME fresh declaration/update program;
old aliases remain OLD while the new local selects headerless cells40..42. -/
theorem fresh_word_vectors :
    observed (cc 3) (machine 2 42)=some
      ([w[43],w[32],w[16],w[16],w[24],w[42],w[2],w[99],w[7],w[8],w[7],w[9],w[10],w[9],w[11],w[12],w[40],w[0],w[0],w[0]],[w[77],w[88]]) ∧
    observed (cc 3 ++ ca 3) (machine 2 42)=some
      ([w[43],w[32],w[16],w[16],w[24],w[42],w[2],w[99],w[7],w[8],w[7],w[9],w[10],w[9],w[11],w[12],w[40],w[0],w[0],w[42]],[w[77],w[88]]) ∧
    observed (cc 3 ++ ca 3 ++ ca 3) (machine 2 42)=some
      ([w[43],w[32],w[16],w[16],w[24],w[42],w[2],w[99],w[7],w[8],w[7],w[9],w[10],w[9],w[11],w[12],w[40],w[0],w[0],w[84]],[w[77],w[88]]) := by
  have h1 := fresh_add_run (postWord 3 2) ⟨40,by decide⟩ ⟨2,by decide⟩ ⟨0,by decide⟩ ⟨42,by decide⟩ (by decide) (by decide) rfl rfl rfl rfl (by decide)
  have h2 := fresh_add_run (writeMachine (postWord 3 2) 42 w[42]) ⟨40,by decide⟩ ⟨2,by decide⟩ ⟨42,by decide⟩ ⟨42,by decide⟩ (by decide) (by decide) rfl rfl rfl rfl (by decide)
  have hC1 : run (cc 3 ++ ca 3) (machine 2 42)=.ok (writeMachine (postWord 3 2) 42 w[42]) 0 := by rw [run_append_ok (declare_run 3 2)];exact h1
  have hC12 : run (cc 3 ++ ca 3 ++ ca 3) (machine 2 42)=.ok (writeMachine (writeMachine (postWord 3 2) 42 w[42]) 42 w[84]) 0 := by rw [run_append_ok hC1];exact h2
  exact ⟨observed_ok (declare_run 3 2),observed_ok hC1,observed_ok hC12⟩

/-- Zero RHS remains canonical and executes successfully at the selected fixed
cell; this does not extend checked target overflow to unchecked wrapping. -/
theorem zero_rhs (p : Roadmap.Pipeline) :
    ∃ (out : Heap H) (z : Source.EMState E0 Γ) (m1 : Machine),
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintFixedIndexedAdd sd si sv)).run (ay 2 0)=
        (.ok (.val (sourceUint (u 9))),z) ∧
      SourceUintFixedAt z 1 out right ∧ [(out.get left).1,(out.get right).1,(out.get neighbor).1]=
        [[u 7,u 8,u 7],[u 9,u 10,u 9],[u 11,u 12]] ∧
      run (ac ++ addCode) (machine 2 0)=.ok m1 0 ∧
      Objects.StateRepr 1 1 8 (Frag.init Δ) ((ast 2 0).withHeap out) base m1 ∧ Source.MemOK E0 SH z := by
  have hA := source_uint_fixed_alias_word (Source.SemanticsExamples.G0 p) F0 0 (sy 2 0) sd ss 1 rfl SH (source_memOK 2 0)
    (state 2 0) td ts right rfl (represented_right 2 0) (initial_repr 2 0) (initial_allocator 2 0) (by decide)
  obtain ⟨out,z,m1,hw,hs,he,hstmt,hi,hc,hr,hm,hmok,hl,hstack,hkeep,hobj,haddr,hex,hev,hlog,hfn⟩ :=
    resolved_uint_fixed_add_word (Source.SemanticsExamples.G0 p) F0 0 (ast 2 0) right hA.2.2.2.2.1 sd si sv td ti tv (u 2) (u 0)
      rfl rfl rfl rfl rfl rfl (by simp only [Heap.len,MObj.elems_fixed];decide) (by simp only [MObj.elems_fixed];decide)
      hA.2.2.2.2.2.2.1 SH hA.2.2.2.2.2.1
  simp only [MObj.elems_fixed] at hw he
  change hp.writeAddr (.index right .fixed (u 2)) (u 9)=some out at hw
  have hv := indexedWrite_elems hp out right .fixed (u 2) (u 9) hw
  simp only [MObj.elems_fixed] at hv
  have hRight : (out.get right).1=[u 9,u 10,u 9] := hv
  have hVec : [(out.get left).1,(out.get right).1,(out.get neighbor).1]=[[u 7,u 8,u 7],[u 9,u 10,u 9],[u 11,u 12]] := by
    rw [hobj left (by change (1 : Nat)≠0;decide),hobj neighbor (by change (1 : Nat)≠2;decide),hRight];rfl
  have hWord : run (ac ++ addCode) (machine 2 0)=.ok m1 0 := by
    change run (aliasLocalCode 1 td ts ++ addCode) (machine 2 0)=_
    rw [run_append_ok hA.2.2.2.1];exact hc
  exact ⟨out,z,m1,he,hr,hVec,hWord,hm,hmok⟩

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedCompoundControls.initial_views' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms initial_views
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedCompoundControls.alias_updates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms alias_updates
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedCompoundControls.late_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms late_overflow
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedCompoundControls.bounds_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bounds_timeout
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedCompoundControls.word_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_vectors
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedCompoundControls.declared_updates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms declared_updates
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedCompoundControls.boundary_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boundary_reads
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedCompoundControls.empty_kernel_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_kernel_only
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedCompoundControls.fresh_word_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fresh_word_vectors
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedCompoundControls.zero_rhs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_rhs
end Solidity.Backend.MemoryOps.SourceUintFixedCompoundControls
