import Solidity.Backend.MemoryOps.SourceUintFixedDeclareCompoundOverflow
import Solidity.Evm.Correct
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.MemoryOps.SourceUintFixedDeclareCompoundControls
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


private def g := hp.allocDefault A rfl
private def fresh := g.val
private def grown (k v : Nat) := ((state k v).adopt g).1.push (t := .mem A) (some fresh)
private def mid (k v : Nat) : Source.EMState E0 (SA::Γ) :=
  (.cons (.memRef rfl 3) (sy k v).1,{(sy k v).2 with heap := ((sy k v).2.heap.alloc ⟨SA,sourceUintFixedZero 3⟩).1})
private def rebound (k v : Nat) : Source.EMState E0 (SA::Γ) := ((mid k v).1.set (.there sd) (.memRef rfl 3),(mid k v).2)
private def renamed (k v : Nat) := (grown k v).setLocal (.there td) (some fresh)
private def cc : List Instr := Objects.defaultDeclareCode (Γ := Δ) (Objects.DefaultBuilder.fixedPrimitive .uint 3).code 1
private def ac : List Instr := aliasLocalCode 1 (.there td) (.here : Idx (.mem A::Δ) (.mem A))
private def addCode : List Instr := fixedUintAddCode (C := C) (Γ := .mem A::Δ) 1 (.there td) (.there ti) (.there tv)

/-- Both actual pipelines execute declaration→OLDbinding→fresh0→42→84.
The complete old/fresh contents, Source table and contexts are observed; runtime
index k is constrained only by the actual length3. Generic length is in the law. -/
theorem reached_program (p : Roadmap.Pipeline) (k : Nat) (hk : k<3) :
    ∃ (base' : Nat → Fin W) (m0 ma m1 m2 : Machine) (o1 o2 : Heap g.H') (z1 z2 : Source.EMState E0 (SA::Γ)),
      (Source.execS (Source.SemanticsExamples.G0 p) F0 10 Γ.length none (.declVar SA : Source.RStmt E0 [] false .body Γ (SA::Γ)) (sy k 42).1).run (.nil,(sy k 42).2)=
        (.ok (.normal (mid k 42).1),(.nil,(mid k 42).2)) ∧
      (Source.execS (Source.SemanticsExamples.G0 p) F0 9 Γ.length none (.expr (sourceLocalAlias (.there sd) .here) : Source.RStmt E0 [] false .body (SA::Γ) (SA::Γ)) (mid k 42).1).run (.nil,(mid k 42).2)=
        (.ok (.normal (rebound k 42).1),(.nil,(rebound k 42).2)) ∧
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 11 Γ.length none (sourceUintFixedDeclareCompound sd si sv) (sy k 42).1).run (.nil,(sy k 42).2)=
        (.ok (.normal z2.1),(.nil,z2.2)) ∧
      Prog.run (state k 42) (intrinsicUintFixedDeclareCompound td ti tv)=.ok ⟨(renamed k 42).withHeap o2,g.ext⟩ ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 7 (sourceUintFixedIndexedAdd (.there sd) (.there si) (.there sv))).run (rebound k 42)=(.ok (.val (sourceUint (u 42))),z1) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 6 (sourceUintFixedIndexedAdd (.there sd) (.there si) (.there sv))).run z1=(.ok (.val (sourceUint (u 84))),z2) ∧
      [(g.heap.get fresh).1,(o1.get fresh).1,(o2.get fresh).1]=
        [[u 0,u 0,u 0],[u 0,u 0,u 0].set k (u 42),[u 0,u 0,u 0].set k (u 84)] ∧
      [(o2.get (left.wk g.ext)).1,(o2.get (right.wk g.ext)).1,(o2.get (neighbor.wk g.ext)).1]=[[u 7,u 8,u 7],[u 9,u 10,u 9],[u 11,u 12]] ∧
      [z1.2.heap.get 0,z1.2.heap.get 1,z1.2.heap.get 2,z1.2.heap.get 3,z2.2.heap.get 0,z2.2.heap.get 1,z2.2.heap.get 2,z2.2.heap.get 3]=
        [(sy k 42).2.heap.get 0,(sy k 42).2.heap.get 1,(sy k 42).2.heap.get 2,some ⟨SA,sourceUintFixedObject (o1.get fresh)⟩,
         (sy k 42).2.heap.get 0,(sy k 42).2.heap.get 1,(sy k 42).2.heap.get 2,some ⟨SA,sourceUintFixedObject (o2.get fresh)⟩] ∧
      SourceUintFixedAt z1 3 o1 fresh ∧ SourceUintFixedAt z2 3 o2 fresh ∧ z1.1=(rebound k 42).1 ∧ z2.1=(rebound k 42).1 ∧
      [z2.1.get .here,z2.1.get (.there sd),z2.1.get (.there sa),z2.1.get (.there ss)]=[.memRef rfl 3,.memRef rfl 3,.memRef rfl 0,.memRef rfl 1] ∧
      (renamed k 42).env=((grown k 42).setLocal (.there td) (some fresh)).env ∧
      TEnv.get (.there td) (renamed k 42).env=some fresh ∧ TEnv.get (.there ta) (renamed k 42).env=some (left.wk g.ext) ∧
      fresh.id=3 ∧ fresh.id≠(left.wk g.ext).id ∧
      run cc (machine k 42)=.ok m0 0 ∧ run ac m0=.ok ma 0 ∧ run addCode ma=.ok m1 0 ∧ run addCode m1=.ok m2 0 ∧
      run (cc ++ ac ++ addCode ++ addCode) (machine k 42)=.ok m2 0 ∧
      Objects.StateRepr 1 1 8 ((Frag.init Δ).push (.mem A) .ok) ((renamed k 42).withHeap o2) base' m2 ∧
      Objects.AllocatorRepr o2 base' 8 ⟨43,by decide⟩ m2 ∧ Source.MemOK E0 SH z1 ∧ Source.MemOK E0 SH z2 ∧
      m2.stack=[w[77],w[88]] ∧ m2.mem 0=w[43] ∧
      z2.2.ex=(sy k 42).2.ex ∧ z2.2.events=(sy k 42).2.events ∧ z2.2.logs=(sy k 42).2.logs ∧ z2.2.fnLocals=(sy k 42).2.fnLocals := by
  have hkw : k<W := by
    have hw : 3<W := by decide
    omega
  have hki : (u k).1.toNat=k := Nat.mod_eq_of_lt hkw
  obtain ⟨base',m0,ma,m1,m2,o1,o2,z1,z2,hd,hAlias,hitems,hprog,hw1,hw2,he1,he2,hr0,hr1,hr2,hc0,hcA,hc1,hc2,hwhole,hm2,ha2,hmok0,hmok1,hmok2,hl1,hl2,hdstS,hnewS,hdstT,hnewT,hsloc,htloc,hobj,haddr,hid,hne,hstack,hfree,haddr1,hex,hev,hlog,hfn⟩ :=
    source_uint_fixed_declare_compound_word (Source.SemanticsExamples.G0 p) F0 (sy k 42) (state k 42) 3 (by decide) sd td si sv ti tv
      (u k) (u 42) rfl rfl rfl rfl (by rw [hki];exact hk) (by decide) SH (source_memOK k 42)
      (initial_repr k 42) (initial_allocator k 42) (by decide) (by decide) (by decide)
  have h84 : (⟨(u 42).1+(u 42).1,by decide⟩ : PrimTy.uint.Denote)=u 84 := by apply Subtype.ext;rfl
  rw [h84] at hw2 he2
  change SourceUintFixedAt z1 3 o1 fresh at hr1
  change SourceUintFixedAt z2 3 o2 fresh at hr2
  have hz : (g.heap.get fresh).1=[u 0,u 0,u 0] := by
    have h := (source_uint_fixed_intrinsic (sy k 42) hp 3 (by decide)).2.1
    rw [show PrimTy.dflt .uint=u 0 from by decide] at h
    simpa only [MObj.elems_fixed,List.replicate_succ,List.replicate_zero] using h
  have hv1 := indexedWrite_elems g.heap o1 fresh .fixed (u k) (u 42) hw1
  have hv2 := indexedWrite_elems o1 o2 fresh .fixed (u k) (u 84) hw2
  have hVec1 : (o1.get fresh).1=[u 0,u 0,u 0].set k (u 42) := by simpa only [MObj.elems_fixed,hki,hz] using hv1
  have hVec2 : (o2.get fresh).1=[u 0,u 0,u 0].set k (u 84) := by
    simp only [MObj.elems_fixed,hki] at hv2
    rw [hv2,hVec1,List.set_set]
  have hOld : [(o2.get (left.wk g.ext)).1,(o2.get (right.wk g.ext)).1,(o2.get (neighbor.wk g.ext)).1]=[[u 7,u 8,u 7],[u 9,u 10,u 9],[u 11,u 12]] := by
    rw [hobj left,hobj right,hobj neighbor];rfl
  have hgetL : (sy k 42).2.heap.get 0≠none := by rw [represented_left k 42];exact Option.some_ne_none _
  have hgetR : (sy k 42).2.heap.get 1≠none := by rw [represented_right k 42];exact Option.some_ne_none _
  have hgetN : (sy k 42).2.heap.get 2≠none := by rw [represented_neighbor k 42];exact Option.some_ne_none _
  have hTable : [z1.2.heap.get 0,z1.2.heap.get 1,z1.2.heap.get 2,z1.2.heap.get 3,z2.2.heap.get 0,z2.2.heap.get 1,z2.2.heap.get 2,z2.2.heap.get 3]=
      [(sy k 42).2.heap.get 0,(sy k 42).2.heap.get 1,(sy k 42).2.heap.get 2,some ⟨SA,sourceUintFixedObject (o1.get fresh)⟩,
       (sy k 42).2.heap.get 0,(sy k 42).2.heap.get 1,(sy k 42).2.heap.get 2,some ⟨SA,sourceUintFixedObject (o2.get fresh)⟩] := by
    rw [haddr1 0 hgetL,haddr1 1 hgetR,haddr1 2 hgetN,hr1,haddr 0 hgetL,haddr 1 hgetR,haddr 2 hgetN,hr2]
  have hLoc : [z2.1.get .here,z2.1.get (.there sd),z2.1.get (.there sa),z2.1.get (.there ss)]=[.memRef rfl 3,.memRef rfl 3,.memRef rfl 0,.memRef rfl 1] := by rw [hl2];rfl
  have hTypedAlias : TEnv.get (.there ta) (renamed k 42).env=some (left.wk g.ext) := rfl
  have hVectors : [(g.heap.get fresh).1,(o1.get fresh).1,(o2.get fresh).1]=
      [[u 0,u 0,u 0],[u 0,u 0,u 0].set k (u 42),[u 0,u 0,u 0].set k (u 84)] := by rw [hz,hVec1,hVec2]
  exact ⟨base',m0,ma,m1,m2,o1,o2,z1,z2,hd,hAlias,hitems,hprog,he1,he2,hVectors,hOld,hTable,hr1,hr2,hl1,hl2,hLoc,rfl,hdstT,hTypedAlias,hid,hne left,hc0,hcA,hc1,hc2,hwhole,hm2,ha2,hmok1,hmok2,hstack,hfree,hex,hev,hlog,hfn⟩

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDeclareCompoundControls.reached_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reached_program
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

private def wordPost (k v : Nat) := writeMachine (allocateStructMachine (machine k v) ⟨40,by decide⟩ 3) 7 w[40]
private theorem declare_run (k v : Nat) : run cc (machine k v)=.ok (wordPost k v) 0 := by
  change run (allocateStructCode 3 ++ [.mstore 7]) (machine k v)=_
  rw [run_append_ok (allocateStruct_run (machine k v) ⟨40,by decide⟩ 3 rfl)];rfl

/-- Complete20word observations for constructor, actual rebind, both reached
updates; skipped and delayed aliasing discriminate stale/wrong-order writes. -/
theorem word_vectors :
    observed cc (machine 2 42)=some
      ([w[43],w[32],w[16],w[16],w[24],w[42],w[2],w[99],w[7],w[8],w[7],w[9],w[10],w[9],w[11],w[12],w[40],w[0],w[0],w[0]],[w[77],w[88]]) ∧
    observed (cc ++ ac) (machine 2 42)=some
      ([w[43],w[32],w[16],w[40],w[24],w[42],w[2],w[99],w[7],w[8],w[7],w[9],w[10],w[9],w[11],w[12],w[40],w[0],w[0],w[0]],[w[77],w[88]]) ∧
    observed (cc ++ ac ++ addCode) (machine 2 42)=some
      ([w[43],w[32],w[16],w[40],w[24],w[42],w[2],w[99],w[7],w[8],w[7],w[9],w[10],w[9],w[11],w[12],w[40],w[0],w[0],w[42]],[w[77],w[88]]) ∧
    observed (cc ++ ac ++ addCode ++ addCode) (machine 2 42)=some
      ([w[43],w[32],w[16],w[40],w[24],w[42],w[2],w[99],w[7],w[8],w[7],w[9],w[10],w[9],w[11],w[12],w[40],w[0],w[0],w[84]],[w[77],w[88]]) ∧
    observed (cc ++ addCode ++ addCode) (machine 2 42)=some
      ([w[43],w[32],w[16],w[16],w[24],w[42],w[2],w[99],w[7],w[8],w[91],w[9],w[10],w[9],w[11],w[12],w[40],w[0],w[0],w[0]],[w[77],w[88]]) ∧
    observed (cc ++ addCode ++ ac ++ addCode) (machine 2 42)=some
      ([w[43],w[32],w[16],w[40],w[24],w[42],w[2],w[99],w[7],w[8],w[49],w[9],w[10],w[9],w[11],w[12],w[40],w[0],w[0],w[42]],[w[77],w[88]]) ∧
    (u 84)≠u 42 ∧ (u 91)≠u 7 := by
  have hC := declare_run 2 42
  let ma := writeMachine (wordPost 2 42) 3 w[40]
  have hA : run ac (wordPost 2 42)=.ok ma 0 := rfl
  have hCA : run (cc ++ ac) (machine 2 42)=.ok ma 0 := by rw [run_append_ok hC];exact hA
  have h1 := add_run ma ⟨40,by decide⟩ ⟨2,by decide⟩ ⟨0,by decide⟩ ⟨42,by decide⟩ (by decide) (by decide) rfl rfl rfl rfl (by decide)
  have h2 := add_run (writeMachine ma 42 w[42]) ⟨40,by decide⟩ ⟨2,by decide⟩ ⟨42,by decide⟩ ⟨42,by decide⟩ (by decide) (by decide) rfl rfl rfl rfl (by decide)
  have hCA1 : run (cc ++ ac ++ addCode) (machine 2 42)=.ok (writeMachine ma 42 w[42]) 0 := by rw [run_append_ok hCA];exact h1
  have hCA12 : run (cc ++ ac ++ addCode ++ addCode) (machine 2 42)=.ok (writeMachine (writeMachine ma 42 w[42]) 42 w[84]) 0 := by rw [run_append_ok hCA1];exact h2
  have hskip1 := add_run (wordPost 2 42) ⟨16,by decide⟩ ⟨2,by decide⟩ ⟨7,by decide⟩ ⟨42,by decide⟩ (by decide) (by decide) rfl rfl rfl rfl (by decide)
  have hskip2 := add_run (writeMachine (wordPost 2 42) 18 w[49]) ⟨16,by decide⟩ ⟨2,by decide⟩ ⟨49,by decide⟩ ⟨42,by decide⟩ (by decide) (by decide) rfl rfl rfl rfl (by decide)
  have hs1 : run (cc ++ addCode) (machine 2 42)=.ok (writeMachine (wordPost 2 42) 18 w[49]) 0 := by rw [run_append_ok hC];exact hskip1
  have hs12 : run (cc ++ addCode ++ addCode) (machine 2 42)=.ok (writeMachine (writeMachine (wordPost 2 42) 18 w[49]) 18 w[91]) 0 := by rw [run_append_ok hs1];exact hskip2
  let mr := writeMachine (writeMachine (wordPost 2 42) 18 w[49]) 3 w[40]
  have hrA : run ac (writeMachine (wordPost 2 42) 18 w[49])=.ok mr 0 := rfl
  have hr1 := add_run mr ⟨40,by decide⟩ ⟨2,by decide⟩ ⟨0,by decide⟩ ⟨42,by decide⟩ (by decide) (by decide) rfl rfl rfl rfl (by decide)
  have hr : run (cc ++ addCode ++ ac ++ addCode) (machine 2 42)=.ok (writeMachine mr 42 w[42]) 0 := by
    rw [List.append_assoc,run_append_ok hs1,run_append_ok hrA];exact hr1
  exact ⟨observed_ok hC,observed_ok hCA,observed_ok hCA1,observed_ok hCA12,observed_ok hs12,observed_ok hr,by decide,by decide⟩

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDeclareCompoundControls.word_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_vectors

private def maximum : PrimTy.uint.Denote := u (W-1)

/-- Actual fresh0→MAX success then checked overflow, retaining the changed
Source prefix and legitimate word prefix only. Frozen fresh0 would not overflow. -/
theorem late_overflow (p : Roadmap.Pipeline) :
    ∃ (base' : Nat → Fin W) (m0 ma m1 : Machine) (o1 : Heap g.H') (z1 : Source.EMState E0 (SA::Γ)),
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 11 Γ.length none (sourceUintFixedDeclareCompound sd si sv) (sy 2 (W-1)).1).run (.nil,(sy 2 (W-1)).2)=
        (.error (.revert (Source.panicData .arithmetic)),(.nil,z1.2)) ∧
      Prog.run (state 2 (W-1)) (intrinsicUintFixedDeclareCompound td ti tv)=.error .revert ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 7 (sourceUintFixedIndexedAdd (.there sd) (.there si) (.there sv))).run (rebound 2 (W-1))=
        (.ok (.val (sourceUint maximum)),z1) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 6 (sourceUintFixedIndexedAdd (.there sd) (.there si) (.there sv))).run z1=
        (.error (.revert (Source.panicData .arithmetic)),z1) ∧
      [(o1.get (left.wk g.ext)).1,(o1.get (right.wk g.ext)).1,(o1.get (neighbor.wk g.ext)).1,(o1.get fresh).1]=
        [[u 7,u 8,u 7],[u 9,u 10,u 9],[u 11,u 12],[u 0,u 0,maximum]] ∧
      [z1.2.heap.get 0,z1.2.heap.get 1,z1.2.heap.get 2,z1.2.heap.get 3]=
        [(sy 2 (W-1)).2.heap.get 0,(sy 2 (W-1)).2.heap.get 1,(sy 2 (W-1)).2.heap.get 2,some ⟨SA,sourceUintFixedObject (o1.get fresh)⟩] ∧
      SourceUintFixedAt z1 3 o1 fresh ∧ z1.1=(rebound 2 (W-1)).1 ∧
      run cc (machine 2 (W-1))=.ok m0 0 ∧ run ac m0=.ok ma 0 ∧ run addCode ma=.ok m1 0 ∧ run addCode m1=.revert ∧
      run (cc ++ ac ++ addCode ++ addCode) (machine 2 (W-1))=.revert ∧
      Objects.StateRepr 1 1 8 ((Frag.init Δ).push (.mem A) .ok) ((renamed 2 (W-1)).withHeap o1) base' m1 ∧
      Objects.AllocatorRepr o1 base' 8 ⟨43,by decide⟩ m1 ∧ Source.MemOK E0 SH z1 ∧
      m1.stack=[w[77],w[88]] ∧ m1.mem 0=w[43] ∧
      z1.2.ex=(sy 2 (W-1)).2.ex ∧ z1.2.events=(sy 2 (W-1)).2.events ∧ z1.2.logs=(sy 2 (W-1)).2.logs ∧ z1.2.fnLocals=(sy 2 (W-1)).2.fnLocals ∧
      PrimTy.uint.inRange ((u 0).1+maximum.1)=true ∧ PrimTy.uint.inRange (maximum.1+maximum.1)≠true ∧ maximum≠u 0 := by
  obtain ⟨base',m0,ma,m1,o1,z1,hd,hitems,hprog,hw1,he1,he2,hc0,hcA,hc1,hc2,hwhole,hr1,hm1,ha1,hmok1,hl1,hobj,haddr,hid,hne,hstack,hfree,hex,hev,hlog,hfn⟩ :=
    source_uint_fixed_declare_compound_overflow_word (Source.SemanticsExamples.G0 p) F0 rfl (sy 2 (W-1)) (state 2 (W-1)) 3 (by decide) sd td si sv ti tv
      (u 2) maximum rfl rfl rfl rfl (by decide) (by decide) SH (source_memOK 2 (W-1))
      (initial_repr 2 (W-1)) (initial_allocator 2 (W-1)) (by decide) (by decide) (by decide)
  change SourceUintFixedAt z1 3 o1 fresh at hr1
  have hz : (g.heap.get fresh).1=List.replicate 3 (PrimTy.dflt .uint) := by
    have h := (source_uint_fixed_intrinsic (sy 2 (W-1)) hp 3 (by decide)).2.1
    simpa only [MObj.elems_fixed] using h
  have hv := indexedWrite_elems g.heap o1 fresh .fixed (u 2) maximum hw1
  have hPayload : (o1.get fresh).1=[u 0,u 0,maximum] := by
    simp only [MObj.elems_fixed] at hv
    rw [hv,hz];rfl
  have hVec : [(o1.get (left.wk g.ext)).1,(o1.get (right.wk g.ext)).1,(o1.get (neighbor.wk g.ext)).1,(o1.get fresh).1]=
      [[u 7,u 8,u 7],[u 9,u 10,u 9],[u 11,u 12],[u 0,u 0,maximum]] := by
    rw [hobj left,hobj right,hobj neighbor,hPayload];rfl
  have hgetL : (sy 2 (W-1)).2.heap.get 0≠none := by rw [represented_left 2 (W-1)];exact Option.some_ne_none _
  have hgetR : (sy 2 (W-1)).2.heap.get 1≠none := by rw [represented_right 2 (W-1)];exact Option.some_ne_none _
  have hgetN : (sy 2 (W-1)).2.heap.get 2≠none := by rw [represented_neighbor 2 (W-1)];exact Option.some_ne_none _
  have hTable : [z1.2.heap.get 0,z1.2.heap.get 1,z1.2.heap.get 2,z1.2.heap.get 3]=
      [(sy 2 (W-1)).2.heap.get 0,(sy 2 (W-1)).2.heap.get 1,(sy 2 (W-1)).2.heap.get 2,some ⟨SA,sourceUintFixedObject (o1.get fresh)⟩] := by
    rw [haddr 0 hgetL,haddr 1 hgetR,haddr 2 hgetN,hr1]
  exact ⟨base',m0,ma,m1,o1,z1,hitems,hprog,he1,he2,hVec,hTable,hr1,hl1,hc0,hcA,hc1,hc2,hwhole,hm1,ha1,hmok1,hstack,hfree,hex,hev,hlog,hfn,by decide,by decide,by decide⟩

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDeclareCompoundControls.late_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms late_overflow

private theorem heap_repr9 (k v : Nat) : Objects.HeapRepr hp base 9 (machine k v) := by
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
private theorem initial_repr9 (k v : Nat) : Objects.StateRepr 1 1 9 (Frag.init Δ) (state k v) base (machine k v) := by
  have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨?_,heap_repr9 k v,?_,by decide⟩
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
private theorem initial_allocator9 (k v : Nat) : Objects.AllocatorRepr hp base 9 ⟨40,by decide⟩ (machine k v) := by
  refine ⟨heap_repr9 k v,⟨by decide,by decide,rfl,?_⟩,?_⟩
  · intro a ha
    change 40≤a at ha
    simp only [machine,if_neg (show a≠0 by omega),if_neg (show a≠1 by omega),if_neg (show a≠2 by omega),
      if_neg (show a≠3 by omega),if_neg (show a≠4 by omega),if_neg (show a≠5 by omega),if_neg (show a≠6 by omega),
      if_neg (show a≠15 by omega),if_neg (show a≠16 by omega),if_neg (show a≠17 by omega),if_neg (show a≠18 by omega),
      if_neg (show a≠24 by omega),if_neg (show a≠25 by omega),if_neg (show a≠26 by omega),if_neg (show a≠32 by omega),if_neg (show a≠33 by omega)]
  · intro R q
    rcases refs q with ⟨rfl,hq|hq⟩ | ⟨rfl,hq⟩ <;> cases hq <;> decide

private abbrev B : RefTy := .fixed (.prim .uint) 33
private abbrev SB := Source.STy.array .memory (.int .u256) (some 33)
private def gb := hp.allocDefault B rfl
private def sb := ((state 32 42).adopt gb).1.push (t := .mem B) (some gb.val)
private def yb : Source.EMState E0 (SB::Γ) :=
  (.cons (.memRef rfl 3) (sy 32 42).1,{(sy 32 42).2 with heap := ((sy 32 42).2.heap.alloc ⟨SB,sourceUintFixedZero 33⟩).1})
private def gc := gb.heap.allocDefault B rfl
private def sc := (((sb.adopt gc).1.push (t := .mem B) (some gc.val)).setLocal (.there .here) (some gc.val))

private def bc1 : List Instr := Objects.defaultDeclareCode (Γ := Δ) (Objects.DefaultBuilder.fixedPrimitive .uint 33).code 1
private def bc2 : List Instr :=
  Objects.defaultDeclareCode (Γ := .mem B::Δ) (Objects.DefaultBuilder.fixedPrimitive .uint 33).code 1 ++
  aliasLocalCode 1 (.there .here : Idx (.mem B::.mem B::Δ) (.mem B)) .here ++
  fixedUintAddCode (C := C) 1 (.there .here : Idx (.mem B::.mem B::Δ) (.mem B)) (.there (.there ti)) (.there (.there tv)) ++
  fixedUintAddCode (C := C) 1 (.there .here : Idx (.mem B::.mem B::Δ) (.mem B)) (.there (.there ti)) (.there (.there tv))

/-- A genuinely reached existing length33 local is redirected to a SECOND fresh
length33 object. The actual combined program changes all and only index32 in
that second object; every33 word, old fresh object and endpoint33 are observed.
The initial constructor is a separate certified prefix, not an invented larger
Source Items program. -/
theorem boundary33 (p : Roadmap.Pipeline) :
    ∃ (base0 base1 : Nat → Fin W) (m0 m1 : Machine) (o1 o2 : Heap gc.H') (z1 z2 : Source.EMState E0 (SB::SB::Γ)),
      (Source.execS (Source.SemanticsExamples.G0 p) F0 37 Γ.length none (.declVar SB : Source.RStmt E0 [] false .body Γ (SB::Γ)) (sy 32 42).1).run (.nil,(sy 32 42).2)=
        (.ok (.normal yb.1),(.nil,yb.2)) ∧
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 41 (SB::Γ).length none (sourceUintFixedDeclareCompound .here (.there si) (.there sv)) yb.1).run (.nil,yb.2)=
        (.ok (.normal z2.1),(.nil,z2.2)) ∧
      Prog.run sb (intrinsicUintFixedDeclareCompound .here (.there ti) (.there tv))=.ok ⟨sc.withHeap o2,gc.ext⟩ ∧
      SourceUintFixedAt z1 4 o1 gc.val ∧ SourceUintFixedAt z2 4 o2 gc.val ∧
      (Source.memElem (E := E0) (Γ := SB::SB::Γ) 4 32 (.int .u256)).run z1=(.ok (sourceUint (u 42)),z1) ∧
      (Source.memElem (E := E0) (Γ := SB::SB::Γ) 4 32 (.int .u256)).run z2=(.ok (sourceUint (u 84)),z2) ∧
      (Source.memElem (E := E0) (Γ := SB::SB::Γ) 4 33 (.int .u256)).run z2=(.error (.revert (Source.panicData .index)),z2) ∧
      [z2.1.get .here,z2.1.get (.there .here)]=[.memRef rfl 4,.memRef rfl 4] ∧
      z2.2.heap.get 3=yb.2.heap.get 3 ∧ (o2.get (HRef.wk gc.ext gb.val)).1=List.replicate 33 (PrimTy.dflt .uint) ∧
      gc.val.id=4 ∧ gc.val.id≠(HRef.wk gc.ext gb.val).id ∧
      (∀ j : Fin 33,m1.mem ((base1 gc.val.id).val+j.val)=if j.val=32 then w[84] else w[0]) ∧
      Objects.StateRepr 1 1 9 (((Frag.init Δ).push (.mem B) .ok).push (.mem B) .ok) (sc.withHeap o2) base1 m1 ∧
      Objects.AllocatorRepr o2 base1 9 ⟨106,by decide⟩ m1 ∧ m1.stack=[w[77],w[88]] ∧
      run bc1 (machine 32 42)=.ok m0 0 ∧ run bc2 m0=.ok m1 0 ∧ run (bc1 ++ bc2) (machine 32 42)=.ok m1 0 ∧
      Objects.StateRepr 1 1 9 ((Frag.init Δ).push (.mem B) .ok) sb base0 m0 ∧
      Objects.AllocatorRepr gb.heap base0 9 ⟨73,by decide⟩ m0 := by
  obtain ⟨base0,m0,hd0,ht0,hc0,hr0,hmok0,hm0,ha0,hbase,hstack0,hid0,hne0,hsource0⟩ :=
    source_uint_fixed_declaration_word (Source.SemanticsExamples.G0 p) F0 (sy 32 42) (state 32 42) 33 (by decide) SH (source_memOK 32 42)
      (initial_repr9 32 42) (initial_allocator9 32 42) (by decide) (by decide) (by decide)
  have hit : TEnv.get (.there ti) sb.env=u 32 := by change TEnv.get ti (TEnv.wk gb.ext Δ (state 32 42).env)=_;rw [TEnv.get_wk];rfl
  have hvt : TEnv.get (.there tv) sb.env=u 42 := by change TEnv.get tv (TEnv.wk gb.ext Δ (state 32 42).env)=_;rw [TEnv.get_wk];rfl
  obtain ⟨base1,md,ma,mw,m1,o1,o2,z1,z2,hd,hAlias,hitems,hprog,hw1,hw2,he1,he2,hrD,hr1,hr2,hcd,hcA,hc1,hc2,hwhole,hm2,ha2,hmokD,hmok1,hmok2,hl1,hl2,hdstS,hnewS,hdstT,hnewT,hsloc,htloc,hobj,haddr,hid,hne,hstack,hfree,haddr1,hex,hev,hlog,hfn⟩ :=
    source_uint_fixed_declare_compound_word (Source.SemanticsExamples.G0 p) F0 yb sb 33 (by decide) .here .here (.there si) (.there sv) (.there ti) (.there tv)
      (u 32) (u 42) rfl rfl hit hvt (by decide) (by decide) SH hmok0 hm0 ha0 (by decide) (by decide) (by decide)
  change SourceUintFixedAt z1 4 o1 gc.val at hr1
  change SourceUintFixedAt z2 4 o2 gc.val at hr2
  have h84 : (⟨(u 42).1+(u 42).1,by decide⟩ : PrimTy.uint.Denote)=u 84 := by apply Subtype.ext;rfl
  rw [h84] at hw2
  have hz : (gc.heap.get gc.val).1=List.replicate 33 (PrimTy.dflt .uint) := by
    simpa only [MObj.elems_fixed] using (source_uint_fixed_intrinsic yb gb.heap 33 (by decide)).2.1
  have hv1 := indexedWrite_elems gc.heap o1 gc.val .fixed (u 32) (u 42) hw1
  have hv2 := indexedWrite_elems o1 o2 gc.val .fixed (u 32) (u 84) hw2
  simp only [MObj.elems_fixed] at hv1 hv2
  have hVec1 : (o1.get gc.val).1=(List.replicate 33 (PrimTy.dflt .uint)).set 32 (u 42) := by rw [hv1,hz];rfl
  have hVec2 : (o2.get gc.val).1=(List.replicate 33 (PrimTy.dflt .uint)).set 32 (u 84) := by rw [hv2,hVec1];exact List.set_set ..
  have hRead1 := hr1.read 32 (by decide)
  have hRead2 := hr2.read 32 (by decide)
  simp only [hVec1,List.getElem_set_self] at hRead1
  simp only [hVec2,List.getElem_set_self] at hRead2
  have hOld : (o2.get (HRef.wk gc.ext gb.val)).1=List.replicate 33 (PrimTy.dflt .uint) := by
    rw [hobj gb.val]
    have hwk : MVal.wk gc.ext (.prim .uint)=(id : PrimTy.uint.Denote → PrimTy.uint.Denote) := rfl
    simpa only [MObj.elems_fixed,MObj.wk,hwk,List.map_id] using (source_uint_fixed_intrinsic (sy 32 42) hp 33 (by decide)).2.1
  change SourceUintFixedAt yb 3 gb.heap gb.val at hr0
  have hget : yb.2.heap.get 3≠none := by rw [hr0];exact Option.some_ne_none _
  have hWords : ∀ j : Fin 33,m1.mem ((base1 gc.val.id).val+j.val)=if j.val=32 then w[84] else w[0] := by
    intro j
    have hgetj : (MObj.elems .fixed (o2.get gc.val))[j.val]?=some (if j.val=32 then u 84 else PrimTy.dflt .uint) := by
      simp only [MObj.elems_fixed,hVec2,List.getElem?_set]
      by_cases he : j.val=32
      · simp only [he,List.length_replicate,show (32 : Nat)<33 from by decide,↓reduceIte]
      · simp only [he,Ne.symm he,↓reduceIte,List.getElem?_replicate_of_lt j.isLt]
    have hw := (hm2.heap.arrays (.fixed : ArrTy B (.prim .uint)) gc.val).elements j.val _ hgetj
    obtain ⟨v,hv,hInt,hW⟩ := hw.uint_inv
    have hW' : m1.mem ((base1 gc.val.id).val+j.val)=.val ⟨v,hv⟩ := by simpa only [Objects.header,Nat.add_zero] using hW
    by_cases he : j.val=32
    · simp only [he,↓reduceIte] at hInt ⊢
      have heq : v=84 := by change (84 : Int)=v at hInt;omega
      simpa only [he,heq] using hW'
    · simp only [he,↓reduceIte] at hInt ⊢
      have heq : v=0 := by change (0 : Int)=v at hInt;omega
      simpa only [heq] using hW'
  have hLoc : [z2.1.get .here,z2.1.get (.there .here)]=[.memRef rfl 4,.memRef rfl 4] := by rw [hl2];rfl
  have hlen : gb.H'.length=4 := by rw [gb,Objects.defaultFixed_copy];rfl
  have hID : gc.val.id=4 := hid.trans hlen
  have hc0' : run bc1 (machine 32 42)=.ok m0 0 := hc0
  have hwhole' : run bc2 m0=.ok m1 0 := hwhole
  have hCombined : run (bc1 ++ bc2) (machine 32 42)=.ok m1 0 := by rw [run_append_ok hc0'];exact hwhole'
  exact ⟨base0,base1,m0,m1,o1,o2,z1,z2,hd0,hitems,hprog,hr1,hr2,hRead1,hRead2,hr2.bounds 33 (by decide),hLoc,haddr 3 hget,hOld,hID,hne gb.val,hWords,hm2,ha2,hstack.trans hstack0,hc0,hwhole,hCombined,hm0,ha0⟩

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDeclareCompoundControls.boundary33' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boundary33
end Solidity.Backend.MemoryOps.SourceUintFixedDeclareCompoundControls
