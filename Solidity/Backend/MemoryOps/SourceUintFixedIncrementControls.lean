import Solidity.Backend.MemoryOps.SourceUintFixedIncrement
import Solidity.Backend.MemoryOps.SourceUintFixedDeclareCompoundControls
import Solidity.Evm.Correct
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.MemoryOps.SourceUintFixedIncrementControls
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


private def code : List Instr := fixedUintIncrementCode (C := C) 1 td ti

/-- The SAME actual write returns8 for prefix and7 for postfix. All Source
locals/objects/world and typed old aliases/neighbour/word ownership are observed. -/
theorem prefix_postfix (p : Roadmap.Pipeline) (pre : Bool) :
    ∃ (out : Heap H) (z : Source.EMState E0 Γ) (target : Machine),
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintFixedIncrement pre sd si)).run (sy 0 42)=
        (.ok (.val (sourceUint (if pre then u 8 else u 7))),z) ∧
      (Source.execS (Source.SemanticsExamples.G0 p) F0 4 Γ.length none (.expr (sourceUintFixedIncrement pre sd si) : Source.RStmt E0 [] false .body Γ Γ) (sy 0 42).1).run (.nil,(sy 0 42).2)=
        (.ok (.normal (sy 0 42).1),(.nil,z.2)) ∧
      TRun.incDec (fixedUintIncrementOp pre) (.mindex .fixed (.var td rfl) (.local ti)) (state 0 42)=.ok ⟨(state 0 42).withHeap out,List.prefix_refl _⟩ ∧
      run code (machine 0 42)=.ok target 0 ∧
      [(hp.get left).1,(out.get left).1,(out.get right).1,(out.get neighbor).1]=[[u 7,u 8,u 7],[u 8,u 8,u 7],[u 9,u 10,u 9],[u 11,u 12]] ∧
      [z.2.heap.get 0,z.2.heap.get 1,z.2.heap.get 2]=[some ⟨SA,sourceUintFixedObject (out.get left)⟩,(sy 0 42).2.heap.get 1,(sy 0 42).2.heap.get 2] ∧
      SourceUintFixedAt z 0 out left ∧ z.1=(sy 0 42).1 ∧
      [z.1.get sd,z.1.get sa,z.1.get ss]=[.memRef rfl 0,.memRef rfl 0,.memRef rfl 1] ∧
      Objects.StateRepr 1 1 8 (Frag.init Δ) ((state 0 42).withHeap out) base target ∧
      Objects.AllocatorRepr out base 8 ⟨40,by decide⟩ target ∧ Source.MemOK E0 SH z ∧
      target.stack=[w[77],w[88]] ∧ target.mem 0=w[40] ∧
      z.2.ex=(sy 0 42).2.ex ∧ z.2.events=(sy 0 42).2.events ∧ z.2.logs=(sy 0 42).2.logs ∧ z.2.fnLocals=(sy 0 42).2.fnLocals ∧
      (u 8)≠u 7 := by
  obtain ⟨out,z,target,hw,hs,he,hstmt,hi,hc,hr,hm,hmok,hl,hstack,hkeep,hobj,haddr,hex,hev,hlog,hfn⟩ :=
    resolved_uint_fixed_increment_word (Source.SemanticsExamples.G0 p) F0 0 pre (state 0 42) left (represented_left 0 42)
      sd si td ti (u 0) rfl rfl rfl rfl (by simp only [Heap.len,MObj.elems_fixed];decide) (by simp only [MObj.elems_fixed];decide) SH (source_memOK 0 42) (initial_repr 0 42)
  simp only [MObj.elems_fixed] at hw he
  change hp.writeAddr (.index left .fixed (u 0)) (u 8)=some out at hw
  have hv := indexedWrite_elems hp out left .fixed (u 0) (u 8) hw
  simp only [MObj.elems_fixed] at hv
  have hVec : [(hp.get left).1,(out.get left).1,(out.get right).1,(out.get neighbor).1]=[[u 7,u 8,u 7],[u 8,u 8,u 7],[u 9,u 10,u 9],[u 11,u 12]] := by
    rw [hv,hobj right (by decide),hobj neighbor (by decide)];rfl
  have hTable : [z.2.heap.get 0,z.2.heap.get 1,z.2.heap.get 2]=[some ⟨SA,sourceUintFixedObject (out.get left)⟩,(sy 0 42).2.heap.get 1,(sy 0 42).2.heap.get 2] := by
    rw [hr,haddr 1 (by decide),haddr 2 (by decide)]
  have hExpr : (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintFixedIncrement pre sd si)).run (sy 0 42)=
      (.ok (.val (sourceUint (if pre then u 8 else u 7))),z) := by
    simpa only [MObj.elems_fixed] using he
  have hLoc : [z.1.get sd,z.1.get sa,z.1.get ss]=[.memRef rfl 0,.memRef rfl 0,.memRef rfl 1] := by rw [hl];rfl
  have ha := hkeep ⟨40,by decide⟩ (by decide) (initial_allocator 0 42)
  exact ⟨out,z,target,hExpr,hstmt,hi,hc,hVec,hTable,hr,hl,hLoc,hm,ha,hmok,hstack,ha.free.cell,hex,hev,hlog,hfn,by decide⟩

private def g := hp.allocDefault A rfl
private def fresh := g.val
private def grown := ((state 2 (W-1)).adopt g).1.push (t := .mem A) (some fresh)
private def renamed := grown.setLocal (.there td) (some fresh)
private def cy : Source.EMState E0 (SA::Γ) :=
  (.cons (.memRef rfl 3) (sy 2 (W-1)).1,{(sy 2 (W-1)).2 with heap := ((sy 2 (W-1)).2.heap.alloc ⟨SA,sourceUintFixedZero 3⟩).1})

/-- Overflow is tested at the REAL changed freshMAX constructor/alias/compound
prefix from C72, not a caller-supplied desired reached relation or frozen0. -/
theorem reached_max_overflow (p : Roadmap.Pipeline) (pre : Bool) :
    ∃ (base' : Nat → Fin W) (out : Heap g.H') (z : Source.EMState E0 (SA::Γ)) (target : Machine),
      SourceUintFixedAt z 3 out fresh ∧
      [(out.get (left.wk g.ext)).1,(out.get (right.wk g.ext)).1,(out.get (neighbor.wk g.ext)).1,(out.get fresh).1]=
        [[u 7,u 8,u 7],[u 9,u 10,u 9],[u 11,u 12],[u 0,u 0,u (W-1)]] ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintFixedIncrement pre (.there sd) (.there si))).run z=
        (.error (.revert (Source.panicData .arithmetic)),z) ∧
      TRun.incDec (fixedUintIncrementOp pre) (.mindex .fixed (.var (.there td) rfl) (.local (.there ti))) (renamed.withHeap out)=.error .revert ∧
      run (fixedUintIncrementCode (C := C) (Γ := .mem A::Δ) 1 (.there td) (.there ti)) target=.revert ∧
      Objects.StateRepr 1 1 8 ((Frag.init Δ).push (.mem A) .ok) (renamed.withHeap out) base' target ∧
      Objects.AllocatorRepr out base' 8 ⟨43,by decide⟩ target ∧ Source.MemOK E0 SH z ∧
      target.stack=[w[77],w[88]] ∧ target.mem 0=w[43] ∧
      z.2.ex=(sy 2 (W-1)).2.ex ∧ z.2.events=(sy 2 (W-1)).2.events ∧ z.2.logs=(sy 2 (W-1)).2.logs ∧ z.2.fnLocals=(sy 2 (W-1)).2.fnLocals ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 7 (sourceUintFixedIndexedAdd (.there sd) (.there si) (.there sv))).run
        ((cy.1.set (.there sd) (.memRef rfl 3)),cy.2)=(.ok (.val (sourceUint (u (W-1)))),z) ∧
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 11 Γ.length none (sourceUintFixedDeclareCompound sd si sv) (sy 2 (W-1)).1).run (.nil,(sy 2 (W-1)).2)=
        (.error (.revert (Source.panicData .arithmetic)),(.nil,z.2)) ∧
      ∃ (m0 ma : Machine),
        run (Objects.defaultDeclareCode (Γ := Δ) (Objects.DefaultBuilder.fixedPrimitive .uint 3).code 1) (machine 2 (W-1))=.ok m0 0 ∧
        run (aliasLocalCode 1 (.there td) (.here : Idx (.mem A::Δ) (.mem A))) m0=.ok ma 0 ∧
        run (fixedUintAddCode (C := C) (Γ := .mem A::Δ) 1 (.there td) (.there ti) (.there tv)) ma=.ok target 0 := by
  obtain ⟨base',m0,ma,target,out,z,hitems,hprog,he1,he2,hVec,hTable,hr,hl,hc0,hcA,hc1,hc2,hwhole,hm,ha,hmok,hstack,hfree,hex,hev,hlog,hfn,hzero,hbad,hneq⟩ :=
    SourceUintFixedDeclareCompoundControls.late_overflow p
  change SourceUintFixedAt z 3 out fresh at hr
  have hv : (out.get fresh).1=[u 0,u 0,u (W-1)] := by
    have h := congrArg (fun xs => xs[3]?) hVec
    simpa only [List.getElem?_cons_zero,List.getElem?_cons_succ,Option.some.injEq] using h
  have hbound : (u 2).1.toNat<out.len fresh .fixed := by simp only [Heap.len,MObj.elems_fixed,(out.get fresh).2];decide
  have hRoot : z.1.get (.there sd)=.memRef rfl 3 := by rw [hl];rfl
  have hIndex : z.1.get (.there si)=sourceUint (u 2) := by rw [hl];rfl
  have hBad : PrimTy.uint.inRange ((MObj.elems .fixed (out.get fresh))[(u 2).1.toNat].1+1)≠true := by
    simp only [MObj.elems_fixed,hv]
    change PrimTy.uint.inRange ((u (W-1)).1+1)≠true
    decide
  have h := resolved_uint_fixed_increment_overflow_word (Source.SemanticsExamples.G0 p) F0 0 pre rfl (renamed.withHeap out) fresh hr
    (.there sd) (.there si) (.there td) (.there ti) (u 2) hRoot hIndex rfl rfl hbound hBad hm
  exact ⟨base',out,z,target,hr,hVec,h.1,h.2.2.1,h.2.2.2,hm,ha,hmok,hstack,hfree,hex,hev,hlog,hfn,he1,hitems,m0,ma,hc0,hcA,hc1⟩

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedIncrementControls.prefix_postfix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_postfix
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedIncrementControls.reached_max_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reached_max_overflow
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
private theorem increment_run (m : Machine) (a k old : Fin W) (hk : k.val<3) (hs : a.val+k.val<W)
    (hp : m.mem 3=.val a) (hi : m.mem 6=.val k) (hc : m.mem (a.val+k.val)=.val old)
    (hadd : old.val+1<W) :
    run code m=.ok (writeMachine m (a.val+k.val) (.val ⟨old.val+1,hadd⟩)) 0 := by
  have hr := read_run m a k old hk hs hp hi hc
  have hvalue : run (binaryCode .uint .add rd [.push w[1]]) m=.ok (m.push (.val ⟨old.val+1,hadd⟩)) 0 := by
    change run (rd ++ ([.push w[1]] ++ uTail .add)) m=_
    rw [run_append_ok hr]
    rw [run_append_ok (show run [.push w[1]] (m.push (.val old))=.ok ((m.push (.val old)).push w[1]) 0 from rfl)]
    exact (add_tail m m.stack old.isLt (show (1 : Nat)<W from by decide)).trans (by rw [dif_pos hadd];rfl)
  change run ((binaryCode .uint .add rd [.push w[1]]) ++ ([.mload 3] ++ ([.mload 6] ++ Objects.writeCode (.fixed : ArrTy A (.prim .uint))))) m=_
  rw [run_append_ok hvalue]
  rw [run_append_ok (show run [.mload 3] (m.push (.val ⟨old.val+1,hadd⟩))=.ok ((m.push (.val ⟨old.val+1,hadd⟩)).push (.val a)) 0 from by change Out.ok ((m.push (.val ⟨old.val+1,hadd⟩)).push (m.mem 3)) 0=_;rw [hp])]
  rw [run_append_ok (show run [.mload 6] ((m.push (.val ⟨old.val+1,hadd⟩)).push (.val a))=.ok (((m.push (.val ⟨old.val+1,hadd⟩)).push (.val a)).push (.val k)) 0 from by change Out.ok (((m.push (.val ⟨old.val+1,hadd⟩)).push (.val a)).push (m.mem 6)) 0=_;rw [hi])]
  have ha := Objects.fixedAddr_run (m.push (.val ⟨old.val+1,hadd⟩)) a k 3
  rw [if_pos hk] at ha
  change run (Objects.fixedAddrCode 3 ++ [.mstoreAt]) (((m.push (.val ⟨old.val+1,hadd⟩)).push (.val a)).push (.val k))=_
  rw [run_append_ok ha]
  simp only [run,Machine.push,exec_cons_zero,Instr.step,wmod_of_lt hs,Out.ok_bind,exec_nil,writeMachine]

/-- Complete20word initial/first/second increment vectors. Prefix versus postfix
changes the independent Source expression result, not this statement's write. -/
theorem word_vectors :
    cells (machine 0 42)=[w[40],w[32],w[16],w[16],w[24],w[42],w[0],w[99],w[7],w[8],w[7],w[9],w[10],w[9],w[11],w[12],w[0],w[0],w[0],w[0]] ∧
    observed code (machine 0 42)=some
      ([w[40],w[32],w[16],w[16],w[24],w[42],w[0],w[99],w[8],w[8],w[7],w[9],w[10],w[9],w[11],w[12],w[0],w[0],w[0],w[0]],[w[77],w[88]]) ∧
    observed (code ++ code) (machine 0 42)=some
      ([w[40],w[32],w[16],w[16],w[24],w[42],w[0],w[99],w[9],w[8],w[7],w[9],w[10],w[9],w[11],w[12],w[0],w[0],w[0],w[0]],[w[77],w[88]]) ∧
    u 9≠u 8 ∧ u 8≠u 7 := by
  have h1 := increment_run (machine 0 42) ⟨16,by decide⟩ ⟨0,by decide⟩ ⟨7,by decide⟩ (by decide) (by decide) rfl rfl rfl (by decide)
  have h2 := increment_run (writeMachine (machine 0 42) 16 w[8]) ⟨16,by decide⟩ ⟨0,by decide⟩ ⟨8,by decide⟩ (by decide) (by decide) rfl rfl rfl (by decide)
  have h12 : run (code ++ code) (machine 0 42)=.ok (writeMachine (writeMachine (machine 0 42) 16 w[8]) 16 w[9]) 0 := by rw [run_append_ok h1];exact h2
  exact ⟨rfl,observed_ok h1,observed_ok h12,by decide,by decide⟩

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedIncrementControls.word_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_vectors
end Solidity.Backend.MemoryOps.SourceUintFixedIncrementControls
