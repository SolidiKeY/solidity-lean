import Solidity.Backend.MemoryOps.SourceUintFixedBumpSequence
import Solidity.Backend.MemoryOps.SourceUintFixedDeclareAliasControls
import Solidity.Evm.Correct
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.MemoryOps.SourceUintFixedDecrementControls
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


private def code : List Instr := fixedUintDecrementCode (C := C) 1 td ti

/-- The SAME actual write returns6 for prefix and7 for postfix. All Source
locals/objects/world and typed old aliases/neighbour/word ownership are observed. -/
theorem prefix_postfix (p : Roadmap.Pipeline) (pre : Bool) :
    ∃ (out : Heap H) (z : Source.EMState E0 Γ) (target : Machine),
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintFixedDecrement pre sd si)).run (sy 0 42)=
        (.ok (.val (sourceUint (if pre then u 6 else u 7))),z) ∧
      (Source.execS (Source.SemanticsExamples.G0 p) F0 4 Γ.length none (.expr (sourceUintFixedDecrement pre sd si) : Source.RStmt E0 [] false .body Γ Γ) (sy 0 42).1).run (.nil,(sy 0 42).2)=
        (.ok (.normal (sy 0 42).1),(.nil,z.2)) ∧
      TRun.incDec (fixedUintDecrementOp pre) (.mindex .fixed (.var td rfl) (.local ti)) (state 0 42)=.ok ⟨(state 0 42).withHeap out,List.prefix_refl _⟩ ∧
      run code (machine 0 42)=.ok target 0 ∧
      [(hp.get left).1,(out.get left).1,(out.get right).1,(out.get neighbor).1]=[[u 7,u 8,u 7],[u 6,u 8,u 7],[u 9,u 10,u 9],[u 11,u 12]] ∧
      [z.2.heap.get 0,z.2.heap.get 1,z.2.heap.get 2]=[some ⟨SA,sourceUintFixedObject (out.get left)⟩,(sy 0 42).2.heap.get 1,(sy 0 42).2.heap.get 2] ∧
      SourceUintFixedAt z 0 out left ∧ z.1=(sy 0 42).1 ∧
      [z.1.get sd,z.1.get sa,z.1.get ss]=[.memRef rfl 0,.memRef rfl 0,.memRef rfl 1] ∧
      Objects.StateRepr 1 1 8 (Frag.init Δ) ((state 0 42).withHeap out) base target ∧
      Objects.AllocatorRepr out base 8 ⟨40,by decide⟩ target ∧ Source.MemOK E0 SH z ∧
      target.stack=[w[77],w[88]] ∧ target.mem 0=w[40] ∧
      z.2.ex=(sy 0 42).2.ex ∧ z.2.events=(sy 0 42).2.events ∧ z.2.logs=(sy 0 42).2.logs ∧ z.2.fnLocals=(sy 0 42).2.fnLocals ∧
      (u 6)≠u 7 := by
  obtain ⟨out,z,target,hw,hs,he,hstmt,hi,hc,hr,hm,hmok,hl,hstack,hkeep,hobj,haddr,hex,hev,hlog,hfn⟩ :=
    resolved_uint_fixed_decrement_word (Source.SemanticsExamples.G0 p) F0 0 pre (state 0 42) left (represented_left 0 42)
      sd si td ti (u 0) rfl rfl rfl rfl (by simp only [Heap.len,MObj.elems_fixed];decide) (by simp only [MObj.elems_fixed];decide) SH (source_memOK 0 42) (initial_repr 0 42)
  simp only [MObj.elems_fixed] at hw he
  change hp.writeAddr (.index left .fixed (u 0)) (u 6)=some out at hw
  have hv := indexedWrite_elems hp out left .fixed (u 0) (u 6) hw
  simp only [MObj.elems_fixed] at hv
  have hVec : [(hp.get left).1,(out.get left).1,(out.get right).1,(out.get neighbor).1]=[[u 7,u 8,u 7],[u 6,u 8,u 7],[u 9,u 10,u 9],[u 11,u 12]] := by
    rw [hv,hobj right (by decide),hobj neighbor (by decide)];rfl
  have hTable : [z.2.heap.get 0,z.2.heap.get 1,z.2.heap.get 2]=[some ⟨SA,sourceUintFixedObject (out.get left)⟩,(sy 0 42).2.heap.get 1,(sy 0 42).2.heap.get 2] := by
    rw [hr,haddr 1 (by decide),haddr 2 (by decide)]
  have hExpr : (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintFixedDecrement pre sd si)).run (sy 0 42)=
      (.ok (.val (sourceUint (if pre then u 6 else u 7))),z) := by
    simpa only [MObj.elems_fixed] using he
  have hLoc : [z.1.get sd,z.1.get sa,z.1.get ss]=[.memRef rfl 0,.memRef rfl 0,.memRef rfl 1] := by rw [hl];rfl
  have ha := hkeep ⟨40,by decide⟩ (by decide) (initial_allocator 0 42)
  exact ⟨out,z,target,hExpr,hstmt,hi,hc,hVec,hTable,hr,hl,hLoc,hm,ha,hmok,hstack,ha.free.cell,hex,hev,hlog,hfn,by decide⟩

private def g := hp.allocDefault A rfl
private def fresh := g.val
private def grown := ((state 2 42).adopt g).1.push (t := .mem A) (some fresh)
private def renamed := grown.setLocal (.there td) (some fresh)
private def mid : Source.EMState E0 (SA::Γ) :=
  (.cons (.memRef rfl 3) (sy 2 42).1,{(sy 2 42).2 with heap := ((sy 2 42).2.heap.alloc ⟨SA,sourceUintFixedZero 3⟩).1})
private def rebound : Source.EMState E0 (SA::Γ) := (mid.1.set (.there sd) (.memRef rfl 3),mid.2)
private def cc : List Instr := Objects.defaultDeclareCode (Γ := Δ) (Objects.DefaultBuilder.fixedPrimitive .uint 3).code 1
private def ac : List Instr := aliasLocalCode 1 (.there td) (.here : Idx (.mem A::Δ) (.mem A))
private def wc : List Instr := Evm.compileVal 1 (.simple (.local (.there tv)) : Val C (.mem A::Δ) .uint) ++
  [.mload (Evm.cellOf 1 (.there td : Idx (.mem A::Δ) (.mem A)))] ++
  Evm.compileVal 1 (.simple (.local (.there ti)) : Val C (.mem A::Δ) .uint) ++ Objects.writeCode (.fixed : ArrTy A (.prim .uint))
private def dc : List Instr := Evm.compileVal 1 (deleteDefaultValue .uint : Val C (.mem A::Δ) .uint) ++
  [.mload (Evm.cellOf 1 (.there td : Idx (.mem A::Δ) (.mem A)))] ++
  Evm.compileVal 1 (.simple (.local (.there ti)) : Val C (.mem A::Δ) .uint) ++ Objects.writeCode (.fixed : ArrTy A (.prim .uint))

/-- Actual declaration→alias→write42→delete0 Source/typed/word execution reaches
zero; checked decrement then fails there. No Source or target prefix is assumed. -/
theorem reached_zero_underflow (p : Roadmap.Pipeline) (pre : Bool) :
    ∃ (base' : Nat → Fin W) (m0 m1 target : Machine) (o1 out : Heap g.H') (z1 z : Source.EMState E0 (SA::Γ)),
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 11 Γ.length none (sourceUintFixedDeclareAlias sd si sv) (sy 2 42).1).run (.nil,(sy 2 42).2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
      Prog.run (state 2 42) (intrinsicUintFixedDeclareAlias td ti tv)=.ok ⟨renamed.withHeap out,g.ext⟩ ∧
      run cc (machine 2 42)=.ok m0 0 ∧ run (ac ++ wc) m0=.ok m1 0 ∧ run dc m1=.ok target 0 ∧
      run (cc ++ ac ++ wc ++ dc) (machine 2 42)=.ok target 0 ∧
      [(o1.get fresh).1,(out.get fresh).1]=[[u 0,u 0,u 42],[u 0,u 0,u 0]] ∧
      [(out.get (left.wk g.ext)).1,(out.get (right.wk g.ext)).1,(out.get (neighbor.wk g.ext)).1]=[[u 7,u 8,u 7],[u 9,u 10,u 9],[u 11,u 12]] ∧
      [z1.2.heap.get 0,z1.2.heap.get 1,z1.2.heap.get 2,z1.2.heap.get 3,z.2.heap.get 0,z.2.heap.get 1,z.2.heap.get 2,z.2.heap.get 3]=
        [(sy 2 42).2.heap.get 0,(sy 2 42).2.heap.get 1,(sy 2 42).2.heap.get 2,some ⟨SA,sourceUintFixedObject (o1.get fresh)⟩,
         (sy 2 42).2.heap.get 0,(sy 2 42).2.heap.get 1,(sy 2 42).2.heap.get 2,some ⟨SA,sourceUintFixedObject (out.get fresh)⟩] ∧
      SourceUintFixedAt z 3 out fresh ∧ z1.1=rebound.1 ∧ z.1=rebound.1 ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 7 (sourceUintFixedIndexedAssign (.there sd) (.there si) (.there sv))).run rebound=
        (.ok (.val (sourceUint (u 42))),z1) ∧
      z1.2.ex=(sy 2 42).2.ex ∧ z1.2.events=(sy 2 42).2.events ∧ z1.2.logs=(sy 2 42).2.logs ∧ z1.2.fnLocals=(sy 2 42).2.fnLocals ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintFixedDecrement pre (.there sd) (.there si))).run z=
        (.error (.revert (Source.panicData .arithmetic)),z) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local (.there sa)) (.local (.there si)) rfl)).run z=
        (.ok (.val (sourceUint (u 7))),z) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local (.there sd)) (.local (.there si)) rfl)).run z=
        (.ok (.val (sourceUint (u 0))),z) ∧
      TRun.incDec (fixedUintDecrementOp pre) (.mindex .fixed (.var (.there td) rfl) (.local (.there ti))) (renamed.withHeap out)=.error .revert ∧
      run (fixedUintDecrementCode (C := C) (Γ := .mem A::Δ) 1 (.there td) (.there ti)) target=.revert ∧
      Objects.StateRepr 1 1 8 ((Frag.init Δ).push (.mem A) .ok) (renamed.withHeap out) base' target ∧
      Objects.AllocatorRepr out base' 8 ⟨43,by decide⟩ target ∧ Source.MemOK E0 SH z ∧
      target.stack=[w[77],w[88]] ∧ target.mem 0=w[43] ∧
      [z.1.get .here,z.1.get (.there sd),z.1.get (.there sa),z.1.get (.there ss)]=[.memRef rfl 3,.memRef rfl 3,.memRef rfl 0,.memRef rfl 1] ∧
      z.2.ex=(sy 2 42).2.ex ∧ z.2.events=(sy 2 42).2.events ∧ z.2.logs=(sy 2 42).2.logs ∧ z.2.fnLocals=(sy 2 42).2.fnLocals := by
  obtain ⟨base',m0,m1,target,o1,out,zOld,z,hd,hitems,hprog,hw,hdw,hr0,hr1,hr2,hc0,hc1,hc2,hwhole,hm,ha,hmok0,hmok1,hmok2,hl1,hl2,hrootS,hnewS,hrootT,hnewT,hobjects,hsource,hid,hne,hstack,hfree,hsource1,hex,hev,hlog,hfn⟩ :=
    source_uint_fixed_declare_alias_word (Source.SemanticsExamples.G0 p) F0 (sy 2 42) (state 2 42) 3 (by decide) sd td si sv ti tv (u 2) (u 42)
      rfl rfl rfl rfl (by decide) SH (source_memOK 2 42) (initial_repr 2 42) (initial_allocator 2 42) (by decide) (by decide) (by decide)
  change SourceUintFixedAt mid 3 g.heap fresh at hr0
  have hrA : SourceUintFixedAt rebound 3 g.heap fresh := hr0
  obtain ⟨ow,z1,hwrite,hwriteS,hrW⟩ := hrA.write_addr F0 6 (u 2) (u 42) (by decide)
  have how : ow=o1 := Option.some.inj (hwrite.symm.trans hw)
  subst ow
  have heWrite := hrA.eval_assign_of_run (Source.SemanticsExamples.G0 p) F0 4 (.there sd) (.there si) (.there sv) (u 2) (u 42) rfl rfl rfl (by decide) hwriteS
  have hfW := hrA.write_frames F0 6 (u 2) (u 42) (by decide) hwrite hwriteS
  change SourceUintFixedAt z1 3 o1 fresh at hrW
  change SourceUintFixedAt z 3 out fresh at hr2
  have hz : (g.heap.get fresh).1=[u 0,u 0,u 0] := by
    have h := (source_uint_fixed_intrinsic (sy 2 42) hp 3 (by decide)).2.1
    rw [show PrimTy.dflt .uint=u 0 from by decide] at h
    simpa only [MObj.elems_fixed,List.replicate_succ,List.replicate_zero] using h
  have hv1 := indexedWrite_elems g.heap o1 fresh .fixed (u 2) (u 42) hw
  have hv2 := indexedWrite_elems o1 out fresh .fixed (u 2) (PrimTy.dflt .uint) hdw
  simp only [MObj.elems_fixed] at hv1 hv2
  have hV1 : (o1.get fresh).1=[u 0,u 0,u 42] := by rw [hv1,hz];rfl
  have hV2 : (out.get fresh).1=[u 0,u 0,u 0] := by rw [hv2,hV1];rfl
  have hVec : [(out.get (left.wk g.ext)).1,(out.get (right.wk g.ext)).1,(out.get (neighbor.wk g.ext)).1]=[[u 7,u 8,u 7],[u 9,u 10,u 9],[u 11,u 12]] := by rw [hobjects left,hobjects right,hobjects neighbor];rfl
  have hgetL : (sy 2 42).2.heap.get 0≠none := by rw [represented_left 2 42];exact Option.some_ne_none _
  have hgetR : (sy 2 42).2.heap.get 1≠none := by rw [represented_right 2 42];exact Option.some_ne_none _
  have hgetN : (sy 2 42).2.heap.get 2≠none := by rw [represented_neighbor 2 42];exact Option.some_ne_none _
  have hTable : [z1.2.heap.get 0,z1.2.heap.get 1,z1.2.heap.get 2,z1.2.heap.get 3,z.2.heap.get 0,z.2.heap.get 1,z.2.heap.get 2,z.2.heap.get 3]=
      [(sy 2 42).2.heap.get 0,(sy 2 42).2.heap.get 1,(sy 2 42).2.heap.get 2,some ⟨SA,sourceUintFixedObject (o1.get fresh)⟩,
       (sy 2 42).2.heap.get 0,(sy 2 42).2.heap.get 1,(sy 2 42).2.heap.get 2,some ⟨SA,sourceUintFixedObject (out.get fresh)⟩] := by
    rw [hfW.2.2.1 0 (by decide),hfW.2.2.1 1 (by decide),hfW.2.2.1 2 (by decide),hrW,hsource 0 hgetL,hsource 1 hgetR,hsource 2 hgetN,hr2]
    rfl
  have hk : (u 2).1.toNat<out.len fresh .fixed := by simp only [Heap.len,MObj.elems_fixed,(out.get fresh).2];decide
  have hbad : PrimTy.uint.inRange ((MObj.elems .fixed (out.get fresh))[(u 2).1.toNat].1-1)≠true := by
    simp only [MObj.elems_fixed,hV2]
    change PrimTy.uint.inRange ((u 0).1-1)≠true
    decide
  have hIndex : z.1.get (.there si)=sourceUint (u 2) := by rw [hl2];rfl
  have h := resolved_uint_fixed_decrement_underflow_word (Source.SemanticsExamples.G0 p) F0 0 pre rfl (renamed.withHeap out) fresh hr2
    (.there sd) (.there si) (.there td) (.there ti) (u 2) hrootS hIndex rfl rfl hk hbad hm
  have hOld : SourceUintFixedAt z 0 out (HRef.wk g.ext left) := by
    unfold SourceUintFixedAt
    rw [hsource 0 hgetL,hobjects left,sourceUintFixedObject_wk]
    exact represented_left 2 42
  have hOldValues : (out.get (HRef.wk g.ext left)).1=[u 7,u 8,u 7] := by
    have h := congrArg (fun xs => xs[0]?) hVec
    simpa only [List.getElem?_cons_zero,Option.some.injEq] using h
  have hReadOld := hOld.eval_index (Source.SemanticsExamples.G0 p) F0 0 (.there sa) (.there si) (u 2)
    (by rw [hl2];rfl) hIndex (by decide)
  have hReadNew := hr2.eval_index (Source.SemanticsExamples.G0 p) F0 0 (.there sd) (.there si) (u 2) hrootS hIndex (by decide)
  simp only [hOldValues] at hReadOld
  simp only [hV2] at hReadNew
  have hLoc : [z.1.get .here,z.1.get (.there sd),z.1.get (.there sa),z.1.get (.there ss)]=[.memRef rfl 3,.memRef rfl 3,.memRef rfl 0,.memRef rfl 1] := by rw [hl2];rfl
  exact ⟨base',m0,m1,target,o1,out,z1,z,hitems,hprog,hc0,hc1,hc2,hwhole,by rw [hV1,hV2],hVec,hTable,hr2,hfW.1,hl2,heWrite,hfW.2.2.2.1,hfW.2.2.2.2.1,hfW.2.2.2.2.2.1,hfW.2.2.2.2.2.2,h.1,hReadOld,hReadNew,h.2.2.1,h.2.2.2,hm,ha,hmok2,hstack,hfree,hLoc,hex,hev,hlog,hfn⟩

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDecrementControls.reached_zero_underflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reached_zero_underflow

/-- Genuine two-statement Source Items, typed Prog and whole target append at
reached LEFT7→8→7. The decrement postfix result8 discriminates stale old7. -/
theorem reached_pair (p : Roadmap.Pipeline) (pinc pdec : Bool) :
    ∃ (o1 o2 : Heap H) (z1 z2 : Source.EMState E0 Γ) (m1 m2 : Machine),
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 4 (sourceUintFixedIncrement pinc sd si)).run (sy 0 42)=
        (.ok (.val (sourceUint (if pinc then u 8 else u 7))),z1) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintFixedDecrement pdec sd si)).run z1=
        (.ok (.val (sourceUint (if pdec then u 7 else u 8))),z2) ∧
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 Γ.length none (sourceUintFixedBumpPair pinc pdec sd si) (sy 0 42).1).run (.nil,(sy 0 42).2)=
        (.ok (.normal z2.1),(.nil,z2.2)) ∧
      Prog.run (state 0 42) (intrinsicUintFixedBumpPair pinc pdec td ti)=.ok ⟨(state 0 42).withHeap o2,List.prefix_refl _⟩ ∧
      [(o1.get left).1,(o1.get right).1,(o1.get neighbor).1,(o2.get left).1,(o2.get right).1,(o2.get neighbor).1]=
        [[u 8,u 8,u 7],[u 9,u 10,u 9],[u 11,u 12],[u 7,u 8,u 7],[u 9,u 10,u 9],[u 11,u 12]] ∧ o2=hp ∧
      [z1.2.heap.get 0,z1.2.heap.get 1,z1.2.heap.get 2,z2.2.heap.get 0,z2.2.heap.get 1,z2.2.heap.get 2]=
        [some ⟨SA,sourceUintFixedObject (o1.get left)⟩,(sy 0 42).2.heap.get 1,(sy 0 42).2.heap.get 2,
         (sy 0 42).2.heap.get 0,(sy 0 42).2.heap.get 1,(sy 0 42).2.heap.get 2] ∧
      SourceUintFixedAt z1 0 o1 left ∧ SourceUintFixedAt z2 0 o2 left ∧ z1.1=(sy 0 42).1 ∧ z2.1=(sy 0 42).1 ∧
      run (fixedUintIncrementCode (C := C) 1 td ti) (machine 0 42)=.ok m1 0 ∧ run code m1=.ok m2 0 ∧
      run (fixedUintIncrementCode (C := C) 1 td ti ++ code) (machine 0 42)=.ok m2 0 ∧
      Objects.StateRepr 1 1 8 (Frag.init Δ) ((state 0 42).withHeap o2) base m2 ∧
      Objects.AllocatorRepr o2 base 8 ⟨40,by decide⟩ m2 ∧ Source.MemOK E0 SH z1 ∧ Source.MemOK E0 SH z2 ∧
      m2.stack=[w[77],w[88]] ∧ m2.mem 0=w[40] ∧
      z2.2.ex=(sy 0 42).2.ex ∧ z2.2.events=(sy 0 42).2.events ∧ z2.2.logs=(sy 0 42).2.logs ∧ z2.2.fnLocals=(sy 0 42).2.fnLocals ∧
      u 8≠u 7 ∧ u 6≠u 8 := by
  obtain ⟨o1,o2,z1,z2,m1,m2,he1,he2,hitems,hprog,hw1,hw2,hrestore,hc1,hc2,hwhole,hr1,hr2,hm2,ha2,hmok1,hmok2,hl1,hl2,hstack,hfree,haddr1,hsource,hex,hev,hlog,hfn⟩ :=
    resolved_uint_fixed_bump_pair_word (Source.SemanticsExamples.G0 p) F0 0 Γ.length pinc pdec (state 0 42) left (represented_left 0 42)
      sd si td ti (u 0) rfl rfl rfl rfl (by simp only [Heap.len,MObj.elems_fixed];decide) (by simp only [MObj.elems_fixed];decide)
      SH (source_memOK 0 42) (initial_repr 0 42) (initial_allocator 0 42) (by decide)
  simp only [MObj.elems_fixed] at he1 he2 hw1
  change hp.writeAddr (.index left .fixed (u 0)) (u 8)=some o1 at hw1
  have hv := indexedWrite_elems hp o1 left .fixed (u 0) (u 8) hw1
  simp only [MObj.elems_fixed] at hv
  have hVec : [(o1.get left).1,(o1.get right).1,(o1.get neighbor).1,(o2.get left).1,(o2.get right).1,(o2.get neighbor).1]=
      [[u 8,u 8,u 7],[u 9,u 10,u 9],[u 11,u 12],[u 7,u 8,u 7],[u 9,u 10,u 9],[u 11,u 12]] := by
    rw [hv,hrestore]
    have hdef : o1=hp.set left (MObj.setElem .fixed (hp.get left) (u 0).1.toNat (u 8)) := by
      simp only [Heap.writeAddr,Heap.setIndex,show (u 0).1.toNat<(MObj.elems .fixed (hp.get left)).length from by simp only [MObj.elems_fixed];decide,↓reduceIte] at hw1
      exact Option.some.inj hw1.symm
    rw [hdef,Heap.get_set_ne _ left right (by decide),Heap.get_set_ne _ left neighbor (by decide)]
    rfl
  have hTable : [z1.2.heap.get 0,z1.2.heap.get 1,z1.2.heap.get 2,z2.2.heap.get 0,z2.2.heap.get 1,z2.2.heap.get 2]=
      [some ⟨SA,sourceUintFixedObject (o1.get left)⟩,(sy 0 42).2.heap.get 1,(sy 0 42).2.heap.get 2,
       (sy 0 42).2.heap.get 0,(sy 0 42).2.heap.get 1,(sy 0 42).2.heap.get 2] := by
    rw [hr1,haddr1 1 (by decide),haddr1 2 (by decide),hsource 0,hsource 1,hsource 2]
  exact ⟨o1,o2,z1,z2,m1,m2,he1,he2,hitems,hprog,hVec,hrestore,hTable,hr1,hr2,hl1,hl2,hc1,hc2,hwhole,hm2,ha2,hmok1,hmok2,hstack,hfree,hex,hev,hlog,hfn,by decide,by decide⟩

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDecrementControls.reached_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reached_pair
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
private def incCode : List Instr := fixedUintIncrementCode (C := C) 1 td ti
private theorem increment_run (m : Machine) (a k old : Fin W) (hk : k.val<3) (hs : a.val+k.val<W)
    (hp : m.mem 3=.val a) (hi : m.mem 6=.val k) (hc : m.mem (a.val+k.val)=.val old)
    (hadd : old.val+1<W) :
    run incCode m=.ok (writeMachine m (a.val+k.val) (.val ⟨old.val+1,hadd⟩)) 0 := by
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

private theorem decrement_run (m : Machine) (a k old : Fin W) (hk : k.val<3) (hs : a.val+k.val<W)
    (hp : m.mem 3=.val a) (hi : m.mem 6=.val k) (hc : m.mem (a.val+k.val)=.val old)
    (hsub : 1≤old.val) (hbelow : old.val-1<W) :
    run code m=.ok (writeMachine m (a.val+k.val) (.val ⟨old.val-1,hbelow⟩)) 0 := by
  have hr := read_run m a k old hk hs hp hi hc
  have hvalue : run (binaryCode .uint .sub rd [.push w[1]]) m=.ok (m.push (.val ⟨old.val-1,hbelow⟩)) 0 := by
    change run (rd ++ ([.push w[1]] ++ uTail .sub)) m=_
    rw [run_append_ok hr]
    rw [run_append_ok (show run [.push w[1]] (m.push (.val old))=.ok ((m.push (.val old)).push w[1]) 0 from rfl)]
    have h := sub_tail m m.stack old.isLt (show (1 : Nat)<W from by decide)
    rw [dif_pos hsub] at h
    simpa only [wmod_of_lt hbelow] using h
  change run ((binaryCode .uint .sub rd [.push w[1]]) ++ ([.mload 3] ++ ([.mload 6] ++ Objects.writeCode (.fixed : ArrTy A (.prim .uint))))) m=_
  rw [run_append_ok hvalue]
  rw [run_append_ok (show run [.mload 3] (m.push (.val ⟨old.val-1,hbelow⟩))=.ok ((m.push (.val ⟨old.val-1,hbelow⟩)).push (.val a)) 0 from by change Out.ok ((m.push (.val ⟨old.val-1,hbelow⟩)).push (m.mem 3)) 0=_;rw [hp])]
  rw [run_append_ok (show run [.mload 6] ((m.push (.val ⟨old.val-1,hbelow⟩)).push (.val a))=.ok (((m.push (.val ⟨old.val-1,hbelow⟩)).push (.val a)).push (.val k)) 0 from by change Out.ok (((m.push (.val ⟨old.val-1,hbelow⟩)).push (.val a)).push (m.mem 6)) 0=_;rw [hi])]
  have ha := Objects.fixedAddr_run (m.push (.val ⟨old.val-1,hbelow⟩)) a k 3
  rw [if_pos hk] at ha
  change run (Objects.fixedAddrCode 3 ++ [.mstoreAt]) (((m.push (.val ⟨old.val-1,hbelow⟩)).push (.val a)).push (.val k))=_
  rw [run_append_ok ha]
  simp only [run,Machine.push,exec_cons_zero,Instr.step,wmod_of_lt hs,Out.ok_bind,exec_nil,writeMachine]

/-- Complete20word initial/decrement/decrement and genuine increment/decrement
restoration vectors; wrong operation and stale postfix value are distinguished. -/
theorem word_vectors :
    cells (machine 0 42)=[w[40],w[32],w[16],w[16],w[24],w[42],w[0],w[99],w[7],w[8],w[7],w[9],w[10],w[9],w[11],w[12],w[0],w[0],w[0],w[0]] ∧
    observed code (machine 0 42)=some
      ([w[40],w[32],w[16],w[16],w[24],w[42],w[0],w[99],w[6],w[8],w[7],w[9],w[10],w[9],w[11],w[12],w[0],w[0],w[0],w[0]],[w[77],w[88]]) ∧
    observed (code ++ code) (machine 0 42)=some
      ([w[40],w[32],w[16],w[16],w[24],w[42],w[0],w[99],w[5],w[8],w[7],w[9],w[10],w[9],w[11],w[12],w[0],w[0],w[0],w[0]],[w[77],w[88]]) ∧
    observed incCode (machine 0 42)=some
      ([w[40],w[32],w[16],w[16],w[24],w[42],w[0],w[99],w[8],w[8],w[7],w[9],w[10],w[9],w[11],w[12],w[0],w[0],w[0],w[0]],[w[77],w[88]]) ∧
    observed (incCode ++ code) (machine 0 42)=some
      ([w[40],w[32],w[16],w[16],w[24],w[42],w[0],w[99],w[7],w[8],w[7],w[9],w[10],w[9],w[11],w[12],w[0],w[0],w[0],w[0]],[w[77],w[88]]) ∧
    u 6≠u 8 ∧ u 6≠u 7 := by
  have h1 := decrement_run (machine 0 42) ⟨16,by decide⟩ ⟨0,by decide⟩ ⟨7,by decide⟩ (by decide) (by decide) rfl rfl rfl (by decide) (by decide)
  have h2 := decrement_run (writeMachine (machine 0 42) 16 w[6]) ⟨16,by decide⟩ ⟨0,by decide⟩ ⟨6,by decide⟩ (by decide) (by decide) rfl rfl rfl (by decide) (by decide)
  have h12 : run (code ++ code) (machine 0 42)=.ok (writeMachine (writeMachine (machine 0 42) 16 w[6]) 16 w[5]) 0 := by rw [run_append_ok h1];exact h2
  have hI := increment_run (machine 0 42) ⟨16,by decide⟩ ⟨0,by decide⟩ ⟨7,by decide⟩ (by decide) (by decide) rfl rfl rfl (by decide)
  have hD := decrement_run (writeMachine (machine 0 42) 16 w[8]) ⟨16,by decide⟩ ⟨0,by decide⟩ ⟨8,by decide⟩ (by decide) (by decide) rfl rfl rfl (by decide) (by decide)
  have hID : run (incCode ++ code) (machine 0 42)=.ok (writeMachine (writeMachine (machine 0 42) 16 w[8]) 16 w[7]) 0 := by rw [run_append_ok hI];exact hD
  exact ⟨rfl,observed_ok h1,observed_ok h12,observed_ok hI,observed_ok hID,by decide,by decide⟩

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDecrementControls.word_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_vectors
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDecrementControls.prefix_postfix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_postfix
end Solidity.Backend.MemoryOps.SourceUintFixedDecrementControls
