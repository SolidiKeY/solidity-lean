import Solidity.Backend.MemoryOps.SourceUintFixedDeclaration
import Solidity.Evm.Correct
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.MemoryOps.SourceUintFixedDefaultControls
open Evm Evm.Memory
open Source.SemanticsExamples (E0 F0 s0)
private def C : Contract := {vars := []}
private abbrev A : RefTy := .fixed (.prim .uint) 1
private abbrev H : HTy := [A,A]
private abbrev Δ : Ctx := [.val .uint,.mem A,.mem A,.mem A]
private abbrev SA := Source.STy.array .memory (.int .u256) (some 1)
private abbrev Γ : Source.RCtx := [.int .u256,SA,SA,SA]
private def u (v : Nat) : PrimTy.uint.Denote := indexValue (wmod v)
private def left : HRef H A := ⟨0,rfl⟩
private def right : HRef H A := ⟨1,rfl⟩
private def hp : Heap H := (⟨[u 7],by decide⟩,⟨[u 9],by decide⟩,())
private def state : State C Δ := {storage := Storage.init C,H := H,heap := hp,env := (u 0,some right,some left,some left,())}
private def base (i : Nat) : Fin W := if i=0 then wmod 16 else wmod 24
private def machine : Machine := {Machine.init with stack := [w[77]],mem := fun a =>
  if a=0 then w[32] else if a=1 then w[16] else if a=2 then w[16] else if a=3 then w[24]
  else if a=15 then w[99] else if a=16 then w[7] else if a=24 then w[9] else w[0]}
private theorem refs {R : RefTy} (q : HRef H R) : R=A ∧ (HEq q left ∨ HEq q right) := by
  rcases q with ⟨i,hi⟩
  cases i with
  | zero => cases hi;exact ⟨rfl,.inl HEq.rfl⟩
  | succ i => cases i with
    | zero => cases hi;exact ⟨rfl,.inr HEq.rfl⟩
    | succ i => cases hi
private theorem no_struct {s : Name} (q : HRef H (.struct s)) : False := by
  obtain ⟨ht,_⟩ := refs q
  cases ht
private theorem heap_repr : Objects.HeapRepr hp base 8 machine := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
  · intro R q
    obtain ⟨rfl,hq|hq⟩ := refs q <;> cases hq <;> decide
  · intro R q
    obtain ⟨rfl,hq|hq⟩ := refs q <;> cases hq <;> decide
  · intro R Q q r hn
    obtain ⟨rfl,hq|hq⟩ := refs q <;> cases hq
      <;> obtain ⟨rfl,hr|hr⟩ := refs r <;> cases hr
      <;> first | exact (hn rfl).elim | decide
  · intro A E a r
    obtain ⟨rfl,hr|hr⟩ := refs r <;> cases hr <;> cases a
    all_goals
      refine ⟨by decide,?_,?_⟩
      · intro hh
        cases (by simpa only [Objects.header] using hh : (0 : Nat)=1)
      · intro i v hv
        simp only [Heap.get,Objs.get,hp,left,right,MObj.elems_fixed] at hv
        cases i with
        | zero => cases Option.some.inj hv;exact ReprV.uint_of rfl
        | succ i => cases hv
  · intro s r
    exact (no_struct r).elim
  · intro s f R r hf
    exact (no_struct r).elim
private theorem initial_repr : Objects.StateRepr 1 1 8 (Frag.init Δ) state base machine := by
  have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨?_,heap_repr,?_,by decide⟩
  · refine ⟨hc.store,?_,?_,hc.net,hc.netSelf,hc.bound,?_,hc.env,hc.funds,hc.oracle⟩
    · intro p i
      cases i with
      | here => exact ReprV.uint_of rfl
      | there i => cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
    · intro R i hi
      cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
    · intro R i hi
      cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
  · intro R i
    cases i with
    | there i => cases i with
      | here => exact ⟨right,rfl,rfl⟩
      | there i => cases i with
        | here => exact ⟨left,rfl,rfl⟩
        | there i => cases i with
          | here => exact ⟨left,rfl,rfl⟩
          | there i => nomatch i
private theorem initial_allocator : Objects.AllocatorRepr hp base 8 ⟨32,by decide⟩ machine := by
  refine ⟨heap_repr,⟨by decide,by decide,rfl,?_⟩,?_⟩
  · intro a ha
    change 32≤a at ha
    simp only [machine,if_neg (show a≠0 by omega),if_neg (show a≠1 by omega),if_neg (show a≠2 by omega),
      if_neg (show a≠3 by omega),if_neg (show a≠15 by omega),if_neg (show a≠16 by omega),if_neg (show a≠24 by omega)]
  · intro R q
    obtain ⟨rfl,hq|hq⟩ := refs q <;> cases hq <;> decide

private def sourceObject (v : PrimTy.uint.Denote) : Source.Data E0.layout SA :=
  .array 1 (fun _ h => by cases h;rfl) (fun _ => .val (sourceUint v))
private theorem one_conversion {K : HTy} (v : PrimTy.uint.Denote) :
    sourceUintFixedObject (D := E0.layout) (⟨[v],by rfl⟩ : MObj K A)=sourceObject v := by
  unfold sourceUintFixedObject sourceObject
  congr 1
  funext i
  have hi : i.val=0 := by have h := i.isLt;omega
  simp only [hi,List.getElem_cons_zero]
private def y0 : Source.EMState E0 [] := (.nil,s0)
private def y1 : Source.EMState E0 [] := ((Source.allocRef (sourceObject (u 7))).run y0).2
private def y2 : Source.EMState E0 [] := ((Source.allocRef (sourceObject (u 9))).run y1).2
private def sy : Source.EMState E0 Γ :=
  (.cons (sourceUint (u 0)) (.cons (.memRef rfl 1) (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil))),y2.2)
private abbrev SH := (Source.Heap.empty (D := E0.layout)).ty
private def si : Source.Idx Γ (.int .u256) := .here
private def sr : Source.Idx Γ SA := .there (.there .here)
private def salias : Source.Idx Γ SA := .there (.there (.there .here))
private theorem represented_left : SourceUintFixedAt sy 0 hp left := by
  unfold SourceUintFixedAt
  change sy.2.heap.get 0=some ⟨SA,sourceUintFixedObject (D := E0.layout) (⟨[u 7],by decide⟩ : MObj H A)⟩
  rw [one_conversion];rfl
private theorem represented_right : SourceUintFixedAt sy 1 hp right := by
  unfold SourceUintFixedAt
  change sy.2.heap.get 1=some ⟨SA,sourceUintFixedObject (D := E0.layout) (⟨[u 9],by decide⟩ : MObj H A)⟩
  rw [one_conversion];rfl
private theorem source_memOK : Source.MemOK E0 SH sy := by
  have h0 : Source.MemOK E0 SH y0 :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have h1 := source_uint_fixed_alloc_memOK (E := E0) (Γ := []) SH (⟨[u 7],by decide⟩ : MObj H A) y0 h0
  rw [one_conversion] at h1
  change Source.MemOK E0 SH y1 ∧ _ at h1
  have h2 := source_uint_fixed_alloc_memOK (E := E0) (Γ := []) SH (⟨[u 9],by decide⟩ : MObj H A) y1 h1.1
  rw [one_conversion] at h2
  change Source.MemOK E0 SH y2 ∧ _ at h2
  exact ⟨⟨h2.1.1.1,⟨trivial,⟨⟨SA,rfl,rfl⟩,⟨⟨SA,rfl,rfl⟩,⟨⟨SA,rfl,rfl⟩,trivial⟩⟩⟩⟩⟩,h2.1.2⟩

private def g (n : Nat) := hp.allocDefault (.fixed (.prim .uint) n) rfl
private def fresh (n : Nat) := (g n).val
private def grownState (n : Nat) := (state.adopt (g n)).1.push (t := .mem (.fixed (.prim .uint) n)) (some (fresh n))
private def post (n : Nat) : Source.EMState E0 ((.array .memory (.int .u256) (some n))::Γ) :=
  (.cons (.memRef rfl 2) sy.1,{sy.2 with heap := (sy.2.heap.alloc ⟨.array .memory (.int .u256) (some n),sourceUintFixedZero n⟩).1})
private def wordPost (n : Nat) := writeMachine (allocateStructMachine machine ⟨32,by decide⟩ (max 1 n)) 5 w[32]
private def code (n : Nat) := Objects.defaultDeclareCode (Γ := Δ) (Objects.DefaultBuilder.fixedPrimitive .uint n).code 1
private def cells (m : Machine) := [m.mem 0,m.mem 1,m.mem 2,m.mem 3,m.mem 4,m.mem 5,m.mem 7,m.mem 15,
  m.mem 16,m.mem 24,m.mem 31,m.mem 32,m.mem 33,m.mem 34,m.mem 35,m.mem 40]
private theorem word_run (n : Nat) : run (code n) machine=.ok (wordPost n) 0 := by
  change run (allocateStructCode (max 1 n) ++ [.mstore 5]) machine=_
  rw [run_append_ok (allocateStruct_run machine ⟨32,by decide⟩ (max 1 n) rfl)]
  rfl

/-- Independently inhabited populated Source and full word ownership inputs. -/
theorem initial_views : Source.MemOK E0 SH sy ∧ SourceUintFixedAt sy 0 hp left ∧
    SourceUintFixedAt sy 1 hp right ∧ Objects.StateRepr 1 1 8 (Frag.init Δ) state base machine ∧
    Objects.AllocatorRepr hp base 8 ⟨32,by decide⟩ machine :=
  ⟨source_memOK,represented_left,represented_right,initial_repr,initial_allocator⟩

/-- Positive admitted-shape APPLICATION, not an admission theorem. Runtime n is
unrestricted beyond positivity and the existing target ownership/space premise.
The whole declaration code, typed local extension, headerless words, old aliases
and independent Source fixed type are observed at the SAME actual outputs. -/
theorem populated_declaration (p : Roadmap.Pipeline) (n : Nat) (hn : 0<n)
    (hs : 32+max 1 n<W) :
    ∃ base',
      (Source.execS (Source.SemanticsExamples.G0 p) F0 (n+4) Γ.length none
        (.declVar (.array .memory (.int .u256) (some n)) : Source.RStmt E0 [] false .body Γ ((.array .memory (.int .u256) (some n))::Γ)) sy.1).run (.nil,sy.2)=
          (.ok (.normal (post n).1),(.nil,(post n).2)) ∧
      TRun.declMem (.fixed (.prim .uint) n) none rfl state=.ok ⟨grownState n,(g n).ext⟩ ∧
      run (code n) machine=.ok (wordPost n) 0 ∧
      SourceUintFixedAt (post n) 2 (g n).heap (fresh n) ∧
      SourceUintFixedAt (post n) 0 (g n).heap (left.wk (g n).ext) ∧
      SourceUintFixedAt (post n) 1 (g n).heap (right.wk (g n).ext) ∧
      MObj.elems .fixed ((g n).heap.get (fresh n))=List.replicate n (PrimTy.dflt .uint) ∧
      [(g n).heap.get (left.wk (g n).ext) |>.1,(g n).heap.get (right.wk (g n).ext) |>.1]=[[u 7],[u 9]] ∧
      [sy.2.heap.get 0,sy.2.heap.get 1,sy.2.heap.get 2,(post n).2.heap.get 0,(post n).2.heap.get 1,(post n).2.heap.get 2]=
        [some ⟨SA,sourceObject (u 7)⟩,some ⟨SA,sourceObject (u 9)⟩,none,
         some ⟨SA,sourceObject (u 7)⟩,some ⟨SA,sourceObject (u 9)⟩,
         some ⟨.array .memory (.int .u256) (some n),sourceUintFixedZero n⟩] ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2
        (.indexArray (.local .here) (.local (.there si)) rfl)).run (post n)=
          (.ok (.val (sourceUint (PrimTy.dflt .uint))),post n) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2
        (.indexArray (.local (.there salias)) (.local (.there si)) rfl)).run (post n)=
          (.ok (.val (sourceUint (u 7))),post n) ∧
      (Source.memElem (E := E0) (Γ := (.array .memory (.int .u256) (some n))::Γ) 2 n (.int .u256)).run (post n)=
        (.error (.revert (Source.panicData .index)),post n) ∧
      [cells machine,cells (wordPost n)]=
        [[w[32],w[16],w[16],w[24],w[0],w[0],w[0],w[99],w[7],w[9],w[0],w[0],w[0],w[0],w[0],w[0]],
         [.val (wmod (32+max 1 n)),w[16],w[16],w[24],w[0],w[32],w[0],w[99],w[7],w[9],w[0],w[0],w[0],w[0],w[0],w[0]]] ∧
      (∀ i, i<n → (wordPost n).mem (32+i)=w[0]) ∧
      (post n).1.get .here=.memRef rfl 2 ∧ (post n).1.get (.there sr)=.memRef rfl 0 ∧
      (post n).1.get (.there salias)=.memRef rfl 0 ∧
      TEnv.get .here (grownState n).env=some (fresh n) ∧
      (fresh n).id=2 ∧ (left.wk (g n).ext).id=0 ∧ (right.wk (g n).ext).id=1 ∧
      base' 0=base 0 ∧ base' 1=base 1 ∧ (wordPost n).stack=[w[77]] ∧
      Objects.StateRepr 1 1 8 ((Frag.init Δ).push (.mem (.fixed (.prim .uint) n)) .ok) (grownState n) base' (wordPost n) ∧
      Objects.AllocatorRepr (g n).heap base' 8 ⟨32+max 1 n,hs⟩ (wordPost n) ∧ Source.MemOK E0 SH (post n) := by
  obtain ⟨base',target,hsrc,hd,hcode,hr,hmok,hm,ha,hbase,hstack,hid,hne,hsource⟩ :=
    source_uint_fixed_declaration_word (Source.SemanticsExamples.G0 p) F0 sy state n hn SH source_memOK
      initial_repr initial_allocator (by decide) hs (by decide)
  have ht : target=wordPost n := (Out.ok.inj (hcode.symm.trans (word_run n))).1
  subst target
  change SourceUintFixedAt (post n) 2 (g n).heap (fresh n) at hr
  have hfixed := source_uint_fixed_intrinsic sy hp n hn
  have hk : Heap.Keeps (g n).ext hp (g n).heap := hfixed.2.2.1
  have hl : SourceUintFixedAt (post n) 0 (g n).heap (left.wk (g n).ext) := by
    have hv := represented_left.keeps (g n).ext hk
    unfold SourceUintFixedAt at hv ⊢
    change (sy.2.heap.alloc ⟨.array .memory (.int .u256) (some n),sourceUintFixedZero n⟩).1.get 0=_
    rw [Source.Heap.alloc_other _ _ (by change (0 : Nat)≠2;decide)]
    exact hv
  have hright : SourceUintFixedAt (post n) 1 (g n).heap (right.wk (g n).ext) := by
    have hv := represented_right.keeps (g n).ext hk
    unfold SourceUintFixedAt at hv ⊢
    change (sy.2.heap.alloc ⟨.array .memory (.int .u256) (some n),sourceUintFixedZero n⟩).1.get 1=_
    rw [Source.Heap.alloc_other _ _ (by change (1 : Nat)≠2;decide)]
    exact hv
  have hfresh : MObj.elems .fixed ((g n).heap.get (fresh n))=List.replicate n (PrimTy.dflt .uint) := hfixed.2.1
  have hread := hr.eval_index (Source.SemanticsExamples.G0 p) F0 0 .here (.there si) (u 0) rfl rfl hn
  have hreadold := hl.eval_index (Source.SemanticsExamples.G0 p) F0 0 (.there salias) (.there si) (u 0) rfl rfl (by decide)
  have hold : MObj.elems .fixed ((g n).heap.get (left.wk (g n).ext))=[u 7] := by
    rw [hk left,MObj.elems_wk,MObj.elems_fixed,List.map_id'' (f := MVal.wk (g n).ext (.prim .uint)) (fun _ => rfl)]
    rfl
  refine ⟨base',hsrc,hd,hcode,hr,hl,hright,hfresh,?_,?_,?_,?_,hr.bounds n (Nat.le_refl _),?_,?_,rfl,rfl,rfl,rfl,hid,rfl,rfl,
    hbase left,hbase right,hstack,hm,ha,hmok⟩
  · rw [hk left,hk right]
    simp only [MObj.wk,List.map_id'' (f := MVal.wk (g n).ext (.prim .uint)) (fun _ => rfl)]
    rfl
  · rfl
  · have he : ((g n).heap.get (fresh n)).1=List.replicate n (PrimTy.dflt .uint) := by
      simpa only [MObj.elems_fixed] using hfresh
    simpa only [he,List.getElem_replicate] using hread
  · have he : ((g n).heap.get (left.wk (g n).ext)).1=[u 7] := by simpa only [MObj.elems_fixed] using hold
    simpa only [he,List.getElem_cons_zero] using hreadold
  · rfl
  · intro i _hi
    change (writeMachine (allocateStructMachine machine ⟨32,by decide⟩ (max 1 n)) 5 w[32]).mem (32+i)=w[0]
    simp only [writeMachine,allocateStructMachine]
    rw [upd_other _ _ (by omega),upd_other _ _ (by omega)]
    exact initial_allocator.free.zero _ (by change 32≤32+i;omega)

/-- Explicit positive length1/multiple/element-boundary applications in both
pipelines. These finite controls do not limit populated_declaration's runtime n. -/
theorem positive_examples (p : Roadmap.Pipeline) (n : Nat) (hc : n=1 ∨ n=3 ∨ n=33) :
    (Source.execS (Source.SemanticsExamples.G0 p) F0 (n+4) Γ.length none
      (.declVar (.array .memory (.int .u256) (some n)) : Source.RStmt E0 [] false .body Γ ((.array .memory (.int .u256) (some n))::Γ)) sy.1).run (.nil,sy.2)=
        (.ok (.normal (post n).1),(.nil,(post n).2)) ∧
    run (code n) machine=.ok (wordPost n) 0 ∧
    (post n).2.heap.get 2=some ⟨.array .memory (.int .u256) (some n),sourceUintFixedZero n⟩ ∧
    [(fresh n).id,(left.wk (g n).ext).id,(right.wk (g n).ext).id]=[2,0,1] := by
  have hn : 0<n := by rcases hc with rfl|rfl|rfl <;> decide
  have hs : 32+max 1 n<W := by rcases hc with rfl|rfl|rfl <;> decide
  obtain ⟨base',h⟩ := populated_declaration p n hn hs
  have hid : (fresh n).id=2 := (source_uint_fixed_intrinsic sy hp n hn).2.2.2
  refine ⟨h.1,h.2.2.1,rfl,?_⟩
  rw [hid];rfl

/-- Logical element32 is read from the actual fixed Source object, not a byte
encoding claim. Exact-end33 fails without a fabricated successful suffix. -/
theorem element_boundary (p : Roadmap.Pipeline) :
    (Source.execS (Source.SemanticsExamples.G0 p) F0 37 Γ.length none
      (.declVar (.array .memory (.int .u256) (some 33)) : Source.RStmt E0 [] false .body Γ ((.array .memory (.int .u256) (some 33))::Γ)) sy.1).run (.nil,sy.2)=
        (.ok (.normal (post 33).1),(.nil,(post 33).2)) ∧
    (Source.memElem (E := E0) (Γ := (.array .memory (.int .u256) (some 33))::Γ) 2 32 (.int .u256)).run (post 33)=
      (.ok (sourceUint (PrimTy.dflt .uint)),post 33) ∧
    (Source.memElem (E := E0) (Γ := (.array .memory (.int .u256) (some 33))::Γ) 2 33 (.int .u256)).run (post 33)=
      (.error (.revert (Source.panicData .index)),post 33) := by
  have hr : SourceUintFixedAt (post 33) 2 (g 33).heap (fresh 33) := by
    have h := (source_uint_fixed_intrinsic sy hp 33 (by decide)).1
    rw [source_uint_fixed_zeroVal] at h
    exact h
  have he : ((g 33).heap.get (fresh 33)).1=List.replicate 33 (PrimTy.dflt .uint) := by
    simpa only [MObj.elems_fixed] using (source_uint_fixed_intrinsic sy hp 33 (by decide)).2.1
  refine ⟨(positive_examples p 33 (.inr (.inr rfl))).1,?_,hr.bounds 33 (Nat.le_refl _)⟩
  simpa only [he,List.getElem_replicate] using hr.read 32 (by decide)

/-- Actual insufficient-fuel failures retain old populated globals and aliases;
there is no new object or success state to observe at these horizons. -/
theorem insufficient_horizons (p : Roadmap.Pipeline) (n fuel : Nat) (hf : fuel≤n+3) :
    (Source.execS (Source.SemanticsExamples.G0 p) F0 fuel Γ.length none
      (.declVar (.array .memory (.int .u256) (some n)) : Source.RStmt E0 [] false .body Γ ((.array .memory (.int .u256) (some n))::Γ)) sy.1).run (.nil,sy.2)=
        (.error .timeout,(.nil,sy.2)) ∧
    sy.2.heap.get 2=none ∧ sy.1.get salias=.memRef rfl 0 :=
  ⟨source_uint_fixed_declaration_timeout (Source.SemanticsExamples.G0 p) F0 sy n fuel hf,rfl,rfl⟩

/-- Dynamic type, wrong fixed length and stale old identity disagree with the
actual produced table. The nonzero old content also distinguishes the n=1 case. -/
theorem wrong_type_length_identity :
    (post 3).2.heap.get 2≠some ⟨.array .memory (.int .u256) none,sourceUintMemory (List.replicate 3 (PrimTy.dflt .uint))⟩ ∧
    (post 3).2.heap.get 2≠some ⟨SA,sourceObject (u 0)⟩ ∧
    ¬SourceUintFixedAt (post 1) 2 hp left ∧
    (wordPost 3).mem 32≠w[3] ∧ (wordPost 1).mem 32≠w[1] := by
  refine ⟨?_,?_,?_,by decide,by decide⟩
  · intro he
    have ht := congrArg Sigma.fst (Option.some.inj he)
    cases ht
  · intro he
    have ht := congrArg Sigma.fst (Option.some.inj he)
    cases ht
  · intro hb
    have hbad := hb.read 0 (by decide)
    have hg : SourceUintFixedAt (post 1) 2 (g 1).heap (fresh 1) := by
      have h := (source_uint_fixed_intrinsic sy hp 1 (by decide)).1
      rw [source_uint_fixed_zeroVal] at h
      exact h
    have hgood := hg.read 0 (by decide)
    have hz : ((g 1).heap.get (fresh 1)).1=List.replicate 1 (PrimTy.dflt .uint) := by
      simpa only [MObj.elems_fixed] using (source_uint_fixed_intrinsic sy hp 1 (by decide)).2.1
    have hg0 : (Source.memElem (E := E0) (Γ := (.array .memory (.int .u256) (some 1))::Γ) 2 0 (.int .u256)).run (post 1)=
        (.ok (sourceUint (PrimTy.dflt .uint)),post 1) := by
      simpa only [hz,List.getElem_replicate] using hgood
    have hb7 : (Source.memElem (E := E0) (Γ := (.array .memory (.int .u256) (some 1))::Γ) 2 0 (.int .u256)).run (post 1)=
        (.ok (sourceUint (u 7)),post 1) := hbad
    have he := Except.ok.inj (congrArg Prod.fst (hg0.symm.trans hb7))
    have hv := congrArg (fun v : Source.Val E0.layout (.int .u256) => match v with | .int k _ => k) he
    change (0 : Int)=7 at hv
    omega

/-- RAW intrinsic/word n=0 reservation consumes one padding cell. No Source
zero-length declaration or source-admission conclusion is asserted here. -/
theorem zero_padding_kernel_only :
    run (Objects.DefaultBuilder.fixedPrimitive .uint 0).code machine=
      .ok ((allocateStructMachine machine ⟨32,by decide⟩ 1).push w[32]) 0 ∧
    (allocateStructMachine machine ⟨32,by decide⟩ 1).mem 0=w[33] ∧
    MObj.elems .fixed ((g 0).heap.get (fresh 0))=[] ∧
    Objects.AllocatorRepr (g 0).heap (upd base 2 ⟨32,by decide⟩) 8 ⟨33,by decide⟩
      (allocateStructMachine machine ⟨32,by decide⟩ 1) := by
  refine ⟨allocateStruct_run machine ⟨32,by decide⟩ 1 rfl,rfl,?_,?_⟩
  · unfold fresh g
    rw [Objects.defaultFixed_copy]
    change MObj.elems .fixed ((hp.alloc (Objects.defaultFixed .uint 0)).1.get (hp.alloc (Objects.defaultFixed .uint 0)).2)=[]
    rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_fixed]
    rfl
  · unfold g
    rw [Objects.defaultFixed_copy]
    exact initial_allocator.allocateFixedPrimitive .uint 0 (by decide)

/-- RAW unchecked space boundary only: the existing allocator wraps at W.
No huge Source/intrinsic payload is evaluated and no checked failure is claimed. -/
theorem raw_space_wrap :
    let n := W-32
    run (Objects.DefaultBuilder.fixedPrimitive .uint n).code machine=
      .ok ((allocateStructMachine machine ⟨32,by decide⟩ (max 1 n)).push w[32]) 0 ∧
    (allocateStructMachine machine ⟨32,by decide⟩ (max 1 n)).mem 0=w[0] ∧
    ∀ {K : HTy} (heap : Heap K) (b : Nat → Fin W),
      ¬Objects.AllocatorRepr heap b 8 ⟨0,W_pos⟩ (allocateStructMachine machine ⟨32,by decide⟩ (max 1 n)) := by
  dsimp only
  refine ⟨allocateStruct_run machine ⟨32,by decide⟩ (max 1 (W-32)) rfl,?_,?_⟩
  · have he : 32+max 1 (W-32)=W := by
      have hw : 33≤W := by decide
      omega
    change Word.val (wmod (32+max 1 (W-32)))=w[0]
    rw [he]
    apply congrArg Word.val
    apply Fin.ext
    exact Nat.mod_self _
  · intro K heap b h
    have hh := h.free.above
    change 8≤0 at hh
    omega

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDefaultControls.initial_views' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms initial_views
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDefaultControls.populated_declaration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms populated_declaration
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDefaultControls.positive_examples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms positive_examples
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDefaultControls.element_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms element_boundary
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDefaultControls.insufficient_horizons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms insufficient_horizons
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDefaultControls.wrong_type_length_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_type_length_identity
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDefaultControls.zero_padding_kernel_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_padding_kernel_only
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDefaultControls.raw_space_wrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_space_wrap
end Solidity.Backend.MemoryOps.SourceUintFixedDefaultControls
