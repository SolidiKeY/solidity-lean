import Solidity.Backend.MemoryOps.SourceUintFixedDeclareAlias
import Solidity.Backend.MemoryOps.SourceUintFixedDeclaration
import Solidity.Evm.Correct
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.MemoryOps.SourceUintFixedDeclareAliasControls
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

private def g := hp.allocDefault A rfl
private def fresh := g.val
private def grown (k v : Nat) := ((state k v).adopt g).1.push (t := .mem A) (some fresh)
private def mid (k v : Nat) : Source.EMState E0 (SA::Γ) :=
  (.cons (.memRef rfl 3) (sy k v).1,{(sy k v).2 with heap := ((sy k v).2.heap.alloc ⟨SA,sourceUintFixedZero 3⟩).1})
private def renamed (k v : Nat) := (grown k v).setLocal (.there td) (some fresh)
private def cc : List Instr := Objects.defaultDeclareCode (Γ := Δ) (Objects.DefaultBuilder.fixedPrimitive .uint 3).code 1
private def ac : List Instr := aliasLocalCode 1 (.there td) (.here : Idx (.mem A::Δ) (.mem A))
private def wc : List Instr := Evm.compileVal 1 (.simple (.local (.there tv)) : Val C (.mem A::Δ) .uint) ++
  [.mload (Evm.cellOf 1 (.there td : Idx (.mem A::Δ) (.mem A)))] ++
    Evm.compileVal 1 (.simple (.local (.there ti)) : Val C (.mem A::Δ) .uint) ++ Objects.writeCode (.fixed : ArrTy A (.prim .uint))
private def dc : List Instr := Evm.compileVal 1 (deleteDefaultValue .uint : Val C (.mem A::Δ) .uint) ++
  [.mload (Evm.cellOf 1 (.there td : Idx (.mem A::Δ) (.mem A)))] ++
    Evm.compileVal 1 (.simple (.local (.there ti)) : Val C (.mem A::Δ) .uint) ++ Objects.writeCode (.fixed : ArrTy A (.prim .uint))

/-- Actual context-changing program: the original destination LEFT now aliases
fresh root3. The retained LEFT local still observes the populated old object. -/
theorem reached_program (p : Roadmap.Pipeline) (k v : Nat) (hk : k<3) :
    ∃ (base' : Nat → Fin W) (m0 m1 m2 : Machine) (out1 out2 : Heap g.H') (z1 z2 : Source.EMState E0 (SA::Γ)),
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 11 Γ.length none
        (sourceUintFixedDeclareAlias sd si sv) (sy k v).1).run (.nil,(sy k v).2)=
          (.ok (.normal z2.1),(.nil,z2.2)) ∧
      Prog.run (state k v) (intrinsicUintFixedDeclareAlias td ti tv)=.ok ⟨(renamed k v).withHeap out2,g.ext⟩ ∧
      run cc (machine k v)=.ok m0 0 ∧ run (ac ++ wc) m0=.ok m1 0 ∧ run dc m1=.ok m2 0 ∧
      run (cc ++ ac ++ wc ++ dc) (machine k v)=.ok m2 0 ∧
      [(out1.get fresh).1,(out2.get fresh).1]=[(List.replicate 3 (PrimTy.dflt .uint)).set k (u v),List.replicate 3 (PrimTy.dflt .uint)] ∧
      [(out2.get (left.wk g.ext)).1,(out2.get (right.wk g.ext)).1,(out2.get (neighbor.wk g.ext)).1]=
        [[u 7,u 8,u 7],[u 9,u 10,u 9],[u 11,u 12]] ∧
      [z1.2.heap.get 0,z1.2.heap.get 1,z1.2.heap.get 2,z2.2.heap.get 0,z2.2.heap.get 1,z2.2.heap.get 2]=
        [(sy k v).2.heap.get 0,(sy k v).2.heap.get 1,(sy k v).2.heap.get 2,
         (sy k v).2.heap.get 0,(sy k v).2.heap.get 1,(sy k v).2.heap.get 2] ∧
      SourceUintFixedAt z1 3 out1 fresh ∧ SourceUintFixedAt z2 3 out2 fresh ∧
      [z2.1.get .here,z2.1.get (.there sd),z2.1.get (.there sa),z2.1.get (.there ss)]=
        [.memRef rfl 3,.memRef rfl 3,.memRef rfl 0,.memRef rfl 1] ∧
      [TEnv.get (.here : Idx (.mem A::Δ) (.mem A)) ((renamed k v).withHeap out2).env,
       TEnv.get (.there td) ((renamed k v).withHeap out2).env,TEnv.get (.there ta) ((renamed k v).withHeap out2).env]=
        [some fresh,some fresh,some (left.wk g.ext)] ∧
      fresh.id=3 ∧ fresh.id≠(left.wk g.ext).id ∧
      Objects.StateRepr 1 1 8 ((Frag.init Δ).push (.mem A) .ok) ((renamed k v).withHeap out2) base' m2 ∧
      Objects.AllocatorRepr out2 base' 8 ⟨43,by decide⟩ m2 ∧
      Source.MemOK E0 SH z1 ∧ Source.MemOK E0 SH z2 ∧ m2.stack=[w[77],w[88]] ∧ m2.mem 0=w[43] := by
  have hki : (u k).1.toNat=k := by change (wmod k).val=k;exact Nat.mod_eq_of_lt (Nat.lt_trans hk (by decide : 3<W))
  obtain ⟨base',m0,m1,m2,o1,o2,z1,z2,hd,hi,hprogram,hwrite,hdelete,hr0,hr1,hr2,hc0,hc1,hc2,hwhole,hm2,ha2,hmok0,hmok1,hmok2,hl1,hl2,hrootS,hnewS,hrootT,hnewT,hobjects,hsource,hid,hne,hstack,hfree,hsource1,hex,hev,hlog,hfn⟩ :=
    source_uint_fixed_declare_alias_word (Source.SemanticsExamples.G0 p) F0 (sy k v) (state k v) 3 (by decide) sd td si sv ti tv (u k) (u v)
      rfl rfl rfl rfl (by rw [hki];exact hk) SH (source_memOK k v) (initial_repr k v) (initial_allocator k v) (by decide) (by decide) (by decide)
  change g.heap.writeAddr (.index fresh .fixed (u k)) (u v)=some o1 at hwrite
  change o1.writeAddr (.index fresh .fixed (u k)) (PrimTy.dflt .uint)=some o2 at hdelete
  have hv1 := indexedWrite_elems g.heap o1 fresh .fixed (u k) (u v) hwrite
  have hv2 := indexedWrite_elems o1 o2 fresh .fixed (u k) (PrimTy.dflt .uint) hdelete
  have hz := (source_uint_fixed_intrinsic (sy k v) hp 3 (by decide)).2.1
  simp only [MObj.elems_fixed] at hv1 hv2 hz
  change (g.heap.get fresh).1=List.replicate 3 (PrimTy.dflt .uint) at hz
  have hh1 : (o1.get fresh).1=(List.replicate 3 (PrimTy.dflt .uint)).set k (u v) := by rw [hv1,hz,hki]
  have hh2 : (o2.get fresh).1=List.replicate 3 (PrimTy.dflt .uint) := by
    rw [hv2,hh1,hki,List.set_set]
    apply List.ext_getElem
    · simp only [List.length_set]
    · intro j hj hj'
      rw [List.getElem_set]
      split <;> simp only [List.getElem_replicate]
  have hgetL : (sy k v).2.heap.get 0≠none := by rw [represented_left k v];exact Option.some_ne_none _
  have hgetR : (sy k v).2.heap.get 1≠none := by rw [represented_right k v];exact Option.some_ne_none _
  have hgetN : (sy k v).2.heap.get 2≠none := by rw [represented_neighbor k v];exact Option.some_ne_none _
  have hleft := hobjects left
  have hright := hobjects right
  have hnbr := hobjects neighbor
  refine ⟨base',m0,m1,m2,o1,o2,z1,z2,hi,hprogram,hc0,hc1,hc2,hwhole,by rw [hh1,hh2],?_,?_,hr1,hr2,?_,?_,hid,hne left,hm2,ha2,hmok1,hmok2,hstack,hfree⟩
  · rw [hleft,hright,hnbr]
    rfl
  · rw [hsource1 0 hgetL,hsource1 1 hgetR,hsource1 2 hgetN,
      hsource 0 hgetL,hsource 1 hgetR,hsource 2 hgetN]
  · rw [hl2];rfl
  · rfl

private def cells (m : Machine) : List Word :=
  [m.mem 0,m.mem 1,m.mem 2,m.mem 3,m.mem 4,m.mem 5,m.mem 6,m.mem 15,
   m.mem 16,m.mem 17,m.mem 18,m.mem 24,m.mem 25,m.mem 26,m.mem 32,m.mem 33,m.mem 7,m.mem 40,m.mem 41,m.mem 42]
private def observed (code : List Instr) (m : Machine) : Option (List Word × List Word) :=
  match run code m with | .ok out 0 => some (cells out,out.stack) | _ => none
private theorem observed_ok {code : List Instr} {m out : Machine} (h : run code m=.ok out 0) :
    observed code m=some (cells out,out.stack) := by unfold observed;rw [h]
private theorem update_run (m : Machine) (a k v : Nat) (hk : k<3) (hkw : k<W) (ha : a+k<W) (hb : a<W)
    (h5 : m.mem 5=Word.val (wmod v)) (h3 : m.mem 3=Word.val (wmod a)) (h6 : m.mem 6=Word.val (wmod k)) :
    run wc m=.ok (writeMachine m (a+k) (.val (wmod v))) 0 := by
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
    run dc m=.ok (writeMachine m (a+k) w[0]) 0 := by
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

private def wordPost (k v : Nat) := writeMachine (allocateStructMachine (machine k v) ⟨40,by decide⟩ 3) 7 w[40]
private theorem declare_run (k v : Nat) : run cc (machine k v)=.ok (wordPost k v) 0 := by
  change run (allocateStructCode 3 ++ [.mstore 7]) (machine k v)=_
  rw [run_append_ok (allocateStruct_run (machine k v) ⟨40,by decide⟩ 3 rfl)]
  rfl
/-- Complete20word vectors include the previous16-cell frame plus new local7
and all three new payload cells. Skipping rebind clears OLD LEFT, not fresh. -/
theorem word_vectors :
    observed cc (machine 2 42)=some
      ([w[43],w[32],w[16],w[16],w[24],w[42],w[2],w[99],w[7],w[8],w[7],w[9],w[10],w[9],w[11],w[12],w[40],w[0],w[0],w[0]],[w[77],w[88]]) ∧
    observed (cc ++ ac) (machine 2 42)=some
      ([w[43],w[32],w[16],w[40],w[24],w[42],w[2],w[99],w[7],w[8],w[7],w[9],w[10],w[9],w[11],w[12],w[40],w[0],w[0],w[0]],[w[77],w[88]]) ∧
    observed (cc ++ ac ++ wc) (machine 2 42)=some
      ([w[43],w[32],w[16],w[40],w[24],w[42],w[2],w[99],w[7],w[8],w[7],w[9],w[10],w[9],w[11],w[12],w[40],w[0],w[0],w[42]],[w[77],w[88]]) ∧
    observed (cc ++ ac ++ wc ++ dc) (machine 2 42)=some
      ([w[43],w[32],w[16],w[40],w[24],w[42],w[2],w[99],w[7],w[8],w[7],w[9],w[10],w[9],w[11],w[12],w[40],w[0],w[0],w[0]],[w[77],w[88]]) ∧
    observed (cc ++ wc ++ dc) (machine 2 42)=some
      ([w[43],w[32],w[16],w[16],w[24],w[42],w[2],w[99],w[7],w[8],w[0],w[9],w[10],w[9],w[11],w[12],w[40],w[0],w[0],w[0]],[w[77],w[88]]) := by
  have hA : run ac (wordPost 2 42)=.ok (writeMachine (wordPost 2 42) 3 w[40]) 0 := by rfl
  have hCA : run (cc ++ ac) (machine 2 42)=.ok (writeMachine (wordPost 2 42) 3 w[40]) 0 := by
    rw [run_append_ok (declare_run 2 42)];exact hA
  have hW : run wc (writeMachine (wordPost 2 42) 3 w[40])=
      .ok (writeMachine (writeMachine (wordPost 2 42) 3 w[40]) 42 w[42]) 0 := by
    simpa only [wmod_of_lt (by decide : 42<W)] using update_run (writeMachine (wordPost 2 42) 3 w[40]) 40 2 42 (by decide) (by decide) (by decide) (by decide) rfl rfl rfl
  have hD := clear_run (writeMachine (writeMachine (wordPost 2 42) 3 w[40]) 42 w[42]) 40 2 (by decide) (by decide) (by decide) (by decide) rfl rfl
  have hCAW : run (cc ++ ac ++ wc) (machine 2 42)=.ok (writeMachine (writeMachine (wordPost 2 42) 3 w[40]) 42 w[42]) 0 := by
    rw [run_append_ok hCA];exact hW
  have hCAWD : run (cc ++ ac ++ wc ++ dc) (machine 2 42)=.ok (writeMachine (writeMachine (writeMachine (wordPost 2 42) 3 w[40]) 42 w[42]) 42 w[0]) 0 := by
    rw [run_append_ok hCAW];exact hD
  have hOld : run wc (wordPost 2 42)=.ok (writeMachine (wordPost 2 42) 18 w[42]) 0 := by
    simpa only [wmod_of_lt (by decide : 42<W)] using update_run (wordPost 2 42) 16 2 42 (by decide) (by decide) (by decide) (by decide) rfl rfl rfl
  have hOldD := clear_run (writeMachine (wordPost 2 42) 18 w[42]) 16 2 (by decide) (by decide) (by decide) (by decide) rfl rfl
  have hskip : run (cc ++ wc ++ dc) (machine 2 42)=.ok (writeMachine (writeMachine (wordPost 2 42) 18 w[42]) 18 w[0]) 0 := by
    rw [List.append_assoc,run_append_ok (declare_run 2 42),run_append_ok hOld];exact hOldD
  exact ⟨observed_ok (declare_run 2 42),observed_ok hCA,observed_ok hCAW,observed_ok hCAWD,observed_ok hskip⟩

/-- Insufficient horizon7 times out at the actual first declaration, without
allocating or inventing a reached suffix. The successful11 is sufficient, not a
minimal-fuel theorem. -/
theorem early_timeout (p : Roadmap.Pipeline) :
    (Source.execItems (Source.SemanticsExamples.G0 p) F0 7 Γ.length none
      (sourceUintFixedDeclareAlias sd si sv) (sy 2 42).1).run (.nil,(sy 2 42).2)=
        (.error .timeout,(.nil,(sy 2 42).2)) := by
  have hd := source_uint_fixed_declaration_timeout (Source.SemanticsExamples.G0 p) F0 (sy 2 42) 3 6 (by decide)
  rw [sourceUintFixedDeclareAlias,Source.execItems,Source.Hoare.run_bind,hd]

/-- Actual immutable old-address and fresh-address reads at the reached write
and delete heaps. The wrong old-address map is refuted by concrete7 versus0. -/
theorem reached_reads (p : Roadmap.Pipeline) :
    ∃ (out1 out2 : Heap g.H') (z1 z2 : Source.EMState E0 (SA::Γ)),
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 11 Γ.length none
        (sourceUintFixedDeclareAlias sd si sv) (sy 2 42).1).run (.nil,(sy 2 42).2)=
          (.ok (.normal z2.1),(.nil,z2.2)) ∧
      SourceUintFixedAt z1 3 out1 fresh ∧ SourceUintFixedAt z2 3 out2 fresh ∧
      (Source.memElem (E := E0) (Γ := SA::Γ) 3 2 (.int .u256)).run z1=(.ok (sourceUint (u 42)),z1) ∧
      (Source.memElem (E := E0) (Γ := SA::Γ) 3 2 (.int .u256)).run z2=(.ok (sourceUint (PrimTy.dflt .uint)),z2) ∧
      (Source.memElem (E := E0) (Γ := SA::Γ) 0 2 (.int .u256)).run z2=(.ok (sourceUint (u 7)),z2) ∧
      ¬SourceUintFixedAt z2 0 out2 fresh := by
  obtain ⟨base',m0,m1,m2,o1,o2,z1,z2,hi,hprogram,hc0,hc1,hc2,hwhole,hvals,hold,htab,hr1,hr2,hloc,htloc,hid,hne,hm,ha,hmok1,hmok2,hstack,hfree⟩ := reached_program p 2 42 (by decide)
  have hv1 : (o1.get fresh).1=[PrimTy.dflt .uint,PrimTy.dflt .uint,u 42] := by
    have h := congrArg (fun xs => xs[0]?) hvals
    simpa only [List.getElem?_cons_zero,Option.some.injEq] using h
  have hv2 : (o2.get fresh).1=[PrimTy.dflt .uint,PrimTy.dflt .uint,PrimTy.dflt .uint] := by
    have h := congrArg (fun xs => xs[1]?) hvals
    simpa only [List.getElem?_cons_zero,List.getElem?_cons_succ,Option.some.injEq] using h
  have h0 : z2.2.heap.get 0=(sy 2 42).2.heap.get 0 := by
    have h := congrArg (fun xs => xs[3]?) htab
    simpa only [List.getElem?_cons_zero,List.getElem?_cons_succ,Option.some.injEq] using h
  have hOld : SourceUintFixedAt z2 0 hp left := by unfold SourceUintFixedAt;rw [h0];exact represented_left 2 42
  have hReadOld := hOld.read 2 (by decide)
  have hRead1 := hr1.read 2 (by decide)
  have hRead2 := hr2.read 2 (by decide)
  simp only [hv1,List.getElem_cons_succ,List.getElem_cons_zero] at hRead1
  simp only [hv2,List.getElem_cons_succ,List.getElem_cons_zero] at hRead2
  refine ⟨o1,o2,z1,z2,hi,hr1,hr2,hRead1,hRead2,hReadOld,?_⟩
  intro hWrong
  have hR := hWrong.read 2 (by decide)
  simp only [hv2,List.getElem_cons_succ,List.getElem_cons_zero] at hR
  have hEq : sourceUint (u 7)=sourceUint (PrimTy.dflt .uint) := Except.ok.inj (congrArg Prod.fst (hReadOld.symm.trans hR))
  have hv := congrArg (fun v : Source.Val E0.layout (.int .u256) => calldataUint (.val v)) hEq
  have h : u 7=PrimTy.dflt .uint := by simpa only [calldataUint_sourceUint] using hv
  exact (by decide : u 7≠PrimTy.dflt .uint) h

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDeclareAliasControls.initial_views' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms initial_views
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDeclareAliasControls.reached_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reached_program
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDeclareAliasControls.word_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_vectors
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDeclareAliasControls.early_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms early_timeout
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDeclareAliasControls.reached_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reached_reads
end Solidity.Backend.MemoryOps.SourceUintFixedDeclareAliasControls
