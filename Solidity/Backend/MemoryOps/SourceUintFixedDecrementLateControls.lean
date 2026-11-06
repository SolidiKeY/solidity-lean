import Solidity.Backend.MemoryOps.SourceUintFixedDecrementLateTiming
import Solidity.Backend.MemoryOps.SourceUintFixedDeclareAliasControls
import Solidity.Evm.Correct
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.MemoryOps.SourceUintFixedDecrementLateControls
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
  have ha : run (Objects.fixedAddrCode 3) ((m.push (.val a)).push (.val k)) =
      if k.val<3 then .ok (m.push (.val (wmod (a.val+k.val)))) 0 else .revert := Objects.fixedAddr_run m a k 3
  rw [if_pos hk] at ha
  change run (Objects.fixedAddrCode 3 ++ [.mloadAt]) ((m.push (.val a)).push (.val k))=_
  rw [run_append_ok ha]
  simp only [run,Machine.push,exec_cons_zero,Instr.step,wmod_of_lt hs,Out.ok_bind,exec_nil,hc,Machine.next]
private def incCode : List Instr := fixedUintIncrementCode (C := C) 1 td ti
private theorem increment_run (m : Machine) (a k old : Fin W) (hk : k.val<3) (hs : a.val+k.val<W)
    (hp : m.mem 3=.val a) (hi : m.mem 6=.val k) (hc : m.mem (a.val+k.val)=.val old)
    (hadd : old.val+1<W) :
    run incCode m=.ok (writeMachine m (a.val+k.val) (.val ⟨old.val+1,hadd⟩)) 0 := by
  have hr : run rd m=.ok (m.push (.val old)) 0 := read_run m a k old hk hs hp hi hc
  have hvalue : run (binaryCode .uint .add rd [.push w[1]]) m=.ok (m.push (.val ⟨old.val+1,hadd⟩)) 0 := by
    change run (rd ++ ([.push w[1]] ++ uTail .add)) m=_
    rw [run_append_ok hr]
    rw [run_append_ok (show run [.push w[1]] (m.push (.val old))=.ok ((m.push (.val old)).push w[1]) 0 from rfl)]
    exact (add_tail m m.stack old.isLt (show (1 : Nat)<W from by decide)).trans (by rw [dif_pos hadd];rfl)
  change run ((binaryCode .uint .add rd [.push w[1]]) ++ ([.mload 3] ++ ([.mload 6] ++ Objects.writeCode (.fixed : ArrTy A (.prim .uint))))) m=_
  rw [run_append_ok hvalue]
  rw [run_append_ok (show run [.mload 3] (m.push (.val ⟨old.val+1,hadd⟩))=.ok ((m.push (.val ⟨old.val+1,hadd⟩)).push (.val a)) 0 from by change Out.ok ((m.push (.val ⟨old.val+1,hadd⟩)).push (m.mem 3)) 0=_;rw [hp])]
  rw [run_append_ok (show run [.mload 6] ((m.push (.val ⟨old.val+1,hadd⟩)).push (.val a))=.ok (((m.push (.val ⟨old.val+1,hadd⟩)).push (.val a)).push (.val k)) 0 from by change Out.ok (((m.push (.val ⟨old.val+1,hadd⟩)).push (.val a)).push (m.mem 6)) 0=_;rw [hi])]
  have ha : run (Objects.fixedAddrCode 3) (((m.push (.val ⟨old.val+1,hadd⟩)).push (.val a)).push (.val k)) =
      if k.val<3 then .ok ((m.push (.val ⟨old.val+1,hadd⟩)).push (.val (wmod (a.val+k.val)))) 0 else .revert := Objects.fixedAddr_run (m.push (.val ⟨old.val+1,hadd⟩)) a k 3
  rw [if_pos hk] at ha
  change run (Objects.fixedAddrCode 3 ++ [.mstoreAt]) (((m.push (.val ⟨old.val+1,hadd⟩)).push (.val a)).push (.val k))=_
  rw [run_append_ok ha]
  simp only [run,Machine.push,exec_cons_zero,Instr.step,wmod_of_lt hs,Out.ok_bind,exec_nil,writeMachine]

private theorem decrement_run (m : Machine) (a k old : Fin W) (hk : k.val<3) (hs : a.val+k.val<W)
    (hp : m.mem 3=.val a) (hi : m.mem 6=.val k) (hc : m.mem (a.val+k.val)=.val old)
    (hsub : 1≤old.val) (hbelow : old.val-1<W) :
    run code m=.ok (writeMachine m (a.val+k.val) (.val ⟨old.val-1,hbelow⟩)) 0 := by
  have hr : run rd m=.ok (m.push (.val old)) 0 := read_run m a k old hk hs hp hi hc
  have hvalue : run (binaryCode .uint .sub rd [.push w[1]]) m=.ok (m.push (.val ⟨old.val-1,hbelow⟩)) 0 := by
    change run (rd ++ ([.push w[1]] ++ uTail .sub)) m=_
    rw [run_append_ok hr]
    rw [run_append_ok (show run [.push w[1]] (m.push (.val old))=.ok ((m.push (.val old)).push w[1]) 0 from rfl)]
    have h : run (uTail .sub) {m with stack := w[1] :: w[old.val] :: m.stack} =
        if _ : 1≤old.val then .ok {m with stack := w[old.val-1] :: m.stack} 0 else .revert := sub_tail m m.stack old.isLt (show (1 : Nat)<W from by decide)
    rw [dif_pos hsub] at h
    simpa only [wmod_of_lt hbelow] using h
  change run ((binaryCode .uint .sub rd [.push w[1]]) ++ ([.mload 3] ++ ([.mload 6] ++ Objects.writeCode (.fixed : ArrTy A (.prim .uint))))) m=_
  rw [run_append_ok hvalue]
  rw [run_append_ok (show run [.mload 3] (m.push (.val ⟨old.val-1,hbelow⟩))=.ok ((m.push (.val ⟨old.val-1,hbelow⟩)).push (.val a)) 0 from by change Out.ok ((m.push (.val ⟨old.val-1,hbelow⟩)).push (m.mem 3)) 0=_;rw [hp])]
  rw [run_append_ok (show run [.mload 6] ((m.push (.val ⟨old.val-1,hbelow⟩)).push (.val a))=.ok (((m.push (.val ⟨old.val-1,hbelow⟩)).push (.val a)).push (.val k)) 0 from by change Out.ok (((m.push (.val ⟨old.val-1,hbelow⟩)).push (.val a)).push (m.mem 6)) 0=_;rw [hi])]
  have ha : run (Objects.fixedAddrCode 3) (((m.push (.val ⟨old.val-1,hbelow⟩)).push (.val a)).push (.val k)) =
      if k.val<3 then .ok ((m.push (.val ⟨old.val-1,hbelow⟩)).push (.val (wmod (a.val+k.val)))) 0 else .revert := Objects.fixedAddr_run (m.push (.val ⟨old.val-1,hbelow⟩)) a k 3
  rw [if_pos hk] at ha
  change run (Objects.fixedAddrCode 3 ++ [.mstoreAt]) (((m.push (.val ⟨old.val-1,hbelow⟩)).push (.val a)).push (.val k))=_
  rw [run_append_ok ha]
  simp only [run,Machine.push,exec_cons_zero,Instr.step,wmod_of_lt hs,Out.ok_bind,exec_nil,writeMachine]


/-! Reached-state decrement controls. Populated original fixture schema, initial LEFT
changed to [1,8,1]; RIGHT [9,10,9] and neighbor [11,12] remain distinct.
The retained alias sa and selected sd both point to LEFT. No new semantics. -/

theorem changed_prefix_late_underflow (p : Roadmap.Pipeline) (first second : Bool) :
    ∃ (out : Heap H) (z : Source.EMState E0 Γ) (target : Machine),
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 4 (sourceUintFixedDecrement first sd si)).run (sy 0 42)=
        (.ok (.val (sourceUint (if first then u 0 else u 1))),z) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintFixedDecrement second sd si)).run z=
        (.error (.revert (Source.panicData .arithmetic)),z) ∧
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 Γ.length none
        (sourceUintFixedDecrementTwice first second sd si) (sy 0 42).1).run (.nil,(sy 0 42).2)=
        (.error (.revert (Source.panicData .arithmetic)),(.nil,z.2)) ∧
      Prog.run (state 0 42) (intrinsicUintFixedDecrementTwice first second td ti)=.error .revert ∧
      run code (machine 0 42)=.ok target 0 ∧ run code target=.revert ∧
      run (code ++ code) (machine 0 42)=.revert ∧
      [(hp.get left).1,(hp.get right).1,(hp.get neighbor).1,
       (out.get left).1,(out.get right).1,(out.get neighbor).1]=
        [[u 1,u 8,u 1],[u 9,u 10,u 9],[u 11,u 12],
         [u 0,u 8,u 1],[u 9,u 10,u 9],[u 11,u 12]] ∧
      [(sy 0 42).2.heap.get 0,(sy 0 42).2.heap.get 1,(sy 0 42).2.heap.get 2,
       z.2.heap.get 0,z.2.heap.get 1,z.2.heap.get 2]=
        [(sy 0 42).2.heap.get 0,(sy 0 42).2.heap.get 1,(sy 0 42).2.heap.get 2,
         some ⟨SA,sourceUintFixedObject (out.get left)⟩,(sy 0 42).2.heap.get 1,(sy 0 42).2.heap.get 2] ∧
      SourceUintFixedAt z 0 out left ∧ z.1=(sy 0 42).1 ∧
      [z.1.get sd,z.1.get sa,z.1.get ss]=[.memRef rfl 0,.memRef rfl 0,.memRef rfl 1] ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local sa) (.local si) rfl)).run z=
        (.ok (.val (sourceUint (u 0))),z) ∧
      Objects.StateRepr 1 1 8 (Frag.init Δ) ((state 0 42).withHeap out) base target ∧
      Objects.AllocatorRepr out base 8 ⟨40,by decide⟩ target ∧ Source.MemOK E0 SH z ∧
      target.stack=[w[77],w[88]] ∧ target.mem 0=w[40] ∧
      cells (machine 0 42)=
        [w[40],w[32],w[16],w[16],w[24],w[42],w[0],w[99],w[1],w[8],w[1],w[9],w[10],w[9],w[11],w[12],w[0],w[0],w[0],w[0]] ∧
      cells target=
        [w[40],w[32],w[16],w[16],w[24],w[42],w[0],w[99],w[0],w[8],w[1],w[9],w[10],w[9],w[11],w[12],w[0],w[0],w[0],w[0]] ∧
      z.2.ex=(sy 0 42).2.ex ∧ z.2.events=(sy 0 42).2.events ∧
      z.2.logs=(sy 0 42).2.logs ∧ z.2.fnLocals=(sy 0 42).2.fnLocals := by
  obtain ⟨out,z,target,he,hf,hitems,hprog,hw,hc,hcf,hwhole,hold,hr,hm,ha,hmok,hl,hstack,hfree,hobj,haddr,hex,hev,hlog,hfn⟩ :=
    resolved_uint_fixed_decrement_late_underflow_word (Source.SemanticsExamples.G0 p) F0 0 Γ.length first second rfl
      (state 0 42) left (represented_left 0 42) sd si td ti (u 0) rfl rfl rfl rfl
      (by simp only [Heap.len,MObj.elems_fixed];decide) (by simp only [MObj.elems_fixed];decide)
      SH (source_memOK 0 42) (initial_repr 0 42) (initial_allocator 0 42) (by decide)
  change hp.writeAddr (.index left .fixed (u 0)) (u 0)=some out at hw
  have hv : MObj.elems .fixed (out.get left)=
      (MObj.elems .fixed (hp.get left)).set (u 0).val.toNat (u 0) :=
    indexedWrite_elems hp out left .fixed (u 0) (u 0) hw
  simp only [MObj.elems_fixed] at hv
  have hvLeft : (out.get left).1=[u 0,u 8,u 1] := by rw [hv];rfl
  have hvec : [(hp.get left).1,(hp.get right).1,(hp.get neighbor).1,
      (out.get left).1,(out.get right).1,(out.get neighbor).1]=
      [[u 1,u 8,u 1],[u 9,u 10,u 9],[u 11,u 12],[u 0,u 8,u 1],[u 9,u 10,u 9],[u 11,u 12]] := by
    rw [hvLeft,hobj right (by decide),hobj neighbor (by decide)];rfl
  have htable : [(sy 0 42).2.heap.get 0,(sy 0 42).2.heap.get 1,(sy 0 42).2.heap.get 2,
      z.2.heap.get 0,z.2.heap.get 1,z.2.heap.get 2]=
      [(sy 0 42).2.heap.get 0,(sy 0 42).2.heap.get 1,(sy 0 42).2.heap.get 2,
       some ⟨SA,sourceUintFixedObject (out.get left)⟩,(sy 0 42).2.heap.get 1,(sy 0 42).2.heap.get 2] := by
    rw [hr,haddr 1 (by decide),haddr 2 (by decide)]
  have hloc : [z.1.get sd,z.1.get sa,z.1.get ss]=[.memRef rfl 0,.memRef rfl 0,.memRef rfl 1] := by rw [hl];rfl
  have hindex : (u 0).val.toNat<(out.get left).1.length := by
    rw [(out.get left).2];decide
  have halias : (Source.evalE (Source.SemanticsExamples.G0 p) F0 2
      (.indexArray (.local sa) (.local si) rfl)).run z=
        (.ok (.val (sourceUint ((out.get left).1[(u 0).val.toNat]'hindex))),z) := hr.eval_index (Source.SemanticsExamples.G0 p) F0 0 sa si (u 0)
    (by rw [hl];rfl) (by rw [hl];rfl) (by decide)
  simp only [hvLeft] at halias
  have hrun : run code (machine 0 42)=.ok (writeMachine (machine 0 42) 16 w[0]) 0 := decrement_run (machine 0 42) ⟨16,by decide⟩ ⟨0,by decide⟩ ⟨1,by decide⟩
    (by decide) (by decide) rfl rfl rfl (by decide) (by decide)
  have ht : target=writeMachine (machine 0 42) 16 w[0] := by
    exact (Out.ok.inj (hc.symm.trans hrun)).1
  have hcells : cells target=
      [w[40],w[32],w[16],w[16],w[24],w[42],w[0],w[99],w[0],w[8],w[1],w[9],w[10],w[9],w[11],w[12],w[0],w[0],w[0],w[0]] := by
    rw [ht];rfl
  refine ⟨out,z,target,?_,hf,hitems,hprog,hc,hcf,hwhole,hvec,htable,hr,hl,hloc,halias,
    hm,ha,hmok,hstack,ha.free.cell,rfl,hcells,hex,hev,hlog,hfn⟩
  simpa only [MObj.elems_fixed] using he

/-- Frozen INITIAL evaluation succeeds; actual reached evaluation above fails.
This is an execution counterexample, not only a scalar arithmetic inequality. -/
theorem frozen_initial_is_not_late_failure (p : Roadmap.Pipeline) (pre : Bool) :
    ∃ (out : Heap H) (z : Source.EMState E0 Γ) (target : Machine),
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintFixedDecrement pre sd si)).run (sy 0 42)=
        (.ok (.val (sourceUint (if pre then u 0 else u 1))),z) ∧
      run code (machine 0 42)=.ok target 0 ∧ (out.get left).1=[u 0,u 8,u 1] ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintFixedDecrement pre sd si)).run (sy 0 42)≠
        (.error (.revert (Source.panicData .arithmetic)),sy 0 42) := by
  obtain ⟨out,z,target,hw,hs,he,hstmt,hi,hc,hr,hm,hmok,hl,hstack,hkeep,hobj,haddr,hex,hev,hlog,hfn⟩ :=
    resolved_uint_fixed_decrement_word (Source.SemanticsExamples.G0 p) F0 0 pre (state 0 42) left (represented_left 0 42)
      sd si td ti (u 0) rfl rfl rfl rfl (by simp only [Heap.len,MObj.elems_fixed];decide)
      (by simp only [MObj.elems_fixed];decide) SH (source_memOK 0 42) (initial_repr 0 42)
  simp only [MObj.elems_fixed] at hw
  change hp.writeAddr (.index left .fixed (u 0)) (u 0)=some out at hw
  have hv : MObj.elems .fixed (out.get left)=
      (MObj.elems .fixed (hp.get left)).set (u 0).val.toNat (u 0) :=
    indexedWrite_elems hp out left .fixed (u 0) (u 0) hw
  simp only [MObj.elems_fixed] at hv
  have hvec : (out.get left).1=[u 0,u 8,u 1] := by rw [hv];rfl
  refine ⟨out,z,target,?_,hc,hvec,?_⟩
  · simpa only [MObj.elems_fixed] using he
  · rw [he];intro h;cases h

theorem low_horizon (p : Roadmap.Pipeline) (pre : Bool) :
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (sourceUintFixedDecrement pre sd si)).run (sy 0 42)=
      (.error .timeout,sy 0 42) :=
  source_uint_fixed_decrement_horizon_two _ _ _ _ _ _

/-- Prefix zero and postfix one are different expression results; swapping
only pre/post flags cannot discriminate the two discarded-result statements. -/
theorem wrong_expression_result : sourceUint (D := E0.layout) (u 0)≠sourceUint (u 1) := by
  intro h
  have hv : calldataUint (.val (sourceUint (u 0)))=calldataUint (.val (sourceUint (u 1))) := congrArg (fun v : Source.Val E0.layout (.int .u256) => calldataUint (.val v)) h
  have heq : u 0=u 1 := by simpa only [calldataUint_sourceUint] using hv
  exact (show u 0≠u 1 from by decide) heq

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDecrementLateControls.changed_prefix_late_underflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms changed_prefix_late_underflow
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDecrementLateControls.frozen_initial_is_not_late_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms frozen_initial_is_not_late_failure

/-- Actual Items5 timeout retains the changed first prefix, contrasting the
Items6 arithmetic panic. The reduced horizon is observation, not admission. -/
theorem changed_prefix_timeout (p : Roadmap.Pipeline) (first second : Bool) :
    ∃ (out : Heap H) (z : Source.EMState E0 Γ) (target : Machine),
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintFixedDecrement first sd si)).run (sy 0 42)=
        (.ok (.val (sourceUint (if first then u 0 else u 1))),z) ∧
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 5 Γ.length none
        (sourceUintFixedDecrementTwice first second sd si) (sy 0 42).1).run (.nil,(sy 0 42).2)=
        (.error .timeout,(.nil,z.2)) ∧
      [(hp.get left).1,(hp.get right).1,(hp.get neighbor).1,
       (out.get left).1,(out.get right).1,(out.get neighbor).1]=
        [[u 1,u 8,u 1],[u 9,u 10,u 9],[u 11,u 12],
         [u 0,u 8,u 1],[u 9,u 10,u 9],[u 11,u 12]] ∧
      SourceUintFixedAt z 0 out left ∧ z.1=(sy 0 42).1 ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local sa) (.local si) rfl)).run z=
        (.ok (.val (sourceUint (u 0))),z) ∧
      run code (machine 0 42)=.ok target 0 ∧
      Objects.StateRepr 1 1 8 (Frag.init Δ) ((state 0 42).withHeap out) base target ∧
      Source.MemOK E0 SH z ∧ target.stack=[w[77],w[88]] ∧
      z.2.ex=(sy 0 42).2.ex ∧ z.2.events=(sy 0 42).2.events ∧
      z.2.logs=(sy 0 42).2.logs ∧ z.2.fnLocals=(sy 0 42).2.fnLocals := by
  obtain ⟨out,z,target,he,ht,hitems,hw,hc,hr,hmok,hl,hm,hstack,keep,hobj,haddr,hex,hev,hlog,hfn⟩ :=
    source_uint_fixed_decrement_prefix_timeout (Source.SemanticsExamples.G0 p) F0 Γ.length first second
      (state 0 42) left (represented_left 0 42) sd si td ti (u 0) rfl rfl rfl rfl
      (by simp only [Heap.len,MObj.elems_fixed];decide)
      (by simp only [MObj.elems_fixed];decide) SH (source_memOK 0 42) (initial_repr 0 42)
  simp only [MObj.elems_fixed] at hw
  change hp.writeAddr (.index left .fixed (u 0)) (u 0)=some out at hw
  have hv : MObj.elems .fixed (out.get left)=
      (MObj.elems .fixed (hp.get left)).set (u 0).val.toNat (u 0) :=
    indexedWrite_elems hp out left .fixed (u 0) (u 0) hw
  simp only [MObj.elems_fixed] at hv
  have hleft : (out.get left).1=[u 0,u 8,u 1] := by rw [hv];rfl
  have hvec : [(hp.get left).1,(hp.get right).1,(hp.get neighbor).1,
      (out.get left).1,(out.get right).1,(out.get neighbor).1]=
      [[u 1,u 8,u 1],[u 9,u 10,u 9],[u 11,u 12],[u 0,u 8,u 1],[u 9,u 10,u 9],[u 11,u 12]] := by
    rw [hleft,hobj right (by decide),hobj neighbor (by decide)];rfl
  have hindex : (u 0).val.toNat<(out.get left).1.length := by
    rw [(out.get left).2];decide
  have halias : (Source.evalE (Source.SemanticsExamples.G0 p) F0 2
      (.indexArray (.local sa) (.local si) rfl)).run z=
        (.ok (.val (sourceUint ((out.get left).1[(u 0).val.toNat]'hindex))),z) := hr.eval_index (Source.SemanticsExamples.G0 p) F0 0 sa si (u 0)
    (by rw [hl];rfl) (by rw [hl];rfl) (by decide)
  simp only [hleft] at halias
  refine ⟨out,z,target,?_,hitems,hvec,hr,hl,halias,hc,hm,hmok,hstack,hex,hev,hlog,hfn⟩
  simpa only [MObj.elems_fixed] using he

/- Expected axiom pins below are diagnostic expectations, not passing output. -/
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDecrementLateControls.changed_prefix_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms changed_prefix_timeout
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDecrementLateControls.low_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms low_horizon
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedDecrementLateControls.wrong_expression_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_expression_result

end Solidity.Backend.MemoryOps.SourceUintFixedDecrementLateControls
