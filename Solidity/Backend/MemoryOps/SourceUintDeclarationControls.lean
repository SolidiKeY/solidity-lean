import Solidity.Backend.MemoryOps.SourceUintDeclaration
import Solidity.Backend.MemoryOps.SourceUintMutationControls
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.MemoryOps.SourceUintDeclarationControls
open Evm Evm.Memory
open Source.SemanticsExamples (E0 F0 s0)
private def C : Contract := {vars := []}
private abbrev A : RefTy := .array (.prim .uint)
private abbrev H : HTy := [A,A]
private abbrev Γ : Ctx := [.val .uint,.val .uint,.val .uint,.mem A,.mem A]
private abbrev SA : Source.STy := .array .memory (.int .u256) none
private abbrev SΓ : Source.RCtx := [.int .u256,.int .u256,.int .u256,SA,SA]
private def r : HRef H A := ⟨0,rfl⟩
private def neighbor : HRef H A := ⟨1,rfl⟩
private def vals (xs : List (Fin W)) := xs.map indexValue
private def hp (xs : List (Fin W)) (hfit : 17+xs.length≤80) : Heap H :=
  (⟨vals xs,by
    simp only [vals,List.length_map]
    have h : 80<2^256 := by decide
    omega⟩,
    ⟨[indexValue ⟨8,by decide⟩,indexValue ⟨9,by decide⟩],by decide⟩,())
private def σ (xs : List (Fin W)) (hfit : 17+xs.length≤80) (k l v : Fin W) : State C Γ :=
  {storage := Storage.init C,H := H,heap := hp xs hfit,env := (indexValue k,indexValue l,indexValue v,some r,some r,())}
private def base (n : Nat) : Fin W := if n=0 then ⟨16,by decide⟩ else ⟨80,by decide⟩
private def machine (xs : List (Fin W)) (k l v : Fin W) : Machine :=
  {Machine.init with stack := [w[42]],mem := fun a =>
    if a=0 then w[96] else
    if a=1 then w[16] else
    if a=2 then w[16] else
    if a=3 then (Word.val v) else
    if a=4 then (Word.val l) else
    if a=5 then (Word.val k) else
    if a=7 then w[99] else
    if a=16 then Word.val (wmod xs.length) else
    if h : 17≤a ∧ a<17+xs.length then Word.val xs[a-17] else
    if a=80 then w[2] else
    if a=81 then w[8] else
    if a=82 then w[9] else w[0]}
private theorem elems (xs : List (Fin W)) (hf : 17+xs.length≤80) : MObj.elems .dyn ((hp xs hf).get r)=vals xs := by
  simp only [Heap.get,Objs.get,hp,r,MObj.elems_dyn]
private theorem neighbor_elems (xs : List (Fin W)) (hf : 17+xs.length≤80) : MObj.elems .dyn ((hp xs hf).get neighbor)=[indexValue ⟨8,by decide⟩,indexValue ⟨9,by decide⟩] := by
  simp only [Heap.get,Objs.get,hp,neighbor,MObj.elems_dyn]
private theorem refs {p : PrimTy} (q : HRef H (.array (.prim p))) : p=.uint ∧ (HEq q r ∨ HEq q neighbor) := by
  rcases q with ⟨i,hi⟩
  cases i with
  | zero => cases hi;exact ⟨rfl,.inl HEq.rfl⟩
  | succ i => cases i with
    | zero => cases hi;exact ⟨rfl,.inr HEq.rfl⟩
    | succ i => cases hi
private def y0 : Source.EMState E0 [] := (.nil,s0)
private def ys (xs : List (Fin W)) : Source.EMState E0 [] :=
  ((Source.allocRef (sourceUintMemory [indexValue ⟨8,by decide⟩,indexValue ⟨9,by decide⟩])).run
    ((Source.allocRef (sourceUintMemory (vals xs))).run y0).2).2
private def sy (xs : List (Fin W)) (k l v : Fin W) : Source.EMState E0 SΓ :=
  (.cons (sourceUint (indexValue k)) (.cons (sourceUint (indexValue l)) (.cons (sourceUint (indexValue v))
    (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil)))),(ys xs).2)
private abbrev SH := (Source.Heap.empty (D := E0.layout)).ty
private def ti : Idx Γ (.val .uint) := .here
private def tj : Idx Γ (.val .uint) := .there .here
private def tv : Idx Γ (.val .uint) := .there (.there .here)
private def tr : Idx Γ (.mem A) := .there (.there (.there .here))
private def si : Source.Idx SΓ (.int .u256) := .here
private def sj : Source.Idx SΓ (.int .u256) := .there .here
private def sv : Source.Idx SΓ (.int .u256) := .there (.there .here)
private def sr : Source.Idx SΓ SA := .there (.there (.there .here))
private def salias : Source.Idx SΓ SA := .there (.there (.there (.there .here)))
private def assignCode := writeLocalCode (C := C) 1 tr (.simple (.local ti)) (.simple (.local tv))
private def deleteCode := deleteLocalCode 1 tr (compileVal 1 (.simple (.local tj) : Val C Γ .uint))
private def contentWords (m : Machine) (n : Nat) := List.ofFn (fun i : Fin n => m.mem (17+i.val))
private def frameWords (m : Machine) := [m.mem 0,m.mem 1,m.mem 2,m.mem 3,m.mem 4,m.mem 5,m.mem 6,m.mem 7,m.mem 8,m.mem 9,m.mem 10,m.mem 16,m.mem 80,m.mem 81,m.mem 82,m.mem 96]

private theorem views (xs : List (Fin W)) (hf : 17+xs.length≤80) (k l v : Fin W) :
    Source.MemOK E0 SH (sy xs k l v) ∧ SourceUintMemoryAt (sy xs k l v) 0 (hp xs hf) r .dyn ∧
    SourceUintMemoryAt (sy xs k l v) 1 (hp xs hf) neighbor .dyn ∧
    StateRepr 1 1 8 (Frag.init Γ) (σ xs hf k l v) base (machine xs k l v) :=
  SourceUintMutationControls.initial_views xs hf k l v
private theorem no_struct {s : Name} (q : HRef H (.struct s)) : False := by
  rcases q with ⟨i,hi⟩
  cases i with
  | zero => cases hi
  | succ i => cases i with
    | zero => cases hi
    | succ i => cases hi
private theorem initial_allocator (xs : List (Fin W)) (hf : 17+xs.length≤80) (k l v : Fin W) : StructAllocatorRepr (hp xs hf) base 8 ⟨96,by decide⟩ (machine xs k l v) := by
  apply AllocatorRepr.withoutStructs (hn := fun q => no_struct q)
  refine ⟨((views xs hf k l v).2.2.2).heap,⟨by decide,by decide,rfl,?_⟩,?_⟩
  · intro a ha
    change 96≤a at ha
    change (machine xs k l v).mem a=w[0]
    simp only [machine]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),dif_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  · intro p q
    obtain ⟨rfl,hq|hq⟩ := refs q <;> cases hq
    · change 16+1+(hp xs hf).len r .dyn≤96
      simp only [Heap.len,elems,vals,List.length_map];omega
    · change 80+1+(hp xs hf).len neighbor .dyn≤96
      rw [Heap.len,neighbor_elems];decide

private def ctorState (xs : List (Fin W)) (hf : 17+xs.length≤80) (k l v : Fin W) :=
  (σ xs hf k l v).allocPush (defaultArray .uint ⟨0,W_pos⟩)
private def ctorRef (xs : List (Fin W)) (hf : 17+xs.length≤80) (k l v : Fin W) :=
  ((σ xs hf k l v).alloc (defaultArray .uint ⟨0,W_pos⟩)).2
private def ctorMachine (xs : List (Fin W)) (k l v : Fin W) :=
  writeMachine (allocateMachine (machine xs k l v) ⟨96,by decide⟩ ⟨0,W_pos⟩) 6 w[96]

/-- A populated numeric context with two old aliases executes the actual
independent declaration and the existing whole word constructor. Runtime old
lengths are bounded here only by this concrete fixture's occupied word region. -/
theorem populated_declaration (p : Roadmap.Pipeline) (xs : List (Fin W))
    (hf : 17+xs.length≤80) (k l v : Fin W) :
    ∃ z : Source.EMState E0 SΓ,
      (Source.execS (Source.SemanticsExamples.G0 p) F0 3 SΓ.length none
        (.declVar SA : Source.RStmt E0 [] false .body SΓ (SA::SΓ)) (sy xs k l v).1).run (.nil,(sy xs k l v).2)=
        (.ok (.normal (.cons (.memRef rfl 2) z.1)),(.nil,z.2)) ∧
      TRun.declMem A none rfl (σ xs hf k l v)=.ok ⟨ctorState xs hf k l v,List.prefix_append _ _⟩ ∧
      run (declareNewCode 1 (.lit 0 rfl : Simple C Γ .uint)) (machine xs k l v)=.ok (ctorMachine xs k l v) 0 ∧
      SourceUintMemoryAt (.cons (.memRef rfl 2 : Source.Val E0.layout SA) z.1,z.2)
        2 (ctorState xs hf k l v).heap (ctorRef xs hf k l v) .dyn ∧
      Source.MemOK E0 SH (.cons (.memRef rfl 2 : Source.Val E0.layout SA) z.1,z.2) ∧
      SourceUintMemoryAt (.cons (.memRef rfl 2 : Source.Val E0.layout SA) z.1,z.2)
        0 (ctorState xs hf k l v).heap (r.wk (List.prefix_append H [A])) .dyn ∧
      SourceUintMemoryAt (.cons (.memRef rfl 2 : Source.Val E0.layout SA) z.1,z.2)
        1 (ctorState xs hf k l v).heap (neighbor.wk (List.prefix_append H [A])) .dyn ∧
      z.1=(sy xs k l v).1 ∧
      (Source.Locals.cons (.memRef rfl 2 : Source.Val E0.layout SA) z.1).get .here=.memRef rfl 2 ∧
      (Source.Locals.cons (.memRef rfl 2 : Source.Val E0.layout SA) z.1).get (.there sr)=.memRef rfl 0 ∧
      (Source.Locals.cons (.memRef rfl 2 : Source.Val E0.layout SA) z.1).get (.there salias)=.memRef rfl 0 ∧
      frameWords (ctorMachine xs k l v)=
        [w[97],w[16],w[16],.val v,.val l,.val k,w[96],w[99],w[0],w[0],w[0],
         .val (wmod xs.length),w[2],w[8],w[9],w[0]] ∧
      contentWords (ctorMachine xs k l v) xs.length=xs.map Word.val ∧
      (ctorMachine xs k l v).stack=[w[42]] ∧
      (ctorRef xs hf k l v).id=2 ∧ r.id=0 ∧ neighbor.id=1 ∧
      StructAllocatorRepr (ctorState xs hf k l v).heap (upd base 2 ⟨96,by decide⟩) 8 ⟨97,by decide⟩ (ctorMachine xs k l v) := by
  obtain ⟨z,hz,hs,hd,hc,hr,hmem,hm,ha,hstack,hid⟩ := source_uint_declaration_word
    (Source.SemanticsExamples.G0 p) F0 (sy xs k l v) 0 SH (views xs hf k l v).1
    (σ xs hf k l v) (views xs hf k l v).2.2.2 (initial_allocator xs hf k l v)
    (by decide) (by decide) (by decide)
  have hz' := source_uint_default_run (sy xs k l v) 0
  have he : z=( (sy xs k l v).1,{(sy xs k l v).2 with heap :=
    ((sy xs k l v).2.heap.alloc ⟨SA,sourceUintMemory []⟩).1}) :=
    congrArg Prod.snd (hz.symm.trans hz')
  have fr := (views xs hf k l v).2.1.declaration_frame (Source.SemanticsExamples.G0 p) F0 0
  have fn := (views xs hf k l v).2.2.1.declaration_frame (Source.SemanticsExamples.G0 p) F0 0
  rw [hz] at fr fn
  refine ⟨z,hs,hd,hc,hr,hmem,fr.2.1,fn.2.1,?_,rfl,?_,?_,?_,?_,hstack,hid,rfl,rfl,ha⟩
  · rw [he]
  · rw [congrArg Prod.fst he];rfl
  · rw [congrArg Prod.fst he];rfl
  · have h80 : ¬80<17+xs.length := by omega
    have h81 : ¬81<17+xs.length := by omega
    have h82 : ¬82<17+xs.length := by omega
    simp [frameWords,ctorMachine,writeMachine,allocateMachine,upd,machine,h80,h81,h82]
    exact Nat.mod_eq_of_lt (by decide)
  · apply List.ext_getElem
    · simp only [contentWords,List.length_ofFn,List.length_map]
    · intro i hi hj
      have hi' : i<xs.length := by simpa only [List.length_map] using hj
      simp only [contentWords,List.getElem_ofFn,List.getElem_map,ctorMachine,writeMachine,allocateMachine,upd]
      rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
      simp only [machine]
      rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),dif_pos (by omega)]
      have heq : 17+i-17=i := by omega
      simp only [heq]

/-- The actual declaration horizons fail before allocation; the old populated
heap and locals are retained, with no fabricated fresh local or suffix. -/
theorem populated_timeouts (p : Roadmap.Pipeline) (xs : List (Fin W)) (k l v : Fin W) :
    ∀ n, n≤2 → (Source.execS (Source.SemanticsExamples.G0 p) F0 n SΓ.length none
      (.declVar SA : Source.RStmt E0 [] false .body SΓ (SA::SΓ)) (sy xs k l v).1).run (.nil,(sy xs k l v).2)=
        (.error .timeout,(.nil,(sy xs k l v).2)) :=
  source_uint_declaration_timeouts (Source.SemanticsExamples.G0 p) F0 (sy xs k l v)

/-- Context/identity discrimination on a nonempty old array with zero and max.
The new local cannot be substituted for either retained old alias. -/
theorem fresh_context_negative :
    (ctorRef [⟨7,by decide⟩,⟨0,W_pos⟩,⟨W-1,by have h := W_pos;omega⟩] (by decide) ⟨0,W_pos⟩ ⟨0,W_pos⟩ ⟨0,W_pos⟩).id≠r.id ∧
    (ctorMachine [⟨7,by decide⟩] ⟨0,W_pos⟩ ⟨0,W_pos⟩ ⟨0,W_pos⟩).mem 6≠w[16] ∧
    (ctorMachine [⟨7,by decide⟩] ⟨0,W_pos⟩ ⟨0,W_pos⟩ ⟨0,W_pos⟩).mem 1=w[16] := by
  decide

/-- Complete actual Source object-table observations, including the retained
old alias object and the fresh empty object, for arbitrary old payloads. -/
theorem source_object_table (xs : List (Fin W)) (k l v : Fin W) :
    let z := ((Source.zeroVal (E := E0) (Γ := SΓ) 2 SA).run (sy xs k l v)).2
    [(sy xs k l v).2.heap.get 0,(sy xs k l v).2.heap.get 1,z.2.heap.get 0,z.2.heap.get 1,z.2.heap.get 2]=
      [some ⟨SA,sourceUintMemory (vals xs)⟩,some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩,
       some ⟨SA,sourceUintMemory (vals xs)⟩,some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩,
       some ⟨SA,sourceUintMemory []⟩] := by
  dsimp only
  rw [source_uint_default_run]
  rfl

/-- An explicit nonempty nonuniform/max-word application in BOTH pipelines.
The actual declaration producer supplies the reached run and whole target run. -/
theorem nonuniform_run (p : Roadmap.Pipeline) :
    let xs : List (Fin W) := [⟨7,by decide⟩,⟨0,W_pos⟩,⟨W-1,by have h := W_pos;omega⟩]
    let zero : Fin W := ⟨0,W_pos⟩
    ∃ z : Source.EMState E0 SΓ,
      (Source.execS (Source.SemanticsExamples.G0 p) F0 3 SΓ.length none
        (.declVar SA : Source.RStmt E0 [] false .body SΓ (SA::SΓ)) (sy xs zero zero zero).1).run (.nil,(sy xs zero zero zero).2)=
        (.ok (.normal (.cons (.memRef rfl 2) z.1)),(.nil,z.2)) ∧
      run (declareNewCode 1 (.lit 0 rfl : Simple C Γ .uint)) (machine xs zero zero zero)=
        .ok (ctorMachine xs zero zero zero) 0 ∧
      contentWords (ctorMachine xs zero zero zero) 3=xs.map Word.val := by
  dsimp only
  obtain ⟨z,h⟩ := populated_declaration p [⟨7,by decide⟩,⟨0,W_pos⟩,⟨W-1,by have h := W_pos;omega⟩]
    (by decide) ⟨0,W_pos⟩ ⟨0,W_pos⟩ ⟨0,W_pos⟩
  exact ⟨z,h.1,h.2.2.1,h.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- Fresh contents, intrinsic locals and exact empty-source endpoint after the
actual default builder. Old bindings weaken; they do not become the fresh root. -/
theorem fresh_empty_observations (xs : List (Fin W)) (hf : 17+xs.length≤80) (k l v : Fin W) :
    let z := ((Source.zeroVal (E := E0) (Γ := SΓ) 2 SA).run (sy xs k l v)).2
    (ctorState xs hf k l v).env.get .here=some (ctorRef xs hf k l v) ∧
    (ctorState xs hf k l v).env.get (.there tr)=some (r.wk (List.prefix_append H [A])) ∧
    MObj.elems .dyn ((ctorState xs hf k l v).heap.get (ctorRef xs hf k l v))=[] ∧
    (ctorState xs hf k l v).heap.index (ctorRef xs hf k l v) .dyn (indexValue ⟨0,W_pos⟩)=none ∧
    (Source.memElem (E := E0) (Γ := SΓ) 2 0 (.int .u256)).run z=
      (.error (.revert (Source.panicData .index)),z) ∧
    (ctorMachine xs k l v).mem 96=w[0] := by
  dsimp only
  have he : MObj.elems .dyn ((ctorState xs hf k l v).heap.get (ctorRef xs hf k l v))=[] := by
    dsimp only [ctorState,ctorRef]
    rw [State.allocPush_get,MObj.elems_wk,MObj.elems_dyn]
    simp only [defaultArray,List.replicate_zero,List.map_nil]
  refine ⟨rfl,rfl,he,?_,?_,?_⟩
  · change (MObj.elems .dyn ((ctorState xs hf k l v).heap.get (ctorRef xs hf k l v)))[0]?=none
    rw [he];rfl
  · apply source_uint_bounds _ _ []
    · rw [source_uint_default_run]
      exact Source.Heap.alloc_get _ _
    · decide
  · rfl

/-- info: 'Solidity.Backend.MemoryOps.SourceUintDeclarationControls.populated_declaration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms populated_declaration
/-- info: 'Solidity.Backend.MemoryOps.SourceUintDeclarationControls.populated_timeouts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms populated_timeouts
/-- info: 'Solidity.Backend.MemoryOps.SourceUintDeclarationControls.fresh_context_negative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fresh_context_negative
/-- info: 'Solidity.Backend.MemoryOps.SourceUintDeclarationControls.source_object_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_object_table
/-- info: 'Solidity.Backend.MemoryOps.SourceUintDeclarationControls.nonuniform_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonuniform_run
/-- info: 'Solidity.Backend.MemoryOps.SourceUintDeclarationControls.fresh_empty_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fresh_empty_observations
end Solidity.Backend.MemoryOps.SourceUintDeclarationControls
