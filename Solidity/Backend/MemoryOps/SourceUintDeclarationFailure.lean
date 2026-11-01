import Solidity.Backend.MemoryOps.SourceUintDeclarationSequence

/-! Actual empty declaration then reached fresh-root rejection. Independent Source
retains reached globals; intrinsic/word errors erase their final state. No rollback
or panic-payload equivalence is inferred from these different outcome types. -/
namespace Solidity.Backend.MemoryOps

def sourceUintDeclareFreshAssign {E : Source.Env} {Γ : Source.RCtx}
    (index rhs : Source.Idx Γ (.int .u256)) :
    Source.RItems E [] false .body Γ ((.array .memory (.int .u256) none)::Γ) :=
  .stmt (.declVar (.array .memory (.int .u256) none))
    (.stmt (.expr (sourceUintIndexedAssign .here (.there index) (.there rhs))) .nil)

/-- All runtime uint indices reject on the genuinely fresh empty root. Initial
alignment and constructor premises derive the successful prefix and actual suffix
rejection; no reached relation or failing operation is an input hypothesis. -/
theorem source_uint_declare_fresh_reject_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fsrc : Source.Fr) (n : Nat) (y : Source.EMState E Γ)
    (σ : State C Δ) (si sv : Source.Idx Γ (.int .u256)) (i v : Idx Δ (.val .uint))
    (k value : PrimTy.uint.Denote)
    (hsi : y.1.get si=sourceUint k) (hsv : y.1.get sv=sourceUint value)
    (hti : TEnv.get i σ.env=k) (htv : TEnv.get v σ.env=value)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m)
    (ha : Evm.Memory.StructAllocatorRepr σ.heap base frame cursor m) (hb : 0<b)
    (hspace : cursor.val+1<Evm.W) (hcap : b+(Δ.length+1)≤frame) :
    let A := RefTy.array (.prim .uint)
    let SA := Source.STy.array .memory (.int .u256) none
    let o := Evm.Memory.defaultArray (H := σ.H) .uint ⟨0,Evm.W_pos⟩
    let σ' := σ.allocPush o
    let e := List.prefix_append σ.H [A]
    let fresh := (σ.alloc o).2
    let base' := Evm.upd base σ.H.length cursor
    let mm := Evm.Memory.writeMachine (Evm.Memory.allocateMachine m cursor ⟨0,Evm.W_pos⟩)
      (Evm.cell (b+Δ.length)) (.val cursor)
    ∃ mid : Source.EMState E (SA::Γ),
      (Source.execS G Fsrc (n+5) Γ.length none (.declVar SA : Source.RStmt E [] false .body Γ (SA::Γ)) y.1).run (.nil,y.2)=
        (.ok (.normal mid.1),(.nil,mid.2)) ∧
      (Source.evalE G Fsrc (n+3) (sourceUintIndexedAssign .here (.there si) (.there sv))).run mid=
        (.error (.revert (Source.panicData .index)),mid) ∧
      (Source.execS G Fsrc (n+4) Γ.length none
        (.expr (sourceUintIndexedAssign .here (.there si) (.there sv)) : Source.RStmt E [] false .body (SA::Γ) (SA::Γ)) mid.1).run (.nil,mid.2)=
        (.error (.revert (Source.panicData .index)),(.nil,mid.2)) ∧
      (Source.execItems G Fsrc (n+6) Γ.length none (sourceUintDeclareFreshAssign si sv) y.1).run (.nil,y.2)=
        (.error (.revert (Source.panicData .index)),(.nil,mid.2)) ∧
      TRun.declMem A none rfl σ=.ok ⟨σ',e⟩ ∧
      σ'.heap.writeAddr (.index fresh .dyn k) value=none ∧
      Stmt.run σ' (.assignMem (.index .dyn (.var .here rfl) (.simple (.local (.there i))))
        (.val (.simple (.local (.there v)))))=.error .revert ∧
      Prog.run σ (.cons (.declMem A (.user "freshUint") none rfl rfl)
        (.cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.local (.there i))))
          (.val (.simple (.local (.there v))))) .nil))=.error .revert ∧
      Evm.run (Evm.Memory.declareNewCode b (.lit 0 rfl : Simple C Δ .uint)) m=.ok mm 0 ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) (Γ := .mem A::Δ) b .here
        (.simple (.local (.there i))) (.simple (.local (.there v)))) mm=.revert ∧
      Evm.run (Evm.Memory.declareNewCode b (.lit 0 rfl : Simple C Δ .uint) ++
        Evm.Memory.writeLocalCode (C := C) (Γ := .mem A::Δ) b .here
          (.simple (.local (.there i))) (.simple (.local (.there v)))) m=.revert ∧
      SourceUintMemoryAt mid y.2.heap.next σ'.heap fresh .dyn ∧
      MObj.elems .dyn (σ'.heap.get fresh)=[] ∧
      Source.MemOK E SH mid ∧
      Evm.Memory.StateRepr L b frame (F.push (.mem A) .ok) σ' base' mm ∧
      Evm.Memory.StructAllocatorRepr σ'.heap base' frame ⟨cursor.val+1,hspace⟩ mm ∧
      mid.2={y.2 with heap := (y.2.heap.alloc ⟨SA,sourceUintMemory []⟩).1} ∧
      mid.1=Source.Locals.cons (.memRef rfl y.2.heap.next) y.1 ∧
      mm.stack=m.stack ∧ fresh.id=σ.H.length ∧
      (∀ {R : RefTy} (r : HRef σ.H R) (a : ArrTy R (.prim .uint)) (address : Nat),
        SourceUintMemoryAt y address σ.heap r a →
          SourceUintMemoryAt mid address σ'.heap (r.wk e) a ∧ fresh.id≠(r.wk e).id ∧ y.2.heap.next≠address) := by
  dsimp only
  let A := RefTy.array (.prim .uint)
  let SA := Source.STy.array .memory (.int .u256) none
  let o := Evm.Memory.defaultArray (H := σ.H) .uint ⟨0,Evm.W_pos⟩
  let σ' := σ.allocPush o
  let e := List.prefix_append σ.H [A]
  obtain ⟨z0,hzero,hdecl,hd,hcode,hfresh,hmk,hm',ha',hstack,hid⟩ :=
    source_uint_declaration_word G Fsrc y (n+2) SH hmem σ hm ha hb hspace hcap
  let mid : Source.EMState E (SA::Γ) := (.cons (.memRef rfl y.2.heap.next) z0.1,z0.2)
  have hzid := congrArg Prod.snd (hzero.symm.trans (source_uint_default_run y (n+2)))
  dsimp only at hzid
  have hlocals : z0.1=y.1 := by rw [hzid]
  have hsi' : mid.1.get (.there si)=sourceUint k := by change z0.1.get si=_;rw [hlocals];exact hsi
  have hsv' : mid.1.get (.there sv)=sourceUint value := by change z0.1.get sv=_;rw [hlocals];exact hsv
  have hti' : TEnv.get (.there i) σ'.env=k := by
    change TEnv.get i (TEnv.wk e Δ σ.env)=_
    rw [TEnv.get_wk];exact hti
  have htv' : TEnv.get (.there v) σ'.env=value := by
    change TEnv.get v (TEnv.wk e Δ σ.env)=_
    rw [TEnv.get_wk];exact htv
  have helem : MObj.elems .dyn (σ'.heap.get (σ.alloc o).2)=[] := by
    dsimp only [σ']
    rw [State.allocPush_get,MObj.elems_wk,MObj.elems_dyn]
    simp only [o,Evm.Memory.defaultArray,List.replicate_zero,List.map_nil]
  have hbound : σ'.heap.len (σ.alloc o).2 .dyn≤k.1.toNat := by rw [Heap.len,helem];exact Nat.zero_le _
  have hn : σ'.heap.writeAddr (.index (σ.alloc o).2 .dyn k) value=none := by
    simp only [Heap.writeAddr,Heap.setIndex,helem,List.length_nil,Nat.not_lt_zero,↓reduceIte]
  have htf : TEnv.get (.here : Idx (.mem A::Δ) (.mem A)) σ'.env=some (σ.alloc o).2 := rfl
  have hi : Stmt.run σ' (.assignMem (.index .dyn (.var .here rfl) (.simple (.local (.there i))))
      (.val (.simple (.local (.there v)))))=.error .revert := by
    change TRun.assignMem _ _ σ'=_
    simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,
      htf,hti',htv',bind,Except.bind,pure,Except.pure,hn,TRes.ofOpt]
  have hbad := resolved_uint_assign_word_bounds G Fsrc n σ' (σ.alloc o).2 hfresh
    .here (.there si) (.there sv) .here (.there i) (.there v) k value rfl hsi' hsv' rfl hti' htv' hbound hm'
  have hs := source_expr_statement_error G Fsrc (n+3) Γ.length _ mid mid _ hbad.1
  refine ⟨mid,hdecl,hbad.1,hs,?_,hd,hn,hi,?_,hcode,hbad.2,?_,hfresh,helem,hmk,hm',ha',?_,?_,hstack,hid,?_⟩
  · exact source_items_context_pair_error G Fsrc (n+3) Γ.length _ _ y mid mid _ hdecl hs
  · have hd' : Stmt.run σ (.declMem A (.user "freshUint") none rfl rfl)=.ok ⟨σ',e⟩ := hd
    rw [Prog.run_cons_ok hd']
    change (TRun.seq (TRun.assignMem (.index .dyn (.var .here rfl) (.simple (.local (.there i))))
      (.val (.simple (.local (.there v))))) TRun.nil σ').map _=_
    change TRun.assignMem _ _ σ'=.error .revert at hi
    unfold TRun.seq
    rw [hi]
    rfl
  · rw [Evm.run_append_ok hcode];exact hbad.2
  · change z0.2=_;rw [hzid]
  · change Source.Locals.cons _ z0.1=Source.Locals.cons _ y.1;rw [hlocals]
  · intro R r a address hr
    have hf := hr.declaration_frame G Fsrc (n+2)
    rw [hzero] at hf
    exact ⟨hf.2.1,by have h := r.id_lt;change σ.H.length≠r.id;omega,hf.2.2.2.2.2.2⟩

/-- A genuine low-horizon failure of the reached assignment, not bounds panic. -/
theorem source_uint_assign_horizon_two {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (y : Source.EMState E Γ)
    (root : Source.Idx Γ (.array .memory (.int .u256) none))
    (i v : Source.Idx Γ (.int .u256)) :
    (Source.evalE G F 2 (sourceUintIndexedAssign root i v)).run y=(.error .timeout,y) := by
  rfl

/-- Horizon5 executes the declaration but times out before the fresh write.
The error exposes the reached globals only; the fresh local is separately known
from the successful prefix, not fabricated as an Items error result. -/
theorem source_uint_declare_fresh_timeout {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (y : Source.EMState E Γ)
    (i v : Source.Idx Γ (.int .u256)) :
    let globals := {y.2 with heap := (y.2.heap.alloc ⟨.array .memory (.int .u256) none,sourceUintMemory []⟩).1}
    (Source.execItems G F 5 Γ.length none (sourceUintDeclareFreshAssign i v) y.1).run (.nil,y.2)=
      (.error .timeout,(.nil,globals)) := by
  dsimp only
  let z : Source.EMState E Γ :=
    (y.1,{y.2 with heap := (y.2.heap.alloc ⟨.array .memory (.int .u256) none,sourceUintMemory []⟩).1})
  let mid : Source.EMState E ((.array .memory (.int .u256) none)::Γ) := (.cons (.memRef rfl y.2.heap.next) z.1,z.2)
  have hs := source_decl_statement_run G F 3 Γ.length y z _ (source_uint_default_run y 1)
  have ht := source_expr_statement_error G F 2 Γ.length _ mid mid .timeout
    (source_uint_assign_horizon_two G F mid .here (.there i) (.there v))
  exact source_items_context_pair_error G F 2 Γ.length _ _ y mid mid .timeout hs ht

/-- A smaller horizon fails inside declaration itself and exposes no new object. -/
theorem source_uint_declare_fresh_early_timeout {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (y : Source.EMState E Γ)
    (i v : Source.Idx Γ (.int .u256)) :
    (Source.execItems G F 3 Γ.length none (sourceUintDeclareFreshAssign i v) y.1).run (.nil,y.2)=
      (.error .timeout,(.nil,y.2)) := by
  have hs := source_uint_declaration_timeouts G F y 2 (by decide)
  rw [sourceUintDeclareFreshAssign,Source.execItems,Source.Hoare.run_bind,hs]

/-- At horizon4 declaration3 succeeds, then the RHS local at horizon0 times
out. This differs from a declaration timeout although both halts are `.timeout`. -/
theorem source_uint_declare_fresh_timeout_four {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (y : Source.EMState E Γ)
    (i v : Source.Idx Γ (.int .u256)) :
    let globals := {y.2 with heap := (y.2.heap.alloc ⟨.array .memory (.int .u256) none,sourceUintMemory []⟩).1}
    (Source.execItems G F 4 Γ.length none (sourceUintDeclareFreshAssign i v) y.1).run (.nil,y.2)=
      (.error .timeout,(.nil,globals)) := by
  dsimp only
  let z : Source.EMState E Γ :=
    (y.1,{y.2 with heap := (y.2.heap.alloc ⟨.array .memory (.int .u256) none,sourceUintMemory []⟩).1})
  let mid : Source.EMState E ((.array .memory (.int .u256) none)::Γ) := (.cons (.memRef rfl y.2.heap.next) z.1,z.2)
  have hs := source_decl_statement_run G F 2 Γ.length y z _ (source_uint_default_run y 0)
  have he : (Source.evalE G F 1 (sourceUintIndexedAssign .here (.there i) (.there v))).run mid=(.error .timeout,mid) := rfl
  have ht := source_expr_statement_error G F 1 Γ.length _ mid mid .timeout he
  exact source_items_context_pair_error G F 1 Γ.length _ _ y mid mid .timeout hs ht

/-- Complete low-horizon classification. The threshold is an observed evaluator
fuel distinction, not a public object-size, payload or admission restriction. -/
theorem source_uint_declare_fresh_low_horizons {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (y : Source.EMState E Γ)
    (i v : Source.Idx Γ (.int .u256)) (fuel : Nat) (hf : fuel≤5) :
    let globals := if fuel<4 then y.2 else
      {y.2 with heap := (y.2.heap.alloc ⟨.array .memory (.int .u256) none,sourceUintMemory []⟩).1}
    (Source.execItems G F fuel Γ.length none (sourceUintDeclareFreshAssign i v) y.1).run (.nil,y.2)=
      (.error .timeout,(.nil,globals)) := by
  match fuel with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => exact source_uint_declare_fresh_early_timeout G F y i v
  | 4 => exact source_uint_declare_fresh_timeout_four G F y i v
  | 5 => exact source_uint_declare_fresh_timeout G F y i v
  | n+6 => omega

/-- info: 'Solidity.Backend.MemoryOps.source_uint_declare_fresh_reject_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_declare_fresh_reject_word
/-- info: 'Solidity.Backend.MemoryOps.source_uint_assign_horizon_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_assign_horizon_two
/-- info: 'Solidity.Backend.MemoryOps.source_uint_declare_fresh_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_declare_fresh_timeout
/-- info: 'Solidity.Backend.MemoryOps.source_uint_declare_fresh_early_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_declare_fresh_early_timeout
/-- info: 'Solidity.Backend.MemoryOps.source_uint_declare_fresh_timeout_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_declare_fresh_timeout_four
/-- info: 'Solidity.Backend.MemoryOps.source_uint_declare_fresh_low_horizons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_declare_fresh_low_horizons
end Solidity.Backend.MemoryOps
