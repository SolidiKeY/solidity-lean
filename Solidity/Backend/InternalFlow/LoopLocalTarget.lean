import Solidity.Backend.InternalFlow.LocalStoreLoop
import Solidity.Backend.InternalFlow.CallerView
import Solidity.Evm.MemoryLoopCompile
import Solidity.Backend.InternalFlow.StoragePrefixFrame
import Solidity.Evm.Compiler
/-! Actual published loop results strengthened by syntax-derived caller locals.
Room remains source-prefix based. No heap-content/liveness oracle is used. -/
namespace Solidity.Backend.InternalFlow.LoopLocalTarget
open Evm Evm.Memory LocalStoreFlow
variable {C : Contract} {Γ Δ Ξ : Ctx}

theorem captured {body : Prog C Γ Δ} (protect : Thin Ξ Γ)
    (plans : ∀ {t : LTy} (i : Idx Ξ t), ProgPlan t body (i.wk protect))
    (ann : LoopAnn C Γ) (c : Val C Γ .bool) (σ : State C Γ) (o : Solidity.Out C σ.H Γ)
    (ran : (Stmt.loop ann c body).run σ = .ok o) :
    TEnv.thin protect o.st.env = TEnv.wk o.ext Ξ (TEnv.thin protect σ.env) := by
  apply TEnv.ext
  intro t i
  rw [CallerFrame.read_thin,TEnv.get_wk,CallerFrame.read_thin]
  exact (plans i).loop_statement ann c σ o ran

/-- Every alternative is the producer's real outcome. Only its successful
state is strengthened with protected typed bindings and actual target words. -/
theorem outcome {b L frame : Nat} {F : Frag Γ} {c : Val C Γ .bool}
    {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) (protect : Thin Ξ Γ)
    (plans : ∀ {t : LTy} (i : Idx Ξ t), ProgPlan t body (i.wk protect))
    (ann : LoopAnn C Γ) {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m)
    (cap : b + frameNeedProg body ≤ frame) (room : LoopRoom b frame c body σ base m) :
    (∃ o m' base' cost, (Stmt.loop ann c body).run σ = .ok o ∧
      run [.loop cond code] m = .ok m' 0 ∧ LoopPrefix c body σ o cost ∧
      StateRepr L b frame F o.st base' m' ∧ m'.stack = m.stack ∧
      BaseExtends σ.H base base' ∧ GrowsAllocator b frame cost σ base m o.st base' m' ∧
      TEnv.thin protect o.st.env = TEnv.wk o.ext Ξ (TEnv.thin protect σ.env) ∧
      (∀ (R : RefTy) (i : Idx Ξ (.mem R)) (r : HRef σ.H R),
        TEnv.get (i.wk protect) σ.env = some r →
          m'.mem (cellOf b (i.wk protect)) = .val (base r.id)) ∧
      (∀ (p : PrimTy) (i : Idx Ξ (.val p)),
        ReprV p (TEnv.get (i.wk protect) σ.env) (m'.mem (cellOf b (i.wk protect))))) ∨
    ((Stmt.loop ann c body).run σ = .error .revert ∧ run [.loop cond code] m = .revert) ∨
    ((Stmt.loop ann c body).run σ = .error .diverge ∧ run [.loop cond code] m = .fault) := by
  rcases cert.correct ann repr cap room with ⟨o,m',base',cost,hs,ht,hc,hr,hk,he,hg⟩ | halt
  · have env := captured protect plans ann c σ o hs
    exact .inl ⟨o,m',base',cost,hs,ht,hc,hr,hk,he,hg,env,
      CallerView.represented o protect env hr he,
      fun p i => CallerView.represented_value_drop o Ext.refl protect env hr i⟩
  · exact .inr halt

/-- An actual two-turn execution classifies ALL source prefixes; no depth
cutoff or assumed Room predicate replaces the source execution equations. -/
theorem two_turn_prefixes (c : Val C Γ .bool) (body : Prog C Γ Δ) (σ : State C Γ)
    (one : Solidity.Out C σ.H Δ)
    (two : Solidity.Out C one.st.H Δ)
    (h0 : body.run σ = .ok one)
    (h1 : body.run (one.st.drop body.ext) = .ok two)
    (c2 : c.evalT (two.st.drop body.ext) = .ok false)
    {o : Solidity.Out C σ.H Γ} {amount : Nat} (pref : LoopPrefix c body σ o amount) :
    (o = ⟨σ,List.prefix_refl _⟩ ∧ amount = 0) ∨
    (o = ⟨one.st.drop body.ext,one.ext⟩ ∧ amount = allocationCostProg body σ) ∨
    (o = ⟨two.st.drop body.ext,one.ext.trans two.ext⟩ ∧
      amount = allocationCostProg body σ + allocationCostProg body (one.st.drop body.ext)) := by
  induction pref with
  | start => exact .inl ⟨rfl,rfl⟩
  | next hp hc hs ih =>
    rcases ih with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · have same := Except.ok.inj (h0.symm.trans hs)
      cases same
      exact .inr (.inl ⟨rfl,Nat.zero_add _⟩)
    · have same := Except.ok.inj (h1.symm.trans hs)
      cases same
      exact .inr (.inr ⟨rfl,rfl⟩)
    · rw [c2] at hc
      cases hc

/-- Genuine summed input and the classified reached source prefixes derive
Room, including each reached allocating turn. -/
theorem room_two_turns {b frame : Nat} (c : Val C Γ .bool) (body : Prog C Γ Δ)
    (σ : State C Γ) (one : Solidity.Out C σ.H Δ) (two : Solidity.Out C one.st.H Δ)
    (h0 : body.run σ = .ok one) (h1 : body.run (one.st.drop body.ext) = .ok two)
    (c2 : c.evalT (two.st.drop body.ext) = .ok false)
    (base : Nat → Fin W) (m : Machine)
    (input : AllocationInput b frame
      (allocationCostProg body σ + allocationCostProg body (one.st.drop body.ext)) σ base m) :
    LoopRoom b frame c body σ base m := by
  intro o amount hp hc
  rcases two_turn_prefixes c body σ one two h0 h1 c2 hp with
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · simpa only [Nat.zero_add] using input.of_le (Nat.le_add_right _ _)
  · exact input
  · rw [c2] at hc
    cases hc

/-- Structural public selector equation kept abstract to avoid re-elaborating
concrete compiler certificates at each projection. All fields come from the
actual checked finite compiler and its actual stable fragment. -/
theorem compile_loop_equation {b : Nat} {F : Frag Γ} {c : Val C Γ .bool}
    {body : Prog C Γ Δ} (ann : LoopAnn C Γ)
    (condition : CompiledVal b F c) (hc : Memory.compileVal b F c = some condition)
    (compiled : Memory.CompiledProg b F body)
    (hb : Memory.compileProg b F body = some compiled)
    (stable : compiled.frag.restrict Γ = F) :
    Loops.compileStmt b F (.loop ann c body) = some
      (⟨F,[.loop condition.code compiled.code],
        .loop ann c body condition.code compiled.code compiled.frag condition.cert compiled.cert stable⟩ :
          Loops.CompiledStmt b F (.loop ann c body)) := by
  change ((Memory.compileVal b F c).bind fun condition =>
    (Memory.compileProg b F body).bind fun compiled =>
      if stable : compiled.frag.restrict Γ = F then some
        (⟨F,[.loop condition.code compiled.code],
          .loop ann c body condition.code compiled.code compiled.frag condition.cert compiled.cert stable⟩ :
            Loops.CompiledStmt b F (.loop ann c body)) else none) = _
  rw [hc]
  simp only [Option.bind_some]
  rw [hb]
  simp only [Option.bind_some,dif_pos stable]

/-- A genuine storage-only compiled prefix preserves an initially empty heap
and allocator. This is an adapter over compile_exact and the actual source
frame, not an assumed represented populated input. -/
theorem storage_prefix {L b frame : Nat} {P : Prog C [] []}
    {σ : State C []} {base : Nat → Fin W} {cursor : Fin W} {m : Evm.Machine}
    (repr : StateRepr L b frame (Frag.init []) σ base m)
    (alloc : StructAllocatorRepr σ.heap base frame cursor m) (empty : σ.H = [])
    (fragment : Evm.inFragP (Frag.init []) P = some (Frag.init []))
    (bound : L + Evm.Prog.pushes P ≤ Lmax) (pays : Evm.Prog.pays P = false)
    (stores : StoragePrefixFrame.storeProg P = true)
    (noMem : (Evm.compileProg b P).all StoragePrefixFrame.noMemoryStore = true)
    (out : Solidity.Out C σ.H []) (ran : P.run σ = .ok out) :
    ∃ m', run (Evm.compileProg b P) m = .ok m' 0 ∧
      StateRepr (L + Evm.Prog.pushes P) b frame (Frag.init []) out.st base m' ∧
      StructAllocatorRepr out.st.heap base frame cursor m' ∧ m'.stack = m.stack := by
  obtain ⟨m',ht,hk,hcore⟩ : ∃ m', run (Evm.compileProg b P) m = .ok m' 0 ∧ m'.stack = m.stack ∧
      Sim C (L + Evm.Prog.pushes P) b (Frag.init []) out.st m' := by
    rcases Evm.compile_exact fragment repr.core bound pays with ⟨o,m',hs,ht,hk,hr⟩ | ⟨hs,ht⟩ | ⟨hs,ht⟩
    · have same : o = out := Except.ok.inj (hs.symm.trans ran)
      subst o
      exact ⟨m',ht,hk,hr⟩
    · rcases hs with hs | ⟨_,hs⟩ <;> rw [ran] at hs <;> contradiction
    · rw [ran] at hs; contradiction
  have hm : m'.mem = m.mem := StoragePrefixFrame.run_mem _ noMem ht
  have sourceFrame := StoragePrefixFrame.store_prog_frame P stores ran
  have allocator : StructAllocatorRepr out.st.heap base frame cursor m' :=
    StoragePrefixFrame.allocator_heap sourceFrame.H.symm sourceFrame.heap.symm (alloc.mem_eq hm)
  have noRef {R : RefTy} (r : HRef out.st.H R) : False := by
    have shape : out.st.H = [] := sourceFrame.H.trans empty
    rw [shape] at r
    cases r.get?
  refine ⟨m',ht,⟨hcore,⟨fun r => (noRef r).elim,fun r => (noRef r).elim,
    fun r => (noRef r).elim⟩,?_,repr.locals,⟨fun r => (noRef r).elim,
    fun r => (noRef r).elim,fun r => (noRef r).elim⟩,
    fun _ r => (noRef r).elim,?_⟩,allocator,hk⟩
  · intro R i; nomatch i
  · intro s f R r hf; exact (noRef r).elim

/-- Pin a successful reached cost from real source prefixes and independently
observed distinct states, without concrete dependent-elimination replay. -/
theorem two_turn_cost (c : Val C Γ .bool) (body : Prog C Γ Δ) (σ : State C Γ)
    (one : Solidity.Out C σ.H Δ) (two : Solidity.Out C one.st.H Δ)
    (h0 : body.run σ = .ok one) (h1 : body.run (one.st.drop body.ext) = .ok two)
    (c2 : c.evalT (two.st.drop body.ext) = .ok false)
    (different0 : (⟨two.st.drop body.ext,one.ext.trans two.ext⟩ : Solidity.Out C σ.H Γ) ≠ ⟨σ,List.prefix_refl _⟩)
    (different1 : (⟨two.st.drop body.ext,one.ext.trans two.ext⟩ : Solidity.Out C σ.H Γ) ≠ ⟨one.st.drop body.ext,one.ext⟩)
    {amount : Nat} (pref : LoopPrefix c body σ
      ⟨two.st.drop body.ext,one.ext.trans two.ext⟩ amount) :
    amount = allocationCostProg body σ + allocationCostProg body (one.st.drop body.ext) := by
  rcases two_turn_prefixes c body σ one two h0 h1 c2 pref with
    ⟨same,cost⟩ | ⟨same,cost⟩ | ⟨same,cost⟩
  · exact (different0 same).elim
  · exact (different1 same).elim
  · exact cost

/-- Pin the real successful source result before instantiating a large client.
All target, cost, frame and protected-word facts still come from outcome. -/
theorem endpoint {b L frame : Nat} {F : Frag Γ} {c : Val C Γ .bool}
    {body : Prog C Γ Δ} {cond code : List Evm.Instr}
    (cert : LoopCert b F c body cond code) (protect : Thin Ξ Γ)
    (plans : ∀ {t : LTy} (i : Idx Ξ t), ProgPlan t body (i.wk protect))
    (ann : LoopAnn C Γ) {σ : State C Γ} {base : Nat → Fin W} {m : Evm.Machine}
    (repr : StateRepr L b frame F σ base m)
    (cap : b + frameNeedProg body ≤ frame) (room : LoopRoom b frame c body σ base m)
    (out : Solidity.Out C σ.H Γ) (ran : (Stmt.loop ann c body).run σ = .ok out) :
    ∃ m' base' cost, run [.loop cond code] m = .ok m' 0 ∧ LoopPrefix c body σ out cost ∧
      StateRepr L b frame F out.st base' m' ∧ m'.stack = m.stack ∧
      BaseExtends σ.H base base' ∧ GrowsAllocator b frame cost σ base m out.st base' m' ∧
      TEnv.thin protect out.st.env = TEnv.wk out.ext Ξ (TEnv.thin protect σ.env) ∧
      (∀ (R : RefTy) (i : Idx Ξ (.mem R)) (r : HRef σ.H R),
        TEnv.get (i.wk protect) σ.env = some r →
          m'.mem (cellOf b (i.wk protect)) = .val (base r.id)) ∧
      (∀ (p : PrimTy) (i : Idx Ξ (.val p)),
        ReprV p (TEnv.get (i.wk protect) σ.env) (m'.mem (cellOf b (i.wk protect)))) := by
  rcases outcome cert protect plans ann repr cap room with
    ⟨o,m',base',cost,hs,ht,hc,hr,hk,he,hg,env,ptrs,vals⟩ | ⟨hs,ht⟩ | ⟨hs,ht⟩
  · have same : o = out := Except.ok.inj (hs.symm.trans ran)
    subst o
    exact ⟨m',base',cost,ht,hc,hr,hk,he,hg,env,ptrs,vals⟩
  · rw [ran] at hs; contradiction
  · rw [ran] at hs; contradiction

/-- If the actual initial condition cannot continue, every reached allocation
demand is impossible. This covers false and error without identifying them. -/
theorem room_initial_not_true {b frame : Nat} (c : Val C Γ .bool) (body : Prog C Γ Δ)
    (σ : State C Γ) (base : Nat → Fin W) (m : Evm.Machine)
    (stops : c.evalT σ ≠ .ok true) : LoopRoom b frame c body σ base m := by
  have onlyStart : ∀ {o : Solidity.Out C σ.H Γ} {cost : Nat}, LoopPrefix c body σ o cost →
      o = ⟨σ,List.prefix_refl _⟩ ∧ cost = 0 := by
    intro o cost hp
    induction hp with
    | start => exact ⟨rfl,rfl⟩
    | next hp hc hs ih =>
      rcases ih with ⟨rfl,rfl⟩
      exact (stops hc).elim
  intro o cost hp hc
  rcases onlyStart hp with ⟨rfl,rfl⟩
  exact (stops hc).elim

/-- Storage-only source and target execution transport arbitrary real allocator
ownership at exact cost zero. No populated StateRepr is assumed or produced. -/
theorem storage_grows {b frame : Nat} {Ξ : Ctx} {P : Prog C Γ Ξ}
    (stores : StoragePrefixFrame.storeProg P = true)
    (noMem : (Evm.compileProg b P).all StoragePrefixFrame.noMemoryStore = true)
    {σ : State C Γ} {out : Solidity.Out C σ.H Ξ} (ran : P.run σ = .ok out)
    {base : Nat → Fin W} {m m' : Evm.Machine}
    (target : run (Evm.compileProg b P) m = .ok m' 0) :
    GrowsAllocator b frame 0 σ base m out.st base m' := by
  have hm := StoragePrefixFrame.run_mem _ noMem target
  have sourceFrame := StoragePrefixFrame.store_prog_frame P stores ran
  intro cursor hb alloc hspace
  have transported := StoragePrefixFrame.allocator_heap sourceFrame.H.symm sourceFrame.heap.symm (alloc.mem_eq hm)
  simpa only [Nat.add_zero] using transported

theorem revert_endpoint {b L frame : Nat} {F : Frag Γ} {c : Val C Γ .bool}
    {body : Prog C Γ Δ} {cond code : List Evm.Instr}
    (cert : LoopCert b F c body cond code) (ann : LoopAnn C Γ)
    {σ : State C Γ} {base : Nat → Fin W} {m : Evm.Machine}
    (repr : StateRepr L b frame F σ base m) (cap : b + frameNeedProg body ≤ frame)
    (room : LoopRoom b frame c body σ base m)
    (failed : (Stmt.loop ann c body).run σ = .error .revert) :
    run [.loop cond code] m = .revert := by
  rcases cert.correct ann repr cap room with ⟨o,m',base',cost,hs,ht,rest⟩ | ⟨hs,ht⟩ | ⟨hs,ht⟩
  · rw [failed] at hs; contradiction
  · exact ht
  · rw [failed] at hs; cases Except.error.inj hs

theorem diverge_endpoint {b L frame : Nat} {F : Frag Γ} {c : Val C Γ .bool}
    {body : Prog C Γ Δ} {cond code : List Evm.Instr}
    (cert : LoopCert b F c body cond code) (ann : LoopAnn C Γ)
    {σ : State C Γ} {base : Nat → Fin W} {m : Evm.Machine}
    (repr : StateRepr L b frame F σ base m) (cap : b + frameNeedProg body ≤ frame)
    (room : LoopRoom b frame c body σ base m)
    (failed : (Stmt.loop ann c body).run σ = .error .diverge) :
    run [.loop cond code] m = .fault := by
  rcases cert.correct ann repr cap room with ⟨o,m',base',cost,hs,ht,rest⟩ | ⟨hs,ht⟩ | ⟨hs,ht⟩
  · rw [failed] at hs; contradiction
  · rw [failed] at hs; cases Except.error.inj hs
  · exact ht
end Solidity.Backend.InternalFlow.LoopLocalTarget
