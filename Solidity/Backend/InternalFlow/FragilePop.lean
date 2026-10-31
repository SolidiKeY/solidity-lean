import Solidity.Backend.InternalFlow.FragileCalls

/-! A root pop consumer of published pop_sim/storeDrop. No shrinking semantics
is reimplemented: the old computed dropFragile classification is retained. -/
namespace Solidity.Backend.InternalFlow.FragilePop
open Evm Evm.Memory
variable {C : Contract}

private theorem core_ok {L b : Nat} {Δ : Ctx} {F : Frag Δ} {H : HTy}
    {res : TRes (Solidity.Out C H Δ)} {out : Evm.Out} {m : Machine}
    (h : StmtOut C L b F true false false res out m) (o : Solidity.Out C H Δ)
    (ho : res = .ok o) : ∃ m', out = .ok m' 0 ∧ m'.stack = m.stack ∧ Sim C L b F o.st m' := by
  rcases h with ⟨o',m',hs,ht,hk,_,hc⟩ | ⟨hs,ht⟩ | ⟨ha,_⟩ | ⟨hp,_⟩ | ⟨hs,_⟩
  · have he : o' = o := Except.ok.inj (hs.symm.trans ho)
    subst o'
    exact ⟨m',ht,hk,hc⟩
  · rw [ho] at hs; contradiction
  · cases ha
  · cases hp
  · rw [ho] at hs; contradiction

private theorem core_error {L b : Nat} {Δ : Ctx} {F : Frag Δ} {H : HTy}
    {res : TRes (Solidity.Out C H Δ)} {out : Evm.Out} {m : Machine}
    (h : StmtOut C L b F true false false res out m) (ho : res = .error .revert) : out = .revert := by
  rcases h with ⟨o,m',hs,_,_,_,_⟩ | ⟨_,ht⟩ | ⟨ha,_⟩ | ⟨hp,_⟩ | ⟨hs,_⟩
  · rw [ho] at hs; contradiction
  · exact ht
  · cases ha
  · cases hp
  · rw [ho] at hs
    cases (Except.error.inj hs)

/-- A core-proved persistent-store update with identical memory preserves all
represented memory objects, pointers and reference fields. -/
theorem sameMemory {L b frame : Nat} {Γ : Ctx} {F G : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m m' : Machine} (st : Storage C)
    (h : StateRepr L b frame F σ base m) (hc : Sim C L b G (σ.withStorage st) m')
    (hm : m'.mem = m.mem) : StateRepr L b frame G (σ.withStorage st) base m' := by
  refine ⟨hc,⟨?_,h.heap.above,h.heap.separated⟩,?_,h.locals,
    ⟨?_,h.structs.above,h.structs.separated⟩,h.separated,RefFieldsRepr.mem_eq h.refs hm⟩
  · intro p r
    exact ⟨(h.heap.arrays r).space,hm ▸ (h.heap.arrays r).length,
      fun i v hv => hm ▸ (h.heap.arrays r).elements i v hv⟩
  · intro R i
    obtain ⟨r,hr,hmem⟩ := h.pointers i
    exact ⟨r,hr,by rw [hm]; exact hmem⟩
  · intro s r
    exact ⟨(h.structs.objects r).space,fun hf => hm ▸ (h.structs.objects r).fields hf⟩

/-- Actual root-array pop, preserving memory while dropping every fragile fact.
It is deliberately not a general shrinking or loop compiler. -/
def popRoot (b : Nat) {Γ : Ctx} (F : Frag Γ) (name : Name) {E : Ty}
    (root : C.rootType name = some (.array E)) :
    Calls.Statement b F (.pop (.loc (.root name root))) where
  frag := F.dropFragile
  code := compileSPath b (.loc (.root name root)) ++ popCode
  need := Γ.length
  cost := fun _ => 0
  allocates := false
  zeroCost := fun _ _ => rfl
  sound := by
    intro L frame σ base m h room capacity
    apply ResultRepr.growing
    let q : SPath C Γ (.array E) := .loc (.root name root)
    have hc := pop_sim q h.core (by rfl)
    cases hs : σ.storage.pop E.isMapping (SRef.ofRoot name root) with
    | none =>
      have source : (Stmt.pop q).run σ = .error .revert := by
        simp only [Stmt.run,Stmt.runR,TRun.pop,q,SPath.resolveT,Loc.resolveT,hs,
          bind,Except.bind,TRes.ofOpt]
      exact .inr ⟨source,core_error hc source⟩
    | some st =>
      have source : (Stmt.pop q).run σ = .ok (⟨σ.withStorage st,List.prefix_refl _⟩ : Solidity.Out C σ.H Γ) := by
        simp only [Stmt.run,Stmt.runR,TRun.pop,q,SPath.resolveT,Loc.resolveT,hs,
          bind,Except.bind,TRes.ofOpt,pure,Except.pure]
      obtain ⟨m',ht,hstack,repr⟩ := core_ok hc _ source
      have hw : m.store (rootSlot C name) < W := by
        have hr := h.core.store name (.array E) root
        generalize hv : σ.storage.get root = v at hr
        cases hr with
        | array hlen hbound hall => rw [hlen]; exact Nat.lt_trans hbound (Nat.lt_of_le_of_lt h.core.bound Lmax_lt_W)
      have step : run (compileSPath b q ++ popCode) m =
          if m.store (rootSlot C name) = 0 then .revert
          else .ok {m with store := WordStore.write m.store (rootSlot C name) (m.store (rootSlot C name) - 1)} 0 := by
        rw [run_append_ok (m' := m.push (.slot (rootSlot C name))) (show run (compileSPath b q) m = .ok (m.push (.slot (rootSlot C name))) 0 from rfl)]
        exact popCode_run m m.stack (rootSlot C name) hw
      have hm : m'.mem = m.mem := by
        rw [ht] at step
        split at step
        · contradiction
        · have he := congrArg Machine.mem (Evm.Out.ok.inj step).1
          exact he
      exact .inl ⟨_,m',source,ht,sameMemory st h repr hm,hstack,fun cursor hb alloc => alloc.mem_eq hm⟩

def statement (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (s : Stmt C Γ Δ) :
    Option (Calls.Statement b F s) :=
  match FragileFrames.statement b F s with
  | some out => some out
  | none => match s with
    | .pop (.loc (.root name root)) => some (popRoot b F name root)
    | _ => none

end Solidity.Backend.InternalFlow.FragilePop
