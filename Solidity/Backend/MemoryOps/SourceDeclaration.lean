import Solidity.Backend.MemoryOps.SourceDefault
import Solidity.Source.StmtProgress

/-! Actual resolved Source default declaration through the published constructor
and existing intrinsic/word certificate. No new constructor or interpreter. -/
namespace Solidity.Backend.MemoryOps

theorem source_decl_statement_run {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (horizon nps : Nat)
    (y z : Source.EMState E Γ) (value : Source.Val E.layout τ)
    (hz : (Source.zeroVal (E := E) (Γ := Γ) horizon τ).run y=(.ok value,z)) :
    (Source.execS G F (horizon+1) nps none
      (.declVar τ : Source.RStmt E [] false .body Γ (τ::Γ)) y.1).run (.nil,y.2)=
        (.ok (.normal (.cons value z.1)),(.nil,z.2)) := by
  have hsub : (Source.EM.sub (Γ := []) y.1 (Source.zeroVal (E := E) (Γ := Γ) horizon τ)).run (.nil,y.2)=
      (.ok (value,z.1),(.nil,z.2)) := by
    unfold Source.EM.sub
    have hz' : (Source.zeroVal (E := E) (Γ := Γ) horizon τ) (y.1,y.2)=(.ok value,z) := hz
    cases z
    simp only [ExceptT.run,ExceptT.mk,hz']
  rw [Source.execS,Source.Hoare.run_bind,hsub]
  rfl

theorem source_decl_statement_error {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (horizon nps : Nat)
    (y z : Source.EMState E Γ) (halt : Source.Halt)
    (hz : (Source.zeroVal (E := E) (Γ := Γ) horizon τ).run y=(.error halt,z)) :
    (Source.execS G F (horizon+1) nps none
      (.declVar τ : Source.RStmt E [] false .body Γ (τ::Γ)) y.1).run (.nil,y.2)=
        (.error halt,(.nil,z.2)) := by
  have hsub : (Source.EM.sub (Γ := []) y.1 (Source.zeroVal (E := E) (Γ := Γ) horizon τ)).run (.nil,y.2)=
      (.error halt,(.nil,z.2)) := by
    unfold Source.EM.sub
    have hz' : (Source.zeroVal (E := E) (Γ := Γ) horizon τ) (y.1,y.2)=(.error halt,z) := hz
    cases z
    simp only [ExceptT.run,ExceptT.mk,hz']
  rw [Source.execS,Source.Hoare.run_bind,hsub]

/-- An actual Source declaration adds the independently constructed reference
local; existing intrinsic/word allocation and all initial capacities stay explicit. -/
theorem source_bool_declaration_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fsrc : Source.Fr) (y : Source.EMState E Γ) (horizon : Nat)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y) (σ : State C Δ)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m)
    (ha : Evm.Memory.StructAllocatorRepr σ.heap base frame cursor m) (hb : 0<b)
    (hspace : cursor.val+1<Evm.W) (hcap : b+(Δ.length+1)≤frame) :
    let τ := Source.STy.array .memory .bool none
    let o := Evm.Memory.defaultArray (H := σ.H) .bool ⟨0,Evm.W_pos⟩
    let σ' := σ.allocPush o
    let r' := (σ.alloc o).2
    let base' := Evm.upd base σ.H.length cursor
    let m' := Evm.Memory.writeMachine (Evm.Memory.allocateMachine m cursor ⟨0,Evm.W_pos⟩)
      (Evm.cell (b+Δ.length)) (.val cursor)
    ∃ z : Source.EMState E Γ,
      (Source.zeroVal (E := E) (Γ := Γ) (horizon+2) (.array .memory .bool none)).run y=(.ok (.memRef rfl y.2.heap.next),z) ∧
      (Source.execS G Fsrc (horizon+3) Γ.length none
        (.declVar τ : Source.RStmt E [] false .body Γ (τ::Γ)) y.1).run (.nil,y.2)=
          (.ok (.normal (.cons (.memRef rfl y.2.heap.next) z.1)),(.nil,z.2)) ∧
      TRun.declMem (.array (.prim .bool)) none rfl σ=.ok ⟨σ',List.prefix_append _ _⟩ ∧
      Evm.run (Evm.Memory.declareNewCode b (.lit 0 rfl : Simple C Δ .uint)) m=.ok m' 0 ∧
      SourceBoolMemoryAt (.cons (.memRef rfl y.2.heap.next : Source.Val E.layout (.array .memory .bool none)) z.1,z.2) y.2.heap.next σ'.heap r' .dyn ∧
      Source.MemOK E SH (.cons (.memRef rfl y.2.heap.next : Source.Val E.layout (.array .memory .bool none)) z.1,z.2) ∧
      Evm.Memory.StateRepr L b frame (F.push (.mem (.array (.prim .bool))) .ok) σ' base' m' ∧
      Evm.Memory.StructAllocatorRepr σ'.heap base' frame ⟨cursor.val+1,hspace⟩ m' ∧
      m'.stack=m.stack ∧ r'.id=σ.H.length := by
  dsimp only
  obtain ⟨z,hz,hd,hc,hr,hm',ha',hs,hi⟩ := source_bool_default_word y horizon σ hm ha hb hspace hcap
  have hmk := source_bool_default_memOK (E := E) (Γ := Γ) SH horizon y hmem
  rw [hz] at hmk
  have hnew : Source.MemOK E SH (.cons (.memRef rfl y.2.heap.next : Source.Val E.layout (.array .memory .bool none)) z.1,z.2) := by
    refine ⟨⟨hmk.1.1.1,?_⟩,hmk.1.2⟩
    exact ⟨hmk.2,hmk.1.1.2⟩
  exact ⟨z,hz,source_decl_statement_run G Fsrc (horizon+2) Γ.length y z _ hz,hd,hc,hr,hnew,hm',ha',hs,hi⟩

/-- The family of Source horizons is retained: small horizons timeout, not an
admission cap or a target allocation failure. -/
theorem source_bool_declaration_timeouts {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (y : Source.EMState E Γ) :
    ∀ n, n≤2 → (Source.execS G F n Γ.length none
      (.declVar (.array .memory .bool none) : Source.RStmt E [] false .body Γ ((.array .memory .bool none)::Γ)) y.1).run (.nil,y.2)=
        (.error .timeout,(.nil,y.2)) := by
  intro n hn
  have hl := source_bool_default_lowfuel y
  match n with
  | 0 => rfl
  | 1 => exact source_decl_statement_error G F 0 Γ.length y y .timeout hl.1
  | 2 => exact source_decl_statement_error G F 1 Γ.length y y .timeout hl.2
  | n+3 => omega

/-- info: 'Solidity.Backend.MemoryOps.source_decl_statement_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_decl_statement_run
/-- info: 'Solidity.Backend.MemoryOps.source_decl_statement_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_decl_statement_error
/-- info: 'Solidity.Backend.MemoryOps.source_bool_declaration_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_bool_declaration_word
/-- info: 'Solidity.Backend.MemoryOps.source_bool_declaration_timeouts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_bool_declaration_timeouts
end Solidity.Backend.MemoryOps
