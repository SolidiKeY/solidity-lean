import Solidity.Backend.MemoryOps.SourceUintDefault
import Solidity.Backend.MemoryOps.SourceDeclaration

/-! Actual uint256 default declaration, including Source-cons and intrinsic-append context extension. -/
namespace Solidity.Backend.MemoryOps

/-- Changing the local context alone does not change this heap observer. This
says nothing about alignment of old local indices with new ones. -/
theorem SourceUintMemoryAt.withLocals {E : Source.Env} {Γ Δ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .uint)} (hr : SourceUintMemoryAt y address hp r a)
    (locals : Source.Locals E.layout Δ) :
    SourceUintMemoryAt (locals,y.2) address hp r a := hr

/-- Existing roots survive the actual Source allocation and intrinsic allocation
used by the empty numeric declaration, then the Source local-context extension.
Fresh Source separation follows from occupied-object freshness, not injectivity. -/
theorem SourceUintMemoryAt.declaration_frame {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .uint)} (hr : SourceUintMemoryAt y address hp r a)
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) :
    let o := Evm.Memory.defaultArray (H := H) .uint ⟨0,Evm.W_pos⟩
    let ext := List.prefix_append H [RefTy.array (.prim .uint)]
    let z := ((Source.zeroVal (E := E) (Γ := Γ) (fuel+2) (.array .memory (.int .u256) none)).run y).2
    let fresh : Source.Val E.layout (.array .memory (.int .u256) none) := .memRef rfl y.2.heap.next
    (Source.execS G F (fuel+3) Γ.length none
      (.declVar (.array .memory (.int .u256) none) : Source.RStmt E [] false .body Γ ((.array .memory (.int .u256) none)::Γ)) y.1).run (.nil,y.2)=
        (.ok (.normal (.cons fresh z.1)),(.nil,z.2)) ∧
    SourceUintMemoryAt (.cons fresh z.1,z.2) address (hp.alloc o).1 (r.wk ext) a ∧
    Heap.Keeps ext hp (hp.alloc o).1 ∧
    (hp.alloc o).2.id=H.length ∧ (r.wk ext).id=r.id ∧
    (hp.alloc o).2.id≠(r.wk ext).id ∧ y.2.heap.next≠address := by
  dsimp only
  let o := Evm.Memory.defaultArray (H := H) .uint ⟨0,Evm.W_pos⟩
  have hk : Heap.Keeps (List.prefix_append H [RefTy.array (.prim .uint)]) hp (hp.alloc o).1 := hp.keeps_alloc o
  have hr' := hr.keeps _ hk
  have ha : address≠y.2.heap.next := by
    intro heq
    have hf := y.2.heap.alloc_fresh ⟨.array .memory (.int .u256) none,sourceUintMemory []⟩
    change y.2.heap.get y.2.heap.next=none at hf
    rw [←heq,hr] at hf
    cases hf
  refine ⟨?_,?_,hk,rfl,rfl,?_,Ne.symm ha⟩
  · apply source_decl_statement_run G F (fuel+2) Γ.length y
    rw [source_uint_default_run]
  · unfold SourceUintMemoryAt
    rw [source_uint_default_run,Source.Heap.alloc_other _ _ ha]
    exact hr'
  · have hi := r.id_lt
    change H.length≠r.id
    omega

theorem source_uint_declaration_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fsrc : Source.Fr) (y : Source.EMState E Γ) (horizon : Nat)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y) (σ : State C Δ)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m)
    (ha : Evm.Memory.StructAllocatorRepr σ.heap base frame cursor m) (hb : 0<b)
    (hspace : cursor.val+1<Evm.W) (hcap : b+(Δ.length+1)≤frame) :
    let τ := Source.STy.array .memory (.int .u256) none
    let o := Evm.Memory.defaultArray (H := σ.H) .uint ⟨0,Evm.W_pos⟩
    let σ' := σ.allocPush o
    let r' := (σ.alloc o).2
    let base' := Evm.upd base σ.H.length cursor
    let m' := Evm.Memory.writeMachine (Evm.Memory.allocateMachine m cursor ⟨0,Evm.W_pos⟩)
      (Evm.cell (b+Δ.length)) (.val cursor)
    ∃ z : Source.EMState E Γ,
      (Source.zeroVal (E := E) (Γ := Γ) (horizon+2) (.array .memory (.int .u256) none)).run y=(.ok (.memRef rfl y.2.heap.next),z) ∧
      (Source.execS G Fsrc (horizon+3) Γ.length none
        (.declVar τ : Source.RStmt E [] false .body Γ (τ::Γ)) y.1).run (.nil,y.2)=
          (.ok (.normal (.cons (.memRef rfl y.2.heap.next) z.1)),(.nil,z.2)) ∧
      TRun.declMem (.array (.prim .uint)) none rfl σ=.ok ⟨σ',List.prefix_append _ _⟩ ∧
      Evm.run (Evm.Memory.declareNewCode b (.lit 0 rfl : Simple C Δ .uint)) m=.ok m' 0 ∧
      SourceUintMemoryAt (.cons (.memRef rfl y.2.heap.next : Source.Val E.layout (.array .memory (.int .u256) none)) z.1,z.2) y.2.heap.next σ'.heap r' .dyn ∧
      Source.MemOK E SH (.cons (.memRef rfl y.2.heap.next : Source.Val E.layout (.array .memory (.int .u256) none)) z.1,z.2) ∧
      Evm.Memory.StateRepr L b frame (F.push (.mem (.array (.prim .uint))) .ok) σ' base' m' ∧
      Evm.Memory.StructAllocatorRepr σ'.heap base' frame ⟨cursor.val+1,hspace⟩ m' ∧
      m'.stack=m.stack ∧ r'.id=σ.H.length := by
  dsimp only
  obtain ⟨z,hz,hd,hc,hr,hm',ha',hs,hi⟩ := source_uint_default_word y horizon σ hm ha hb hspace hcap
  have hmk := source_uint_default_memOK (E := E) (Γ := Γ) SH horizon y hmem
  rw [hz] at hmk
  have hnew : Source.MemOK E SH (.cons (.memRef rfl y.2.heap.next : Source.Val E.layout (.array .memory (.int .u256) none)) z.1,z.2) := by
    refine ⟨⟨hmk.1.1.1,?_⟩,hmk.1.2⟩
    exact ⟨hmk.2,hmk.1.1.2⟩
  exact ⟨z,hz,source_decl_statement_run G Fsrc (horizon+2) Γ.length y z _ hz,hd,hc,hr,hnew,hm',ha',hs,hi⟩

/-- The family of Source horizons is retained: small horizons timeout, not an
admission cap or a target allocation failure. -/
theorem source_uint_declaration_timeouts {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (y : Source.EMState E Γ) :
    ∀ n, n≤2 → (Source.execS G F n Γ.length none
      (.declVar (.array .memory (.int .u256) none) : Source.RStmt E [] false .body Γ ((.array .memory (.int .u256) none)::Γ)) y.1).run (.nil,y.2)=
        (.error .timeout,(.nil,y.2)) := by
  intro n hn
  have hl := source_uint_default_lowfuel y
  match n with
  | 0 => rfl
  | 1 => exact source_decl_statement_error G F 0 Γ.length y y .timeout hl.1
  | 2 => exact source_decl_statement_error G F 1 Γ.length y y .timeout hl.2
  | n+3 => omega

/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryAt.withLocals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintMemoryAt.withLocals
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryAt.declaration_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintMemoryAt.declaration_frame
/-- info: 'Solidity.Backend.MemoryOps.source_uint_declaration_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_declaration_word
/-- info: 'Solidity.Backend.MemoryOps.source_uint_declaration_timeouts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_declaration_timeouts
end Solidity.Backend.MemoryOps
