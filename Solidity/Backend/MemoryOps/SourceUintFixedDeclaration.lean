import Solidity.Backend.MemoryOps.SourceUintFixedDefault
import Solidity.Evm.MemoryReferenceDefaultSource

/-! Positive fixed uint Source declaration and the EXISTING typed declaration/
headerless word builder. Constructor producers and their semantics remain read-only. -/
namespace Solidity.Backend.MemoryOps

/-- Arbitrary populated fixed uint objects can be existing Source inputs. -/
theorem source_uint_fixed_alloc_memOK {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    (SH : Source.HeapTy) (o : MObj H (.fixed (.prim .uint) n)) :
    Source.Hoare (Source.MemOK E SH)
      (Source.allocRef (E := E) (Γ := Γ) (sourceUintFixedObject o))
      (fun v y => Source.MemOK E SH y ∧ v.RefOK E y.2.heap.ty) (fun _ y => Source.MemOK E SH y) := by
  apply Source.Hoare.conseq (Source.allocRef_mem' (E := E) (Γ := Γ) (H := SH) (sourceUintFixedObject o) (by trivial)
    (by change ∀ j : Fin n, ∃ v, Source.Data.val (sourceUint (o.1[j.val]'(by rw [o.2];exact j.isLt)))=Source.Data.val v
        intro j;exact ⟨_,rfl⟩))
  · intro y hy
    exact ⟨hy,.array (fun _ => .val trivial)⟩
  · intro v y h;exact h
  · intro h y hy;exact hy

/-- Full context-changing fixed declaration applied to INITIAL source memory and
object-word ownership premises. Actual Source and intrinsic contexts are extended
separately. The same g indexes the word state and fixed Source observer. -/
theorem source_uint_fixed_declaration_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fsrc : Source.Fr) (y : Source.EMState E Γ)
    (σ : State C Δ) (n : Nat) (hn : 0<n) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m)
    (ha : Evm.Memory.Objects.AllocatorRepr σ.heap base frame cursor m) (hb : 0<b)
    (hs : cursor.val+max 1 n<Evm.W) (hcap : b+(Δ.length+1)≤frame) :
    let SA := Source.STy.array .memory (.int .u256) (some n)
    let R := RefTy.fixed (.prim .uint) n
    let g := σ.heap.allocDefault R rfl
    let σ' := (σ.adopt g).1.push (t := .mem R) (some g.val)
    let z : Source.EMState E (SA::Γ) :=
      (.cons (.memRef rfl y.2.heap.next) y.1,{y.2 with heap := (y.2.heap.alloc ⟨SA,sourceUintFixedZero n⟩).1})
    ∃ base' target,
      (Source.execS G Fsrc (n+4) Γ.length none (.declVar SA : Source.RStmt E [] false .body Γ (SA::Γ)) y.1).run (.nil,y.2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
      TRun.declMem R none rfl σ=.ok ⟨σ',g.ext⟩ ∧
      Evm.run (Evm.Memory.Objects.defaultDeclareCode (Γ := Δ)
        (Evm.Memory.Objects.DefaultBuilder.fixedPrimitive .uint n).code b) m=.ok target 0 ∧
      SourceUintFixedAt z y.2.heap.next g.heap g.val ∧ Source.MemOK E SH z ∧
      Evm.Memory.Objects.StateRepr L b frame (F.push (.mem R) .ok) σ' base' target ∧
      Evm.Memory.Objects.AllocatorRepr g.heap base' frame ⟨cursor.val+max 1 n,hs⟩ target ∧
      Evm.Memory.BaseExtends σ.H base base' ∧ target.stack=m.stack ∧
      g.val.id=σ.H.length ∧
      (∀ {Q : RefTy} (q : HRef σ.H Q),g.val.id≠(q.wk g.ext).id) ∧
      (∀ address,y.2.heap.get address≠none → y.2.heap.next≠address ∧ z.2.heap.get address=y.2.heap.get address) := by
  dsimp only
  obtain ⟨base',target,hd,hc,hm',ha',hb',hstack⟩ := Evm.Memory.Objects.defaultDeclare_correct hm ha hb
    (.fixed (.prim .uint) n) rfl (Evm.Memory.Objects.DefaultBuilder.fixedPrimitive .uint n) hs hcap
  have hsrc := source_uint_fixed_declaration G Fsrc y σ.heap n hn SH hmem
  have hframe := source_uint_fixed_old_frame y σ.heap n hn
  rw [source_uint_fixed_zeroVal] at hframe
  exact ⟨base',target,hsrc.1,hd,hc,hsrc.2.1,hsrc.2.2,hm',ha',hb',hstack,
    (source_uint_fixed_intrinsic y σ.heap n hn).2.2.2,hframe.2.1,hframe.2.2⟩

/-- All smaller constructor horizons genuinely timeout before allocating a
fixed root. This does not increase or restrict the evaluator's public fuel. -/
theorem source_uint_fixed_declaration_timeout {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (y : Source.EMState E Γ)
    (n fuel : Nat) (hf : fuel≤n+3) :
    (Source.execS G F fuel Γ.length none
      (.declVar (.array .memory (.int .u256) (some n)) : Source.RStmt E [] false .body Γ ((.array .memory (.int .u256) (some n))::Γ)) y.1).run (.nil,y.2)=
        (.error .timeout,(.nil,y.2)) := by
  cases fuel with
  | zero => rfl
  | succ k =>
    exact source_decl_statement_error G F k Γ.length y y .timeout
      (source_uint_fixed_zeroVal_timeout y k n (by omega))

/-- info: 'Solidity.Backend.MemoryOps.source_uint_fixed_alloc_memOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_fixed_alloc_memOK
/-- info: 'Solidity.Backend.MemoryOps.source_uint_fixed_declaration_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_fixed_declaration_word
/-- info: 'Solidity.Backend.MemoryOps.source_uint_fixed_declaration_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_fixed_declaration_timeout
end Solidity.Backend.MemoryOps
