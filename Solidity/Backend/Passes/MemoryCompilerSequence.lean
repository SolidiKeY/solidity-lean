import Solidity.Backend.Passes.ReindexedMemory

/-! Structural composition of the EXISTING memory compiler. The result is
produced by Memory.compileProg itself; no alternate producer or evaluator is used. -/
namespace Solidity.Backend.Passes
open Evm Evm.Memory

theorem memory_compile_join {C : Contract} {b : Nat} {Γ Δ Ξ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ}
    (left : CompiledProg b F P) (right : CompiledProg b left.frag Q)
    (hl : Memory.compileProg b F P = some left)
    (hr : Memory.compileProg b left.frag Q = some right) :
    ∃ joined : CompiledProg b F (P.join Q),
      Memory.compileProg b F (P.join Q) = some joined ∧
      joined.frag = right.frag ∧ joined.code = left.code ++ right.code := by
  cases P with
  | nil =>
    have eq : (⟨F,[],.nil F⟩ : CompiledProg b F .nil) = left := Option.some.inj hl
    cases eq
    exact ⟨right,hr,rfl,rfl⟩
  | cons s P =>
    cases hs : Memory.compileStmt b F s with
    | none =>
      simp only [Memory.compileProg,hs,bind,Option.bind,reduceCtorEq] at hl
    | some head =>
      cases ht : Memory.compileProg b head.frag P with
      | none =>
        simp only [Memory.compileProg,hs,bind,Option.bind,ht,reduceCtorEq] at hl
      | some tail =>
        have eq : (⟨tail.frag,head.code ++ tail.code,.cons head.cert tail.cert⟩ :
            CompiledProg b F (.cons s P)) = left := by
          simpa only [Memory.compileProg,hs,ht,bind,Option.bind,pure,Option.some.injEq] using hl
        cases eq
        obtain ⟨joined,hj,hfrag,hcode⟩ := memory_compile_join (C := C) (b := b) (F := head.frag) (P := P) (Q := Q) tail right ht hr
        refine ⟨⟨joined.frag,head.code ++ joined.code,.cons head.cert joined.cert⟩,?_,hfrag,?_⟩
        · simp only [Prog.join,Memory.compileProg,hs,hj,bind,Option.bind,pure]
        · simp only [hcode,List.append_assoc]

termination_by sizeOf P
decreasing_by decreasing_tactic

end Solidity.Backend.Passes
