import Solidity.Evm.MemoryRefArrayStatements

/-! A narrow checked compiler for nonallocating reference-array programs.
The supplementary input relation owns every reference array, rather than
assuming pointer words from the primitive-only compiler relation. -/
namespace Solidity.Evm.Memory.ReferenceArrays
open Semantics
variable {C : Contract}

inductive StmtFrag (b : Nat) : {Γ Δ : Ctx} → Frag Γ → Frag Δ → Stmt C Γ Δ → List Instr → Prop where
  | rebind {Γ : Ctx} (F : Frag Γ) {R : RefTy} (dst : Idx Γ (.mem R))
      (src : MPath C Γ (.ref R)) (code : List Instr) (hs : RefPtrFrag b F src code) :
      StmtFrag b F F (.rebindMem dst (.alias src)) (code ++ [.mstore (cellOf b dst)])
  | reference {Γ : Ctx} (F : Frag Γ) {R : RefTy}
      (dst : MPath C Γ (.ref (.array (.ref R)))) (src : MPath C Γ (.ref R))
      (pointer value : List Instr) (hd : RefPtrFrag b F dst pointer) (hs : RefPtrFrag b F src value)
      (i : Val C Γ .uint) (hi : valIn F i = true) :
      StmtFrag b F F (.assignMem (.index .dyn dst i) (.ref src))
        (value ++ pointer ++ compileVal b i ++ writeArrayStackCode)
  | primitive {Γ : Ctx} (F : Frag Γ) {p : PrimTy}
      (dst : MPath C Γ (.ref (.array (.prim p)))) (pointer : List Instr)
      (hd : RefPtrFrag b F dst pointer) (v : Val C Γ p) (hv : valIn F v = true)
      (i : Val C Γ .uint) (hi : valIn F i = true) :
      StmtFrag b F F (.assignMem (.index .dyn dst i) (.val v))
        (compileVal b v ++ pointer ++ compileVal b i ++ writeArrayStackCode)

inductive ProgFrag (b : Nat) : {Γ Δ : Ctx} → Frag Γ → Frag Δ → Prog C Γ Δ → List Instr → Prop where
  | nil {Γ : Ctx} (F : Frag Γ) : ProgFrag b F F .nil []
  | cons {Γ Δ Ξ : Ctx} {F : Frag Γ} {G : Frag Δ} {K : Frag Ξ}
      {s : Stmt C Γ Δ} {P : Prog C Δ Ξ} {head tail : List Instr}
      (hs : StmtFrag b F G s head) (hp : ProgFrag b G K P tail) :
      ProgFrag b F K (.cons s P) (head ++ tail)

structure CompiledStmt (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (s : Stmt C Γ Δ) where
  frag : Frag Δ
  code : List Instr
  cert : StmtFrag b F frag s code

structure CompiledProg (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) where
  frag : Frag Δ
  code : List Instr
  cert : ProgFrag b F frag P code

def compileStmt (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) :
    (s : Stmt C Γ Δ) → Option (CompiledStmt b F s)
  | .rebindMem dst (.alias src) => do
    let result ← compileRefPtr b F src
    pure ⟨F, _, .rebind F dst src result.code result.cert⟩
  | .assignMem (.index .dyn dst i) (.ref src) => do
    let parent ← compileRefPtr b F dst
    let value ← compileRefPtr b F src
    if hi : valIn F i = true then
      pure ⟨F, _, .reference F dst src parent.code value.code parent.cert value.cert i hi⟩
    else none
  | .assignMem (.index .dyn dst i) (.val v) => do
    let parent ← compileRefPtr b F dst
    if hv : valIn F v = true then
      if hi : valIn F i = true then
        pure ⟨F, _, .primitive F dst parent.code parent.cert v hv i hi⟩
      else none
    else none
  | _ => none

/-- This boundary follows the existing checked compiler; certificates are proof data. -/
def compileProg (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) :
    (P : Prog C Γ Δ) → Option (CompiledProg b F P)
  | .nil => some ⟨F, [], .nil F⟩
  | .cons s P => do
    let head ← compileStmt b F s
    let tail ← compileProg b head.frag P
    pure ⟨tail.frag, head.code ++ tail.code, .cons head.cert tail.cert⟩

theorem StmtFrag.correct {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {s : Stmt C Γ Δ} {code : List Instr} (hs : StmtFrag b F G s code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : RefArrayStateRepr L b frame F σ base m) :
    RefArrayResultRepr L b frame G σ base m (s.run σ) (run code m) := by
  cases hs with
  | rebind F dst src code hs => exact hs.rebind h dst
  | reference F dst src pointer value hd hs i hi => exact hd.writeReference h hs i hi
  | primitive F dst pointer hd v hv i hi => exact hd.writePrimitive h v hv i hi

private theorem run_cons_revert {Γ Δ Ξ : Ctx} {σ : State C Γ}
    {s : Stmt C Γ Δ} {P : Prog C Δ Ξ} (h : s.run σ = .error .revert) :
    (Prog.cons s P).run σ = .error .revert := by
  show TRun.seq s.runR P.runR σ = _
  simp only [TRun.seq, Solidity.Stmt.run] at h ⊢
  rw [h]

theorem ProgFrag.correct {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {P : Prog C Γ Δ} {code : List Instr} (hp : ProgFrag b F G P code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : RefArrayStateRepr L b frame F σ base m) :
    RefArrayResultRepr L b frame G σ base m (P.run σ) (run code m) := by
  induction hp generalizing m with
  | nil F => exact .inl ⟨⟨σ, List.prefix_refl _⟩, m, rfl, rfl, h, rfl⟩
  | cons hs hp ih =>
    rcases hs.correct h with ⟨o, m₁, ho, hc, hm, hst⟩ | ⟨ho, hc⟩
    · rw [Solidity.Prog.run_cons_ok ho, run_append_ok hc]
      rcases ih hm with ⟨o', m₂, ho', hc', hm', hst'⟩ | ⟨ho', hc'⟩
      · exact .inl ⟨⟨o'.st, o.ext.trans o'.ext⟩, m₂, by rw [ho']; rfl,
          hc', hm', hst'.trans hst⟩
      · exact .inr ⟨by rw [ho']; rfl, hc'⟩
    · exact .inr ⟨run_cons_revert ho, run_append_revert hc⟩

theorem ProgFrag.pushes_zero {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {P : Prog C Γ Δ} {code : List Instr} (hp : ProgFrag b F G P code) :
    Evm.Prog.pushes P = 0 := by
  induction hp with
  | nil => rfl
  | cons hs hp ih =>
    cases hs <;> change 0 + Evm.Prog.pushes _ = 0 <;> simpa only [Nat.zero_add] using ih

end Solidity.Evm.Memory.ReferenceArrays
