import Solidity.Evm.MemoryObjectStatements
import Solidity.Evm.MemoryCompile

/-! A narrow public certificate compiler for populated typed array objects. -/
namespace Solidity.Evm.Memory.Objects
open Semantics
variable {C : Contract}

inductive StmtFrag (b : Nat) : {Γ Δ : Ctx} → Frag Γ → Frag Δ → Stmt C Γ Δ → List Instr → Prop where
  | rebind {Γ : Ctx} (F : Frag Γ) {R : RefTy} (dst : Idx Γ (.mem R))
      (src : MPath C Γ (.ref R)) (code : List Instr) (hs : PtrFrag b F src code) :
      StmtFrag b F F (.rebindMem dst (.alias src)) (code ++ [.mstore (cellOf b dst)])
  | alias {Γ : Ctx} (F : Frag Γ) {R : RefTy} (x : Var)
      (src : MPath C Γ (.ref R)) (code : List Instr) (hs : PtrFrag b F src code) (hm) :
      StmtFrag b F (F.push (.mem R) .ok) (.declMem R x (some (.alias src)) rfl hm)
        (code ++ [.mstore (cell (b + Γ.length))])
  | write {Γ : Ctx} (F : Frag Γ) {A : RefTy} {E : Ty} (a : ArrTy A E)
      (dst : MPath C Γ (.ref A)) (v : MSrc C Γ E) (pointer value : List Instr)
      (hd : PtrFrag b F dst pointer) (hv : SrcFrag b F v value)
      (i : Val C Γ .uint) (hi : valIn F i = true) :
      StmtFrag b F F (.assignMem (.index a dst i) v)
        (value ++ pointer ++ Evm.compileVal b i ++ writeCode a)
  | fieldWrite {Γ : Ctx} (F : Frag Γ) {s f : Name} {p : PrimTy}
      (dst : MPath C Γ (.ref (.struct s))) (v : Val C Γ p)
      (pointer value : List Instr) (hd : PtrFrag b F dst pointer) (hv : ValFrag b F v value)
      (hf : C.fieldType s f = some (.prim p)) :
      StmtFrag b F F (.assignMem (.field dst f hf) (.val v))
        (value ++ pointer ++ writeFieldCode (fieldOffset (structDef s) f))
  | assign {Γ : Ctx} (F : Frag Γ) {p : PrimTy} (dst : Idx Γ (.val p))
      (v : Val C Γ p) (code : List Instr) (hv : ValFrag b F v code) :
      StmtFrag b F F (.assignLocal dst v) (code ++ [.mstore (cellOf b dst)])
  | declare {Γ : Ctx} (F : Frag Γ) {p : PrimTy} (x : Var)
      (v : Val C Γ p) (code : List Instr) (hv : ValFrag b F v code) :
      StmtFrag b F (F.push (.val p) .ok) (.declLocal p x (some v))
        (code ++ [.mstore (cell (b + Γ.length))])

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
    let r ← compilePtr b F src
    pure ⟨F, _, .rebind F dst src r.code r.cert⟩
  | .declMem R x (some (.alias src)) rfl hm => do
    let r ← compilePtr b F src
    pure ⟨_, _, .alias F x src r.code r.cert hm⟩
  | .assignMem (.index a dst i) v => do
    let p ← compilePtr b F dst
    let r ← compileSrc b F v
    if hi : valIn F i = true then pure ⟨F, _, .write F a dst v p.code r.code p.cert r.cert i hi⟩
    else none
  | .assignMem (.field dst _ hf) (.val v) => do
    let p ← compilePtr b F dst
    let r ← compileVal b F v
    pure ⟨F, _, .fieldWrite F dst v p.code r.code p.cert r.cert hf⟩
  | .assignLocal dst v => do
    let r ← compileVal b F v
    pure ⟨F, _, .assign F dst v r.code r.cert⟩
  | .declLocal _ x (some v) => do
    let r ← compileVal b F v
    pure ⟨_, _, .declare F x v r.code r.cert⟩
  | _ => none

def compileProg (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) :
    (P : Prog C Γ Δ) → Option (CompiledProg b F P)
  | .nil => some ⟨F, [], .nil F⟩
  | .cons s P => do
    let h ← compileStmt b F s
    let t ← compileProg b h.frag P
    pure ⟨t.frag, _, .cons h.cert t.cert⟩

theorem StmtFrag.correct {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {s : Stmt C Γ Δ} {code : List Instr} (hs : StmtFrag b F G s code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) (hcap : b + frameNeedStmt s ≤ frame) :
    ResultRepr L b frame G σ base m (s.run σ) (run code m) := by
  cases hs with
  | rebind F dst src code hs => exact hs.rebind h dst
  | alias F x src code hs hm => exact hs.declareAlias h hm (by
      have he := frameNeedStmt_end (Stmt.declMem _ x (some (.alias src)) rfl hm)
      exact Nat.le_trans (Nat.add_le_add_left he b) hcap)
  | write F a dst v pointer value hd hv i hi => exact hd.write h a hv i hi
  | fieldWrite F dst v pointer value hd hv hf => exact hd.writeField h hv hf
  | assign F dst v code hv => exact assignValue_correct h dst v code (hv.correct h)
  | declare F x v code hv => exact declareValue_correct h v code (hv.correct h) (by
      have he := frameNeedStmt_end (Stmt.declLocal _ x (some v))
      exact Nat.le_trans (Nat.add_le_add_left he b) hcap)

private theorem run_cons_revert {Γ Δ Ξ : Ctx} {σ : State C Γ}
    {s : Stmt C Γ Δ} {P : Prog C Δ Ξ} (h : s.run σ = .error .revert) :
    (Prog.cons s P).run σ = .error .revert := by
  show TRun.seq s.runR P.runR σ = _
  simp only [TRun.seq, Solidity.Stmt.run] at h ⊢
  rw [h]

theorem ProgFrag.correct {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {P : Prog C Γ Δ} {code : List Instr} (hp : ProgFrag b F G P code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m)
    (hcap : b + frameNeedProg P ≤ frame) :
    ResultRepr L b frame G σ base m (P.run σ) (run code m) := by
  induction hp generalizing m with
  | nil F => exact .inl ⟨⟨σ, List.prefix_refl _⟩, m, rfl, rfl, h, rfl, fun _ _ ha => ha⟩
  | cons hs hp ih =>
    rcases hs.correct h (by simpa only [frameNeedProg, frameNeedStmt] using (Nat.le_trans (Nat.add_le_add_left (Nat.le_max_left _ _) b) hcap)) with ⟨o, m₁, ho, hc, hm, hst, ha⟩ | ⟨ho, hc⟩
    · rw [Solidity.Prog.run_cons_ok ho, run_append_ok hc]
      rcases ih hm (Nat.le_trans (Nat.add_le_add_left (Nat.le_max_right _ _) b) hcap) with ⟨o', m₂, ho', hc', hm', hst', ha'⟩ | ⟨ho', hc'⟩
      · exact .inl ⟨⟨o'.st, o.ext.trans o'.ext⟩, m₂, by rw [ho']; rfl,
          hc', hm', hst'.trans hst, fun c hb hc => ha' c hb (ha c hb hc)⟩
      · exact .inr ⟨by rw [ho']; rfl, hc'⟩
    · exact .inr ⟨run_cons_revert ho, run_append_revert hc⟩

theorem ProgFrag.pushes_zero {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {P : Prog C Γ Δ} {code : List Instr} (hp : ProgFrag b F G P code) :
    Evm.Prog.pushes P = 0 := by
  induction hp with
  | nil => rfl
  | cons hs hp ih =>
    cases hs <;> change 0 + Evm.Prog.pushes _ = 0 <;> simpa only [Nat.zero_add] using ih

end Solidity.Evm.Memory.Objects
