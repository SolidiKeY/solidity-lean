import Solidity.Evm.MemoryFixedMixedCopy
import Solidity.Evm.MemoryCompile
import Solidity.Evm.MemoryCopyBound

/-!
# A typed, memory-preserving fixed-copy compiler fragment

The fixed payload refinement is preserved explicitly. This route deliberately
admits no heap mutation or allocation: their interval-ownership proofs must not
be inferred from the weaker legacy heap relation. It composes finite copies,
guards, branches and scopes directly over the intrinsic source syntax.
-/
namespace Solidity.Evm.Memory
variable {C : Contract}

theorem FixedStateRepr.push {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : FixedStateRepr L b frame F σ base m) (w : Word) :
    FixedStateRepr L b frame F σ base (m.push w) :=
  ⟨h.legacy.push w, h.fixed.mem_eq rfl⟩

theorem FixedStateRepr.drop {L b frame : Nat} {Γ Δ : Ctx} {F : Frag Δ}
    {σ : State C Δ} {base : Nat → Fin W} {m : Machine}
    (h : FixedStateRepr L b frame F σ base m) (e : Ext Γ Δ) :
    FixedStateRepr L b frame (F.restrict Γ) (σ.drop e) base m :=
  ⟨h.legacy.drop e, h.fixed⟩

theorem FixedStateRepr.meet {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : FixedStateRepr L b frame F σ base m) (G : Frag Γ) :
    FixedStateRepr L b frame (F.meet G) σ base m := ⟨h.legacy.meet G, h.fixed⟩

theorem FixedStateRepr.meetRight {L b frame : Nat} {Γ : Ctx} {G : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : FixedStateRepr L b frame G σ base m) (F : Frag Γ) :
    FixedStateRepr L b frame (F.meet G) σ base m := Frag.meet_comm G F ▸ h.meet F

namespace Fixed

private theorem assign_copyMem_eq {Γ : Ctx} {R : RefTy}
    (dst : Loc C Γ (.ref R)) (src : MPath C Γ (.ref R)) (σ : State C Γ) :
    TRun.assign dst (.copyMem src) σ = TRun.assignFromMem dst src σ := by
  simp only [TRun.assign, Src.valueT, TRun.assignFromMem]
  cases src.mvalT σ <;> rfl

private theorem require_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : FixedStateRepr L b frame F σ base m) (c : Val C Γ .bool) (code : List Instr)
    (hc : ValOutT .bool (c.evalT σ) (run code m) m) :
    FixedResult L b frame F σ base m (TRun.require c σ) (run (code ++ assertTop) m) := by
  rcases hc with ⟨vc, wc, hvc, hrc, hrunc⟩ | ⟨hvc, hrunc⟩
  · obtain rfl := hrc.bool_inv
    cases vc
    · exact .inr ⟨by simp only [TRun.require, hvc, bind, Except.bind,
        Solidity.boolT, Bool.false_eq_true, ↓reduceIte], by rw [run_append_skip hrunc]; rfl⟩
    · exact .inl ⟨⟨σ, List.prefix_refl _⟩, m,
        by simp only [TRun.require, hvc, bind, Except.bind, Solidity.boolT, ↓reduceIte, pure, Except.pure],
        by rw [run_append_skip hrunc]; rfl, h, rfl, rfl, rfl, HEq.rfl⟩
  · exact .inr ⟨by simp only [TRun.require, hvc, bind, Except.bind], run_append_revert hrunc⟩

mutual
inductive StmtFrag (b : Nat) : {Γ Δ : Ctx} → Frag Γ → Frag Δ → Stmt C Γ Δ → List Instr → Prop where
  | copy {Γ : Ctx} (F : Frag Γ) {p : PrimTy} {n : Nat}
      (dst : Loc C Γ (.ref (.fixed (.prim p) n))) (src : MPath C Γ (.ref (.fixed (.prim p) n)))
      (pointer : List Instr) (hp : PtrFrag b src pointer) (hl : locIn F false dst = true)
      (hn : n < W) : StmtFrag b F F (.assignFromMem dst src) (assignMemoryFixedCode b dst pointer)
  | copyMem {Γ : Ctx} (F : Frag Γ) {p : PrimTy} {n : Nat}
      (dst : Loc C Γ (.ref (.fixed (.prim p) n))) (src : MPath C Γ (.ref (.fixed (.prim p) n)))
      (pointer : List Instr) (hp : PtrFrag b src pointer) (hl : locIn F false dst = true)
      (hn : n < W) : StmtFrag b F F (.assign dst (.copyMem src)) (assignMemoryFixedCode b dst pointer)
  | arrayCopy {Γ : Ctx} (F : Frag Γ) {p : PrimTy}
      (dst : Loc C Γ (.ref (.array (.prim p)))) (src : MPath C Γ (.ref (.array (.prim p))))
      (pointer : List Instr) (hp : PtrFrag b src pointer) (hl : locIn F false dst = true) :
      StmtFrag b F F.dropFragile (.assignFromMem dst src) (assignMemoryArrayCode b dst pointer)
  | structCopy {Γ : Ctx} (F : Frag Γ) {s : Name}
      (dst : Loc C Γ (.ref (.struct s))) (src : MPath C Γ (.ref (.struct s)))
      (pointer : List Instr) (hp : PtrFrag b src pointer) (hl : locIn F false dst = true)
      (hprim : primitiveMembers (Semantics.structDef s) = true)
      (hst : static (.ref (.struct s)) = true) (hfit : (Semantics.structDef s).length < W) :
      StmtFrag b F F (.assignFromMem dst src) (assignMemoryStructCode b dst pointer)
  | dynamic {Γ : Ctx} (F : Frag Γ) {p : PrimTy} {n : Nat}
      (dst : Loc C Γ (.ref (.array (.prim p)))) (src : MPath C Γ (.ref (.fixed (.prim p) n)))
      (pointer : List Instr) (hp : PtrFrag b src pointer) (hl : locIn F false dst = true)
      (hn : n < W) : StmtFrag b F F.dropFragile (.assign dst (.fixedCopyMem src (.dynamic hn)))
        (assignFixedDynamicCode b n dst pointer)
  | pad {Γ : Ctx} (F : Frag Γ) {p : PrimTy} {n k : Nat}
      (dst : Loc C Γ (.ref (.fixed (.prim p) k))) (src : MPath C Γ (.ref (.fixed (.prim p) n)))
      (pointer : List Instr) (hp : PtrFrag b src pointer) (hl : locIn F false dst = true)
      (hfit : n ≤ k) (hk : k < W) : StmtFrag b F F (.assign dst (.fixedCopyMem src (.fixed k hfit)))
        (assignFixedPadCode b n dst pointer)
  | require {Γ : Ctx} (F : Frag Γ) (c : Val C Γ .bool) (code : List Instr) (hc : ValFrag b F c code) :
      StmtFrag b F F (.require c) (code ++ assertTop)
  | revert {Γ : Ctx} (F : Frag Γ) : StmtFrag b F F .revert [.revert]
  | block {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ} (body : Prog C Γ Δ)
      (code : List Instr) (hp : ProgFrag b F G body code) :
      StmtFrag b F (G.restrict Γ) (.block body) code
  | ite {Γ Δ Ξ : Ctx} {F : Frag Γ} {G : Frag Δ} {K : Frag Ξ}
      (c : Val C Γ .bool) (thn : Prog C Γ Δ) (els : Prog C Γ Ξ)
      (cond left right : List Instr) (hc : ValFrag b F c cond)
      (ht : ProgFrag b F G thn left) (he : ProgFrag b F K els right) :
      StmtFrag b F ((G.restrict Γ).meet (K.restrict Γ)) (.ite c thn els)
        (conditionalCode cond left right)

inductive ProgFrag (b : Nat) : {Γ Δ : Ctx} → Frag Γ → Frag Δ → Prog C Γ Δ → List Instr → Prop where
  | nil {Γ : Ctx} (F : Frag Γ) : ProgFrag b F F .nil []
  | cons {Γ Δ Ξ : Ctx} {F : Frag Γ} {G : Frag Δ} {K : Frag Ξ}
      {s : Stmt C Γ Δ} {P : Prog C Δ Ξ} {head tail : List Instr}
      (hs : StmtFrag b F G s head) (hp : ProgFrag b G K P tail) :
      ProgFrag b F K (.cons s P) (head ++ tail)
end

structure CompiledStmt (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (s : Stmt C Γ Δ) where
  frag : Frag Δ
  code : List Instr
  cert : StmtFrag b F frag s code

structure CompiledProg (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) where
  frag : Frag Δ
  code : List Instr
  cert : ProgFrag b F frag P code

theorem ProgFrag.pushes_zero {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {P : Prog C Γ Δ} {code : List Instr} (hp : ProgFrag b F G P code) :
    Evm.Prog.pushes P = 0 := by
  induction hp using ProgFrag.rec
    (motive_1 := fun _ _ s _ _ => Evm.Stmt.pushes s = 0)
  case block body code hp ih => exact ih
  case ite c thn els cond left right hc ht he iht ihe =>
    change Evm.Prog.pushes thn + Evm.Prog.pushes els = 0
    rw [iht, ihe]
  case cons hs hp ihs ihp =>
    change Evm.Stmt.pushes _ + Evm.Prog.pushes _ = 0
    rw [ihs, ihp]
  all_goals rfl

private def StmtSound (L b frame : Nat) {Γ Δ : Ctx} (F : Frag Γ) (G : Frag Δ)
    (s : Stmt C Γ Δ) (code : List Instr) : Prop :=
  ∀ {σ : State C Γ} {base : Nat → Fin W} {m : Machine}, FixedStateRepr L b frame F σ base m →
    copyBoundStmt s σ ≤ L → FixedResult L b frame G σ base m (s.run σ) (run code m)
private def ProgSound (L b frame : Nat) {Γ Δ : Ctx} (F : Frag Γ) (G : Frag Δ)
    (P : Prog C Γ Δ) (code : List Instr) : Prop :=
  ∀ {σ : State C Γ} {base : Nat → Fin W} {m : Machine}, FixedStateRepr L b frame F σ base m →
    copyBoundProg P σ ≤ L → FixedResult L b frame G σ base m (P.run σ) (run code m)

private theorem run_cons_revert {Γ Δ Ξ : Ctx} {σ : State C Γ}
    {s : Stmt C Γ Δ} {P : Prog C Δ Ξ} (h : s.run σ = .error .revert) :
    (Prog.cons s P).run σ = .error .revert := by
  show TRun.seq s.runR P.runR σ = _
  simp only [TRun.seq, Solidity.Stmt.run] at h ⊢
  rw [h]

private theorem cons_sound {L b frame : Nat} {Γ Δ Ξ : Ctx} {F : Frag Γ} {G : Frag Δ} {K : Frag Ξ}
    {s : Stmt C Γ Δ} {P : Prog C Δ Ξ} {head tail : List Instr}
    (ihs : StmtSound L b frame F G s head) (ihp : ProgSound L b frame G K P tail) :
    ProgSound L b frame F K (.cons s P) (head ++ tail) := by
  intro σ base m h hb
  rw [copyBoundProg_cons] at hb
  rcases ihs h (Nat.le_trans (Nat.le_max_left _ _) hb) with
    ⟨o, m₁, ho, hc, hm, hst, hmem, hH, hheap⟩ | ⟨ho, hc⟩
  · rw [Solidity.Prog.run_cons_ok ho, run_append_ok hc]
    have hbt : copyBoundProg P o.st ≤ L := by
      rw [ho] at hb
      exact Nat.le_trans (Nat.le_max_right _ _) hb
    rcases ihp hm hbt with ⟨o', m₂, ho', hc', hm', hst', hmem', hH', hheap'⟩ | ⟨ho', hc'⟩
    · exact .inl ⟨⟨o'.st, o.ext.trans o'.ext⟩, m₂,
        by rw [ho']; rfl, hc', hm', hst'.trans hst, hmem'.trans hmem,
        hH'.trans hH, HEq.trans hheap' hheap⟩
    · exact .inr ⟨by rw [ho']; rfl, hc'⟩
  · exact .inr ⟨run_cons_revert ho, run_append_revert hc⟩

private theorem block_sound {L b frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {body : Prog C Γ Δ} {code : List Instr} (ih : ProgSound L b frame F G body code) :
    StmtSound L b frame F (G.restrict Γ) (.block body) code := by
  intro σ base m h hb
  rw [copyBoundStmt_block] at hb
  rcases ih h hb with ⟨o, m', ho, hc, hm, hst, hmem, hH, hheap⟩ | ⟨ho, hc⟩
  · refine .inl ⟨⟨o.st.drop body.ext, o.ext⟩, m', ?_, hc,
      hm.drop body.ext, hst, hmem, hH, hheap⟩
    change (body.run σ).map (fun o => (⟨o.st.drop body.ext, o.ext⟩ : Solidity.Out C σ.H Γ)) = _
    rw [ho]; rfl
  · refine .inr ⟨?_, hc⟩
    change (body.run σ).map (fun o => (⟨o.st.drop body.ext, o.ext⟩ : Solidity.Out C σ.H Γ)) = _
    rw [ho]; rfl

private theorem ite_sound {L b frame : Nat} {Γ Δ Ξ : Ctx}
    {F : Frag Γ} {G : Frag Δ} {K : Frag Ξ} {c : Val C Γ .bool}
    {thn : Prog C Γ Δ} {els : Prog C Γ Ξ} {cond left right : List Instr}
    (hc : ValFrag b F c cond) (iht : ProgSound L b frame F G thn left)
    (ihe : ProgSound L b frame F K els right) :
    StmtSound L b frame F ((G.restrict Γ).meet (K.restrict Γ)) (.ite c thn els)
      (conditionalCode cond left right) := by
  intro σ base m h hb
  change FixedResult _ _ _ _ _ _ _ (TRun.ite c thn.ext thn.runR els.ext els.runR σ) _
  simp only [TRun.ite, conditionalCode, List.append_assoc]
  rcases hc.correct h.legacy with ⟨vc, wc, hvc, hrc, hrunc⟩ | ⟨hvc, hrunc⟩
  · obtain rfl := hrc.bool_inv
    rw [run_append_ok hrunc, hvc]
    simp only [bind, Except.bind, Solidity.boolT]
    cases vc
    · rw [run_append_skip (m' := m) (k := left.length + 1) rfl,
        show left.length + 1 = left.length + 1 from rfl, exec_append, exec_skip]
      simp only [Out.ok_bind, Bool.false_eq_true, ↓reduceIte]
      have hbb : copyBoundStmt (.block els) σ ≤ L := by
        rw [copyBoundStmt_block]
        rw [copyBoundStmt_ite, hvc] at hb
        exact hb
      rcases block_sound ihe h hbb with ⟨o, m', ho, ht, hm, hs, hmem, hH, hheap⟩ | ⟨ho, ht⟩
      · exact .inl ⟨o, m', ho, ht, hm.meetRight _, hs, hmem, hH, hheap⟩
      · exact .inr ⟨ho, ht⟩
    · rw [run_append_skip (m' := m) (k := 0) rfl]
      simp only [↓reduceIte]
      have hbb : copyBoundStmt (.block thn) σ ≤ L := by
        rw [copyBoundStmt_block]
        rw [copyBoundStmt_ite, hvc] at hb
        exact hb
      rcases block_sound iht h hbb with ⟨o, m', ho, ht, hm, hs, hmem, hH, hheap⟩ | ⟨ho, ht⟩
      · refine .inl ⟨o, m', ho, ?_, hm.meet _, hs, hmem, hH, hheap⟩
        change run _ m = _
        rw [run_append_ok ht]
        exact exec_length _ _
      · exact .inr ⟨ho, run_append_revert ht⟩
  · exact .inr ⟨by simp only [bind, Except.bind, hvc], run_append_revert hrunc⟩

private theorem stmt_sound {L b frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {s : Stmt C Γ Δ} {code : List Instr} (hs : StmtFrag b F G s code) :
    StmtSound L b frame F G s code := by
  induction hs using StmtFrag.rec
    (motive_2 := fun F G P code _ => ProgSound L b frame F G P code) with
  | copy F dst src pointer hp hl hn =>
    intro σ base m h hb
    exact assignMemoryFixed_correct h dst src pointer hp hl hn
  | copyMem F dst src pointer hp hl hn =>
    intro σ base m h hb
    change FixedResult _ _ _ _ _ _ _ (TRun.assign dst (.copyMem src) σ) _
    rw [assign_copyMem_eq]
    exact assignMemoryFixed_correct h dst src pointer hp hl hn
  | arrayCopy F dst src pointer hp hl =>
    intro σ base m h hb
    exact assignFixedAwareArray_correct h dst src pointer hp hl (copyBoundStmt_array dst src σ L hb)
  | structCopy F dst src pointer hp hl hprim hst hfit =>
    intro σ base m h hb
    exact assignFixedAwareStruct_correct h dst src pointer hp hl hprim hst hfit
  | dynamic F dst src pointer hp hl hn =>
    intro σ base m h hb
    exact assignFixedDynamic_correct h dst src pointer hp hl hn
      (copyBoundStmt_fixedDynamic dst src hn σ L hb)
  | pad F dst src pointer hp hl hfit hk =>
    intro σ base m h hb
    exact assignFixedPad_correct h dst src pointer hp hl hfit hk
  | require F c code hc =>
    intro σ base m h hb
    exact require_correct h c code (hc.correct h.legacy)
  | revert F =>
    intro σ base m h hb
    exact .inr ⟨rfl, rfl⟩
  | block body code hp ih => exact block_sound ih
  | ite c thn els cond left right hc ht he iht ihe => exact ite_sound hc iht ihe
  | nil F =>
    intro σ base m h hb
    exact .inl ⟨⟨σ, List.prefix_refl _⟩, m, rfl, rfl, h, rfl, rfl, rfl, HEq.rfl⟩
  | cons hs hp ihs ihp => exact cons_sound ihs ihp

/-- The read-only statement certificate exposes its actual source/machine simulation. -/
theorem StmtFrag.correct {L b frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {s : Stmt C Γ Δ} {code : List Instr} (hs : StmtFrag b F G s code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : FixedStateRepr L b frame F σ base m) (hb : copyBoundStmt s σ ≤ L) :
    FixedResult L b frame G σ base m (s.run σ) (run code m) := stmt_sound hs h hb

private theorem ProgFrag.sound {L b frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {P : Prog C Γ Δ} {code : List Instr} (hp : ProgFrag b F G P code) :
    ProgSound L b frame F G P code := by
  induction hp using ProgFrag.rec
    (motive_1 := fun F G s code _ => StmtSound L b frame F G s code) with
  | copy F dst src pointer hp hl hn => exact stmt_sound (.copy F dst src pointer hp hl hn)
  | copyMem F dst src pointer hp hl hn => exact stmt_sound (.copyMem F dst src pointer hp hl hn)
  | arrayCopy F dst src pointer hp hl => exact stmt_sound (.arrayCopy F dst src pointer hp hl)
  | structCopy F dst src pointer hp hl hprim hst hfit =>
    exact stmt_sound (.structCopy F dst src pointer hp hl hprim hst hfit)
  | dynamic F dst src pointer hp hl hn => exact stmt_sound (.dynamic F dst src pointer hp hl hn)
  | pad F dst src pointer hp hl hfit hk => exact stmt_sound (.pad F dst src pointer hp hl hfit hk)
  | require F c code hc => exact stmt_sound (.require F c code hc)
  | revert F => exact stmt_sound (.revert F)
  | block body code hp ih => exact block_sound ih
  | ite c thn els cond left right hc ht he iht ihe => exact ite_sound hc iht ihe
  | nil F =>
    intro σ base m h hb
    exact .inl ⟨⟨σ, List.prefix_refl _⟩, m, rfl, rfl, h, rfl, rfl, rfl, HEq.rfl⟩
  | cons hs hp ihs ihp => exact cons_sound ihs ihp

/-- The program certificate exposes its actual source/machine simulation. -/
theorem ProgFrag.correct {L b frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {P : Prog C Γ Δ} {code : List Instr} (hp : ProgFrag b F G P code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : FixedStateRepr L b frame F σ base m) (hb : copyBoundProg P σ ≤ L) :
    FixedResult L b frame G σ base m (P.run σ) (run code m) := ProgFrag.sound hp h hb

private def compileCopy (b : Nat) {Γ : Ctx} (F : Frag Γ) :
    {R : RefTy} → (dst : Loc C Γ (.ref R)) → (src : MPath C Γ (.ref R)) →
      Option (CompiledStmt b F (.assignFromMem dst src))
  | .array (.prim _), dst, src => do
    let pointer ← compilePtr b src
    if hl : locIn F false dst = true then
      pure ⟨F.dropFragile, _, .arrayCopy F dst src pointer.code pointer.cert hl⟩
    else none
  | .struct s, dst, src => do
    if hl : locIn F false dst = true then
      if hprim : primitiveMembers (Semantics.structDef s) = true then
        if hst : static (.ref (.struct s)) = true then
          if hfit : (Semantics.structDef s).length < W then
            let pointer ← compilePtr b src
            pure ⟨F, _, .structCopy F dst src pointer.code pointer.cert hl hprim hst hfit⟩
          else none
        else none
      else none
    else none
  | .fixed (.prim _) n, dst, src =>
    if hn : n < W then do
      let pointer ← compilePtr b src
      if hl : locIn F false dst = true then
        pure ⟨F, _, .copy F dst src pointer.code pointer.cert hl hn⟩
      else none
    else none
  | _, _, _ => none

private def compileCopyMem (b : Nat) {Γ : Ctx} (F : Frag Γ) :
    {R : RefTy} → (dst : Loc C Γ (.ref R)) → (src : MPath C Γ (.ref R)) →
      Option (CompiledStmt b F (.assign dst (.copyMem src)))
  | .fixed (.prim _) n, dst, src =>
    if hn : n < W then do
      let pointer ← compilePtr b src
      if hl : locIn F false dst = true then
        pure ⟨F, _, .copyMem F dst src pointer.code pointer.cert hl hn⟩
      else none
    else none
  | _, _, _ => none

private def compileShape (b : Nat) {Γ : Ctx} (F : Frag Γ) :
    {E : Ty} → {n : Nat} → {R : RefTy} → (dst : Loc C Γ (.ref R)) →
    (src : MPath C Γ (.ref (.fixed E n))) → (shape : FixedCopy E n R) →
    Option (CompiledStmt b F (.assign dst (.fixedCopyMem src shape)))
  | .prim _, _, _, dst, src, shape =>
    FixedCopy.casesOn (motive := fun R shape => (dst : Loc C Γ (.ref R)) →
      Option (CompiledStmt b F (.assign dst (.fixedCopyMem src shape)))) shape
      (dynamic := fun hn dst => do
        let pointer ← compilePtr b src
        if hl : locIn F false dst = true then
          pure ⟨F.dropFragile, _, .dynamic F dst src pointer.code pointer.cert hl hn⟩
        else none)
      (fixed := fun k hfit dst =>
        if hk : k < W then do
          let pointer ← compilePtr b src
          if hl : locIn F false dst = true then
            pure ⟨F, _, .pad F dst src pointer.code pointer.cert hl hfit hk⟩
          else none
        else none) dst
  | .ref _, _, _, _, _, _ => none

private def compileAssign (b : Nat) {Γ : Ctx} (F : Frag Γ) {T : Ty}
    (dst : Loc C Γ T) (rhs : Src C Γ T) : Option (CompiledStmt b F (.assign dst rhs)) :=
  Src.casesOn (motive := fun T rhs =>
    (dst : Loc C Γ T) → Option (CompiledStmt b F (.assign dst rhs))) rhs
    (val := fun _ _ => none)
    (copy := fun _ _ _ => none)
    (fixedCopy := fun _ _ _ _ => none)
    (copyMem := fun src dst => compileCopyMem b F dst src)
    (fixedCopyMem := fun src shape dst => compileShape b F dst src shape) dst

variable (b : Nat)
mutual
/-- Generalized recursors retain every intrinsic context index at acceptance. -/
def compileStmt : {Γ Δ : Ctx} → (F : Frag Γ) → (s : Stmt C Γ Δ) → Option (CompiledStmt b F s)
  | _, _, F, s => Stmt.casesOn (motive_1 := fun Γ _ s =>
      (F : Frag Γ) → Option (CompiledStmt b F s)) s
    (assign := fun dst rhs F => compileAssign b F dst rhs)
    (rebind := fun _ _ _ => none)
    (assignLocal := fun _ _ _ => none)
    (declLocal := fun _ _ _ _ => none)
    (declStorage := fun _ _ _ _ => none)
    (opAssign := fun _ _ _ _ _ _ => none)
    (incDec := fun _ _ _ _ => none)
    (assignIncDec := fun _ _ _ _ _ _ => none)
    (assignLocalPush := fun _ _ _ => none)
    (pushOpAssign := fun _ _ _ _ _ _ => none)
    (pushIncDec := fun _ _ _ _ => none)
    (push := fun _ _ _ _ => none)
    (pop := fun _ _ => none)
    (transfer := fun _ _ _ => none)
    (send := fun _ _ _ _ _ => none)
    (declMem := fun _ _ _ _ _ _ => none)
    (rebindMem := fun _ _ _ => none)
    (assignFromMem := fun dst src F => compileCopy b F dst src)
    (assignMem := fun _ _ _ => none)
    (delete := fun _ _ => none)
    (deleteMem := fun _ _ _ => none)
    (assignNew := fun _ _ _ _ => none)
    (ite := fun c thn els F => do
      let cond ← Solidity.Evm.Memory.compileVal b F c
      let left ← compileProg F thn
      let right ← compileProg F els
      pure ⟨(left.frag.restrict _).meet (right.frag.restrict _), _,
        .ite c thn els cond.code left.code right.code cond.cert left.cert right.cert⟩)
    (require := fun c F => do
      let value ← Solidity.Evm.Memory.compileVal b F c
      pure ⟨F, _, .require F c value.code value.cert⟩)
    (assert := fun _ _ => none)
    (revert := fun F => some ⟨F, _, .revert F⟩)
    (assumeFalse := fun  _ => none)
    (call := fun _ _ _ _ _ => none)
    (callReceiver := fun _ _ _ _ _ _ => none)
    (callReceiverPush := fun _ _ _ _ _ _ _ => none)
    (tryCall := fun _ _ _ _ _ _ _ _ _ _ _ => none)
    (loop := fun _ _ _ _ => none)
    (block := fun body F => do
      let result ← compileProg F body
      pure ⟨result.frag.restrict _, result.code, .block body result.code result.cert⟩)
    (callRec := fun _ _ _ _ _ _ => none)
    (revertData := fun _ _ => none)
    (catchData := fun _ _ _ _ _ _ _ _ _ => none) F

  termination_by structural _ _ _F s => s

def compileProg : {Γ Δ : Ctx} → (F : Frag Γ) → (P : Prog C Γ Δ) → Option (CompiledProg b F P)
  | _, _, F, P => Prog.casesOn (motive_2 := fun Γ _ P =>
      (F : Frag Γ) → Option (CompiledProg b F P)) P
      (fun F => some ⟨F, [], .nil F⟩)
      (fun s tail F => do
        let head ← compileStmt F s
        let rest ← compileProg head.frag tail
        pure ⟨rest.frag, head.code ++ rest.code, .cons head.cert rest.cert⟩) F
  termination_by structural _ _ _F P => P
end

end Fixed
end Solidity.Evm.Memory
