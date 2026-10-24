import Solidity.Evm.Expr
import Solidity.Semantics.NoPanic

/-!
# Statements over the typed run

One lemma per statement of the fragment (`docs/intrinsic.md`, M5, W1): the
statement's step (`Semantics/Run.lean`'s `TRun.*`) and its code
(`Evm/Compile.lean`) agree, as `StmtOut` says.  A storage write is the
typed save, which `Evm/Repr.lean`'s `save_repr` relates to the machine's
writes.  `stmt_sim`
(`Evm/Correct.lean`) dispatches to them, so each elaborates on its own.

`StmtOut` is the statements' dichotomy (the machine's outcome and the
typed run's agree), with two facts kept
by every outcome that goes on (`Keeps`): the cells below the frame's base
are as they were, and, unless the statement may shrink an array
(`Stmt.shrinks`), no array's length went down.  A call needs both of its
body, whose frame sits above the caller's locals: the first keeps the
caller's locals, the second its fragile aliases in bounds.  The refused
outcome carries them too, since the interpreter goes on from a machine the
world paid (`compile_correct`'s third case).  A panic is the outcome of an
`assert` only (`Stmt.asserts`, `Semantics/NoPanic.lean`, where
`Prog.run_noPanic` says so of every typed run), so code without one never
panics (`compile_exact`).
-/

namespace Solidity.Evm

open Semantics (structDef lookupBy tyRank)
open Solidity (Ctx Idx Ext TEnv State SRef TRes HTy)

variable {C : Contract}

/-! ## What a statement keeps -/

/-- What a run from `m` to `m'` keeps: the cells below the frame's base
`b`, and, unless it may shrink an array (`sh`), every array's length or
more. -/
structure Keeps (C : Contract) (b : Nat) (sh : Bool) (m m' : Machine) : Prop where
  mem : ∀ l, l < b → m'.memAt l = m.memAt l
  len : sh = false → ∀ x, LenSlot C x → m.store x ≤ m'.store x

namespace Keeps

variable {b : Nat} {sh : Bool}

theorem refl (m : Machine) : Keeps C b sh m m := ⟨fun _ _ => rfl, fun _ _ _ => Nat.le_refl _⟩

theorem trans {sh₁ sh₂ : Bool} {m₁ m₂ m₃ : Machine} (h₁ : Keeps C b sh₁ m₁ m₂)
    (h₂ : Keeps C b sh₂ m₂ m₃) : Keeps C b (sh₁ || sh₂) m₁ m₃ :=
  ⟨fun l hl => (h₂.mem l hl).trans (h₁.mem l hl), fun h x hx => by
    simp only [Bool.or_eq_false_iff] at h
    exact Nat.le_trans (h₁.len h.1 x hx) (h₂.len h.2 x hx)⟩

theorem base {b' : Nat} {m m' : Machine} (h : Keeps C b' sh m m') (hb : b ≤ b') :
    Keeps C b sh m m' :=
  ⟨fun l hl => h.mem l (Nat.lt_of_lt_of_le hl hb), h.len⟩

/-- A cell at or above the base written. -/
theorem upd {m : Machine} {l : Nat} (hl : b ≤ l) (w : Word) :
    Keeps C b sh m { m with mem := upd m.mem (cell l) w } :=
  ⟨fun l' hl' => by rw [memAt_upd, if_neg (by omega)], fun _ _ _ => Nat.le_refl _⟩

/-- Two cells at or above the base written. -/
theorem upd₂ {m : Machine} {l₁ l₂ : Nat} (h₁ : b ≤ l₁) (h₂ : b ≤ l₂) (w₁ w₂ : Word) :
    Keeps C b sh m { m with mem := Evm.upd (Evm.upd m.mem (cell l₁) w₁) (cell l₂) w₂ } :=
  ⟨fun l hl => by
    show Evm.upd (Evm.upd m.mem (cell l₁) w₁) (cell l₂) w₂ (cell l) = m.mem (cell l)
    rw [upd_other _ _ (fun h => by have := cell_inj h; omega),
      upd_other _ _ (fun h => by have := cell_inj h; omega)],
   fun _ _ _ => Nat.le_refl _⟩

/-- A storage write that lowers no length, and a cell at or above the base. -/
theorem storeUpd {m : Machine} {l : Nat} {st' : WordStore} (hl : b ≤ l) (w : Word)
    (hlen : ∀ x, LenSlot C x → m.store x ≤ st' x) :
    Keeps C b sh m { m with store := st', mem := Evm.upd m.mem (cell l) w } :=
  ⟨fun l' hl' => by
    show Evm.upd m.mem (cell l) w (cell l') = m.mem (cell l')
    exact upd_other _ _ (fun h => by have := cell_inj h; omega), fun _ => hlen⟩

/-- A storage write that lowers no length. -/
theorem store {m : Machine} {st' : WordStore} (hlen : ∀ x, LenSlot C x → m.store x ≤ st' x) :
    Keeps C b sh m { m with store := st' } := ⟨fun _ _ => rfl, fun _ => hlen⟩

/-- A storage write that may lower a length, in a statement that may shrink. -/
theorem shrink {m : Machine} {st' : WordStore} : Keeps C b true m { m with store := st' } :=
  ⟨fun _ _ => rfl, fun h => nomatch h⟩

end Keeps

/-! ## A statement's outcome -/

/-- A statement's outcome: both succeed, the machine's stack as it was, what
it keeps kept (`Keeps`) and the states related; or both revert; or the
typed run panics (a failed `assert`, solc's `Panic(0x01)`), only in code
that `asserts`, where the machine reverts; or the machine reverts because
the world refused a payment — only code that `pays` has one — and the
typed run succeeds in a state some machine represents, the one where the
world had paid. -/
inductive StmtOut (C : Contract) (L b : Nat) {Γ' : Ctx} (F' : Frag Γ') (sh pays asserts : Bool)
    {H : HTy} (res : TRes (Solidity.Out C H Γ')) (out : Out) (m : Machine) : Prop where
  | inl (h : ∃ o m', res = .ok o ∧ out = .ok m' 0 ∧ m'.stack = m.stack ∧ Keeps C b sh m m' ∧
      Sim C L b F' o.st m')
  | inr (h : res = .error .revert ∧ out = .revert)
  | panic (ha : asserts = true) (h : res = .error .panic ∧ out = .revert)
  | refused (hp : pays = true) (h : out = .revert ∧ ∃ o m', res = .ok o ∧ Keeps C b sh m m' ∧
      Sim C L b F' o.st m')
  /-- A loop no number of turns ends: the run diverges, and the machine has
  no outcome (`loopRun`'s fault), or, in code that pays, it reverted at a
  refused payment before the loop. -/
  | diverge (h : res = .error .diverge ∧ (out = .fault ∨ (pays = true ∧ out = .revert)))

/-- `StmtOut` under a looser bound on the arrays. -/
theorem StmtOut.mono {L b : Nat} {Γ' : Ctx} {F' : Frag Γ'} {sh pays asserts : Bool} {H : HTy}
    {res : TRes (Solidity.Out C H Γ')} {out : Out} {m : Machine} {L' : Nat}
    (h : StmtOut C L b F' sh pays asserts res out m) (hL : L ≤ L') (hL' : L' ≤ Lmax) :
    StmtOut C L' b F' sh pays asserts res out m := by
  rcases h with ⟨o, m', h1, h2, h3, h4, h5⟩ | h | ⟨ha, h⟩ | ⟨hp, h1, o, m', h2, h4, h5⟩ | h
  · exact .inl ⟨o, m', h1, h2, h3, h4, h5.mono hL hL'⟩
  · exact .inr h
  · exact .panic ha h
  · exact .refused hp ⟨h1, o, m', h2, h4, h5.mono hL hL'⟩
  · exact .diverge h

/-! ## The state's locals, changed -/

section States

variable {L b : Nat} {Γ : Ctx} {F : Frag Γ} {σ : State C Γ} {m : Machine}

/-- `x = e;` on a value local. -/
theorem Sim.setLocalVal (hm : Sim C L b F σ m) {p : PrimTy}
    (i : Idx Γ (.val p)) {v : p.Denote} {w : Word} (hv : ReprV p v w) :
    Sim C L b F (σ.setLocal i v) { m with mem := upd m.mem (cellOf b i) w } :=
  (SimL.setVal hm i hv).congrLook fun j => Look.ofTEnv_set i v σ.env j

/-- `uint x = e;`. -/
theorem Sim.pushVal (hm : Sim C L b F σ m) {p : PrimTy} {v : p.Denote}
    {w : Word} (hv : ReprV p v w) :
    Sim C L b (F.push (.val p) .ok) (σ.push (t := .val p) v)
      { m with mem := upd m.mem (cell (b + Γ.length)) w } :=
  (SimL.consVal hm hv).congrLook fun j => Look.ofTEnv_cons (u := .val p) v σ.env j

/-- `p = q;` with `q` indexing no array. -/
theorem Sim.setAliasE (hm : Sim C L b F σ m) {R : RefTy}
    (i : Idx Γ (.alias R)) {r : SRef C (.ref R)} {s : Slot} (hp : PathSlot C true r s) :
    Sim C L b (F.set i .ok) (σ.setLocal i (some r))
      { m with mem := upd m.mem (cellOf b i) (.slot s) } :=
  (SimL.setAlias hm i hp).congrLook fun j => Look.ofTEnv_set i (some r) σ.env j

/-- `p = persons[i];`. -/
theorem Sim.setFragileE (hm : Sim C L b F σ m) {R : RefTy}
    (i : Idx Γ (.alias R)) {r : SRef C (.ref R)} {s : Slot} (hp : PathSlot C false r s)
    (hlive : ∃ sv, σ.storage.findLive r = some sv) :
    Sim C L b (F.set i .fragile) (σ.setLocal i (some r))
      { m with mem := upd m.mem (cellOf b i) (.slot s) } :=
  (SimL.setFragile hm i hp hlive).congrLook fun j => Look.ofTEnv_set i (some r) σ.env j

/-- `Person storage p = q;` with `q` indexing no array. -/
theorem Sim.pushAlias (hm : Sim C L b F σ m) {R : RefTy}
    {r : SRef C (.ref R)} {s : Slot} (hp : PathSlot C true r s) :
    Sim C L b (F.push (.alias R) .ok) (σ.push (t := .alias R) (some r))
      { m with mem := upd m.mem (cell (b + Γ.length)) (.slot s) } :=
  (SimL.consAlias hm hp).congrLook fun j => Look.ofTEnv_cons (u := .alias R) (some r) σ.env j

/-- `Person storage p = persons[i];`. -/
theorem Sim.pushFragile (hm : Sim C L b F σ m) {R : RefTy}
    {r : SRef C (.ref R)} {s : Slot} (hp : PathSlot C false r s)
    (hlive : ∃ sv, σ.storage.findLive r = some sv) :
    Sim C L b (F.push (.alias R) .fragile) (σ.push (t := .alias R) (some r))
      { m with mem := upd m.mem (cell (b + Γ.length)) (.slot s) } :=
  (SimL.consFragile hm hp hlive).congrLook fun j =>
    Look.ofTEnv_cons (u := .alias R) (some r) σ.env j

/-- `Person storage p;`. -/
theorem Sim.pushDead (hm : Sim C L b F σ m) (R : RefTy)
    (v : Option (SRef C (.ref R))) :
    Sim C L b (F.push (.alias R) .dead) (σ.push (t := .alias R) v) m :=
  (SimL.consDead hm R v).congrLook fun j => Look.ofTEnv_cons (u := .alias R) v σ.env j

end States

/-! ## Assignments and declarations -/

section Stmts

variable {L b : Nat} {Γ : Ctx} {F : Frag Γ} {σ : State C Γ} {m : Machine}

/-- `alice.age = 10;`: the value, the slot, the write. -/
theorem assign_sim {p : PrimTy} (l : Solidity.Loc C Γ (.prim p))
    (v : Solidity.Val C Γ p) (hm : Sim C L b F σ m)
    (hwl : locIn F false l = true) (hwv : valIn F v = true) :
    StmtOut C L b F false false false (Solidity.TRun.assign l (.val v) σ)
      (run (compileVal b v ++ compileLoc b l ++ [.sstore]) m) m := by
  simp only [List.append_assoc]
  rcases val_sim v hm hwv with ⟨vv, w, hvv, hrv, hrun⟩ | ⟨hvv, hrun⟩
  · rw [run_append_ok hrun]
    rcases loc_sim l (hm.push w) hwl with ⟨r, s, sv, hres, hsv, hps, _, hrunl⟩ | ⟨hres, hrunl⟩
    · rw [run_append_ok hrunl]
      obtain ⟨a, rfl, hnew⟩ := repr_write (L := L) hrv m.store s
      obtain ⟨st', hst', hrep⟩ := save_repr hm.store hps ⟨sv, hsv⟩ hnew
        (fun x hx => WordStore.write_other _ _ fun he => hx (he ▸ Occ.prim))
      refine .inl ⟨⟨σ.withStorage st', List.prefix_refl _⟩, { m with store := WordStore.write m.store s a },
        ?_, rfl, rfl, Keeps.store (upd_len hps a),
        hm.store' hrep (upd_len hps a)⟩
      simp only [Solidity.TRun.assign, Solidity.Src.valueT, hvv, hres, bind,
        Except.bind, pure, Except.pure, Solidity.Storage.write, Solidity.SVal.isPrim,
        Ty.isPrimitive, ↓reduceIte, hst', TRes.ofOpt]
    · exact .inr ⟨by simp only [Solidity.TRun.assign, Solidity.Src.valueT, hvv, hres,
        bind, Except.bind, pure, Except.pure], run_append_revert hrunl⟩
  · exact .inr ⟨by simp only [Solidity.TRun.assign, Solidity.Src.valueT, hvv, bind,
      Except.bind], run_append_revert hrun⟩

/-- `x = e;` on a value local. -/
theorem assignLocal_sim {p : PrimTy} (i : Idx Γ (.val p)) (r : Solidity.Val C Γ p)
    (hm : Sim C L b F σ m) (hwr : valIn F r = true) :
    StmtOut C L b F false false false (Solidity.TRun.assignLocal i r σ)
      (run (compileVal b r ++ [.mstore (cellOf b i)]) m) m := by
  rcases val_sim r hm hwr with ⟨v, w, hv, hrv, hrun⟩ | ⟨hv, hrun⟩
  · refine .inl ⟨⟨σ.setLocal i v, List.prefix_refl _⟩, { m with mem := upd m.mem (cellOf b i) w },
      by simp only [Solidity.TRun.assignLocal, hv, bind, Except.bind, pure, Except.pure], ?_,
      rfl, Keeps.upd (le_lvl b i) w, hm.setLocalVal i hrv⟩
    rw [run_append_ok hrun]; rfl
  · exact .inr ⟨by simp only [Solidity.TRun.assignLocal, hv, bind, Except.bind],
      run_append_revert hrun⟩

/-- `uint x = e;` (or `uint x;`, the default). -/
theorem declLocal_sim (p : PrimTy) (init : Option (Solidity.Val C Γ p))
    (hm : Sim C L b F σ m) (hw : init.all (valIn F) = true) :
    StmtOut C L b (F.push (.val p) .ok) false false false (Solidity.TRun.declLocal p init σ)
      (run (match init with
        | none => [.push w[0], .mstore (cell (b + Γ.length))]
        | some e => compileVal b e ++ [.mstore (cell (b + Γ.length))]) m) m := by
  cases init with
  | none =>
    exact .inl ⟨⟨σ.push (t := .val p) (PrimTy.dflt p), List.prefix_refl _⟩,
      { m with mem := upd m.mem (cell (b + Γ.length)) w[0] }, rfl, rfl, rfl,
      Keeps.upd (Nat.le_add_right b _) _,
      hm.pushVal (ReprV.dflt_zero p)⟩
  | some e =>
    simp only [Option.all_some] at hw
    rcases val_sim e hm hw with ⟨v, w, hv, hrv, hrun⟩ | ⟨hv, hrun⟩
    · refine .inl ⟨⟨σ.push (t := .val p) v, List.prefix_refl _⟩,
        { m with mem := upd m.mem (cell (b + Γ.length)) w },
        by simp only [Solidity.TRun.declLocal, hv, bind, Except.bind, pure, Except.pure], ?_,
        rfl, Keeps.upd (Nat.le_add_right b _) _, hm.pushVal hrv⟩
      rw [run_append_ok hrun]; rfl
    · exact .inr ⟨by simp only [Solidity.TRun.declLocal, hv, bind, Except.bind],
        run_append_revert hrun⟩

/-- `p = q;`: an alias rebound, plain or fragile as `q` indexes an array. -/
theorem rebind_sim {R : RefTy} (i : Idx Γ (.alias R)) (q : Solidity.SPath C Γ (.ref R))
    {F' : Frag Γ} (hm : Sim C L b F σ m)
    (hw : (bindFl F q).map (F.set i) = some F') :
    StmtOut C L b F' false false false (Solidity.TRun.rebind i (.path q) σ)
      (run (compileSPath b q ++ [.mstore (cellOf b i)]) m) m := by
  unfold bindFl at hw
  by_cases h1 : spathIn F true q = true
  · rw [if_pos h1] at hw; cases hw
    rcases spath_sim q hm h1 with ⟨r, s, sv, hres, _, hp, _, hrun⟩ | ⟨hres, hrun⟩
    · refine .inl ⟨⟨σ.setLocal i (some r), List.prefix_refl _⟩,
        { m with mem := upd m.mem (cellOf b i) (.slot s) }, ?_, ?_, rfl,
        Keeps.upd (le_lvl b i) _, hm.setAliasE i hp⟩
      · simp only [Solidity.TRun.rebind, Solidity.ARhs.evalT, hres, bind, Except.bind,
          pure, Except.pure]; rfl
      · rw [run_append_ok hrun]; rfl
    · exact .inr ⟨by simp only [Solidity.TRun.rebind, Solidity.ARhs.evalT, hres, bind,
        Except.bind], run_append_revert hrun⟩
  · rw [if_neg h1] at hw
    by_cases h2 : spathIn F false q = true
    · rw [if_pos h2] at hw; cases hw
      rcases spath_sim q hm h2 with ⟨r, s, sv, hres, hsv, hp, _, hrun⟩ | ⟨hres, hrun⟩
      · refine .inl ⟨⟨σ.setLocal i (some r), List.prefix_refl _⟩,
          { m with mem := upd m.mem (cellOf b i) (.slot s) }, ?_, ?_, rfl,
          Keeps.upd (le_lvl b i) _, hm.setFragileE i hp ⟨sv, hsv⟩⟩
        · simp only [Solidity.TRun.rebind, Solidity.ARhs.evalT, hres, bind, Except.bind,
            pure, Except.pure]; rfl
        · rw [run_append_ok hrun]; rfl
      · exact .inr ⟨by simp only [Solidity.TRun.rebind, Solidity.ARhs.evalT, hres, bind,
          Except.bind], run_append_revert hrun⟩
    · rw [if_neg h2] at hw; cases hw

/-- `Person storage p = q;`, plain or fragile as `q` indexes an array. -/
theorem declAlias_sim {R : RefTy} (q : Solidity.SPath C Γ (.ref R))
    {F' : Frag (.alias R :: Γ)} (hm : Sim C L b F σ m)
    (hw : (bindFl F q).map (F.push (.alias R)) = some F') :
    StmtOut C L b F' false false false (Solidity.TRun.declStorage R (some (.path q)) σ)
      (run (compileSPath b q ++ [.mstore (cell (b + Γ.length))]) m) m := by
  unfold bindFl at hw
  by_cases h1 : spathIn F true q = true
  · rw [if_pos h1] at hw; cases hw
    rcases spath_sim q hm h1 with ⟨r, s, sv, hres, _, hp, _, hrun⟩ | ⟨hres, hrun⟩
    · refine .inl ⟨⟨σ.push (t := .alias R) (some r), List.prefix_refl _⟩,
        { m with mem := upd m.mem (cell (b + Γ.length)) (.slot s) }, ?_, ?_, rfl,
        Keeps.upd (Nat.le_add_right b _) _, hm.pushAlias hp⟩
      · simp only [Solidity.TRun.declStorage, Solidity.ARhs.evalT, hres, bind,
          Except.bind, pure, Except.pure]; rfl
      · rw [run_append_ok hrun]; rfl
    · exact .inr ⟨by simp only [Solidity.TRun.declStorage, Solidity.ARhs.evalT, hres,
        bind, Except.bind], run_append_revert hrun⟩
  · rw [if_neg h1] at hw
    by_cases h2 : spathIn F false q = true
    · rw [if_pos h2] at hw; cases hw
      rcases spath_sim q hm h2 with ⟨r, s, sv, hres, hsv, hp, _, hrun⟩ | ⟨hres, hrun⟩
      · refine .inl ⟨⟨σ.push (t := .alias R) (some r), List.prefix_refl _⟩,
          { m with mem := upd m.mem (cell (b + Γ.length)) (.slot s) }, ?_, ?_, rfl,
          Keeps.upd (Nat.le_add_right b _) _, hm.pushFragile hp ⟨sv, hsv⟩⟩
        · simp only [Solidity.TRun.declStorage, Solidity.ARhs.evalT, hres, bind,
            Except.bind, pure, Except.pure]; rfl
        · rw [run_append_ok hrun]; rfl
      · exact .inr ⟨by simp only [Solidity.TRun.declStorage, Solidity.ARhs.evalT, hres,
          bind, Except.bind], run_append_revert hrun⟩
    · rw [if_neg h2] at hw; cases hw

/-- `require(c);` reverts on `false`; `assert(c);` panics. -/
theorem require_sim (c : Solidity.Val C Γ .bool)
    (hm : Sim C L b F σ m) (hwc : valIn F c = true) :
    StmtOut C L b F false false false (Solidity.TRun.require c σ)
      (run (compileVal b c ++ assertTop) m) m := by
  rcases val_sim c hm hwc with ⟨vc, wc, hvc, hrc, hrunc⟩ | ⟨hvc, hrunc⟩
  · obtain rfl := hrc.bool_inv
    cases vc
    · exact .inr ⟨by simp only [Solidity.TRun.require, hvc, bind, Except.bind,
        Solidity.boolT, Bool.false_eq_true, ↓reduceIte], by rw [run_append_skip hrunc]; rfl⟩
    · exact .inl ⟨⟨σ, List.prefix_refl _⟩, m, by simp only [Solidity.TRun.require, hvc, bind,
        Except.bind, Solidity.boolT, ↓reduceIte, pure, Except.pure],
        by rw [run_append_skip hrunc]; rfl, rfl, Keeps.refl m, hm⟩
  · exact .inr ⟨by simp only [Solidity.TRun.require, hvc, bind, Except.bind],
      run_append_revert hrunc⟩

theorem assert_sim (c : Solidity.Val C Γ .bool)
    (hm : Sim C L b F σ m) (hwc : valIn F c = true) :
    StmtOut C L b F false false true (Solidity.TRun.assert c σ)
      (run (compileVal b c ++ assertTop) m) m := by
  rcases val_sim c hm hwc with ⟨vc, wc, hvc, hrc, hrunc⟩ | ⟨hvc, hrunc⟩
  · obtain rfl := hrc.bool_inv
    cases vc
    · exact .panic rfl ⟨by simp only [Solidity.TRun.assert, hvc, bind, Except.bind,
        Solidity.boolT, Bool.false_eq_true, ↓reduceIte], by rw [run_append_skip hrunc]; rfl⟩
    · exact .inl ⟨⟨σ, List.prefix_refl _⟩, m, by simp only [Solidity.TRun.assert, hvc, bind,
        Except.bind, Solidity.boolT, ↓reduceIte, pure, Except.pure],
        by rw [run_append_skip hrunc]; rfl, rfl, Keeps.refl m, hm⟩
  · exact .inr ⟨by simp only [Solidity.TRun.assert, hvc, bind, Except.bind],
      run_append_revert hrunc⟩

/-! ## Compound assignments and `++` -/

/-- An `op=` on a storage target resolves the target once. -/
theorem opLocT_store {p : PrimTy} {l : Solidity.OpLoc C Γ p}
    {loc : Solidity.Loc C Γ (.prim p)} (h : opLocToLoc l = some loc) (op : BinOp)
    (v : p.Denote) :
    l.storeT σ op v = (loc.resolveT σ >>= fun r => Solidity.opStoreT σ op r v) := by
  cases l <;> simp only [opLocToLoc, reduceCtorEq, Option.some.injEq] at h <;> subst h <;> rfl

/-- `++` on a storage target resolves it once. -/
theorem opLocT_bump {p : PrimTy} {l : Solidity.OpLoc C Γ p}
    {loc : Solidity.Loc C Γ (.prim p)} (h : opLocToLoc l = some loc) (op : IncDec) :
    l.bumpT σ op = (loc.resolveT σ >>= fun r => Solidity.bumpStoreT σ op r) := by
  cases l <;> simp only [opLocToLoc, reduceCtorEq, Option.some.injEq] at h <;> subst h <;> rfl

/-- `total += e;` on a storage target: the target resolved and read once,
the right-hand side, the checked operator, the write back. -/
theorem opStore_sim {p : PrimTy} (hpn : p.isNumeric = true) {op : BinOp} (hop : op.hasCompoundAssign = true)
    {l : Solidity.OpLoc C Γ p} {loc : Solidity.Loc C Γ (.prim p)}
    (hl : opLocToLoc l = some loc) (r : Solidity.Val C Γ p)
    (hm : Sim C L b F σ m) (hwl : locIn F false loc = true)
    (hwr : valIn F r = true) :
    StmtOut C L b F false false false (Solidity.TRun.opAssign op l r σ)
      (run (compileLoc b loc ++ [.dup 1, .sload] ++ compileVal b r ++ binTail p op ++
        [.swap 1, .sstore]) m) m := by
  simp only [List.append_assoc]
  rcases loc_sim loc hm hwl with ⟨rt, s, sv, hres, hsv, hps, hr, hrunl⟩ | ⟨hres, hrunl⟩
  · obtain ⟨told, rfl, hrold⟩ := prim_read hr
    have hf := Sto.find_of_findLive hsv
    rw [run_append_ok hrunl,
      run_append_ok (m' := { m with stack := .val (m.store.cells s) :: .slot s :: m.stack })
      (by simp only [run, Machine.push, exec_cons_zero, Instr.step, Nat.sub_self, List.length_cons,
          Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero, Machine.next, Out.ok_bind,
          exec_nil])]
    rcases val_sim r (hm.stack _) hwr with ⟨vr, wr, hvr, hrv, hrunr⟩ | ⟨hvr, hrunr⟩
    · rw [run_append_ok hrunr]
      have ht := compound_simT hop hpn hrold hrv { m with stack := .slot s :: m.stack }
      rcases ht.opt_cases with ⟨vn, wn, hc, hrn, hrunt⟩ | ⟨hc, hrunt⟩
      · obtain ⟨an, rfl, hnew⟩ := repr_write (L := L) hrn m.store s
        obtain ⟨st', hst', hrep⟩ := save_repr hm.store hps ⟨_, hsv⟩ hnew
          (fun x hx => WordStore.write_other _ _ fun he => hx (he ▸ Occ.prim))
        refine .inl ⟨⟨σ.withStorage st', List.prefix_refl _⟩, { m with store := WordStore.write m.store s an },
          ?_, ?_, rfl, Keeps.store (upd_len hps an),
          hm.store' hrep (upd_len hps an)⟩
        · simp only [Solidity.TRun.opAssign, hvr, opLocT_store hl, hres,
            Solidity.opStoreT, hf, SVal.view_prim, hc, hst', bind, Except.bind, TRes.ofOpt, pure,
            Except.pure]
        · change run (binTail p op ++ _)
            { m with stack := wr :: .val (m.store.cells s) :: .slot s :: m.stack } = _
          rw [run_append_ok hrunt]; rfl
      · refine .inr ⟨?_, ?_⟩
        · simp only [Solidity.TRun.opAssign, hvr, opLocT_store hl, hres,
            Solidity.opStoreT, hf, SVal.view_prim, hc, bind, Except.bind, TRes.ofOpt]
        · change run (binTail p op ++ _)
            { m with stack := wr :: .val (m.store.cells s) :: .slot s :: m.stack } = _
          rw [run_append_revert hrunt]
    · exact .inr ⟨by simp only [Solidity.TRun.opAssign, hvr, bind, Except.bind],
        run_append_revert hrunr⟩
  · rcases val_sim r hm hwr with ⟨vr, wr, hvr, _, _⟩ | ⟨hvr, _⟩
    · exact .inr ⟨by simp only [Solidity.TRun.opAssign, hvr, opLocT_store hl, hres, bind,
        Except.bind], run_append_revert hrunl⟩
    · exact .inr ⟨by simp only [Solidity.TRun.opAssign, hvr, bind, Except.bind],
        run_append_revert hrunl⟩

/-- `x += e;` on a numeric local: its cell read, the checked operator, the
cell written. -/
theorem opLocal_sim {p : PrimTy} (hpn : p.isNumeric = true) {op : BinOp} (hop : op.hasCompoundAssign = true)
    (i : Idx Γ (.val p)) (r : Solidity.Val C Γ p)
    (hm : Sim C L b F σ m) (hwr : valIn F r = true) :
    StmtOut C L b F false false false (Solidity.TRun.opAssign op (.local i) r σ)
      (run ([.mload (cellOf b i)] ++ compileVal b r ++ binTail p op ++ [.mstore (cellOf b i)]) m)
      m := by
  have hrold := hm.vals i
  simp only [List.append_assoc]
  rw [run_append_ok (m' := m.push (m.memAt (lvl b i))) rfl]
  rcases val_sim r (hm.push _) hwr with ⟨vr, wr, hvr, hrv, hrunr⟩ | ⟨hvr, hrunr⟩
  · rw [run_append_ok hrunr]
    have ht := compound_simT hop hpn hrold hrv m
    rcases ht.opt_cases with ⟨vn, wn, hc, hrn, hrunt⟩ | ⟨hc, hrunt⟩
    · refine .inl ⟨⟨σ.setLocal i vn, List.prefix_refl _⟩,
        { m with mem := upd m.mem (cellOf b i) wn }, ?_, ?_, rfl,
        Keeps.upd (le_lvl b i) _, hm.setLocalVal i hrn⟩
      · simp only [Solidity.TRun.opAssign, hvr, Solidity.OpLoc.storeT, bind,
          Except.bind, TRes.ofOpt, pure, Except.pure]
        rw [show Look.ofTEnv σ.env i = TEnv.get i σ.env from rfl] at hc
        rw [hc]
      · change run (binTail p op ++ _) { m with stack := wr :: m.memAt (lvl b i) :: m.stack } = _
        rw [run_append_ok hrunt]; rfl
    · refine .inr ⟨?_, ?_⟩
      · simp only [Solidity.TRun.opAssign, hvr, Solidity.OpLoc.storeT, bind,
          Except.bind, TRes.ofOpt]
        rw [show Look.ofTEnv σ.env i = TEnv.get i σ.env from rfl] at hc
        rw [hc]
      · change run (binTail p op ++ _) { m with stack := wr :: m.memAt (lvl b i) :: m.stack } = _
        rw [run_append_revert hrunt]
  · exact .inr ⟨by simp only [Solidity.TRun.opAssign, hvr, bind, Except.bind],
      run_append_revert hrunr⟩

/-- `total++;` on a storage target: read once, the checked increment, the
write back. -/
theorem bumpStore_sim {p : PrimTy} (hpn : p.isNumeric = true) (op : IncDec) {l : Solidity.OpLoc C Γ p}
    {loc : Solidity.Loc C Γ (.prim p)} (hl : opLocToLoc l = some loc)
    (hm : Sim C L b F σ m) (hwl : locIn F false loc = true) :
    StmtOut C L b F false false false (Solidity.TRun.incDec op l σ)
      (run (compileLoc b loc ++ [.dup 1, .sload, .push w[1]] ++ binTail p op.binOp ++
        [.swap 1, .sstore]) m) m := by
  simp only [List.append_assoc]
  rcases loc_sim loc hm hwl with ⟨rt, s, sv, hres, hsv, hps, hr, hrunl⟩ | ⟨hres, hrunl⟩
  · obtain ⟨told, rfl, hrold⟩ := prim_read hr
    have hf := Sto.find_of_findLive hsv
    have hv := bump_simT hpn op hrold { m with stack := .slot s :: m.stack }
    rw [run_append_ok hrunl, show [Instr.dup 1, .sload, .push w[1]] ++ (binTail p op.binOp ++
        [.swap 1, .sstore]) = [Instr.dup 1, .sload] ++ (([.push w[1]] ++ binTail p op.binOp) ++
        [.swap 1, .sstore]) by simp only [List.cons_append, List.nil_append],
      run_append_ok (m' := { m with stack := .val (m.store.cells s) :: .slot s :: m.stack })
      (by simp only [run, Machine.push, exec_cons_zero, Instr.step, Nat.sub_self, List.length_cons,
          Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero, Machine.next, Out.ok_bind,
          exec_nil])]
    rcases hv.opt_cases with ⟨vn, wn, hc, hrn, hrunt⟩ | ⟨hc, hrunt⟩
    · obtain ⟨an, rfl, hnew⟩ := repr_write (L := L) hrn m.store s
      obtain ⟨st', hst', hrep⟩ := save_repr hm.store hps ⟨_, hsv⟩ hnew
        (fun x hx => WordStore.write_other _ _ fun he => hx (he ▸ Occ.prim))
      refine .inl ⟨⟨σ.withStorage st', List.prefix_refl _⟩, { m with store := WordStore.write m.store s an },
        ?_, ?_, rfl, Keeps.store (upd_len hps an),
        hm.store' hrep (upd_len hps an)⟩
      · simp only [Solidity.TRun.incDec, opLocT_bump hl, hres, Solidity.bumpStoreT, hf, SVal.view_prim,
          hc, hst', bind, Except.bind, TRes.ofOpt, pure, Except.pure]
      · rw [run_append_ok hrunt]; rfl
    · refine .inr ⟨?_, run_append_revert hrunt⟩
      simp only [Solidity.TRun.incDec, opLocT_bump hl, hres, Solidity.bumpStoreT, hf, SVal.view_prim,
        hc, bind, Except.bind, TRes.ofOpt]
  · exact .inr ⟨by simp only [Solidity.TRun.incDec, opLocT_bump hl, hres, bind, Except.bind],
      run_append_revert hrunl⟩

/-- `x++;` on a numeric local. -/
theorem bumpLocal_sim {p : PrimTy} (hpn : p.isNumeric = true) (op : IncDec) (i : Idx Γ (.val p))
    (hm : Sim C L b F σ m) :
    StmtOut C L b F false false false (Solidity.TRun.incDec op (.local i) σ)
      (run ([.mload (cellOf b i), .push w[1]] ++ binTail p op.binOp ++ [.mstore (cellOf b i)]) m)
      m := by
  have hrold := hm.vals i
  have hv := bump_simT hpn op hrold m
  rw [show [Instr.mload (cellOf b i), .push w[1]] ++ binTail p op.binOp ++
      [.mstore (cellOf b i)] = [Instr.mload (cellOf b i)] ++ (([.push w[1]] ++
      binTail p op.binOp) ++ [.mstore (cellOf b i)]) by simp only [List.cons_append,
          List.nil_append],
    run_append_ok (m' := { m with stack := m.memAt (lvl b i) :: m.stack }) rfl]
  rcases hv.opt_cases with ⟨vn, wn, hc, hrn, hrunt⟩ | ⟨hc, hrunt⟩
  · refine .inl ⟨⟨σ.setLocal i vn, List.prefix_refl _⟩,
      { m with mem := upd m.mem (cellOf b i) wn }, ?_, ?_, rfl,
      Keeps.upd (le_lvl b i) _, hm.setLocalVal i hrn⟩
    · simp only [Solidity.TRun.incDec, Solidity.OpLoc.bumpT, bind, Except.bind,
        TRes.ofOpt, pure, Except.pure]
      rw [show Look.ofTEnv σ.env i = TEnv.get i σ.env from rfl] at hc
      rw [hc]
    · rw [run_append_ok hrunt]; rfl
  · refine .inr ⟨?_, run_append_revert hrunt⟩
    simp only [Solidity.TRun.incDec, Solidity.OpLoc.bumpT, bind, Except.bind,
      TRes.ofOpt]
    rw [show Look.ofTEnv σ.env i = TEnv.get i σ.env from rfl] at hc
    rw [hc]

/-- `v = x++;` on a numeric local: `x`'s cell bumped, `v` given the old or the
new word. -/
theorem assignBumpLocal_sim {p : PrimTy} (hpn : p.isNumeric = true) (op : IncDec) (i j : Idx Γ (.val p))
    (hm : Sim C L b F σ m) :
    StmtOut C L b F false false false (Solidity.TRun.assignIncDec i op (.local j) σ)
      (run ([.mload (cellOf b j)] ++ bumpCode p op ++ [.mstore (cellOf b j), .mstore (cellOf b i)]) m)
      m := by
  have hrold := hm.vals j
  have hv := bumpCode_simT hpn op hrold m
  rw [show Look.ofTEnv σ.env j = TEnv.get j σ.env from rfl] at hv
  rw [List.append_assoc, run_append_ok (m' := { m with stack := m.memAt (lvl b j) :: m.stack }) rfl]
  rcases hv with ⟨tn, wn, htn, hrn, hrunt⟩ | ⟨h, hrunt⟩
  · have hs := (hm.setLocalVal j hrn).setLocalVal i
      (v := if op.isPre then tn else TEnv.get j σ.env)
      (w := if op.isPre then wn else m.memAt (lvl b j))
      (by cases op.isPre <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> first | exact hrn | exact hrold)
    have hk' := Keeps.upd₂ (C := C) (sh := false) (m := m) (le_lvl b j) (le_lvl b i) wn
      (if op.isPre then wn else m.memAt (lvl b j))
    refine .inl ⟨⟨(σ.setLocal j tn).setLocal i (if op.isPre then tn else TEnv.get j σ.env),
      List.prefix_refl _⟩, _, ?_, ?_, ?_, hk', hs⟩
    rotate_left 2; · rfl
    · simp only [Solidity.TRun.assignIncDec, Solidity.OpLoc.bumpT, bind, Except.bind,
        TRes.ofOpt, htn, pure, Except.pure]
    · rw [run_append_ok hrunt]; rfl
  · refine .inr ⟨?_, run_append_revert hrunt⟩
    simp only [Solidity.TRun.assignIncDec, Solidity.OpLoc.bumpT, bind, Except.bind,
      TRes.ofOpt, h]

/-- `v = total++;`: the target bumped, `v` given the old or the new word. -/
theorem assignBumpStore_sim {p : PrimTy} (hpn : p.isNumeric = true) (op : IncDec) (i : Idx Γ (.val p))
    {l : Solidity.OpLoc C Γ p} {loc : Solidity.Loc C Γ (.prim p)}
    (hl : opLocToLoc l = some loc) (hm : Sim C L b F σ m)
    (hwl : locIn F false loc = true) :
    StmtOut C L b F false false false (Solidity.TRun.assignIncDec i op l σ)
      (run (compileLoc b loc ++ [.dup 1, .sload] ++ bumpCode p op ++
        [.dup 3, .sstore, .swap 1, .pop, .mstore (cellOf b i)]) m) m := by
  simp only [List.append_assoc]
  rcases loc_sim loc hm hwl with ⟨rt, s, sv, hres, hsv, hps, hr, hrunl⟩ | ⟨hres, hrunl⟩
  · obtain ⟨told, rfl, hrold⟩ := prim_read hr
    have hf := Sto.find_of_findLive hsv
    have hv := bumpCode_simT hpn op hrold { m with stack := .slot s :: m.stack }
    rw [run_append_ok hrunl,
      run_append_ok (m' := { m with stack := .val (m.store.cells s) :: .slot s :: m.stack })
      (by simp only [run, Machine.push, exec_cons_zero, Instr.step, Nat.sub_self, List.length_cons,
          Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero, Machine.next, Out.ok_bind,
          exec_nil])]
    rcases hv with ⟨tn, wn, htn, hrn, hrunt⟩ | ⟨h, hrunt⟩
    · obtain ⟨an, rfl, hnew⟩ := repr_write (L := L) hrn m.store s
      obtain ⟨st', hst', hrep⟩ := save_repr hm.store hps ⟨_, hsv⟩ hnew
        (fun x hx => WordStore.write_other _ _ fun he => hx (he ▸ Occ.prim))
      have hs := (hm.store' hrep (upd_len hps an)).setLocalVal i
        (v := if op.isPre then tn else told)
        (w := if op.isPre then .val an else .val (m.store.cells s))
        (by cases op.isPre <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> first | exact hrn | exact hrold)
      refine .inl ⟨⟨(σ.withStorage st').setLocal i
          (if op.isPre then tn else told), List.prefix_refl _⟩, { m with
          store := WordStore.write m.store s an
          mem := upd m.mem (cellOf b i) (if op.isPre then .val an else .val (m.store.cells s)) },
        ?_, ?_, rfl, Keeps.storeUpd (le_lvl b i) _ (upd_len hps an), hs⟩
      · simp only [Solidity.TRun.assignIncDec, opLocT_bump hl, hres,
          Solidity.bumpStoreT, hf, SVal.view_prim, htn, hst', bind, Except.bind, TRes.ofOpt, pure,
          Except.pure]
      · simp only at hrunt
        rw [run_append_ok hrunt]
        simp only [run, exec_cons_zero, Instr.step, Nat.add_one_sub_one, List.length_cons,
            Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_succ,
            List.getElem_cons_zero, Machine.next, Out.ok_bind, List.set_cons_zero, exec_nil]
    · refine .inr ⟨?_, run_append_revert hrunt⟩
      simp only [Solidity.TRun.assignIncDec, opLocT_bump hl, hres, Solidity.bumpStoreT,
        hf, SVal.view_prim, h, bind, Except.bind, TRes.ofOpt]
  · exact .inr ⟨by simp only [Solidity.TRun.assignIncDec, opLocT_bump hl, hres, bind,
      Except.bind], run_append_revert hrunl⟩

/-! ## Copies, arrays, `delete`, payments -/

/-- The offsets the fragment pushes are words. -/
theorem leavesFit_mem {T : Ty} (h : leavesFit T = true) : ∀ o ∈ leaves T, o < W :=
  fun o ho => by simpa only [decide_eq_true_eq] using List.all_eq_true.1 h o ho

theorem leavesFit_rev {T : Ty} (h : leavesFit T = true) : ∀ o ∈ (leaves T).reverse, o < W :=
  fun o ho => leavesFit_mem h o (List.mem_reverse.1 ho)

/-- **`alice = bob;`** of a static type: the source's words loaded, the
target resolved, the words stored at the target's slots. -/
theorem copy_sim {R : RefTy} (l : Solidity.Loc C Γ (.ref R))
    (q : Solidity.SPath C Γ (.ref R)) (hq : (Ty.ref R).mapFree = true)
    (hst : static (.ref R) = true) (hfit : leavesFit (.ref R) = true)
    (hm : Sim C L b F σ m)
    (hwq : spathIn F false q = true) (hwl : locIn F false l = true) :
    StmtOut C L b F false false false (Solidity.TRun.assign l (.copy q hq) σ)
      (run (compileSPath b q ++ loadLeaves (leaves (.ref R)) ++ [.pop] ++ compileLoc b l ++
        storeLeaves (leaves (.ref R)).reverse ++ [.pop]) m) m := by
  simp only [List.append_assoc]
  rcases spath_sim q hm hwq with ⟨r, s, sv, hres, hsv, hpq, hr, hrun⟩ | ⟨hres, hrun⟩
  · have hf := Sto.find_of_findLive hsv
    rw [run_append_ok hrun]
    simp only [Machine.push]
    rw [run_append_ok (loadLeaves_run m s _ (leavesFit_mem hfit) m.stack)]
    generalize hvs : ((leaves (.ref R)).map fun o => m.store.cells (s.add o)).reverse = vs
    rw [run_append_ok (m' := { m with stack := vs.map Word.val ++ m.stack }) rfl]
    rcases loc_sim l (hm.stack (vs.map Word.val ++ m.stack)) hwl with
      ⟨r', d, old, hres', hold, hpl, hro, hrunl⟩ | ⟨hres', hrunl⟩
    · rw [run_append_ok hrunl]
      simp only [Machine.push]
      have hlen : (leaves (.ref R)).reverse.length = vs.length := by
        rw [← hvs]; simp only [List.length_reverse, List.length_map]
      rw [run_append_ok (storeLeaves_run { m with stack := vs.map Word.val ++ m.stack } d _ vs
        m.stack m.store (leavesFit_rev hfit) hlen)]
      have hvs' : vs.map Fin.val = (leaves (.ref R)).reverse.map fun o => m.store (s.add o) := by
        simp only [← hvs, List.map_reverse, List.map_map]; rfl
      rw [hvs']
      have hmove := move_repr (st' := storeAt m.store d (leaves (.ref R)).reverse
          ((leaves (.ref R)).reverse.map fun o => m.store (s.add o))) hr _ d
        (Nat.lt_succ_self _) hst fun o ho => storeAt_map _ (fun o => WordStore.read_lt m.store _) (List.mem_reverse.2 ho)
      have hov := (overlay_repr hmove _ (Nat.lt_succ_self _) hst).2 old
      obtain ⟨st', hsave, hrep⟩ := save_repr hm.store hpl ⟨_, hold⟩ hov
        (fun x hx => storeAt_other fun o ho hxo =>
          hx (hxo ▸ leavesF_occ _ _ d o (List.mem_reverse.1 ho)))
      have hst' : σ.storage.write r' sv = some st' := by
        rw [write_ref _ _ _ (Sto.find_of_findLive hold)]; exact hsave
      refine .inl ⟨⟨σ.withStorage st', List.prefix_refl _⟩, _, ?_, rfl, rfl,
        Keeps.store (storeAt_len hpl hst _),
        hm.store' hrep (storeAt_len hpl hst _)⟩
      simp only [Solidity.TRun.assign, Solidity.Src.valueT, hres, hf, hres', hst', bind,
        Except.bind, TRes.ofOpt, pure, Except.pure]
    · exact .inr ⟨by simp only [Solidity.TRun.assign, Solidity.Src.valueT, hres, hf,
        hres', bind, Except.bind, TRes.ofOpt], run_append_revert hrunl⟩
  · exact .inr ⟨by simp only [Solidity.TRun.assign, Solidity.Src.valueT, hres, bind,
      Except.bind], run_append_revert hrun⟩

/-- **`b.push(…)`**: the array's slot, the value, the length checked against
solc's `2^64` and grown, the element stored. -/
theorem push_sim {E : Ty} (q : Solidity.SPath C Γ (.array E))
    (v : Option (Solidity.Src C Γ E)) (hm : Sim C L b F σ m)
    (hwp : pushIn F v q = true) (hL : L + 1 ≤ Lmax) :
    StmtOut C (L + 1) b F false false false (Solidity.TRun.push q v σ)
      (run (pushCode b v q) m) m := by
  have hm' := hm.mono (Nat.le_succ L) hL
  have hLW := Lmax_lt_W
  cases v with
  | none =>
    rw [pushIn] at hwp
    simp only [Bool.and_eq_true] at hwp
    obtain ⟨hE, hwb⟩ := hwp
    obtain ⟨p, rfl⟩ : ∃ p, E = .prim p := by cases E <;> simp_all only [Nat.succ_eq_add_one,
        Ty.isPrimitive, Ty.prim.injEq, exists_eq', Bool.false_eq_true]
    simp only [pushCode, List.append_assoc]
    rcases spath_sim q hm hwb with ⟨r, s, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
    · have hr' := hr
      cases hr with
      | @array _ kk _ e sh hk hl hW hall =>
        rw [run_append_ok hrun]
        simp only [Machine.push]
        rw [run_append_ok (m' := { m with stack := .slot s :: w[0] :: .slot s :: m.stack }) rfl,
          run_append_ok (pushSlotCode_run m _ 1 s (by omega))]
        obtain ⟨st', hst'⟩ : ∃ st', st' =
            WordStore.write (WordStore.write m.store s (m.store s + 1)) (.data s (m.store s * 1)) 0 := ⟨_, rfl⟩
        have hb : kk + 1 < 2 ^ 256 := by unfold W at hLW; omega
        have hnew : ReprAt st' (L + 1) (.prim p) (.data s (kk * size (.prim p)))
            (SVal.dflt (.prim p)) := zero_prim_repr (by rw [size_prim, ← hl, hst', WordStore.write_same, Nat.zero_mod])
        have hout : ∀ x, x ≠ s → x ≠ .data s (kk * 1) → st' x = m.store x :=
          fun x h1 h2 => by rw [hst', hl, WordStore.write_other _ _ h2, WordStore.write_other _ _ h1]
        have harr := push_repr (sh' := .ofList (pushSlot (.prim p) sh.toList).2)
          (SVec.snoc_lt_bound e _ hb) hr'
          (st' := st') (by rw [hst', WordStore.write_other _ _ (Slot.ne_data _ _), WordStore.write_same, hl]; exact Nat.mod_eq_of_lt hb) hnew
          (fun x hx hx' => hout x hx fun he => hx' (by rw [he, size_prim]; exact Occ.prim))
        obtain ⟨st'', hsave, hrep⟩ := save_repr hm'.store hp ⟨_, hsv⟩ harr
          (fun x hx => hout x (fun he => hx (he ▸ Occ.len))
            (fun he => hx (he ▸ Occ.elem kk (by rw [size_prim]; exact Occ.prim))))
        have hlen : ∀ x, LenSlot C x → m.store x ≤ st' x := push_len hp (m.store s)
          (by rw [hst', WordStore.write_other _ _ (Slot.ne_data _ _), WordStore.write_same]; exact Nat.mod_eq_of_lt (by rw [hl]; exact hb))
          (fun x h1 h2 => by
            by_cases hx : x = .data s (m.store s * 1)
            · rw [hx]; exact OccAt.prim
            · exact absurd (by rw [hst', WordStore.write_other _ _ hx, WordStore.write_other _ _ h1]) h2)
        subst hst'
        obtain ⟨hfull, hpush⟩ := push_eq (Sto.find_of_findLive hsv)
          (fun slot => some ((none : Option (SVal (.prim p))).getD slot))
          (x := SVal.dflt (.prim p)) (by rw [pushSlot_prim]; rfl) hb
        refine .inl ⟨⟨σ.withStorage st'', List.prefix_refl _⟩, _, ?_, rfl, rfl, Keeps.store hlen,
          hm'.store' hrep hlen⟩
        simp only [Solidity.TRun.push, hres, hfull, Bool.false_eq_true, ↓reduceIte, hpush, hsave,
          bind, Except.bind, TRes.ofOpt, pure, Except.pure]
    · exact .inr ⟨by simp only [Solidity.TRun.push, hres, bind, Except.bind],
        run_append_revert hrun⟩
  | some src =>
    cases src with
    | copyMem p => cases hwp
    | fixedCopy p shape hm => cases hwp
    | @val p e =>
      rw [pushIn] at hwp
      simp only [Bool.and_eq_true] at hwp
      obtain ⟨hwb, hwe⟩ := hwp
      simp only [pushCode, List.append_assoc]
      rcases spath_sim q hm hwb with ⟨r, s, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
      · have hr' := hr
        cases hr with
        | @array _ kk _ e' sh hk hl hW hall =>
          rw [run_append_ok hrun]
          rcases val_sim e (hm.push (.slot s)) hwe with ⟨ve, we, hve, hrve, hrune⟩ | ⟨hve, hrune⟩
          · rw [run_append_ok hrune]
            simp only [Machine.push]
            obtain ⟨a, rfl, hnew⟩ := repr_write (L := L + 1) hrve
              (WordStore.write m.store s (m.store s + 1)) (.data s (m.store s * 1))
            rw [run_append_ok (m' := { m with stack := .slot s :: .val a :: .slot s :: m.stack })
                rfl,
              run_append_ok (pushSlotCode_run m _ 1 s (by omega))]
            obtain ⟨st', hst'⟩ : ∃ st', st' =
                WordStore.write (WordStore.write m.store s (m.store s + 1)) (.data s (m.store s * 1)) a := ⟨_, rfl⟩
            rw [← hst', hl, show kk * 1 = kk * size (.prim _) by
              simp only [Nat.mul_one, size_prim]] at hnew
            have hb : kk + 1 < 2 ^ 256 := by unfold W at hLW; omega
            have hout : ∀ x, x ≠ s → x ≠ .data s (kk * 1) → st' x = m.store x :=
              fun x h1 h2 => by rw [hst', hl, WordStore.write_other _ _ h2, WordStore.write_other _ _ h1]
            have harr := push_repr (sh' := .ofList (pushSlot (.prim p) sh.toList).2)
              (SVec.snoc_lt_bound e' _ hb) hr'
              (st' := st') (by rw [hst', WordStore.write_other _ _ (Slot.ne_data _ _), WordStore.write_same, hl]; exact Nat.mod_eq_of_lt hb) hnew
              (fun x hx hx' => hout x hx fun he => hx' (by rw [he, size_prim]; exact Occ.prim))
            obtain ⟨st'', hsave, hrep⟩ := save_repr hm'.store hp ⟨_, hsv⟩ harr
              (fun x hx => hout x (fun he => hx (he ▸ Occ.len))
                (fun he => hx (he ▸ Occ.elem kk (by rw [size_prim]; exact Occ.prim))))
            have hlen : ∀ x, LenSlot C x → m.store x ≤ st' x := push_len hp (m.store s)
              (by rw [hst', WordStore.write_other _ _ (Slot.ne_data _ _), WordStore.write_same]; exact Nat.mod_eq_of_lt (by rw [hl]; exact hb))
              (fun x h1 h2 => by
                by_cases hx : x = .data s (m.store s * 1)
                · rw [hx]; exact OccAt.prim
                · exact absurd (by rw [hst', WordStore.write_other _ _ hx, WordStore.write_other _ _ h1]) h2)
            subst hst'
            obtain ⟨hfull, hpush⟩ := push_eq (Sto.find_of_findLive hsv)
              (fun slot => some ((some (SVal.prim ve).strip).getD slot))
              (x := SVal.prim ve) (by rw [SVal.strip_prim]; rfl) hb
            refine .inl ⟨⟨σ.withStorage st'', List.prefix_refl _⟩, _, ?_, rfl, rfl,
              Keeps.store hlen, hm'.store' hrep hlen⟩
            simp only [Solidity.TRun.push, Solidity.Src.valueT, hres, hve, hfull,
              Bool.false_eq_true, ↓reduceIte, hpush, hsave, bind, Except.bind, TRes.ofOpt, pure,
              Except.pure]
          · refine .inr ⟨?_, run_append_revert hrune⟩
            simp only [Solidity.TRun.push, Solidity.Src.valueT, hres, hve, bind,
              Except.bind]
      · exact .inr ⟨by simp only [Solidity.TRun.push, hres, bind, Except.bind],
          run_append_revert hrun⟩
    | @copy R q' hq =>
      rw [pushIn] at hwp
      simp only [Bool.and_eq_true] at hwp
      obtain ⟨⟨⟨hst, hfit⟩, hwb⟩, hwq⟩ := hwp
      simp only [pushCode, List.append_assoc]
      rcases spath_sim q hm hwb with ⟨r, s, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
      · have hr' := hr
        cases hr with
        | @array _ kk _ e sh hk hl hW hall =>
          rw [run_append_ok hrun]
          rcases spath_sim q' (hm.push (.slot s)) hwq with
            ⟨r', src, sv', hres', hsv', hpq, hrq, hrunq⟩ | ⟨hres', hrunq⟩
          · have hf' := Sto.find_of_findLive hsv'
            rw [run_append_ok hrunq]
            simp only [Machine.push]
            rw [run_append_ok (loadLeaves_run m src _ (leavesFit_mem hfit) (.slot s :: m.stack))]
            generalize hvs : ((leaves (.ref R)).map fun o => m.store.cells (src.add o)).reverse = vs
            have hlen : (leaves (.ref R)).reverse.length = vs.length := by
              rw [← hvs]; simp only [List.length_reverse, List.length_map]
            rw [run_append_ok (m' := { m with stack := .slot s :: (vs.map Word.val ++
                .slot s :: m.stack) })
              (by simp only [run, exec_cons_zero, Instr.step, Machine.next, Out.ok_bind,
                  Nat.add_one_sub_one, List.length_append, List.length_map, ← hlen,
                  List.length_reverse, List.length_cons, Nat.lt_add_right_iff_pos,
                  Nat.zero_lt_succ, getElem?_pos, Nat.le_refl, List.getElem_append_right,
                  Nat.sub_self, List.getElem_cons_zero, exec_nil]),
              run_append_ok (pushSlotCode_run m _ (size (.ref R)) s (by omega)),
              run_append_ok (storeLeaves_run m _ _ vs (.slot s :: m.stack) _ (leavesFit_rev hfit) hlen)]
            have hvs' : vs.map Fin.val =
                (leaves (.ref R)).reverse.map fun o => m.store (src.add o) := by
              simp only [← hvs, List.map_reverse, List.map_map]; rfl
            rw [hvs']
            obtain ⟨st', hst'⟩ : ∃ st', st' = storeAt (WordStore.write m.store s (m.store s + 1))
                (.data s (m.store s * size (.ref R))) (leaves (.ref R)).reverse
                ((leaves (.ref R)).reverse.map fun o => m.store (src.add o)) := ⟨_, rfl⟩
            have hmove := move_repr (st' := st') hrq _ (.data s (kk * size (.ref R)))
              (Nat.lt_succ_self _) hst fun o ho => by
                rw [hst', ← hl]; exact storeAt_map _ (fun o => WordStore.read_lt m.store _) (List.mem_reverse.2 ho)
            have hnew := ((overlay_repr hmove _ (Nat.lt_succ_self _) hst).1).mono (Nat.le_succ L)
            have hb : kk + 1 < 2 ^ 256 := by unfold W at hLW; omega
            have hout : ∀ x, x ≠ s → ¬ Occ (.ref R) (.data s (kk * size (.ref R))) x →
                st' x = m.store x := fun x h1 h2 => by
              rw [hst', hl, storeAt_other fun o ho hxo =>
                h2 (by rw [hxo]; exact leavesF_occ _ _ _ o (List.mem_reverse.1 ho)),
                WordStore.write_other _ _ h1]
            have harr := push_repr (sh' := .ofList (pushSlot (.ref R) sh.toList).2)
              (SVec.snoc_lt_bound e _ hb) hr' (st' := st')
              (by rw [hst', storeAt_other fun o _ he => Slot.ne_data s _ he,
                WordStore.write_same, hl]; exact Nat.mod_eq_of_lt hb) hnew hout
            obtain ⟨st'', hsave, hrep⟩ := save_repr hm'.store hp ⟨_, hsv⟩ harr
              (fun x hx => hout x (fun he => hx (he ▸ Occ.len))
                (fun he => hx (Occ.elem kk he)))
            have hlen : ∀ x, LenSlot C x → m.store x ≤ st' x := push_len hp (m.store s)
              (by rw [hst', storeAt_other fun o _ he => Slot.ne_data s _ he, WordStore.write_same]; exact Nat.mod_eq_of_lt (by rw [hl]; exact hb))
              (fun x h1 h2 => by
                by_cases hx : ∃ o ∈ (leaves (.ref R)).reverse,
                    x = (Slot.data s (m.store s * size (.ref R))).add o
                · obtain ⟨o, ho, rfl⟩ := hx
                  exact leavesF_occAt _ _ _ o hst (List.mem_reverse.1 ho)
                · refine absurd ?_ h2
                  rw [hst', storeAt_other fun o ho he => hx ⟨o, ho, he⟩, WordStore.write_other _ _ h1])
            obtain ⟨hfull, hpush⟩ := push_eq (Sto.find_of_findLive hsv)
              (fun slot => some ((some sv'.strip).getD slot)) (x := sv'.strip) rfl hb
            refine .inl ⟨⟨σ.withStorage st'', List.prefix_refl _⟩, { m with store := st' }, ?_,
              ?_, rfl, Keeps.store hlen, hm'.store' hrep hlen⟩
            · simp only [Solidity.TRun.push, Solidity.Src.valueT, hres, hres', hf',
                hfull, Bool.false_eq_true, ↓reduceIte, hpush, hsave, bind, Except.bind,
                TRes.ofOpt, pure, Except.pure]
            · rw [hst']; rfl
          · exact .inr ⟨by simp only [Solidity.TRun.push, Solidity.Src.valueT, hres,
              hres', bind, Except.bind], run_append_revert hrunq⟩
      · exact .inr ⟨by simp only [Solidity.TRun.push, hres, bind, Except.bind],
          run_append_revert hrun⟩

/-- `b.pop();`: the length decremented, reverting on an empty array; the
fragile aliases forgotten. -/
theorem pop_sim {E : Ty} (q : Solidity.SPath C Γ (.array E))
    (hm : Sim C L b F σ m) (hwb : spathIn F false q = true) :
    StmtOut C L b F.dropFragile true false false (Solidity.TRun.pop q σ)
      (run (compileSPath b q ++ popCode) m) m := by
  rcases spath_sim q hm hwb with ⟨r, s, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
  · have hr' := hr
    cases hr with
    | @array _ kk _ e sh hk hl hW hall =>
      rw [run_append_ok hrun]
      have hpc := popCode_run m m.stack s
        (by rw [hl]; have := hm.bound; have := Lmax_lt_W; omega)
      simp only [Machine.push] at hpc ⊢
      rw [hpc, hl]
      have hf := Sto.find_of_findLive hsv
      have he : e.toList.length = kk := SVec.length_toList e
      by_cases h0 : kk = 0
      · rw [if_pos h0]
        have hnil : e.toList = [] := List.eq_nil_of_length_eq_zero (by rw [he, h0])
        refine .inr ⟨?_, rfl⟩
        simp only [Solidity.TRun.pop, hres, Solidity.Storage.pop, hf, SVal.view_array, hnil,
          List.reverse_nil, bind, Except.bind, Option.bind, TRes.ofOpt]
      · rw [if_neg h0]
        obtain ⟨last, restRev, hrev⟩ : ∃ last restRev, e.toList.reverse = last :: restRev := by
          cases h : e.toList.reverse with
          | nil =>
            simp only [List.reverse_eq_nil_iff] at h
            rw [h, List.length_nil] at he; exact absurd he.symm h0
          | cons last restRev => exact ⟨last, restRev, rfl⟩
        have hnew := pop_repr (L := L)
          (sh' := .ofList ((if E.isMapping then last else last.defaultOf) :: sh.toList))
          (SVec.dropLast_lt_bound e hk) hr'
        obtain ⟨st', hsave, hrep⟩ := save_repr hm.store hp ⟨_, hsv⟩ hnew
          (fun x hx => WordStore.write_other _ _ fun he => hx (he ▸ Occ.len))
        refine .inl ⟨⟨σ.withStorage st', List.prefix_refl _⟩, _, ?_, rfl, rfl, Keeps.shrink,
          hm.storeDrop hrep⟩
        simp only [Solidity.TRun.pop, hres, Solidity.Storage.pop, hf, SVal.view_array, hrev,
          hsave, bind, Except.bind, Option.bind, TRes.ofOpt, pure, Except.pure]
  · exact .inr ⟨by simp only [Solidity.TRun.pop, hres, bind, Except.bind],
      run_append_revert hrun⟩

/-- `delete l;`: every leaf of `l` zeroed; the fragile aliases forgotten. -/
theorem delete_sim {T : Ty} (l : Solidity.Loc C Γ T)
    (hm : Sim C L b F σ m) (hfit : leavesFit T = true) (hwl : locIn F false l = true) :
    StmtOut C L b F.dropFragile true false false (Solidity.TRun.delete l σ)
      (run (compileLoc b l ++ zeroCode (leaves T) ++ [.pop]) m) m := by
  simp only [List.append_assoc]
  rcases loc_sim l hm hwl with ⟨r, s, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
  · rw [run_append_ok hrun]
    simp only [Machine.push]
    rw [run_append_ok (zeroCode_run m m.stack s (leaves T) (leavesFit_mem hfit))]
    have hnew := zero_repr hr (tyRank T + 1) (Nat.lt_succ_self _)
      (st' := zeroAt m.store s (leaves T)) (fun o ho => zeroAt_zero ⟨o, ho, rfl⟩)
      (fun x _ hx => zeroAt_other hx)
    obtain ⟨st', hsave, hrep⟩ := save_repr hm.store hp ⟨_, hsv⟩ hnew
      (fun x hx => zeroAt_other fun o ho hxo => hx (hxo ▸ leavesF_occ _ T s o ho))
    refine .inl ⟨⟨σ.withStorage st',
      List.prefix_refl _⟩, { m with store := zeroAt m.store s (leaves T) }, ?_, rfl, rfl,
      Keeps.shrink, hm.storeDrop hrep⟩
    simp only [Solidity.TRun.delete, hres, Solidity.Storage.delete, Sto.find_of_findLive hsv,
      hsave, bind, Except.bind, Option.bind, TRes.ofOpt, pure, Except.pure]
  · exact .inr ⟨by simp only [Solidity.TRun.delete, hres, bind, Except.bind],
      run_append_revert hrun⟩

/-- **A payment**: `to.transfer(5);` books `net(to) - 5`; the machine's
`CALL` moves `5`, or nothing when `to` is the contract, or is refused and
reverts, the typed run's state then represented by the world that paid. -/
theorem transfer_sim (r a : Solidity.Val C Γ .uint)
    (hm : Sim C L b F σ m) (hwr : valIn F r = true)
    (hwa : valIn F a = true) :
    StmtOut C L b F false true false (Solidity.TRun.transfer r a σ)
      (run (compileVal b r ++ compileVal b a ++ [.call] ++ assertTop) m) m := by
  simp only [List.append_assoc]
  rcases val_sim r hm hwr with ⟨vr, wr, hvr, hrv, hrunr⟩ | ⟨hvr, hrunr⟩
  · obtain ⟨x, rfl, hx1⟩ := hrv
    rw [run_append_ok hrunr]
    rcases val_sim a (hm.push _) hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
    · obtain ⟨y, rfl, hy1⟩ := hra
      rw [run_append_ok hruna]
      have hc : σ.canPay vr va =
          (decide (y.1 ≤ m.bal m.self) && m.accepts x y) := by
        simp only [State.canPay, hm.funds, hy1, Int.ofNat_le]
        exact congrArg (fun z => decide (y.1 ≤ m.bal m.self) && z)
          (hm.oracle vr va x y hx1 hy1)
      obtain ⟨-, -, -, hself⟩ := hm.env
      have hpay : ∀ c : Fin W, netAt (σ.pay vr y.1).net c.1 =
          if x = m.self then netAt σ.net c.1 else if c = x then netAt σ.net x.1 - y.1
          else netAt σ.net c.1 := by
        intro c
        rw [netAt_pay, hx1, hself]
        simp only [Int.ofNat_inj, Fin.val_inj]
      have hns : netAt (σ.pay vr y.1).net m.self.1 = 0 := by
        rw [hpay m.self]
        split
        · exact hm.netSelf
        · rename_i hxs
          rw [if_neg (fun h => hxs h.symm)]
          exact hm.netSelf
      by_cases hrf : m.bal m.self < y.1 ∨ m.accepts x y = false
      · have hn : σ.canPay vr va = false := by
          rw [hc]
          rcases hrf with hrf | hrf
          · simp only [show ¬ y.1 ≤ m.bal m.self by omega, decide_false, Bool.false_and]
          · simp only [hrf, Bool.and_false]
        refine .inr ⟨?_, ?_⟩
        · simp only [Solidity.TRun.transfer, hvr, hva, bind, Except.bind, hn,
            Bool.false_eq_true, ↓reduceIte]
          rfl
        · simp only [run, assertTop, List.cons_append, List.nil_append,
            Machine.push, exec_cons_zero, Instr.step, hrf, ↓reduceIte, Machine.next,
            Out.ok_bind, exec_nil, Out.revert_bind]
      · have hrf' : y.1 ≤ m.bal m.self ∧ m.accepts x y = true := by
          simp only [not_or, Bool.not_eq_false] at hrf
          exact ⟨by omega, hrf.2⟩
        have hn : σ.canPay vr va = true := by simp only [hc, hrf'.1, decide_true, hrf'.2, Bool.and_self]
        have hres : Solidity.TRun.transfer r a σ =
            .ok ⟨σ.pay vr y.1, List.prefix_refl _⟩ := by
          simp only [Solidity.TRun.transfer, hvr, hva, bind, Except.bind, hn,
            ↓reduceIte, hy1]
          rfl
        rw [hres]
        have hbal := balance_pay σ vr y.1 (by rw [hm.funds]; exact_mod_cast hrf'.1)
        rw [hx1, hself] at hbal
        simp only [Int.ofNat_inj, Fin.val_inj] at hbal
        by_cases hxe : x = m.self
        · have hb := hm.book _ _ m.bal m.bal₀ (fun c hcs => by
            rw [hpay c, if_pos hxe]; exact hm.net c hcs) hns (by rw [hbal, if_pos hxe, hm.funds])
          refine .inl ⟨⟨σ.pay vr y.1, List.prefix_refl _⟩, m, rfl, ?_, rfl, Keeps.refl m, hb⟩
          subst hxe
          simp only [run, assertTop, List.cons_append, List.nil_append, Machine.push,
              exec_cons_zero, Instr.step, hrf, ↓reduceIte, Machine.next, Out.ok_bind,
              Nat.succ_ne_self, exec_cons_succ, exec_nil]
        · simp only [not_or, Bool.not_eq_false] at hrf
          refine .inl ⟨⟨σ.pay vr y.1, List.prefix_refl _⟩, { m with bal := pay m.bal m.self x y.1 },
            rfl, ?_, rfl, ⟨fun _ _ => rfl, fun _ _ _ => Nat.le_refl _⟩,
            hm.book vr y.1 _ m.bal₀ (fun c hcs => ?_) hns ?_⟩
          · simp only [run, assertTop, List.cons_append, List.nil_append, Machine.push,
              exec_cons_zero, Instr.step, hrf, Bool.true_eq_false, or_self, ↓reduceIte, hxe,
              Out.ok_bind, Nat.succ_ne_self, exec_cons_succ, exec_nil]
          · have h1 := hm.net c hcs
            rw [hpay c]
            simp only [pay, upd, hxe, ↓reduceIte]
            by_cases hcx : c = x
            · subst hcx; simp only [↓reduceIte]; omega
            · simp only [hcx, hcs, ↓reduceIte]; exact h1
          · rw [hbal, if_neg hxe, hm.funds]
            simp only [pay, upd, hxe, if_neg (Ne.symm hxe), ↓reduceIte]
            omega
    · exact .inr ⟨by simp only [Solidity.TRun.transfer, hvr, hva, bind, Except.bind],
        run_append_revert hruna⟩
  · exact .inr ⟨by simp only [Solidity.TRun.transfer, hvr, bind, Except.bind],
      run_append_revert hrunr⟩

end Stmts

end Solidity.Evm
