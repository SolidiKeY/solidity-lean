import Solidity.Evm.CoreExpr

/-!
# Statements over the scoped interpreter

One lemma per statement of the fragment (`docs/intrinsic.md`, M5): the
statement's step (`Semantics/Core.lean`'s `Run.*`) and its code
(`Evm/CoreCompile.lean`) agree, as `StmtOut` says.  `stmt_sim`
(`Evm/CoreCorrect.lean`) dispatches to them, so each elaborates on its own.

`StmtOut` is `Evm/Correctness.lean`'s dichotomy with two facts more, kept
by every outcome that goes on (`Keeps`): the cells below the frame's base
are as they were, and, unless the statement may shrink an array
(`Stmt.shrinks`), no array's length went down.  A call needs both of its
body, whose frame sits above the caller's locals: the first keeps the
caller's locals, the second its fragile aliases in bounds.  The refused
outcome carries them too, since the interpreter goes on from a machine the
world paid (`compile_correct`'s third case).  A panic is the outcome of an
`assert` only (`Stmt.asserts`), so code without one never panics
(`compile_exact`).
-/

namespace Solidity.Evm
namespace Core

open Semantics hiding Ctx
open SemanticsProperties
open Solidity.Core (Ctx Idx Ext Env)

variable {C : Contract}

/-! ## Assertions -/

mutual
/-- Whether a statement has an `assert` (in a branch, a block or a called
body): only those panic. -/
def Stmt.asserts {Γ Γ' : Ctx} : Solidity.Core.Stmt C Γ Γ' → Bool
  | .assert _ => true
  | .ite _ t e => Prog.asserts t || Prog.asserts e
  | .block body => Prog.asserts body
  | .call _ _ _ body => Prog.asserts body
  | .tryCall _ _ ok err _ pnc other =>
    Prog.asserts ok || Prog.asserts err || Prog.asserts pnc || Prog.asserts other
  | .loop _ _ body => Prog.asserts body
  | .assign .. | .rebind .. | .assignLocal .. | .declLocal .. | .declStorage .. | .opAssign ..
  | .incDec .. | .assignIncDec .. | .push .. | .pop _ | .transfer .. | .send .. | .declMem ..
  | .rebindMem .. | .assignFromMem .. | .assignMem .. | .delete _ | .deleteMem .. | .assignNew ..
  | .require _ | .revert => false
def Prog.asserts {Γ Γ' : Ctx} : Solidity.Core.Prog C Γ Γ' → Bool
  | .nil => false
  | .cons s P => Stmt.asserts s || Prog.asserts P
end

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

theorem or_left {sh' : Bool} {m m' : Machine} (h : Keeps C b sh m m') :
    Keeps C b (sh || sh') m m' :=
  ⟨h.mem, fun hs => h.len (by simp only [Bool.or_eq_false_iff] at hs; exact hs.1)⟩

theorem or_right {sh' : Bool} {m m' : Machine} (h : Keeps C b sh' m m') :
    Keeps C b (sh || sh') m m' :=
  ⟨h.mem, fun hs => h.len (by simp only [Bool.or_eq_false_iff] at hs; exact hs.2)⟩

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
theorem storeUpd {m : Machine} {l : Nat} {st' : Slot → Nat} (hl : b ≤ l) (w : Word)
    (hlen : ∀ x, LenSlot C x → m.store x ≤ st' x) :
    Keeps C b sh m { m with store := st', mem := Evm.upd m.mem (cell l) w } :=
  ⟨fun l' hl' => by
    show Evm.upd m.mem (cell l) w (cell l') = m.mem (cell l')
    exact upd_other _ _ (fun h => by have := cell_inj h; omega), fun _ => hlen⟩

/-- A storage write that lowers no length. -/
theorem store {m : Machine} {st' : Slot → Nat} (hlen : ∀ x, LenSlot C x → m.store x ≤ st' x) :
    Keeps C b sh m { m with store := st' } := ⟨fun _ _ => rfl, fun _ => hlen⟩

/-- A storage write that may lower a length, in a statement that may shrink. -/
theorem shrink {m : Machine} {st' : Slot → Nat} : Keeps C b true m { m with store := st' } :=
  ⟨fun _ _ => rfl, fun h => nomatch h⟩

end Keeps

/-! ## A statement's outcome -/

/-- A statement's outcome: both succeed, the machine's stack as it was, what
it keeps kept (`Keeps`) and the states related; or both revert; or the
interpreter panics (a failed `assert`, solc's `Panic(0x01)`), only in code
that `asserts`, where the machine reverts; or the machine reverts because
the world refused a payment — only code that `pays` has one — and the
interpreter succeeds in a state some machine represents, the one where the
world had paid. -/
inductive StmtOut (C : Contract) (L b : Nat) {Γ' : Ctx} (F' : Frag Γ') (sh pays asserts : Bool)
    (res : Res (Solidity.Core.State C Γ')) (out : Out) (m : Machine) : Prop where
  | inl (h : ∃ σ' m', res = .ok σ' ∧ out = .ok m' 0 ∧ m'.stack = m.stack ∧ Keeps C b sh m m' ∧
      Sim C L b F' σ'.glob (Look.ofEnv σ'.env) m')
  | inr (h : res = .error .revert ∧ out = .revert)
  | panic (ha : asserts = true) (h : res = .error .panic ∧ out = .revert)
  | refused (hp : pays = true) (h : out = .revert ∧ ∃ σ' m', res = .ok σ' ∧ Keeps C b sh m m' ∧
      Sim C L b F' σ'.glob (Look.ofEnv σ'.env) m')

/-- `StmtOut` under a looser bound on the arrays. -/
theorem StmtOut.mono {L b : Nat} {Γ' : Ctx} {F' : Frag Γ'} {sh pays asserts : Bool}
    {res : Res (Solidity.Core.State C Γ')} {out : Out} {m : Machine} {L' : Nat}
    (h : StmtOut C L b F' sh pays asserts res out m) (hL : L ≤ L') (hL' : L' ≤ Lmax) :
    StmtOut C L' b F' sh pays asserts res out m := by
  rcases h with ⟨σ', m', h1, h2, h3, h4, h5⟩ | h | ⟨ha, h⟩ | ⟨hp, h1, σ', m', h2, h4, h5⟩
  · exact .inl ⟨σ', m', h1, h2, h3, h4, h5.mono hL hL'⟩
  · exact .inr h
  · exact .panic ha h
  · exact .refused hp ⟨h1, σ', m', h2, h4, h5.mono hL hL'⟩

/-! ## The state's locals and global part, changed -/

section States

variable {L b : Nat} {Γ : Ctx} {F : Frag Γ} {σ : Solidity.Core.State C Γ} {m : Machine}

/-- The global part replaced. -/
theorem Sim.withGlob {τ : State} (h : Sim C L b F τ (Look.ofEnv σ.env) m) :
    Sim C L b F (σ.withGlob τ).glob (Look.ofEnv (σ.withGlob τ).env) m :=
  h.congrGlob rfl rfl rfl

/-- `x = e;` on a value local. -/
theorem Sim.setLocalVal (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m) {p : PrimTy}
    (i : Idx Γ (.val p)) {v : Value} {w : Word} (hv : ReprV p v w) :
    Sim C L b F (σ.setLocal i v).glob (Look.ofEnv (σ.setLocal i v).env)
      { m with mem := upd m.mem (cellOf b i) w } :=
  (hm.setVal i hv).congrLook fun j => Look.ofEnv_set i v σ.env j

/-- `uint x = e;`. -/
theorem Sim.pushVal (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m) {p : PrimTy} {v : Value}
    {w : Word} (hv : ReprV p v w) :
    Sim C L b (F.push (.val p) .ok) (σ.push (t := .val p) v).glob
      (Look.ofEnv (σ.push (t := .val p) v).env) { m with mem := upd m.mem (cell (b + Γ.length)) w } :=
  (hm.consVal hv).congrLook fun j => Look.ofEnv_cons (u := .val p) v σ.env j

/-- `p = q;` with `q` indexing no array. -/
theorem Sim.setAliasE (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m) {R : RefTy}
    (i : Idx Γ (.alias R)) {r : Name} {segs : List Seg} {s : Slot}
    (hp : PathSlot C true r segs (.ref R) s) :
    Sim C L b (F.set i .ok) (σ.setLocal i (some (r, segs))).glob
      (Look.ofEnv (σ.setLocal i (some (r, segs))).env)
      { m with mem := upd m.mem (cellOf b i) (.slot s) } :=
  (hm.setAlias i hp).congrLook fun j => Look.ofEnv_set i (some (r, segs)) σ.env j

/-- `p = persons[i];`. -/
theorem Sim.setFragileE (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m) {R : RefTy}
    (i : Idx Γ (.alias R)) {r : Name} {segs : List Seg} {s : Slot}
    (hp : PathSlot C false r segs (.ref R) s) (hlive : ∃ sv, σ.glob.findLive r segs = .ok sv) :
    Sim C L b (F.set i .fragile) (σ.setLocal i (some (r, segs))).glob
      (Look.ofEnv (σ.setLocal i (some (r, segs))).env)
      { m with mem := upd m.mem (cellOf b i) (.slot s) } :=
  (hm.setFragile i hp hlive).congrLook fun j => Look.ofEnv_set i (some (r, segs)) σ.env j

/-- `Person storage p = q;` with `q` indexing no array. -/
theorem Sim.pushAlias (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m) {R : RefTy} {r : Name}
    {segs : List Seg} {s : Slot} (hp : PathSlot C true r segs (.ref R) s) :
    Sim C L b (F.push (.alias R) .ok) (σ.push (t := .alias R) (some (r, segs))).glob
      (Look.ofEnv (σ.push (t := .alias R) (some (r, segs))).env)
      { m with mem := upd m.mem (cell (b + Γ.length)) (.slot s) } :=
  (hm.consAlias hp).congrLook fun j => Look.ofEnv_cons (u := .alias R) (some (r, segs)) σ.env j

/-- `Person storage p = persons[i];`. -/
theorem Sim.pushFragile (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m) {R : RefTy} {r : Name}
    {segs : List Seg} {s : Slot} (hp : PathSlot C false r segs (.ref R) s)
    (hlive : ∃ sv, σ.glob.findLive r segs = .ok sv) :
    Sim C L b (F.push (.alias R) .fragile) (σ.push (t := .alias R) (some (r, segs))).glob
      (Look.ofEnv (σ.push (t := .alias R) (some (r, segs))).env)
      { m with mem := upd m.mem (cell (b + Γ.length)) (.slot s) } :=
  (hm.consFragile hp hlive).congrLook fun j =>
    Look.ofEnv_cons (u := .alias R) (some (r, segs)) σ.env j

/-- `Person storage p;`. -/
theorem Sim.pushDead (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m) (R : RefTy)
    (v : Option (Name × List Seg)) :
    Sim C L b (F.push (.alias R) .dead) (σ.push (t := .alias R) v).glob
      (Look.ofEnv (σ.push (t := .alias R) v).env) m :=
  (hm.consDead R _).congrLook fun j => Look.ofEnv_cons (u := .alias R) v σ.env j

end States

/-! ## Assignments and declarations -/

section Stmts

variable {L b : Nat} {Γ : Ctx} {F : Frag Γ} {σ : Solidity.Core.State C Γ} {m : Machine}

theorem Res.map_error {α β : Type} (f : α → β) (e : Halt) :
    f <$> (Except.error e : Res α) = .error e := rfl

theorem Res.map_pure {α β : Type} (f : α → β) (a : α) : f <$> (pure a : Res α) = .ok (f a) := rfl

theorem Res.map_ok {α β : Type} (f : α → β) (a : α) : f <$> (Except.ok a : Res α) = .ok (f a) :=
  rfl

attribute [local simp] Res.ok_bind Res.error_bind Res.map_error Res.map_ok

/-- `alice.age = 10;`: the value, the slot, the write. -/
theorem assign_sim {p : PrimTy} (l : Solidity.Core.Loc C Γ (.prim p))
    (v : Solidity.Core.Val C Γ p) (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m)
    (hwl : locIn F false l = true) (hwv : valIn F v = true) :
    StmtOut C L b F false false false (Solidity.Core.Run.assign l (.val v) σ)
      (run (compileVal b v ++ compileLoc b l ++ [.sstore]) m) m := by
  simp only [List.append_assoc]
  rcases val_sim v hm hwv with ⟨vv, w, hvv, hrv, hrun⟩ | ⟨hvv, hrun⟩
  · rw [run_append_ok hrun]
    rcases loc_sim l (hm.push w) hwl with ⟨r, segs, s, sv, hres, hsv, hps, _, hrunl⟩ |
        ⟨hres, hrunl⟩
    · rw [run_append_ok hrunl]
      obtain ⟨a, rfl, hnew⟩ := repr_write (L := L) hrv m.store s
      obtain ⟨stor, hsave, hrep⟩ := save_repr hm.store hps ⟨sv, hsv⟩ hnew
        (fun x hx => upd_other _ _ fun he => hx (he ▸ Occ.prim))
      refine .inl ⟨σ.withGlob { σ.glob with storage := stor }, { m with store := upd m.store s a },
        ?_, rfl, rfl, Keeps.store (upd_len hps a),
        Sim.withGlob (hm.store' hrep (upd_len hps a))⟩
      cases vv <;>
        simp [Solidity.Core.Run.assign, Solidity.Core.Src.value, hvv, hres, Value.toSVal,
          State.writeStorage, hsave] at hsave ⊢ <;> rfl
    · exact .inr ⟨by simp [Solidity.Core.Run.assign, Solidity.Core.Src.value, hvv, hres],
        run_append_revert hrunl⟩
  · exact .inr ⟨by simp [Solidity.Core.Run.assign, Solidity.Core.Src.value, hvv],
      run_append_revert hrun⟩

/-- `x = e;` on a value local. -/
theorem assignLocal_sim {p : PrimTy} (i : Idx Γ (.val p)) (r : Solidity.Core.Val C Γ p)
    (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m) (hwr : valIn F r = true) :
    StmtOut C L b F false false false (Solidity.Core.Run.assignLocal i r σ)
      (run (compileVal b r ++ [.mstore (cellOf b i)]) m) m := by
  rcases val_sim r hm hwr with ⟨v, w, hv, hrv, hrun⟩ | ⟨hv, hrun⟩
  · refine .inl ⟨σ.setLocal i v, { m with mem := upd m.mem (cellOf b i) w },
      by simp [Solidity.Core.Run.assignLocal, hv], ?_, rfl, Keeps.upd (le_lvl b i) w,
      hm.setLocalVal i hrv⟩
    rw [run_append_ok hrun]; rfl
  · exact .inr ⟨by simp [Solidity.Core.Run.assignLocal, hv], run_append_revert hrun⟩

/-- `uint x = e;` (or `uint x;`, the default). -/
theorem declLocal_sim (p : PrimTy) (init : Option (Solidity.Core.Val C Γ p))
    (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m) (hw : init.all (valIn F) = true) :
    StmtOut C L b (F.push (.val p) .ok) false false false (Solidity.Core.Run.declLocal p init σ)
      (run (match init with
        | none => [.push (.val 0), .mstore (cell (b + Γ.length))]
        | some e => compileVal b e ++ [.mstore (cell (b + Γ.length))]) m) m := by
  cases init with
  | none =>
    exact .inl ⟨_, { m with mem := upd m.mem (cell (b + Γ.length)) (.val 0) }, rfl, rfl, rfl,
      Keeps.upd (Nat.le_add_right b _) _, hm.pushVal (ReprV.default p)⟩
  | some e =>
    simp only [Option.all_some] at hw
    rcases val_sim e hm hw with ⟨v, w, hv, hrv, hrun⟩ | ⟨hv, hrun⟩
    · refine .inl ⟨σ.push (t := .val p) v, { m with mem := upd m.mem (cell (b + Γ.length)) w },
        by simp [Solidity.Core.Run.declLocal, hv], ?_, rfl,
        Keeps.upd (Nat.le_add_right b _) _, hm.pushVal hrv⟩
      rw [run_append_ok hrun]; rfl
    · exact .inr ⟨by simp [Solidity.Core.Run.declLocal, hv], run_append_revert hrun⟩

/-- `p = q;`: an alias rebound, plain or fragile as `q` indexes an array. -/
theorem rebind_sim {R : RefTy} (i : Idx Γ (.alias R)) (q : Solidity.Core.SPath C Γ (.ref R))
    {F' : Frag Γ} (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m)
    (hw : (bindFl F q).map (F.set i) = some F') :
    StmtOut C L b F' false false false (Solidity.Core.Run.rebind i (.path q) σ)
      (run (compileSPath b q ++ [.mstore (cellOf b i)]) m) m := by
  unfold bindFl at hw
  by_cases h1 : spathIn F true q = true
  · rw [if_pos h1] at hw; cases hw
    rcases spath_sim q hm h1 with ⟨r, segs, s, sv, hres, _, hp, _, hrun⟩ | ⟨hres, hrun⟩
    · refine .inl ⟨σ.setLocal i (some (r, segs)), { m with mem := upd m.mem (cellOf b i) (.slot s) },
        ?_, ?_, rfl, Keeps.upd (le_lvl b i) _, hm.setAliasE i hp⟩
      · simp [Solidity.Core.Run.rebind, Solidity.Core.ARhs.eval, hres]
      · rw [run_append_ok hrun]; rfl
    · exact .inr ⟨by simp [Solidity.Core.Run.rebind, Solidity.Core.ARhs.eval, hres],
        run_append_revert hrun⟩
  · rw [if_neg h1] at hw
    by_cases h2 : spathIn F false q = true
    · rw [if_pos h2] at hw; cases hw
      rcases spath_sim q hm h2 with ⟨r, segs, s, sv, hres, hsv, hp, _, hrun⟩ | ⟨hres, hrun⟩
      · refine .inl ⟨σ.setLocal i (some (r, segs)),
          { m with mem := upd m.mem (cellOf b i) (.slot s) }, ?_, ?_, rfl,
          Keeps.upd (le_lvl b i) _, hm.setFragileE i hp ⟨sv, hsv⟩⟩
        · simp [Solidity.Core.Run.rebind, Solidity.Core.ARhs.eval, hres]
        · rw [run_append_ok hrun]; rfl
      · exact .inr ⟨by simp [Solidity.Core.Run.rebind, Solidity.Core.ARhs.eval, hres],
          run_append_revert hrun⟩
    · rw [if_neg h2] at hw; cases hw

/-- `Person storage p = q;`, plain or fragile as `q` indexes an array. -/
theorem declAlias_sim {R : RefTy} (q : Solidity.Core.SPath C Γ (.ref R))
    {F' : Frag (.alias R :: Γ)} (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m)
    (hw : (bindFl F q).map (F.push (.alias R)) = some F') :
    StmtOut C L b F' false false false (Solidity.Core.Run.declStorage R (some (.path q)) σ)
      (run (compileSPath b q ++ [.mstore (cell (b + Γ.length))]) m) m := by
  unfold bindFl at hw
  by_cases h1 : spathIn F true q = true
  · rw [if_pos h1] at hw; cases hw
    rcases spath_sim q hm h1 with ⟨r, segs, s, sv, hres, _, hp, _, hrun⟩ | ⟨hres, hrun⟩
    · refine .inl ⟨σ.push (t := .alias R) (some (r, segs)),
        { m with mem := upd m.mem (cell (b + Γ.length)) (.slot s) }, ?_, ?_, rfl,
        Keeps.upd (Nat.le_add_right b _) _, hm.pushAlias hp⟩
      · simp [Solidity.Core.Run.declStorage, Solidity.Core.ARhs.eval, hres]
      · rw [run_append_ok hrun]; rfl
    · exact .inr ⟨by simp [Solidity.Core.Run.declStorage, Solidity.Core.ARhs.eval, hres],
        run_append_revert hrun⟩
  · rw [if_neg h1] at hw
    by_cases h2 : spathIn F false q = true
    · rw [if_pos h2] at hw; cases hw
      rcases spath_sim q hm h2 with ⟨r, segs, s, sv, hres, hsv, hp, _, hrun⟩ | ⟨hres, hrun⟩
      · refine .inl ⟨σ.push (t := .alias R) (some (r, segs)),
          { m with mem := upd m.mem (cell (b + Γ.length)) (.slot s) }, ?_, ?_, rfl,
          Keeps.upd (Nat.le_add_right b _) _, hm.pushFragile hp ⟨sv, hsv⟩⟩
        · simp [Solidity.Core.Run.declStorage, Solidity.Core.ARhs.eval, hres]
        · rw [run_append_ok hrun]; rfl
      · exact .inr ⟨by simp [Solidity.Core.Run.declStorage, Solidity.Core.ARhs.eval, hres],
          run_append_revert hrun⟩
    · rw [if_neg h2] at hw; cases hw

/-- `require(c);` reverts on `false`; `assert(c);` panics. -/
theorem require_sim (c : Solidity.Core.Val C Γ .bool) (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m)
    (hwc : valIn F c = true) :
    StmtOut C L b F false false false (do Solidity.Core.guardOk (← c.eval σ) σ)
      (run (compileVal b c ++ assertTop) m) m := by
  rcases val_sim c hm hwc with ⟨vc, wc, hvc, hrc, hrunc⟩ | ⟨hvc, hrunc⟩
  · obtain ⟨x, rfl, rfl⟩ := hrc.bool_inv
    cases x
    · exact .inr ⟨by simp [hvc, Solidity.Core.guardOk], by rw [run_append_skip hrunc]; rfl⟩
    · exact .inl ⟨σ, m, by simp [hvc, Solidity.Core.guardOk]; rfl,
        by rw [run_append_skip hrunc]; rfl, rfl, Keeps.refl m, hm⟩
  · exact .inr ⟨by simp [hvc], run_append_revert hrunc⟩

theorem assert_sim (c : Solidity.Core.Val C Γ .bool) (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m)
    (hwc : valIn F c = true) :
    StmtOut C L b F false false true (do Solidity.Core.assertOk (← c.eval σ) σ)
      (run (compileVal b c ++ assertTop) m) m := by
  rcases val_sim c hm hwc with ⟨vc, wc, hvc, hrc, hrunc⟩ | ⟨hvc, hrunc⟩
  · obtain ⟨x, rfl, rfl⟩ := hrc.bool_inv
    cases x
    · exact .panic rfl ⟨by simp [hvc, Solidity.Core.assertOk], by rw [run_append_skip hrunc]; rfl⟩
    · exact .inl ⟨σ, m, by simp [hvc, Solidity.Core.assertOk]; rfl,
        by rw [run_append_skip hrunc]; rfl, rfl, Keeps.refl m, hm⟩
  · exact .inr ⟨by simp [hvc], run_append_revert hrunc⟩

/-! ## Compound assignments and `++` -/

/-- Reassociating a checked result, at any result type. -/
theorem bind_bind_ok' {α : Type} {x : Res Value} {f : Value → Res Value} {g : Value → Res α}
    {v : Value} (h : (x >>= f) = .ok v) : (x >>= fun a => f a >>= g) = g v := by
  cases x with
  | error e => cases h
  | ok a => simp only [Res.ok_bind] at h ⊢; rw [h]; rfl

theorem bind_bind_error' {α : Type} {x : Res Value} {f : Value → Res Value} {g : Value → Res α}
    {e : Halt} (h : (x >>= f) = .error e) : (x >>= fun a => f a >>= g) = .error e := by
  cases x with
  | error e' => simp only [Res.error_bind, Except.error.injEq] at h ⊢; exact h
  | ok a => simp only [Res.ok_bind] at h ⊢; rw [h]; rfl

/-- An `op=` on a storage target resolves the target once. -/
theorem opLoc_store {p : PrimTy} {l : Solidity.Core.OpLoc C Γ p}
    {loc : Solidity.Core.Loc C Γ (.prim p)} (h : opLocToLoc l = some loc) (op : BinOp) (v : Value) :
    l.store σ op v = (loc.resolve σ >>= fun rs => σ.withGlob <$> opStore σ.glob op p rs.1 rs.2 v) := by
  cases l <;> simp [opLocToLoc] at h <;> subst h <;> rfl

/-- `++` on a storage target resolves it once; the state its global part replaced. -/
theorem opLoc_bump {p : PrimTy} {l : Solidity.Core.OpLoc C Γ p}
    {loc : Solidity.Core.Loc C Γ (.prim p)} (h : opLocToLoc l = some loc) (op : IncDec) :
    ∃ g : State × Value → Solidity.Core.State C Γ × Value, (∀ τ v, g (τ, v) = (σ.withGlob τ, v)) ∧
      l.bump σ op = (loc.resolve σ >>= fun rs => g <$> bumpStore σ.glob op p rs.1 rs.2) := by
  cases l <;> simp [opLocToLoc] at h <;> subst h <;> refine ⟨_, ?_, rfl⟩ <;> intro τ v <;> rfl

/-- `total += e;` on a storage target: the target resolved and read once,
the right-hand side, the checked operator, the write back. -/
theorem opStore_sim {p : PrimTy} (hp : p ≠ .bool) {op : BinOp} (hop : op.hasCompoundAssign = true)
    {l : Solidity.Core.OpLoc C Γ p} {loc : Solidity.Core.Loc C Γ (.prim p)}
    (hl : opLocToLoc l = some loc) (r : Solidity.Core.Val C Γ p)
    (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m) (hwl : locIn F false loc = true)
    (hwr : valIn F r = true) :
    StmtOut C L b F false false false (Solidity.Core.Run.opAssign op l r σ)
      (run (compileLoc b loc ++ [.dup 1, .sload] ++ compileVal b r ++ binTail p op ++
        [.swap 1, .sstore]) m) m := by
  obtain ⟨hfrag, hand, hor, hret, hretTy⟩ := compound_frag hop hp
  simp only [Solidity.Core.Run.opAssign, opLoc_store hl, List.append_assoc]
  rcases loc_sim loc hm hwl with ⟨rt, segs, s, sv, hres, hsv, hps, hr, hrunl⟩ | ⟨hres, hrunl⟩
  · obtain ⟨old, hold, hrold, rfl⟩ := prim_read hr
    rw [run_append_ok hrunl,
      run_append_ok (m' := { m with stack := .val (m.store s) :: .slot s :: m.stack })
      (by simp [run, Instr.step, Machine.next, Machine.push])]
    rcases val_sim r (hm.stack _) hwr with ⟨vr, wr, hvr, hrv, hrunr⟩ | ⟨hvr, hrunr⟩
    · rw [run_append_ok hrunr]
      have ht := tail_sim hfrag hand hor hrold hrv { m with stack := .slot s :: m.stack }
      rw [hret, hretTy] at ht
      rcases ht with ⟨vn, wn, hvn, hrn, hrunt⟩ | ⟨hvn, hrunt⟩
      · obtain ⟨an, rfl, hnew⟩ := repr_write (L := L) hrn m.store s
        obtain ⟨stor, hsave, hrep⟩ := save_repr hm.store hps ⟨_, hsv⟩ hnew
          (fun x hx => upd_other _ _ fun he => hx (he ▸ Occ.prim))
        refine .inl ⟨σ.withGlob { σ.glob with storage := stor }, { m with store := upd m.store s an },
          ?_, ?_, rfl, Keeps.store (upd_len hps an), Sim.withGlob (hm.store' hrep (upd_len hps an))⟩
        · simp only [hvr, hres, Res.ok_bind, opStore, State.findStorage_of_findLive hsv, hold]
          rw [bind_bind_ok hvn, hsave]; rfl
        · change run (binTail p op ++ _)
            { m with stack := wr :: .val (m.store s) :: .slot s :: m.stack } = _
          rw [run_append_ok hrunt]; rfl
      · refine .inr ⟨?_, ?_⟩
        · simp only [hvr, hres, Res.ok_bind, opStore, State.findStorage_of_findLive hsv, hold]
          rw [bind_bind_error hvn]; rfl
        · change run (binTail p op ++ _)
            { m with stack := wr :: .val (m.store s) :: .slot s :: m.stack } = _
          rw [run_append_revert hrunt]
    · exact .inr ⟨by simp [hvr], run_append_revert hrunr⟩
  · rcases val_sim r hm hwr with ⟨vr, wr, hvr, _, _⟩ | ⟨hvr, _⟩
    · exact .inr ⟨by simp [hvr, hres], run_append_revert hrunl⟩
    · exact .inr ⟨by simp [hvr], run_append_revert hrunl⟩

/-- `x += e;` on a numeric local: its cell read, the checked operator, the
cell written. -/
theorem opLocal_sim {p : PrimTy} (hp : p ≠ .bool) {op : BinOp} (hop : op.hasCompoundAssign = true)
    (i : Idx Γ (.val p)) (r : Solidity.Core.Val C Γ p)
    (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m) (hwr : valIn F r = true) :
    StmtOut C L b F false false false (Solidity.Core.Run.opAssign op (.local i) r σ)
      (run ([.mload (cellOf b i)] ++ compileVal b r ++ binTail p op ++ [.mstore (cellOf b i)]) m)
      m := by
  obtain ⟨hfrag, hand, hor, hret, hretTy⟩ := compound_frag hop hp
  obtain ⟨old, henv, hrold⟩ := hm.vals i
  rw [Look.ofEnv_val, Binding.val.injEq] at henv
  simp only [List.append_assoc]
  rw [run_append_ok (m' := m.push (m.memAt (lvl b i))) rfl]
  rcases val_sim r (hm.push _) hwr with ⟨vr, wr, hvr, hrv, hrunr⟩ | ⟨hvr, hrunr⟩
  · rw [run_append_ok hrunr]
    have ht := tail_sim hfrag hand hor hrold hrv m
    rw [hret, hretTy] at ht
    rcases ht with ⟨vn, wn, hvn, hrn, hrunt⟩ | ⟨hvn, hrunt⟩
    · refine .inl ⟨σ.setLocal i vn, { m with mem := upd m.mem (cellOf b i) wn }, ?_, ?_, rfl,
        Keeps.upd (le_lvl b i) _, hm.setLocalVal i hrn⟩
      · simp only [Solidity.Core.Run.opAssign, hvr, Res.ok_bind, Solidity.Core.OpLoc.store,
          Solidity.Core.opLocal, henv]
        rw [bind_bind_ok' hvn]; rfl
      · change run (binTail p op ++ _) { m with stack := wr :: m.memAt (lvl b i) :: m.stack } = _
        rw [run_append_ok hrunt]; rfl
    · refine .inr ⟨?_, ?_⟩
      · simp only [Solidity.Core.Run.opAssign, hvr, Res.ok_bind, Solidity.Core.OpLoc.store,
          Solidity.Core.opLocal, henv]
        rw [bind_bind_error' hvn]
      · change run (binTail p op ++ _) { m with stack := wr :: m.memAt (lvl b i) :: m.stack } = _
        rw [run_append_revert hrunt]
  · exact .inr ⟨by simp [Solidity.Core.Run.opAssign, hvr], run_append_revert hrunr⟩

/-- `total++;` on a storage target: read once, the checked increment, the
write back. -/
theorem bumpStore_sim {p : PrimTy} (hp : p ≠ .bool) (op : IncDec) {l : Solidity.Core.OpLoc C Γ p}
    {loc : Solidity.Core.Loc C Γ (.prim p)} (hl : opLocToLoc l = some loc)
    (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m) (hwl : locIn F false loc = true) :
    StmtOut C L b F false false false (Solidity.Core.Run.incDec op l σ)
      (run (compileLoc b loc ++ [.dup 1, .sload, .push (.val 1)] ++ binTail p op.binOp ++
        [.swap 1, .sstore]) m) m := by
  obtain ⟨g, hg, hbump⟩ := opLoc_bump (σ := σ) hl op
  simp only [Solidity.Core.Run.incDec, hbump, List.append_assoc]
  rcases loc_sim loc hm hwl with ⟨rt, segs, s, sv, hres, hsv, hps, hr, hrunl⟩ | ⟨hres, hrunl⟩
  · obtain ⟨old, hold, hrold, rfl⟩ := prim_read hr
    obtain ⟨n, rfl, hv⟩ := bump_sim hp op hrold { m with stack := .slot s :: m.stack }
    rw [run_append_ok hrunl, show [Instr.dup 1, .sload, .push (.val 1)] ++ (binTail p op.binOp ++
        [.swap 1, .sstore]) = [Instr.dup 1, .sload] ++ (([.push (.val 1)] ++ binTail p op.binOp) ++
        [.swap 1, .sstore]) by simp,
      run_append_ok (m' := { m with stack := .val (m.store s) :: .slot s :: m.stack })
      (by simp [run, Instr.step, Machine.next, Machine.push])]
    rcases hv with ⟨vn, wn, hvn, hrn, hrunt⟩ | ⟨hvn, hrunt⟩
    · obtain ⟨an, rfl, hnew⟩ := repr_write (L := L) hrn m.store s
      obtain ⟨stor, hsave, hrep⟩ := save_repr hm.store hps ⟨_, hsv⟩ hnew
        (fun x hx => upd_other _ _ fun he => hx (he ▸ Occ.prim))
      refine .inl ⟨σ.withGlob { σ.glob with storage := stor }, { m with store := upd m.store s an },
        ?_, ?_, rfl, Keeps.store (upd_len hps an), Sim.withGlob (hm.store' hrep (upd_len hps an))⟩
      · simp only [hres, Res.ok_bind, bumpStore, State.findStorage_of_findLive hsv, hold,
          Value.asInt, hvn, hsave, Res.map_ok, Res.map_pure, hg]; rfl
      · rw [run_append_ok hrunt]; rfl
    · refine .inr ⟨?_, run_append_revert hrunt⟩
      simp only [hres, Res.ok_bind, bumpStore, State.findStorage_of_findLive hsv, hold,
        Value.asInt, hvn]; rfl
  · exact .inr ⟨by simp [hres], run_append_revert hrunl⟩

/-- `x++;` on a numeric local. -/
theorem bumpLocal_sim {p : PrimTy} (hp : p ≠ .bool) (op : IncDec) (i : Idx Γ (.val p))
    (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m) :
    StmtOut C L b F false false false (Solidity.Core.Run.incDec op (.local i) σ)
      (run ([.mload (cellOf b i), .push (.val 1)] ++ binTail p op.binOp ++ [.mstore (cellOf b i)]) m)
      m := by
  obtain ⟨old, henv, hrold⟩ := hm.vals i
  rw [Look.ofEnv_val, Binding.val.injEq] at henv
  obtain ⟨n, rfl, hv⟩ := bump_sim hp op hrold m
  rw [show [Instr.mload (cellOf b i), .push (.val 1)] ++ binTail p op.binOp ++
      [.mstore (cellOf b i)] = [Instr.mload (cellOf b i)] ++ (([.push (.val 1)] ++
      binTail p op.binOp) ++ [.mstore (cellOf b i)]) by simp,
    run_append_ok (m' := { m with stack := m.memAt (lvl b i) :: m.stack }) rfl]
  rcases hv with ⟨vn, wn, hvn, hrn, hrunt⟩ | ⟨hvn, hrunt⟩
  · refine .inl ⟨σ.setLocal i vn, { m with mem := upd m.mem (cellOf b i) wn }, ?_, ?_, rfl,
      Keeps.upd (le_lvl b i) _, hm.setLocalVal i hrn⟩
    · simp only [Solidity.Core.Run.incDec, Solidity.Core.OpLoc.bump, Solidity.Core.bumpLocal, henv,
        Res.ok_bind, Value.asInt, hvn]; rfl
    · rw [run_append_ok hrunt]; rfl
  · refine .inr ⟨?_, run_append_revert hrunt⟩
    simp only [Solidity.Core.Run.incDec, Solidity.Core.OpLoc.bump, Solidity.Core.bumpLocal, henv,
      Res.ok_bind, Value.asInt, hvn]; rfl

/-- `v = x++;` on a numeric local: `x`'s cell bumped, `v` given the old or the
new word. -/
theorem assignBumpLocal_sim {p : PrimTy} (hp : p ≠ .bool) (op : IncDec) (i j : Idx Γ (.val p))
    (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m) :
    StmtOut C L b F false false false (Solidity.Core.Run.assignIncDec i op (.local j) σ)
      (run ([.mload (cellOf b j)] ++ bumpCode p op ++ [.mstore (cellOf b j), .mstore (cellOf b i)]) m)
      m := by
  obtain ⟨old, henv, hrold⟩ := hm.vals j
  rw [Look.ofEnv_val, Binding.val.injEq] at henv
  obtain ⟨n, rfl, hv⟩ := bumpCode_sim hp op hrold m
  rw [List.append_assoc, run_append_ok (m' := { m with stack := m.memAt (lvl b j) :: m.stack }) rfl]
  rcases hv with ⟨vn, wn, hvn, hrn, hrunt⟩ | ⟨hvn, hrunt⟩
  · have hs := (hm.setLocalVal j hrn).setLocalVal i (v := if op.isPre then vn else .int n)
      (w := if op.isPre then wn else m.memAt (lvl b j)) (by cases op.isPre <;> simpa)
    have hk := Keeps.upd₂ (C := C) (sh := false) (m := m) (le_lvl b j) (le_lvl b i) wn
      (if op.isPre then wn else m.memAt (lvl b j))
    refine .inl ⟨_, _, ?_, ?_, ?_, hk, hs⟩
    rotate_left 2; · rfl
    · simp only [Solidity.Core.Run.assignIncDec, Solidity.Core.OpLoc.bump, Solidity.Core.bumpLocal,
        henv, Res.ok_bind, Value.asInt, hvn]; rfl
    · rw [run_append_ok hrunt]; rfl
  · refine .inr ⟨?_, run_append_revert hrunt⟩
    simp only [Solidity.Core.Run.assignIncDec, Solidity.Core.OpLoc.bump, Solidity.Core.bumpLocal,
      henv, Res.ok_bind, Value.asInt, hvn]; rfl

/-- `v = total++;`: the target bumped, `v` given the old or the new word. -/
theorem assignBumpStore_sim {p : PrimTy} (hp : p ≠ .bool) (op : IncDec) (i : Idx Γ (.val p))
    {l : Solidity.Core.OpLoc C Γ p} {loc : Solidity.Core.Loc C Γ (.prim p)}
    (hl : opLocToLoc l = some loc) (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m)
    (hwl : locIn F false loc = true) :
    StmtOut C L b F false false false (Solidity.Core.Run.assignIncDec i op l σ)
      (run (compileLoc b loc ++ [.dup 1, .sload] ++ bumpCode p op ++
        [.dup 3, .sstore, .swap 1, .pop, .mstore (cellOf b i)]) m) m := by
  obtain ⟨g, hg, hbump⟩ := opLoc_bump (σ := σ) hl op
  simp only [Solidity.Core.Run.assignIncDec, hbump, List.append_assoc]
  rcases loc_sim loc hm hwl with ⟨rt, segs, s, sv, hres, hsv, hps, hr, hrunl⟩ | ⟨hres, hrunl⟩
  · obtain ⟨old, hold, hrold, rfl⟩ := prim_read hr
    obtain ⟨n, rfl, hv⟩ := bumpCode_sim hp op hrold { m with stack := .slot s :: m.stack }
    rw [run_append_ok hrunl,
      run_append_ok (m' := { m with stack := .val (m.store s) :: .slot s :: m.stack })
      (by simp [run, Instr.step, Machine.next, Machine.push])]
    rcases hv with ⟨vn, wn, hvn, hrn, hrunt⟩ | ⟨hvn, hrunt⟩
    · obtain ⟨an, rfl, hnew⟩ := repr_write (L := L) hrn m.store s
      obtain ⟨stor, hsave, hrep⟩ := save_repr hm.store hps ⟨_, hsv⟩ hnew
        (fun x hx => upd_other _ _ fun he => hx (he ▸ Occ.prim))
      have hs := (Sim.withGlob (σ := σ) (hm.store' hrep (upd_len hps an))).setLocalVal i
        (v := if op.isPre then vn else .int n)
        (w := if op.isPre then .val an else .val (m.store s)) (by cases op.isPre <;> simpa)
      refine .inl ⟨(σ.withGlob { σ.glob with storage := stor }).setLocal i
          (if op.isPre then vn else .int n), { m with
          store := upd m.store s an
          mem := upd m.mem (cellOf b i) (if op.isPre then .val an else .val (m.store s)) },
        ?_, ?_, rfl, Keeps.storeUpd (le_lvl b i) _ (upd_len hps an), hs⟩
      · simp only [hres, Res.ok_bind, bumpStore, State.findStorage_of_findLive hsv, hold,
          Value.asInt, hvn, hsave, Res.map_ok, Res.map_pure, hg]; rfl
      · simp only at hrunt
        rw [run_append_ok hrunt]
        simp [run, Instr.step, Machine.next]
    · refine .inr ⟨?_, run_append_revert hrunt⟩
      simp only [hres, Res.ok_bind, bumpStore, State.findStorage_of_findLive hsv, hold,
        Value.asInt, hvn]; rfl
  · exact .inr ⟨by simp [hres], run_append_revert hrunl⟩

end Stmts

end Core
end Solidity.Evm
