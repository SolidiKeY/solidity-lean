import Solidity.Evm.CoreExpr

/-!
# Statements over the typed run

One lemma per statement of the fragment (`docs/intrinsic.md`, M5, W1): the
statement's step (`Semantics/Core/TypedRun.lean`'s `TRun.*`) and its code
(`Evm/CoreCompile.lean`) agree, as `StmtOut` says.  A storage write is the
untyped one's (`Evm/Repr.lean`'s `save_repr`) read back typed through its
agreement (`Storage.saveStorage_erase`, `into_ok`).  `stmt_sim`
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

open Semantics
open SemanticsProperties
open Solidity.Core (Ctx Idx Ext TEnv TState SRef TRes HTy)

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
typed run panics (a failed `assert`, solc's `Panic(0x01)`), only in code
that `asserts`, where the machine reverts; or the machine reverts because
the world refused a payment — only code that `pays` has one — and the
typed run succeeds in a state some machine represents, the one where the
world had paid. -/
inductive StmtOut (C : Contract) (L b : Nat) {Γ' : Ctx} (F' : Frag Γ') (sh pays asserts : Bool)
    {H : HTy} (res : TRes (Solidity.Core.Out C H Γ')) (out : Out) (m : Machine) : Prop where
  | inl (h : ∃ o m', res = .ok o ∧ out = .ok m' 0 ∧ m'.stack = m.stack ∧ Keeps C b sh m m' ∧
      Sim C L b F' o.st.sem (Look.ofTEnv o.st.env) m')
  | inr (h : res = .error .revert ∧ out = .revert)
  | panic (ha : asserts = true) (h : res = .error .panic ∧ out = .revert)
  | refused (hp : pays = true) (h : out = .revert ∧ ∃ o m', res = .ok o ∧ Keeps C b sh m m' ∧
      Sim C L b F' o.st.sem (Look.ofTEnv o.st.env) m')

/-- `StmtOut` under a looser bound on the arrays. -/
theorem StmtOut.mono {L b : Nat} {Γ' : Ctx} {F' : Frag Γ'} {sh pays asserts : Bool} {H : HTy}
    {res : TRes (Solidity.Core.Out C H Γ')} {out : Out} {m : Machine} {L' : Nat}
    (h : StmtOut C L b F' sh pays asserts res out m) (hL : L ≤ L') (hL' : L' ≤ Lmax) :
    StmtOut C L' b F' sh pays asserts res out m := by
  rcases h with ⟨o, m', h1, h2, h3, h4, h5⟩ | h | ⟨ha, h⟩ | ⟨hp, h1, o, m', h2, h4, h5⟩
  · exact .inl ⟨o, m', h1, h2, h3, h4, h5.mono hL hL'⟩
  · exact .inr h
  · exact .panic ha h
  · exact .refused hp ⟨h1, o, m', h2, h4, h5.mono hL hL'⟩

/-! ## Typed and untyped operations -/

section Agree

variable {Γ : Ctx}

/-- A storage operation the untyped side completed, typed: the typed state
over the new storage is the untyped one. -/
theorem into_ok {σ : TState C Γ} {o : Option (Solidity.Core.Storage C)}
    {stor : List (Name × SVal)}
    (h : Solidity.Core.toRes (Solidity.Core.Storage.into σ.sem) o =
      .ok { σ.sem with storage := stor }) :
    ∃ st', o = some st' ∧ (σ.withStorage st').sem = { σ.sem with storage := stor } := by
  cases o with
  | none => cases h
  | some st' =>
    refine ⟨st', rfl, ?_⟩
    simp only [Solidity.Core.toRes, Except.ok.injEq] at h
    rw [← h]; rfl

theorem toRes_none {α β : Type} {f : α → β} {o : Option α} {e : Halt}
    (h : Solidity.Core.toRes f o = .error e) : o = none := by
  cases o with
  | none => rfl
  | some _ => cases h

/-- A word stored, erased. -/
theorem toSVal_erase {p : PrimTy} (x : p.Denote) :
    (PrimTy.erase x).toSVal = (Solidity.Core.SVal.prim x).erase := by
  rw [Solidity.Core.SVal.erase_prim]; cases p <;> rfl

theorem erase_numeric {p : PrimTy} (hp : p.isNumeric = true) (x : p.Denote) :
    PrimTy.erase x = .int (PrimTy.key x) := by
  cases p <;> first | rfl | cases hp

/-- `a ⊕= b`'s operator, checked: `compoundT` erased. -/
theorem compound_erase {op : BinOp} (hop : op.hasCompoundAssign = true) {p : PrimTy}
    (hp : p.isNumeric = true) (x y : p.Denote) :
    (applyBinOp op (PrimTy.erase x) (PrimTy.erase y) >>= checkArith (.prim p)) =
      Solidity.Core.toRes PrimTy.erase
        (Solidity.Core.compoundT op p (PrimTy.key x) (PrimTy.key y)) := by
  have hA : op.isArith = true := by
    cases op <;> simp only [BinOp.hasCompoundAssign, Bool.false_eq_true] at hop <;> rfl
  rw [erase_numeric hp x, erase_numeric hp y, BinOp.applyBinOp_int hA]
  unfold Solidity.Core.compoundT
  cases BinOp.arithInt op (PrimTy.key x) (PrimTy.key y) with
  | none => rfl
  | some n => exact PrimTy.checkArith_ofInt hp n

/-- `x++`'s new value, checked: `bumpT` erased. -/
theorem bump_erase {p : PrimTy} (hp : p.isNumeric = true) (op : IncDec) (x : Int) :
    checkArith (.prim p) (.int (if op.isIncrement then x + 1 else x - 1)) =
      Solidity.Core.toRes PrimTy.erase (Solidity.Core.bumpT op p x) :=
  PrimTy.checkArith_ofInt hp _

/-- An untyped outcome read off a typed `Option`. -/
theorem ValOut.toRes_cases {p : PrimTy} {o : Option p.Denote} {out : Out} {m : Machine}
    (h : ValOut p (Solidity.Core.toRes PrimTy.erase o) out m) :
    (∃ v w, o = some v ∧ ReprV p (PrimTy.erase v) w ∧ out = .ok (m.push w) 0) ∨
      (o = none ∧ out = .revert) := by
  cases o with
  | none =>
    rcases h with ⟨_, _, h, _⟩ | ⟨_, h⟩
    · cases h
    · exact .inr ⟨rfl, h⟩
  | some v =>
    rcases h with ⟨v', w, h, hr, hout⟩ | ⟨h, _⟩
    · cases h; exact .inl ⟨v, w, rfl, hr, hout⟩
    · cases h

/-- A word read from storage, typed. -/
theorem prim_find {σ : TState C Γ} {p : PrimTy} {r : SRef C (.prim p)} {old : Value}
    (hsv : σ.sem.findLive r.root r.path.erase = .ok old.toSVal) (hold : old.toSVal.asValue = .ok old) :
    ∃ told, σ.storage.find r = some told ∧ old = PrimTy.erase (Solidity.Core.SVal.view told) := by
  obtain ⟨told, hf, ht⟩ := find_of_findLive hsv
  refine ⟨told, hf, ?_⟩
  have := asValue_erase_prim told
  rw [ht, hold] at this
  exact Except.ok.inj this

end Agree

/-! ## The state's locals and storage, changed -/

section States

variable {L b : Nat} {Γ : Ctx} {F : Frag Γ} {σ : TState C Γ} {m : Machine}

/-- The storage replaced. -/
theorem Sim.withStore {st : Solidity.Core.Storage C} {τ : State} (hτ : (σ.withStorage st).sem = τ)
    (h : Sim C L b F τ (Look.ofTEnv σ.env) m) :
    Sim C L b F (σ.withStorage st).sem (Look.ofTEnv (σ.withStorage st).env) m := by
  rw [hτ]; exact h

/-- `x = e;` on a value local. -/
theorem Sim.setLocalVal (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) {p : PrimTy}
    (i : Idx Γ (.val p)) {v : p.Denote} {w : Word} (hv : ReprV p (PrimTy.erase v) w) :
    Sim C L b F (σ.setLocal i v).sem (Look.ofTEnv (σ.setLocal i v).env)
      { m with mem := upd m.mem (cellOf b i) w } :=
  (hm.setVal i hv).congrLook fun j => Look.ofTEnv_set i v σ.env j

/-- `uint x = e;`. -/
theorem Sim.pushVal (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) {p : PrimTy} {v : p.Denote}
    {w : Word} (hv : ReprV p (PrimTy.erase v) w) :
    Sim C L b (F.push (.val p) .ok) (σ.push (t := .val p) v).sem
      (Look.ofTEnv (σ.push (t := .val p) v).env)
      { m with mem := upd m.mem (cell (b + Γ.length)) w } :=
  (hm.consVal hv).congrLook fun j => Look.ofTEnv_cons (u := .val p) v σ.env j

/-- `p = q;` with `q` indexing no array. -/
theorem Sim.setAliasE (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) {R : RefTy}
    (i : Idx Γ (.alias R)) {r : SRef C (.ref R)} {s : Slot}
    (hp : PathSlot C true r.root r.path.erase (.ref R) s) :
    Sim C L b (F.set i .ok) (σ.setLocal i (some r)).sem
      (Look.ofTEnv (σ.setLocal i (some r)).env)
      { m with mem := upd m.mem (cellOf b i) (.slot s) } :=
  (hm.setAlias i hp).congrLook fun j => Look.ofTEnv_set i (some r) σ.env j

/-- `p = persons[i];`. -/
theorem Sim.setFragileE (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) {R : RefTy}
    (i : Idx Γ (.alias R)) {r : SRef C (.ref R)} {s : Slot}
    (hp : PathSlot C false r.root r.path.erase (.ref R) s)
    (hlive : ∃ sv, σ.sem.findLive r.root r.path.erase = .ok sv) :
    Sim C L b (F.set i .fragile) (σ.setLocal i (some r)).sem
      (Look.ofTEnv (σ.setLocal i (some r)).env)
      { m with mem := upd m.mem (cellOf b i) (.slot s) } :=
  (hm.setFragile i hp hlive).congrLook fun j => Look.ofTEnv_set i (some r) σ.env j

/-- `Person storage p = q;` with `q` indexing no array. -/
theorem Sim.pushAlias (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) {R : RefTy}
    {r : SRef C (.ref R)} {s : Slot} (hp : PathSlot C true r.root r.path.erase (.ref R) s) :
    Sim C L b (F.push (.alias R) .ok) (σ.push (t := .alias R) (some r)).sem
      (Look.ofTEnv (σ.push (t := .alias R) (some r)).env)
      { m with mem := upd m.mem (cell (b + Γ.length)) (.slot s) } :=
  (hm.consAlias hp).congrLook fun j => Look.ofTEnv_cons (u := .alias R) (some r) σ.env j

/-- `Person storage p = persons[i];`. -/
theorem Sim.pushFragile (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) {R : RefTy}
    {r : SRef C (.ref R)} {s : Slot} (hp : PathSlot C false r.root r.path.erase (.ref R) s)
    (hlive : ∃ sv, σ.sem.findLive r.root r.path.erase = .ok sv) :
    Sim C L b (F.push (.alias R) .fragile) (σ.push (t := .alias R) (some r)).sem
      (Look.ofTEnv (σ.push (t := .alias R) (some r)).env)
      { m with mem := upd m.mem (cell (b + Γ.length)) (.slot s) } :=
  (hm.consFragile hp hlive).congrLook fun j =>
    Look.ofTEnv_cons (u := .alias R) (some r) σ.env j

/-- `Person storage p;`. -/
theorem Sim.pushDead (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) (R : RefTy)
    (v : Option (SRef C (.ref R))) :
    Sim C L b (F.push (.alias R) .dead) (σ.push (t := .alias R) v).sem
      (Look.ofTEnv (σ.push (t := .alias R) v).env) m :=
  (hm.consDead R v).congrLook fun j => Look.ofTEnv_cons (u := .alias R) v σ.env j

end States

/-! ## Assignments and declarations -/

section Stmts

variable {L b : Nat} {Γ : Ctx} {F : Frag Γ} {σ : TState C Γ} {m : Machine}

/-- `alice.age = 10;`: the value, the slot, the write. -/
theorem assign_sim {p : PrimTy} (l : Solidity.Core.Loc C Γ (.prim p))
    (v : Solidity.Core.Val C Γ p) (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m)
    (hwl : locIn F false l = true) (hwv : valIn F v = true) :
    StmtOut C L b F false false false (Solidity.Core.TRun.assign l (.val v) σ)
      (run (compileVal b v ++ compileLoc b l ++ [.sstore]) m) m := by
  simp only [List.append_assoc]
  rcases val_sim v hm hwv with ⟨vv, w, hvv, hrv, hrun⟩ | ⟨hvv, hrun⟩
  · rw [run_append_ok hrun]
    rcases loc_sim l (hm.push w) hwl with ⟨r, s, sv, hres, hsv, hps, _, hrunl⟩ | ⟨hres, hrunl⟩
    · rw [run_append_ok hrunl]
      obtain ⟨a, rfl, hnew⟩ := repr_write (L := L) hrv m.store s
      obtain ⟨stor, hsave, hrep⟩ := save_repr hm.store hps ⟨sv, hsv⟩ hnew
        (fun x hx => upd_other _ _ fun he => hx (he ▸ Occ.prim))
      rw [toSVal_erase, Solidity.Core.Storage.saveStorage_erase (σ := σ.sem) rfl] at hsave
      obtain ⟨st', hst', hsem⟩ := into_ok hsave
      refine .inl ⟨⟨σ.withStorage st', List.prefix_refl _⟩, { m with store := upd m.store s a },
        ?_, rfl, rfl, Keeps.store (upd_len hps a),
        Sim.withStore hsem (hm.store' hrep (upd_len hps a))⟩
      simp only [Solidity.Core.TRun.assign, Solidity.Core.Src.valueT, hvv, hres, bind,
        Except.bind, pure, Except.pure, Solidity.Core.Storage.write, Solidity.Core.SVal.isPrim,
        Ty.isPrimitive, ↓reduceIte, hst', TRes.ofOpt]
    · exact .inr ⟨by simp only [Solidity.Core.TRun.assign, Solidity.Core.Src.valueT, hvv, hres,
        bind, Except.bind, pure, Except.pure], run_append_revert hrunl⟩
  · exact .inr ⟨by simp only [Solidity.Core.TRun.assign, Solidity.Core.Src.valueT, hvv, bind,
      Except.bind], run_append_revert hrun⟩

/-- `x = e;` on a value local. -/
theorem assignLocal_sim {p : PrimTy} (i : Idx Γ (.val p)) (r : Solidity.Core.Val C Γ p)
    (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) (hwr : valIn F r = true) :
    StmtOut C L b F false false false (Solidity.Core.TRun.assignLocal i r σ)
      (run (compileVal b r ++ [.mstore (cellOf b i)]) m) m := by
  rcases val_sim r hm hwr with ⟨v, w, hv, hrv, hrun⟩ | ⟨hv, hrun⟩
  · refine .inl ⟨⟨σ.setLocal i v, List.prefix_refl _⟩, { m with mem := upd m.mem (cellOf b i) w },
      by simp only [Solidity.Core.TRun.assignLocal, hv, bind, Except.bind, pure, Except.pure], ?_,
      rfl, Keeps.upd (le_lvl b i) w, hm.setLocalVal i hrv⟩
    rw [run_append_ok hrun]; rfl
  · exact .inr ⟨by simp only [Solidity.Core.TRun.assignLocal, hv, bind, Except.bind],
      run_append_revert hrun⟩

/-- `uint x = e;` (or `uint x;`, the default). -/
theorem declLocal_sim (p : PrimTy) (init : Option (Solidity.Core.Val C Γ p))
    (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) (hw : init.all (valIn F) = true) :
    StmtOut C L b (F.push (.val p) .ok) false false false (Solidity.Core.TRun.declLocal p init σ)
      (run (match init with
        | none => [.push (.val 0), .mstore (cell (b + Γ.length))]
        | some e => compileVal b e ++ [.mstore (cell (b + Γ.length))]) m) m := by
  cases init with
  | none =>
    exact .inl ⟨⟨σ.push (t := .val p) (PrimTy.dflt p), List.prefix_refl _⟩,
      { m with mem := upd m.mem (cell (b + Γ.length)) (.val 0) }, rfl, rfl, rfl,
      Keeps.upd (Nat.le_add_right b _) _,
      hm.pushVal (by rw [PrimTy.erase_dflt]; exact ReprV.default p)⟩
  | some e =>
    simp only [Option.all_some] at hw
    rcases val_sim e hm hw with ⟨v, w, hv, hrv, hrun⟩ | ⟨hv, hrun⟩
    · refine .inl ⟨⟨σ.push (t := .val p) v, List.prefix_refl _⟩,
        { m with mem := upd m.mem (cell (b + Γ.length)) w },
        by simp only [Solidity.Core.TRun.declLocal, hv, bind, Except.bind, pure, Except.pure], ?_,
        rfl, Keeps.upd (Nat.le_add_right b _) _, hm.pushVal hrv⟩
      rw [run_append_ok hrun]; rfl
    · exact .inr ⟨by simp only [Solidity.Core.TRun.declLocal, hv, bind, Except.bind],
        run_append_revert hrun⟩

/-- `p = q;`: an alias rebound, plain or fragile as `q` indexes an array. -/
theorem rebind_sim {R : RefTy} (i : Idx Γ (.alias R)) (q : Solidity.Core.SPath C Γ (.ref R))
    {F' : Frag Γ} (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m)
    (hw : (bindFl F q).map (F.set i) = some F') :
    StmtOut C L b F' false false false (Solidity.Core.TRun.rebind i (.path q) σ)
      (run (compileSPath b q ++ [.mstore (cellOf b i)]) m) m := by
  unfold bindFl at hw
  by_cases h1 : spathIn F true q = true
  · rw [if_pos h1] at hw; cases hw
    rcases spath_sim q hm h1 with ⟨r, s, sv, hres, _, hp, _, hrun⟩ | ⟨hres, hrun⟩
    · refine .inl ⟨⟨σ.setLocal i (some r), List.prefix_refl _⟩,
        { m with mem := upd m.mem (cellOf b i) (.slot s) }, ?_, ?_, rfl,
        Keeps.upd (le_lvl b i) _, hm.setAliasE i hp⟩
      · simp only [Solidity.Core.TRun.rebind, Solidity.Core.ARhs.evalT, hres, bind, Except.bind,
          pure, Except.pure]; rfl
      · rw [run_append_ok hrun]; rfl
    · exact .inr ⟨by simp only [Solidity.Core.TRun.rebind, Solidity.Core.ARhs.evalT, hres, bind,
        Except.bind], run_append_revert hrun⟩
  · rw [if_neg h1] at hw
    by_cases h2 : spathIn F false q = true
    · rw [if_pos h2] at hw; cases hw
      rcases spath_sim q hm h2 with ⟨r, s, sv, hres, hsv, hp, _, hrun⟩ | ⟨hres, hrun⟩
      · refine .inl ⟨⟨σ.setLocal i (some r), List.prefix_refl _⟩,
          { m with mem := upd m.mem (cellOf b i) (.slot s) }, ?_, ?_, rfl,
          Keeps.upd (le_lvl b i) _, hm.setFragileE i hp ⟨sv, hsv⟩⟩
        · simp only [Solidity.Core.TRun.rebind, Solidity.Core.ARhs.evalT, hres, bind, Except.bind,
            pure, Except.pure]; rfl
        · rw [run_append_ok hrun]; rfl
      · exact .inr ⟨by simp only [Solidity.Core.TRun.rebind, Solidity.Core.ARhs.evalT, hres, bind,
          Except.bind], run_append_revert hrun⟩
    · rw [if_neg h2] at hw; cases hw

/-- `Person storage p = q;`, plain or fragile as `q` indexes an array. -/
theorem declAlias_sim {R : RefTy} (q : Solidity.Core.SPath C Γ (.ref R))
    {F' : Frag (.alias R :: Γ)} (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m)
    (hw : (bindFl F q).map (F.push (.alias R)) = some F') :
    StmtOut C L b F' false false false (Solidity.Core.TRun.declStorage R (some (.path q)) σ)
      (run (compileSPath b q ++ [.mstore (cell (b + Γ.length))]) m) m := by
  unfold bindFl at hw
  by_cases h1 : spathIn F true q = true
  · rw [if_pos h1] at hw; cases hw
    rcases spath_sim q hm h1 with ⟨r, s, sv, hres, _, hp, _, hrun⟩ | ⟨hres, hrun⟩
    · refine .inl ⟨⟨σ.push (t := .alias R) (some r), List.prefix_refl _⟩,
        { m with mem := upd m.mem (cell (b + Γ.length)) (.slot s) }, ?_, ?_, rfl,
        Keeps.upd (Nat.le_add_right b _) _, hm.pushAlias hp⟩
      · simp only [Solidity.Core.TRun.declStorage, Solidity.Core.ARhs.evalT, hres, bind,
          Except.bind, pure, Except.pure]; rfl
      · rw [run_append_ok hrun]; rfl
    · exact .inr ⟨by simp only [Solidity.Core.TRun.declStorage, Solidity.Core.ARhs.evalT, hres,
        bind, Except.bind], run_append_revert hrun⟩
  · rw [if_neg h1] at hw
    by_cases h2 : spathIn F false q = true
    · rw [if_pos h2] at hw; cases hw
      rcases spath_sim q hm h2 with ⟨r, s, sv, hres, hsv, hp, _, hrun⟩ | ⟨hres, hrun⟩
      · refine .inl ⟨⟨σ.push (t := .alias R) (some r), List.prefix_refl _⟩,
          { m with mem := upd m.mem (cell (b + Γ.length)) (.slot s) }, ?_, ?_, rfl,
          Keeps.upd (Nat.le_add_right b _) _, hm.pushFragile hp ⟨sv, hsv⟩⟩
        · simp only [Solidity.Core.TRun.declStorage, Solidity.Core.ARhs.evalT, hres, bind,
            Except.bind, pure, Except.pure]; rfl
        · rw [run_append_ok hrun]; rfl
      · exact .inr ⟨by simp only [Solidity.Core.TRun.declStorage, Solidity.Core.ARhs.evalT, hres,
          bind, Except.bind], run_append_revert hrun⟩
    · rw [if_neg h2] at hw; cases hw

/-- `require(c);` reverts on `false`; `assert(c);` panics. -/
theorem require_sim (c : Solidity.Core.Val C Γ .bool)
    (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) (hwc : valIn F c = true) :
    StmtOut C L b F false false false (Solidity.Core.TRun.require c σ)
      (run (compileVal b c ++ assertTop) m) m := by
  rcases val_sim c hm hwc with ⟨vc, wc, hvc, hrc, hrunc⟩ | ⟨hvc, hrunc⟩
  · obtain ⟨x, hx, rfl⟩ := hrc.bool_inv
    obtain rfl : vc = x := Semantics.PrimVal.bool.inj hx
    cases vc
    · exact .inr ⟨by simp only [Solidity.Core.TRun.require, hvc, bind, Except.bind,
        Solidity.Core.boolT, Bool.false_eq_true, ↓reduceIte], by rw [run_append_skip hrunc]; rfl⟩
    · exact .inl ⟨⟨σ, List.prefix_refl _⟩, m, by simp only [Solidity.Core.TRun.require, hvc, bind,
        Except.bind, Solidity.Core.boolT, ↓reduceIte, pure, Except.pure],
        by rw [run_append_skip hrunc]; rfl, rfl, Keeps.refl m, hm⟩
  · exact .inr ⟨by simp only [Solidity.Core.TRun.require, hvc, bind, Except.bind],
      run_append_revert hrunc⟩

theorem assert_sim (c : Solidity.Core.Val C Γ .bool)
    (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) (hwc : valIn F c = true) :
    StmtOut C L b F false false true (Solidity.Core.TRun.assert c σ)
      (run (compileVal b c ++ assertTop) m) m := by
  rcases val_sim c hm hwc with ⟨vc, wc, hvc, hrc, hrunc⟩ | ⟨hvc, hrunc⟩
  · obtain ⟨x, hx, rfl⟩ := hrc.bool_inv
    obtain rfl : vc = x := Semantics.PrimVal.bool.inj hx
    cases vc
    · exact .panic rfl ⟨by simp only [Solidity.Core.TRun.assert, hvc, bind, Except.bind,
        Solidity.Core.boolT, Bool.false_eq_true, ↓reduceIte], by rw [run_append_skip hrunc]; rfl⟩
    · exact .inl ⟨⟨σ, List.prefix_refl _⟩, m, by simp only [Solidity.Core.TRun.assert, hvc, bind,
        Except.bind, Solidity.Core.boolT, ↓reduceIte, pure, Except.pure],
        by rw [run_append_skip hrunc]; rfl, rfl, Keeps.refl m, hm⟩
  · exact .inr ⟨by simp only [Solidity.Core.TRun.assert, hvc, bind, Except.bind],
      run_append_revert hrunc⟩

/-! ## Compound assignments and `++` -/

/-- An `op=` on a storage target resolves the target once. -/
theorem opLocT_store {p : PrimTy} {l : Solidity.Core.OpLoc C Γ p}
    {loc : Solidity.Core.Loc C Γ (.prim p)} (h : opLocToLoc l = some loc) (op : BinOp)
    (v : p.Denote) :
    l.storeT σ op v = (loc.resolveT σ >>= fun r => Solidity.Core.opStoreT σ op r v) := by
  cases l <;> simp only [opLocToLoc, reduceCtorEq, Option.some.injEq] at h <;> subst h <;> rfl

/-- `++` on a storage target resolves it once. -/
theorem opLocT_bump {p : PrimTy} {l : Solidity.Core.OpLoc C Γ p}
    {loc : Solidity.Core.Loc C Γ (.prim p)} (h : opLocToLoc l = some loc) (op : IncDec) :
    l.bumpT σ op = (loc.resolveT σ >>= fun r => Solidity.Core.bumpStoreT σ op r) := by
  cases l <;> simp only [opLocToLoc, reduceCtorEq, Option.some.injEq] at h <;> subst h <;> rfl

theorem numeric_of_ne {p : PrimTy} (hp : p ≠ .bool) : p.isNumeric = true := by
  cases p <;> first | rfl | exact absurd rfl hp

/-- `total += e;` on a storage target: the target resolved and read once,
the right-hand side, the checked operator, the write back. -/
theorem opStore_sim {p : PrimTy} (hp : p ≠ .bool) {op : BinOp} (hop : op.hasCompoundAssign = true)
    {l : Solidity.Core.OpLoc C Γ p} {loc : Solidity.Core.Loc C Γ (.prim p)}
    (hl : opLocToLoc l = some loc) (r : Solidity.Core.Val C Γ p)
    (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) (hwl : locIn F false loc = true)
    (hwr : valIn F r = true) :
    StmtOut C L b F false false false (Solidity.Core.TRun.opAssign op l r σ)
      (run (compileLoc b loc ++ [.dup 1, .sload] ++ compileVal b r ++ binTail p op ++
        [.swap 1, .sstore]) m) m := by
  obtain ⟨hfrag, hand, hor, hret, hretTy⟩ := compound_frag hop hp
  have hpn := numeric_of_ne hp
  simp only [List.append_assoc]
  rcases loc_sim loc hm hwl with ⟨rt, s, sv, hres, hsv, hps, hr, hrunl⟩ | ⟨hres, hrunl⟩
  · obtain ⟨old, hold, hrold, rfl⟩ := prim_read hr
    obtain ⟨told, hf, rfl⟩ := prim_find hsv hold
    rw [run_append_ok hrunl,
      run_append_ok (m' := { m with stack := .val (m.store s) :: .slot s :: m.stack })
      (by simp only [run, Machine.push, exec_cons_zero, Instr.step, Nat.sub_self, List.length_cons,
          Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero, Machine.next, Out.ok_bind,
          exec_nil])]
    rcases val_sim r (hm.stack _) hwr with ⟨vr, wr, hvr, hrv, hrunr⟩ | ⟨hvr, hrunr⟩
    · rw [run_append_ok hrunr]
      have ht := tail_sim hfrag hand hor hrold hrv { m with stack := .slot s :: m.stack }
      rw [hret, hretTy, compound_erase hop hpn] at ht
      rcases ValOut.toRes_cases ht with ⟨vn, wn, hc, hrn, hrunt⟩ | ⟨hc, hrunt⟩
      · obtain ⟨an, rfl, hnew⟩ := repr_write (L := L) hrn m.store s
        obtain ⟨stor, hsave, hrep⟩ := save_repr hm.store hps ⟨_, hsv⟩ hnew
          (fun x hx => upd_other _ _ fun he => hx (he ▸ Occ.prim))
        rw [toSVal_erase, Solidity.Core.Storage.saveStorage_erase (σ := σ.sem) rfl] at hsave
        obtain ⟨st', hst', hsem⟩ := into_ok hsave
        refine .inl ⟨⟨σ.withStorage st', List.prefix_refl _⟩, { m with store := upd m.store s an },
          ?_, ?_, rfl, Keeps.store (upd_len hps an),
          Sim.withStore hsem (hm.store' hrep (upd_len hps an))⟩
        · simp only [Solidity.Core.TRun.opAssign, hvr, opLocT_store hl, hres,
            Solidity.Core.opStoreT, hf, hc, hst', bind, Except.bind, TRes.ofOpt, pure,
            Except.pure]
        · change run (binTail p op ++ _)
            { m with stack := wr :: .val (m.store s) :: .slot s :: m.stack } = _
          rw [run_append_ok hrunt]; rfl
      · refine .inr ⟨?_, ?_⟩
        · simp only [Solidity.Core.TRun.opAssign, hvr, opLocT_store hl, hres,
            Solidity.Core.opStoreT, hf, hc, bind, Except.bind, TRes.ofOpt]
        · change run (binTail p op ++ _)
            { m with stack := wr :: .val (m.store s) :: .slot s :: m.stack } = _
          rw [run_append_revert hrunt]
    · exact .inr ⟨by simp only [Solidity.Core.TRun.opAssign, hvr, bind, Except.bind],
        run_append_revert hrunr⟩
  · rcases val_sim r hm hwr with ⟨vr, wr, hvr, _, _⟩ | ⟨hvr, _⟩
    · exact .inr ⟨by simp only [Solidity.Core.TRun.opAssign, hvr, opLocT_store hl, hres, bind,
        Except.bind], run_append_revert hrunl⟩
    · exact .inr ⟨by simp only [Solidity.Core.TRun.opAssign, hvr, bind, Except.bind],
        run_append_revert hrunl⟩

/-- `x += e;` on a numeric local: its cell read, the checked operator, the
cell written. -/
theorem opLocal_sim {p : PrimTy} (hp : p ≠ .bool) {op : BinOp} (hop : op.hasCompoundAssign = true)
    (i : Idx Γ (.val p)) (r : Solidity.Core.Val C Γ p)
    (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) (hwr : valIn F r = true) :
    StmtOut C L b F false false false (Solidity.Core.TRun.opAssign op (.local i) r σ)
      (run ([.mload (cellOf b i)] ++ compileVal b r ++ binTail p op ++ [.mstore (cellOf b i)]) m)
      m := by
  obtain ⟨hfrag, hand, hor, hret, hretTy⟩ := compound_frag hop hp
  have hpn := numeric_of_ne hp
  have hrold := hm.vals i
  simp only [List.append_assoc]
  rw [run_append_ok (m' := m.push (m.memAt (lvl b i))) rfl]
  rcases val_sim r (hm.push _) hwr with ⟨vr, wr, hvr, hrv, hrunr⟩ | ⟨hvr, hrunr⟩
  · rw [run_append_ok hrunr]
    have ht := tail_sim hfrag hand hor hrold hrv m
    rw [hret, hretTy, compound_erase hop hpn] at ht
    rcases ValOut.toRes_cases ht with ⟨vn, wn, hc, hrn, hrunt⟩ | ⟨hc, hrunt⟩
    · refine .inl ⟨⟨σ.setLocal i vn, List.prefix_refl _⟩,
        { m with mem := upd m.mem (cellOf b i) wn }, ?_, ?_, rfl,
        Keeps.upd (le_lvl b i) _, hm.setLocalVal i hrn⟩
      · simp only [Solidity.Core.TRun.opAssign, hvr, Solidity.Core.OpLoc.storeT, bind,
          Except.bind, TRes.ofOpt, pure, Except.pure]
        rw [show Look.ofTEnv σ.env i = TEnv.get i σ.env from rfl] at hc
        rw [hc]
      · change run (binTail p op ++ _) { m with stack := wr :: m.memAt (lvl b i) :: m.stack } = _
        rw [run_append_ok hrunt]; rfl
    · refine .inr ⟨?_, ?_⟩
      · simp only [Solidity.Core.TRun.opAssign, hvr, Solidity.Core.OpLoc.storeT, bind,
          Except.bind, TRes.ofOpt]
        rw [show Look.ofTEnv σ.env i = TEnv.get i σ.env from rfl] at hc
        rw [hc]
      · change run (binTail p op ++ _) { m with stack := wr :: m.memAt (lvl b i) :: m.stack } = _
        rw [run_append_revert hrunt]
  · exact .inr ⟨by simp only [Solidity.Core.TRun.opAssign, hvr, bind, Except.bind],
      run_append_revert hrunr⟩

/-- `x++`'s operand, read off its word: the key the typed run bumps. -/
theorem bump_key {p : PrimTy} (hpn : p.isNumeric = true) {x : p.Denote} {n : Int}
    (h : PrimTy.erase x = .int n) : PrimTy.key x = n := by
  rw [erase_numeric hpn] at h
  exact Semantics.PrimVal.int.inj h

/-- `total++;` on a storage target: read once, the checked increment, the
write back. -/
theorem bumpStore_sim {p : PrimTy} (hp : p ≠ .bool) (op : IncDec) {l : Solidity.Core.OpLoc C Γ p}
    {loc : Solidity.Core.Loc C Γ (.prim p)} (hl : opLocToLoc l = some loc)
    (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) (hwl : locIn F false loc = true) :
    StmtOut C L b F false false false (Solidity.Core.TRun.incDec op l σ)
      (run (compileLoc b loc ++ [.dup 1, .sload, .push (.val 1)] ++ binTail p op.binOp ++
        [.swap 1, .sstore]) m) m := by
  have hpn := numeric_of_ne hp
  simp only [List.append_assoc]
  rcases loc_sim loc hm hwl with ⟨rt, s, sv, hres, hsv, hps, hr, hrunl⟩ | ⟨hres, hrunl⟩
  · obtain ⟨old, hold, hrold, rfl⟩ := prim_read hr
    obtain ⟨told, hf, rfl⟩ := prim_find hsv hold
    obtain ⟨n, hn, hv⟩ := bump_sim hp op hrold { m with stack := .slot s :: m.stack }
    rw [bump_erase hpn, ← bump_key hpn hn] at hv
    rw [run_append_ok hrunl, show [Instr.dup 1, .sload, .push (.val 1)] ++ (binTail p op.binOp ++
        [.swap 1, .sstore]) = [Instr.dup 1, .sload] ++ (([.push (.val 1)] ++ binTail p op.binOp) ++
        [.swap 1, .sstore]) by simp only [List.cons_append, List.nil_append],
      run_append_ok (m' := { m with stack := .val (m.store s) :: .slot s :: m.stack })
      (by simp only [run, Machine.push, exec_cons_zero, Instr.step, Nat.sub_self, List.length_cons,
          Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero, Machine.next, Out.ok_bind,
          exec_nil])]
    rcases ValOut.toRes_cases hv with ⟨vn, wn, hc, hrn, hrunt⟩ | ⟨hc, hrunt⟩
    · obtain ⟨an, rfl, hnew⟩ := repr_write (L := L) hrn m.store s
      obtain ⟨stor, hsave, hrep⟩ := save_repr hm.store hps ⟨_, hsv⟩ hnew
        (fun x hx => upd_other _ _ fun he => hx (he ▸ Occ.prim))
      rw [toSVal_erase, Solidity.Core.Storage.saveStorage_erase (σ := σ.sem) rfl] at hsave
      obtain ⟨st', hst', hsem⟩ := into_ok hsave
      refine .inl ⟨⟨σ.withStorage st', List.prefix_refl _⟩, { m with store := upd m.store s an },
        ?_, ?_, rfl, Keeps.store (upd_len hps an),
        Sim.withStore hsem (hm.store' hrep (upd_len hps an))⟩
      · simp only [Solidity.Core.TRun.incDec, opLocT_bump hl, hres, Solidity.Core.bumpStoreT, hf,
          hc, hst', bind, Except.bind, TRes.ofOpt, pure, Except.pure]
      · rw [run_append_ok hrunt]; rfl
    · refine .inr ⟨?_, run_append_revert hrunt⟩
      simp only [Solidity.Core.TRun.incDec, opLocT_bump hl, hres, Solidity.Core.bumpStoreT, hf,
        hc, bind, Except.bind, TRes.ofOpt]
  · exact .inr ⟨by simp only [Solidity.Core.TRun.incDec, opLocT_bump hl, hres, bind, Except.bind],
      run_append_revert hrunl⟩

/-- `x++;` on a numeric local. -/
theorem bumpLocal_sim {p : PrimTy} (hp : p ≠ .bool) (op : IncDec) (i : Idx Γ (.val p))
    (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) :
    StmtOut C L b F false false false (Solidity.Core.TRun.incDec op (.local i) σ)
      (run ([.mload (cellOf b i), .push (.val 1)] ++ binTail p op.binOp ++ [.mstore (cellOf b i)]) m)
      m := by
  have hpn := numeric_of_ne hp
  have hrold := hm.vals i
  obtain ⟨n, hn, hv⟩ := bump_sim hp op hrold m
  rw [bump_erase hpn, ← bump_key hpn hn] at hv
  rw [show [Instr.mload (cellOf b i), .push (.val 1)] ++ binTail p op.binOp ++
      [.mstore (cellOf b i)] = [Instr.mload (cellOf b i)] ++ (([.push (.val 1)] ++
      binTail p op.binOp) ++ [.mstore (cellOf b i)]) by simp only [List.cons_append,
          List.nil_append],
    run_append_ok (m' := { m with stack := m.memAt (lvl b i) :: m.stack }) rfl]
  rcases ValOut.toRes_cases hv with ⟨vn, wn, hc, hrn, hrunt⟩ | ⟨hc, hrunt⟩
  · refine .inl ⟨⟨σ.setLocal i vn, List.prefix_refl _⟩,
      { m with mem := upd m.mem (cellOf b i) wn }, ?_, ?_, rfl,
      Keeps.upd (le_lvl b i) _, hm.setLocalVal i hrn⟩
    · simp only [Solidity.Core.TRun.incDec, Solidity.Core.OpLoc.bumpT, bind, Except.bind,
        TRes.ofOpt, pure, Except.pure]
      rw [show Look.ofTEnv σ.env i = TEnv.get i σ.env from rfl] at hc
      rw [hc]
    · rw [run_append_ok hrunt]; rfl
  · refine .inr ⟨?_, run_append_revert hrunt⟩
    simp only [Solidity.Core.TRun.incDec, Solidity.Core.OpLoc.bumpT, bind, Except.bind,
      TRes.ofOpt]
    rw [show Look.ofTEnv σ.env i = TEnv.get i σ.env from rfl] at hc
    rw [hc]

/-- `v = x++;` on a numeric local: `x`'s cell bumped, `v` given the old or the
new word. -/
theorem assignBumpLocal_sim {p : PrimTy} (hp : p ≠ .bool) (op : IncDec) (i j : Idx Γ (.val p))
    (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) :
    StmtOut C L b F false false false (Solidity.Core.TRun.assignIncDec i op (.local j) σ)
      (run ([.mload (cellOf b j)] ++ bumpCode p op ++ [.mstore (cellOf b j), .mstore (cellOf b i)]) m)
      m := by
  have hpn := numeric_of_ne hp
  have hrold := hm.vals j
  obtain ⟨n, hn, hv⟩ := bumpCode_sim hp op hrold m
  have hk := bump_key hpn hn
  rw [List.append_assoc, run_append_ok (m' := { m with stack := m.memAt (lvl b j) :: m.stack }) rfl]
  rcases hv with ⟨vn, wn, hvn, hrn, hrunt⟩ | ⟨hvn, hrunt⟩
  · rw [bump_erase hpn, ← hk] at hvn
    obtain ⟨tn, htn, rfl⟩ : ∃ tn, Solidity.Core.bumpT op p (PrimTy.key (TEnv.get j σ.env)) =
        some tn ∧ vn = PrimTy.erase tn := by
      cases h : Solidity.Core.bumpT op p (PrimTy.key (TEnv.get j σ.env)) with
      | none => rw [show Look.ofTEnv σ.env j = TEnv.get j σ.env from rfl, h] at hvn; cases hvn
      | some tn =>
        rw [show Look.ofTEnv σ.env j = TEnv.get j σ.env from rfl, h] at hvn
        exact ⟨tn, rfl, (Except.ok.inj hvn).symm⟩
    have hs := (hm.setLocalVal j hrn).setLocalVal i
      (v := if op.isPre then tn else TEnv.get j σ.env)
      (w := if op.isPre then wn else m.memAt (lvl b j))
      (by cases op.isPre <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> first | exact hrn | exact hrold)
    have hk' := Keeps.upd₂ (C := C) (sh := false) (m := m) (le_lvl b j) (le_lvl b i) wn
      (if op.isPre then wn else m.memAt (lvl b j))
    refine .inl ⟨⟨(σ.setLocal j tn).setLocal i (if op.isPre then tn else TEnv.get j σ.env),
      List.prefix_refl _⟩, _, ?_, ?_, ?_, hk', hs⟩
    rotate_left 2; · rfl
    · simp only [Solidity.Core.TRun.assignIncDec, Solidity.Core.OpLoc.bumpT, bind, Except.bind,
        TRes.ofOpt, htn, pure, Except.pure]
    · rw [run_append_ok hrunt]; rfl
  · refine .inr ⟨?_, run_append_revert hrunt⟩
    rw [bump_erase hpn, ← hk] at hvn
    have h := toRes_none hvn
    rw [show Look.ofTEnv σ.env j = TEnv.get j σ.env from rfl] at h
    simp only [Solidity.Core.TRun.assignIncDec, Solidity.Core.OpLoc.bumpT, bind, Except.bind,
      TRes.ofOpt, h]

/-- `v = total++;`: the target bumped, `v` given the old or the new word. -/
theorem assignBumpStore_sim {p : PrimTy} (hp : p ≠ .bool) (op : IncDec) (i : Idx Γ (.val p))
    {l : Solidity.Core.OpLoc C Γ p} {loc : Solidity.Core.Loc C Γ (.prim p)}
    (hl : opLocToLoc l = some loc) (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m)
    (hwl : locIn F false loc = true) :
    StmtOut C L b F false false false (Solidity.Core.TRun.assignIncDec i op l σ)
      (run (compileLoc b loc ++ [.dup 1, .sload] ++ bumpCode p op ++
        [.dup 3, .sstore, .swap 1, .pop, .mstore (cellOf b i)]) m) m := by
  have hpn := numeric_of_ne hp
  simp only [List.append_assoc]
  rcases loc_sim loc hm hwl with ⟨rt, s, sv, hres, hsv, hps, hr, hrunl⟩ | ⟨hres, hrunl⟩
  · obtain ⟨old, hold, hrold, rfl⟩ := prim_read hr
    obtain ⟨told, hf, rfl⟩ := prim_find hsv hold
    obtain ⟨n, hn, hv⟩ := bumpCode_sim hp op hrold { m with stack := .slot s :: m.stack }
    have hk := bump_key hpn hn
    rw [run_append_ok hrunl,
      run_append_ok (m' := { m with stack := .val (m.store s) :: .slot s :: m.stack })
      (by simp only [run, Machine.push, exec_cons_zero, Instr.step, Nat.sub_self, List.length_cons,
          Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero, Machine.next, Out.ok_bind,
          exec_nil])]
    rcases hv with ⟨vn, wn, hvn, hrn, hrunt⟩ | ⟨hvn, hrunt⟩
    · rw [bump_erase hpn, ← hk] at hvn
      obtain ⟨tn, htn, rfl⟩ : ∃ tn, Solidity.Core.bumpT op p
          (PrimTy.key (Solidity.Core.SVal.view told)) = some tn ∧ vn = PrimTy.erase tn := by
        cases h : Solidity.Core.bumpT op p (PrimTy.key (Solidity.Core.SVal.view told)) with
        | none => rw [h] at hvn; cases hvn
        | some tn => rw [h] at hvn; exact ⟨tn, rfl, (Except.ok.inj hvn).symm⟩
      obtain ⟨an, rfl, hnew⟩ := repr_write (L := L) hrn m.store s
      obtain ⟨stor, hsave, hrep⟩ := save_repr hm.store hps ⟨_, hsv⟩ hnew
        (fun x hx => upd_other _ _ fun he => hx (he ▸ Occ.prim))
      rw [toSVal_erase, Solidity.Core.Storage.saveStorage_erase (σ := σ.sem) rfl] at hsave
      obtain ⟨st', hst', hsem⟩ := into_ok hsave
      have hs := (Sim.withStore hsem (hm.store' hrep (upd_len hps an))).setLocalVal i
        (v := if op.isPre then tn else Solidity.Core.SVal.view told)
        (w := if op.isPre then .val an else .val (m.store s))
        (by cases op.isPre <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> first | exact hrn | exact hrold)
      refine .inl ⟨⟨(σ.withStorage st').setLocal i
          (if op.isPre then tn else Solidity.Core.SVal.view told), List.prefix_refl _⟩, { m with
          store := upd m.store s an
          mem := upd m.mem (cellOf b i) (if op.isPre then .val an else .val (m.store s)) },
        ?_, ?_, rfl, Keeps.storeUpd (le_lvl b i) _ (upd_len hps an), hs⟩
      · simp only [Solidity.Core.TRun.assignIncDec, opLocT_bump hl, hres,
          Solidity.Core.bumpStoreT, hf, htn, hst', bind, Except.bind, TRes.ofOpt, pure,
          Except.pure]
      · simp only at hrunt
        rw [run_append_ok hrunt]
        simp only [run, exec_cons_zero, Instr.step, Nat.add_one_sub_one, List.length_cons,
            Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_succ,
            List.getElem_cons_zero, Machine.next, Out.ok_bind, List.set_cons_zero, exec_nil]
    · refine .inr ⟨?_, run_append_revert hrunt⟩
      rw [bump_erase hpn, ← hk] at hvn
      have h := toRes_none hvn
      simp only [Solidity.Core.TRun.assignIncDec, opLocT_bump hl, hres, Solidity.Core.bumpStoreT,
        hf, h, bind, Except.bind, TRes.ofOpt]
  · exact .inr ⟨by simp only [Solidity.Core.TRun.assignIncDec, opLocT_bump hl, hres, bind,
      Except.bind], run_append_revert hrunl⟩

/-! ## Copies, arrays, `delete`, payments -/

/-- **`alice = bob;`** of a static type: the source's words loaded, the
target resolved, the words stored at the target's slots. -/
theorem copy_sim {R : RefTy} (l : Solidity.Core.Loc C Γ (.ref R))
    (q : Solidity.Core.SPath C Γ (.ref R)) (hq : (Ty.ref R).mapFree = true)
    (hst : static (.ref R) = true) (hnd : (Ty.ref R).nodupS = true)
    (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m)
    (hwq : spathIn F false q = true) (hwl : locIn F false l = true) :
    StmtOut C L b F false false false (Solidity.Core.TRun.assign l (.copy q hq) σ)
      (run (compileSPath b q ++ loadLeaves (leaves (.ref R)) ++ [.pop] ++ compileLoc b l ++
        storeLeaves (leaves (.ref R)).reverse ++ [.pop]) m) m := by
  simp only [List.append_assoc]
  rcases spath_sim q hm hwq with ⟨r, s, sv, hres, hsv, hpq, hr, hrun⟩ | ⟨hres, hrun⟩
  · obtain ⟨tsv, hf, rfl⟩ := find_of_findLive hsv
    rw [run_append_ok hrun]
    simp only [Machine.push]
    rw [run_append_ok (loadLeaves_run m s _ m.stack)]
    generalize hvs : ((leaves (.ref R)).map fun o => m.store (s.add o)).reverse = vs
    rw [run_append_ok (m' := { m with stack := vs.map Word.val ++ m.stack }) rfl]
    rcases loc_sim l (hm.stack (vs.map Word.val ++ m.stack)) hwl with
      ⟨r', d, old, hres', hold, hpl, hro, hrunl⟩ | ⟨hres', hrunl⟩
    · rw [run_append_ok hrunl]
      simp only [Machine.push]
      have hlen : (leaves (.ref R)).reverse.length = vs.length := by
        rw [← hvs]; simp only [List.length_reverse, List.length_map]
      rw [run_append_ok (storeLeaves_run { m with stack := vs.map Word.val ++ m.stack } d _ vs
        m.stack m.store hlen)]
      have hvs' : vs = (leaves (.ref R)).reverse.map fun o => m.store (s.add o) := by
        rw [← hvs, List.map_reverse]
      subst hvs'
      have hmove := move_repr (st' := storeAt m.store d (leaves (.ref R)).reverse
          ((leaves (.ref R)).reverse.map fun o => m.store (s.add o))) hr _ d
        (Nat.lt_succ_self _) hst fun o ho => storeAt_map _ (List.mem_reverse.2 ho)
      have hov := (overlay_repr hmove _ (Nat.lt_succ_self _) hst).2 old
      obtain ⟨stor, hsave, hrep⟩ := save_repr hm.store hpl ⟨_, hold⟩ hov
        (fun x hx => storeAt_other fun o ho hxo =>
          hx (hxo ▸ leavesF_occ _ _ d o (List.mem_reverse.1 ho)))
      rw [← writeStorage_static hr hst (State.findStorage_of_findLive hold),
        Solidity.Core.Storage.writeStorage_erase (σ := σ.sem) rfl
          (Solidity.Core.TyNodup.of_nodupS hnd)] at hsave
      obtain ⟨st', hst', hsem⟩ := into_ok hsave
      refine .inl ⟨⟨σ.withStorage st', List.prefix_refl _⟩, _, ?_, rfl, rfl,
        Keeps.store (storeAt_len hpl hst _),
        Sim.withStore hsem (hm.store' hrep (storeAt_len hpl hst _))⟩
      simp only [Solidity.Core.TRun.assign, Solidity.Core.Src.valueT, hres, hf, hres', hst', bind,
        Except.bind, TRes.ofOpt, pure, Except.pure]
    · exact .inr ⟨by simp only [Solidity.Core.TRun.assign, Solidity.Core.Src.valueT, hres, hf,
        hres', bind, Except.bind, TRes.ofOpt], run_append_revert hrunl⟩
  · exact .inr ⟨by simp only [Solidity.Core.TRun.assign, Solidity.Core.Src.valueT, hres, bind,
      Except.bind], run_append_revert hrun⟩

/-- A `push` the untyped side completed, typed. -/
theorem push_ok {E : Ty} {r : SRef C (.ref (.array E))} {elems shadow : List SVal}
    {val : SVal → Res SVal} {val' : Solidity.Core.SVal E → Option (Solidity.Core.SVal E)}
    (hval : ∀ x : Solidity.Core.SVal E, val x.erase = Solidity.Core.toRes Solidity.Core.SVal.erase (val' x))
    {new : SVal} (hnew : val (pushSlot E shadow).1 = .ok new)
    (hsv : σ.sem.findLive r.root r.path.erase = .ok (.array elems shadow false))
    {stor : List (Name × SVal)}
    (hsave : σ.sem.saveStorage r.root r.path.erase
      (.array (elems ++ [new]) (pushSlot E shadow).2 false) = .ok { σ.sem with storage := stor })
    (hb : elems.length + 1 < 2 ^ 256) :
    σ.storage.full r = false ∧ ∃ st', σ.storage.push r val' = some st' ∧
      (σ.withStorage st').sem = { σ.sem with storage := stor } := by
  have hfull : σ.storage.full r = false :=
    Solidity.Core.Storage.full_eq_false (σ := σ.sem) rfl r fun elems' sh fx hf => by
      rw [State.findStorage_of_findLive hsv] at hf
      cases hf
      exact hb
  have hpa : pushAt σ.sem E r.root r.path.erase val = .ok { σ.sem with storage := stor } := by
    simp only [pushAt, State.findStorage_of_findLive hsv, bind, Except.bind, hnew, hsave]
  rw [Solidity.Core.Storage.pushAt_erase (σ := σ.sem) rfl r val val' hval (.inl hfull)] at hpa
  exact ⟨hfull, into_ok hpa⟩

/-- **`b.push(…)`**: the array's slot, the value, the length checked against
solc's `2^64` and grown, the element stored. -/
theorem push_sim {E : Ty} (q : Solidity.Core.SPath C Γ (.array E))
    (v : Option (Solidity.Core.Src C Γ E)) (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m)
    (hwp : pushIn F v q = true) (hL : L + 1 ≤ Lmax) :
    StmtOut C (L + 1) b F false false false (Solidity.Core.TRun.push q v σ)
      (run (pushCode b v q) m) m := by
  have hm' := hm.mono (Nat.le_succ L) hL
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
      | @array _ _ elems shadow hl hW hall =>
        rw [run_append_ok hrun]
        simp only [Machine.push]
        rw [run_append_ok (m' := { m with stack := .slot s :: .val 0 :: .slot s :: m.stack }) rfl,
          run_append_ok (pushSlotCode_run m _ 1 s (by omega))]
        obtain ⟨st', hst'⟩ : ∃ st', st' =
            upd (upd m.store s (m.store s + 1)) (.data s (m.store s * 1)) 0 := ⟨_, rfl⟩
        have hnew : ReprAt st' (L + 1) (.prim p) (.data s (elems.length * size (.prim p)))
            (defaultForTy (.prim p)) := zero_prim_repr (by rw [size_prim, ← hl, hst', upd_same])
        have hout : ∀ x, x ≠ s → x ≠ .data s (elems.length * 1) → st' x = m.store x :=
          fun x h1 h2 => by rw [hst', hl, upd_other _ _ h2, upd_other _ _ h1]
        have harr := push_repr (shadow' := (pushSlot (.prim p) shadow).2) hr'
          (st' := st') (by rw [hst', upd_other _ _ (Slot.ne_data _ _), upd_same, hl]) hnew
          (fun x hx hx' => hout x hx fun he => hx' (by rw [he, size_prim]; exact Occ.prim))
        obtain ⟨stor, hsave, hrep⟩ := save_repr hm'.store hp ⟨_, hsv⟩ harr
          (fun x hx => hout x (fun he => hx (he ▸ Occ.len))
            (fun he => hx (he ▸ Occ.elem elems.length (by rw [size_prim]; exact Occ.prim))))
        have hlen : ∀ x, LenSlot C x → m.store x ≤ st' x := push_len hp (m.store s)
          (by rw [hst', upd_other _ _ (Slot.ne_data _ _), upd_same])
          (fun x h1 h2 => by
            by_cases hx : x = .data s (m.store s * 1)
            · rw [hx]; exact OccAt.prim
            · exact absurd (by rw [hst', upd_other _ _ hx, upd_other _ _ h1]) h2)
        subst hst'
        obtain ⟨hfull, st', hst', hsem⟩ := push_ok (val := fun x => .ok x)
          (val' := fun slot => some ((none : Option (Solidity.Core.SVal (.prim p))).getD slot))
          (fun _ => rfl) (by rw [pushSlot_isPrim rfl]) hsv hsave
          (by have := Lmax_lt_W; unfold W at this; omega)
        refine .inl ⟨⟨σ.withStorage st', List.prefix_refl _⟩, _, ?_, rfl, rfl, Keeps.store hlen,
          Sim.withStore hsem (hm'.store' hrep hlen)⟩
        simp only [Solidity.Core.TRun.push, hres, hfull, Bool.false_eq_true, ↓reduceIte, hst',
          bind, Except.bind, TRes.ofOpt, pure, Except.pure]
    · exact .inr ⟨by simp only [Solidity.Core.TRun.push, hres, bind, Except.bind],
        run_append_revert hrun⟩
  | some src =>
    cases src with
    | @val p e =>
      rw [pushIn] at hwp
      simp only [Bool.and_eq_true] at hwp
      obtain ⟨hwb, hwe⟩ := hwp
      simp only [pushCode, List.append_assoc]
      rcases spath_sim q hm hwb with ⟨r, s, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
      · have hr' := hr
        cases hr with
        | @array _ _ elems shadow hl hW hall =>
          rw [run_append_ok hrun]
          rcases val_sim e (hm.push (.slot s)) hwe with ⟨ve, we, hve, hrve, hrune⟩ | ⟨hve, hrune⟩
          · rw [run_append_ok hrune]
            simp only [Machine.push]
            obtain ⟨a, rfl, hnew⟩ := repr_write (L := L + 1) hrve
              (upd m.store s (m.store s + 1)) (.data s (m.store s * 1))
            rw [run_append_ok (m' := { m with stack := .slot s :: .val a :: .slot s :: m.stack })
                rfl,
              run_append_ok (pushSlotCode_run m _ 1 s (by omega))]
            obtain ⟨st', hst'⟩ : ∃ st', st' =
                upd (upd m.store s (m.store s + 1)) (.data s (m.store s * 1)) a := ⟨_, rfl⟩
            rw [← hst', hl, show elems.length * 1 = elems.length * size (.prim _) by
              simp only [Nat.mul_one, size_prim]] at hnew
            have hout : ∀ x, x ≠ s → x ≠ .data s (elems.length * 1) → st' x = m.store x :=
              fun x h1 h2 => by rw [hst', hl, upd_other _ _ h2, upd_other _ _ h1]
            have harr := push_repr (shadow' := (pushSlot (.prim p) shadow).2) hr'
              (st' := st') (by rw [hst', upd_other _ _ (Slot.ne_data _ _), upd_same, hl]) hnew
              (fun x hx hx' => hout x hx fun he => hx' (by rw [he, size_prim]; exact Occ.prim))
            obtain ⟨stor, hsave, hrep⟩ := save_repr hm'.store hp ⟨_, hsv⟩ harr
              (fun x hx => hout x (fun he => hx (he ▸ Occ.len))
                (fun he => hx (he ▸ Occ.elem elems.length (by rw [size_prim]; exact Occ.prim))))
            have hlen : ∀ x, LenSlot C x → m.store x ≤ st' x := push_len hp (m.store s)
              (by rw [hst', upd_other _ _ (Slot.ne_data _ _), upd_same])
              (fun x h1 h2 => by
                by_cases hx : x = .data s (m.store s * 1)
                · rw [hx]; exact OccAt.prim
                · exact absurd (by rw [hst', upd_other _ _ hx, upd_other _ _ h1]) h2)
            subst hst'
            obtain ⟨hfull, st', hst', hsem⟩ := push_ok
              (val := fun _ => .ok (PrimTy.erase ve).toSVal)
              (val' := fun slot => some ((some (Solidity.Core.SVal.prim ve).strip).getD slot))
              (fun _ => by
                simp only [Option.getD_some, Solidity.Core.toRes,
                  Solidity.Core.SVal.strip_erase, ← toSVal_erase, Value.toSVal_strip])
              rfl hsv hsave (by have := Lmax_lt_W; unfold W at this; omega)
            refine .inl ⟨⟨σ.withStorage st', List.prefix_refl _⟩, _, ?_, rfl, rfl,
              Keeps.store hlen, Sim.withStore hsem (hm'.store' hrep hlen)⟩
            simp only [Solidity.Core.TRun.push, Solidity.Core.Src.valueT, hres, hve, hfull,
              Bool.false_eq_true, ↓reduceIte, hst', bind, Except.bind, TRes.ofOpt, pure,
              Except.pure]
          · refine .inr ⟨?_, run_append_revert hrune⟩
            simp only [Solidity.Core.TRun.push, Solidity.Core.Src.valueT, hres, hve, bind,
              Except.bind]
      · exact .inr ⟨by simp only [Solidity.Core.TRun.push, hres, bind, Except.bind],
          run_append_revert hrun⟩
    | @copy R q' hq =>
      rw [pushIn] at hwp
      simp only [Bool.and_eq_true] at hwp
      obtain ⟨⟨hst, hwb⟩, hwq⟩ := hwp
      simp only [pushCode, List.append_assoc]
      rcases spath_sim q hm hwb with ⟨r, s, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
      · have hr' := hr
        cases hr with
        | @array _ _ elems shadow hl hW hall =>
          rw [run_append_ok hrun]
          rcases spath_sim q' (hm.push (.slot s)) hwq with
            ⟨r', src, sv', hres', hsv', hpq, hrq, hrunq⟩ | ⟨hres', hrunq⟩
          · obtain ⟨tsv', hf', rfl⟩ := find_of_findLive hsv'
            rw [run_append_ok hrunq]
            simp only [Machine.push]
            rw [run_append_ok (loadLeaves_run m src _ (.slot s :: m.stack))]
            generalize hvs : ((leaves (.ref R)).map fun o => m.store (src.add o)).reverse = vs
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
              run_append_ok (storeLeaves_run m _ _ vs (.slot s :: m.stack) _ hlen)]
            have hvs' : vs = (leaves (.ref R)).reverse.map fun o => m.store (src.add o) := by
              rw [← hvs, List.map_reverse]
            subst hvs'
            obtain ⟨st', hst'⟩ : ∃ st', st' = storeAt (upd m.store s (m.store s + 1))
                (.data s (m.store s * size (.ref R))) (leaves (.ref R)).reverse
                ((leaves (.ref R)).reverse.map fun o => m.store (src.add o)) := ⟨_, rfl⟩
            have hmove := move_repr (st' := st') hrq _ (.data s (elems.length * size (.ref R)))
              (Nat.lt_succ_self _) hst fun o ho => by
                rw [hst', ← hl]; exact storeAt_map _ (List.mem_reverse.2 ho)
            have hnew := ((overlay_repr hmove _ (Nat.lt_succ_self _) hst).1).mono (Nat.le_succ L)
            have hout : ∀ x, x ≠ s → ¬ Occ (.ref R) (.data s (elems.length * size (.ref R))) x →
                st' x = m.store x := fun x h1 h2 => by
              rw [hst', hl, storeAt_other fun o ho hxo =>
                h2 (by rw [hxo]; exact leavesF_occ _ _ _ o (List.mem_reverse.1 ho)),
                upd_other _ _ h1]
            have harr := push_repr (shadow' := (pushSlot (.ref R) shadow).2) hr' (st' := st')
              (by rw [hst', storeAt_other fun o _ he => Slot.ne_data s _ he,
                upd_same, hl]) hnew hout
            obtain ⟨stor, hsave, hrep⟩ := save_repr hm'.store hp ⟨_, hsv⟩ harr
              (fun x hx => hout x (fun he => hx (he ▸ Occ.len))
                (fun he => hx (Occ.elem elems.length he)))
            have hlen : ∀ x, LenSlot C x → m.store x ≤ st' x := push_len hp (m.store s)
              (by rw [hst', storeAt_other fun o _ he => Slot.ne_data s _ he, upd_same])
              (fun x h1 h2 => by
                by_cases hx : ∃ o ∈ (leaves (.ref R)).reverse,
                    x = (Slot.data s (m.store s * size (.ref R))).add o
                · obtain ⟨o, ho, rfl⟩ := hx
                  exact leavesF_occAt _ _ _ o hst (List.mem_reverse.1 ho)
                · refine absurd ?_ h2
                  rw [hst', storeAt_other fun o ho he => hx ⟨o, ho, he⟩, upd_other _ _ h1])
            obtain ⟨hfull, st'', hst'', hsem⟩ := push_ok (val := fun _ => .ok tsv'.erase.strip)
              (val' := fun slot => some ((some tsv'.strip).getD slot))
              (fun _ => by
                simp only [Option.getD_some, Solidity.Core.toRes, Solidity.Core.SVal.strip_erase])
              rfl hsv hsave (by have := Lmax_lt_W; unfold W at this; omega)
            refine .inl ⟨⟨σ.withStorage st'', List.prefix_refl _⟩, { m with store := st' }, ?_,
              ?_, rfl, Keeps.store hlen, Sim.withStore hsem (hm'.store' hrep hlen)⟩
            · simp only [Solidity.Core.TRun.push, Solidity.Core.Src.valueT, hres, hres', hf',
                hfull, Bool.false_eq_true, ↓reduceIte, hst'', bind, Except.bind, TRes.ofOpt, pure,
                Except.pure]
            · rw [hst']; rfl
          · exact .inr ⟨by simp only [Solidity.Core.TRun.push, Solidity.Core.Src.valueT, hres,
              hres', bind, Except.bind], run_append_revert hrunq⟩
      · exact .inr ⟨by simp only [Solidity.Core.TRun.push, hres, bind, Except.bind],
          run_append_revert hrun⟩

/-- `b.pop();`: the length decremented, reverting on an empty array; the
fragile aliases forgotten. -/
theorem pop_sim {E : Ty} (q : Solidity.Core.SPath C Γ (.array E))
    (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) (hwb : spathIn F false q = true) :
    StmtOut C L b F.dropFragile true false false (Solidity.Core.TRun.pop q σ)
      (run (compileSPath b q ++ popCode) m) m := by
  rcases spath_sim q hm hwb with ⟨r, s, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
  · have hr' := hr
    cases hr with
    | array hl hW hall =>
      rename_i elems shadow
      rw [run_append_ok hrun]
      have hpc := popCode_run m m.stack s
        (by rw [hl]; have := hm.bound; have := Lmax_lt_W; omega)
      simp only [Machine.push] at hpc ⊢
      rw [hpc, hl]
      have hpa := Solidity.Core.Storage.popAt_erase (σ := σ.sem) rfl E.isMapping r
      by_cases h0 : elems.length = 0
      · rw [if_pos h0]
        have : elems = [] := List.eq_nil_of_length_eq_zero h0
        subst this
        rw [show popAt σ.sem E.isMapping r.root r.path.erase = .error .revert by
          simp only [popAt, State.findStorage_of_findLive hsv, bind, Except.bind,
            List.reverse_nil]] at hpa
        exact .inr ⟨by simp only [Solidity.Core.TRun.pop, hres, toRes_none hpa.symm, bind,
          Except.bind, TRes.ofOpt], rfl⟩
      · rw [if_neg h0]
        obtain ⟨last, restRev, hrev⟩ : ∃ last restRev, elems.reverse = last :: restRev := by
          cases h : elems.reverse with
          | nil => simp only [List.reverse_eq_nil_iff] at h; exact absurd (by simp only [h,
              List.length_nil]) h0
          | cons last restRev => exact ⟨last, restRev, rfl⟩
        have hnew := pop_repr (if E.isMapping then last else last.defaultOf) hr' hrev
        obtain ⟨stor, hsave, hrep⟩ := save_repr hm.store hp ⟨_, hsv⟩ hnew
          (fun x hx => upd_other _ _ fun he => hx (he ▸ Occ.len))
        rw [show popAt σ.sem E.isMapping r.root r.path.erase = .ok { σ.sem with storage := stor } by
          simp only [popAt, State.findStorage_of_findLive hsv, bind, Except.bind, hrev,
            hsave]] at hpa
        obtain ⟨st', hst', hsem⟩ := into_ok hpa.symm
        refine .inl ⟨⟨σ.withStorage st', List.prefix_refl _⟩, _, ?_, rfl, rfl, Keeps.shrink,
          Sim.withStore hsem (hm.storeDrop hrep)⟩
        simp only [Solidity.Core.TRun.pop, hres, hst', bind, Except.bind, TRes.ofOpt, pure,
          Except.pure]
  · exact .inr ⟨by simp only [Solidity.Core.TRun.pop, hres, bind, Except.bind],
      run_append_revert hrun⟩

/-- `delete l;`: every leaf of `l` zeroed; the fragile aliases forgotten. -/
theorem delete_sim {T : Ty} (l : Solidity.Core.Loc C Γ T)
    (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) (hwl : locIn F false l = true) :
    StmtOut C L b F.dropFragile true false false (Solidity.Core.TRun.delete l σ)
      (run (compileLoc b l ++ zeroCode (leaves T) ++ [.pop]) m) m := by
  simp only [List.append_assoc]
  rcases loc_sim l hm hwl with ⟨r, s, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
  · rw [run_append_ok hrun]
    simp only [Machine.push]
    rw [run_append_ok (zeroCode_run m m.stack s (leaves T))]
    have hnew := zero_repr hr (tyRank T + 1) (Nat.lt_succ_self _)
      (st' := zeroAt m.store s (leaves T)) (fun o ho => zeroAt_zero ⟨o, ho, rfl⟩)
      (fun x _ hx => zeroAt_other hx)
    obtain ⟨stor, hsave, hrep⟩ := save_repr hm.store hp ⟨_, hsv⟩ hnew
      (fun x hx => zeroAt_other fun o ho hxo => hx (hxo ▸ leavesF_occ _ T s o ho))
    have hde := Solidity.Core.Storage.delete_erase (σ := σ.sem) rfl r
    rw [show (do
        let cur ← σ.sem.findStorage r.root r.path.erase
        σ.sem.saveStorage r.root r.path.erase cur.defaultOf) =
        Except.ok { σ.sem with storage := stor } by
      simp only [State.findStorage_of_findLive hsv, bind, Except.bind, hsave]] at hde
    obtain ⟨st', hst', hsem⟩ := into_ok hde.symm
    refine .inl ⟨⟨σ.withStorage st', List.prefix_refl _⟩,
      { m with store := zeroAt m.store s (leaves T) }, ?_, rfl, rfl, Keeps.shrink,
      Sim.withStore hsem (hm.storeDrop hrep)⟩
    simp only [Solidity.Core.TRun.delete, hres, hst', bind, Except.bind, TRes.ofOpt, pure,
      Except.pure]
  · exact .inr ⟨by simp only [Solidity.Core.TRun.delete, hres, bind, Except.bind],
      run_append_revert hrun⟩

/-- **A payment**: `to.transfer(5);` books `net(to) - 5`; the machine's
`CALL` moves `5`, or nothing when `to` is the contract, or is refused and
reverts, the typed run's state then represented by the world that paid. -/
theorem transfer_sim (r a : Solidity.Core.Val C Γ .uint)
    (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) (hwr : valIn F r = true)
    (hwa : valIn F a = true) :
    StmtOut C L b F false true false (Solidity.Core.TRun.transfer r a σ)
      (run (compileVal b r ++ compileVal b a ++ [.call] ++ assertTop) m) m := by
  simp only [List.append_assoc]
  rcases val_sim r hm hwr with ⟨vr, wr, hvr, hrv, hrunr⟩ | ⟨hvr, hrunr⟩
  · obtain ⟨x, hx, hxv, rfl⟩ := hrv.uint_inv
    have hx1 : vr.1 = (x : Int) := Semantics.PrimVal.int.inj hxv
    rw [run_append_ok hrunr]
    rcases val_sim a (hm.push _) hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
    · obtain ⟨y, hy, hyv, rfl⟩ := hra.uint_inv
      have hy1 : va.1 = (y : Int) := Semantics.PrimVal.int.inj hyv
      rw [run_append_ok hruna]
      have hres : Solidity.Core.TRun.transfer r a σ =
          .ok ⟨σ.pay x y, List.prefix_refl _⟩ := by
        simp only [Solidity.Core.TRun.transfer, hvr, hva, bind, Except.bind, pure, Except.pure,
          hx1, hy1]
      rw [hres]
      obtain ⟨-, -, -, hself, -, -, -, hsw⟩ := hm.env
      have hpay : ∀ a : Nat, (σ.sem.pay x y).getNet a =
          if x = m.self then σ.sem.getNet a else if a = x then σ.sem.getNet x - y
          else σ.sem.getNet a := by
        intro a
        rw [getNet_pay, hself]
        simp only [Int.ofNat_inj]
      have hns : (σ.sem.pay x y).getNet m.self = 0 := by
        rw [hpay m.self]
        split
        · exact hm.netSelf
        · rename_i hxs
          rw [if_neg (fun h => hxs h.symm)]
          exact hm.netSelf
      by_cases hrf : m.bal m.self < y ∨ m.accepts x y = false
      · refine .refused rfl ⟨by simp only [run, assertTop, List.cons_append, List.nil_append,
          Machine.push, exec_cons_zero, Instr.step, hrf, ↓reduceIte, Machine.next, Out.ok_bind,
          exec_nil, Out.revert_bind],
          ⟨σ.pay x y, List.prefix_refl _⟩, { m with bal := upd m.bal x (m.bal x + y) }, rfl,
          ⟨fun _ _ => rfl, fun _ _ _ => Nat.le_refl _⟩,
          hm.book x y _ _ (fun c hc hcs => ?_) hns⟩
        have h1 := hm.net c hc hcs
        rw [hpay c]
        simp only [upd]
        by_cases hxs : x = m.self
        · subst hxs
          simp only [hcs, ↓reduceIte]; exact h1
        · by_cases hcx : c = x
          · subst hcx; simp only [hxs, ↓reduceIte]; omega
          · simp only [hxs, hcx, ↓reduceIte]; exact h1
      · by_cases hxe : x = m.self
        · subst hxe
          have hb := hm.book _ _ m.bal m.bal₀ (fun c hc hcs => by
            rw [hpay c]; simp only [↓reduceIte]; exact hm.net c hc hcs) hns
          refine .inl ⟨⟨σ.pay _ y, List.prefix_refl _⟩, m, rfl, ?_, rfl, Keeps.refl m, hb⟩
          simp only [run, assertTop, List.cons_append, List.nil_append, Machine.push,
              exec_cons_zero, Instr.step, hrf, ↓reduceIte, Machine.next, Out.ok_bind,
              Nat.succ_ne_self, exec_cons_succ, exec_nil]
        · simp only [not_or, Bool.not_eq_false] at hrf
          refine .inl ⟨⟨σ.pay x y, List.prefix_refl _⟩, { m with bal := pay m.bal m.self x y },
            rfl, ?_, rfl, ⟨fun _ _ => rfl, fun _ _ _ => Nat.le_refl _⟩,
            hm.book x y _ m.bal₀ (fun c hc hcs => ?_) hns⟩
          · simp only [run, assertTop, List.cons_append, List.nil_append, Machine.push,
              exec_cons_zero, Instr.step, hrf, Bool.true_eq_false, or_self, ↓reduceIte, hxe,
              Out.ok_bind, Nat.succ_ne_self, exec_cons_succ, exec_nil]
          · have h1 := hm.net c hc hcs
            rw [hpay c]
            simp only [pay, upd, hxe, ↓reduceIte]
            by_cases hcx : c = x
            · subst hcx; simp only [↓reduceIte]; omega
            · simp only [hcx, hcs, ↓reduceIte]; exact h1
    · exact .inr ⟨by simp only [Solidity.Core.TRun.transfer, hvr, hva, bind, Except.bind],
        run_append_revert hruna⟩
  · exact .inr ⟨by simp only [Solidity.Core.TRun.transfer, hvr, bind, Except.bind],
      run_append_revert hrunr⟩

end Stmts

end Core
end Solidity.Evm
