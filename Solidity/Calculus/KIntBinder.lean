import Solidity.Calculus.LedgerCut

/-!
# Binders of KeY's `int` read as ledger entries (M7, feature 26)

The leaf language (`LFml`, `LTm`) binds atoms of a `PrimTy` only (`AEnv`,
`LFml.all`), so a binder of KeY's unbounded `int` (`Fml.bind _ _ .kint`)
has no position of its own there.  The ledger has one: an entry `net(c)` of
the starting state is a KeY `int`, any integer in some state, and the
ledger pipeline (`ledgerReduction?`, `Calculus/LedgerReduction.lean`)
compiles it as two unbounded natural codes (`Inputs.AgreeZ`).  So a binder
of KeY's `int` in a positive position of a leaf that reads no ledger is
read as the entry at an address of its own, the `n`-th binder on a path at
the address `n` (`Fml.zT`): `∀ int z. φ` becomes `{z := net(n)} φ`.

* **Refutation** (`Fml.holds_zT`): where the leaf holds, so does the
  rewritten one, each binder taken at the entry its address holds.  A state
  refuting the rewritten leaf refutes the leaf, as it is.
* **Soundness** (`Fml.zT_valid`): where the rewritten leaf holds in every
  state, so does the leaf.  At a state `σ` and a binder's value `v`, the
  rewritten leaf holds in `σ` with the ledger holding `v` at the binder's
  address and the outer binders' values at theirs (`LedgerAgree`); past the
  binders the leaf reads no ledger (`Fml.netFree`), so it holds in `σ`
  (`holds_setNet`).

The fragment (`Fml.zOK`): binders of KeY's `int` under `∀`, `∧` and the
consequent of `→`, everything else reading no ledger and first-order
(`Fml.netFree`: equations, `wt`, the connectives and value quantifiers),
at most `2^256` binders on a path (`Fml.zDepth`), so that their
addresses are distinct.  A binder in a negative position (an `∃` of KeY's
`int`) is outside: it needs an unbounded binder of the leaf language.
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-! ## The ledger replaced -/

/-- The state `σ` with the ledger `L`. -/
abbrev State.setNet {Γ : Ctx} (σ : State C Γ) (L : Ledger) : State C Γ := { σ with net := L }

/-- `copyMem`: its denotation reads the memory through a `match` the frame
lemma does not unfold (`Tm.denote_setNet`). -/
def Op2.isCopyMem {a b s : Srt} : Op2 C a b s → Bool
  | .copyMem => true
  | _ => false

/-- A term that reads no ledger: no `net`, no snapshot read. -/
def Tm.netFree {Γ : Ctx} : {s : Srt} → Tm C Γ s → Bool
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ | _, .pvZ _ | _, .app0 _ => true
  | _, .netOf .. => false
  | _, .app1 o x => !o.isNetB && x.netFree
  | _, .app2 o x y => !o.isCopyMem && x.netFree && y.netFree
  | _, .app3 _ x y z => x.netFree && y.netFree && z.netFree

theorem Tm.eval_setNet {Γ : Ctx} (σ : State C Γ) (L : Ledger) :
    {s : Srt} → (t : Tm C Γ s) → t.netFree = true → t.eval (σ.setNet L) = t.eval σ
  | _, .pvV _, _ | _, .pvP _, _ | _, .pvS _, _ | _, .pvI _, _ | _, .pvZ _, _ => rfl
  | _, .app0 o, _ => by cases o <;> rfl
  | _, .app1 o x, h => by
    simp only [Tm.netFree, Bool.and_eq_true, Bool.not_eq_true'] at h
    rw [Tm.eval_app1, Tm.eval_app1, Tm.eval_setNet σ L x h.2]
    exact Decide.Op1.eval_withLedger σ.glob L o h.1 _
  | _, .app2 o x y, h => by
    simp only [Tm.netFree, Bool.and_eq_true] at h
    rw [Tm.eval_app2, Tm.eval_app2, Tm.eval_setNet σ L x h.1.2, Tm.eval_setNet σ L y h.2]
    cases o <;> rfl
  | _, .app3 o x y z, h => by
    simp only [Tm.netFree, Bool.and_eq_true] at h
    rw [Tm.eval_app3, Tm.eval_app3, Tm.eval_setNet σ L x h.1.1, Tm.eval_setNet σ L y h.1.2,
      Tm.eval_setNet σ L z h.2]
    cases o <;> rfl

theorem Tm.denote_setNet {Γ : Ctx} (σ : State C Γ) (L : Ledger) :
    {s : Srt} → (t : Tm C Γ s) → t.netFree = true → t.denote (σ.setNet L) = t.denote σ
  | _, .pvV _, _ | _, .pvS _, _ | _, .pvI _, _ | _, .pvZ _, _ => by rfl
  | _, .pvP i, _ => by
    simp only [Tm.denote]
    generalize (TEnv.get i σ.env : Option _) = o
    cases o <;> rfl
  | _, .app0 o, _ => by cases o <;> rfl
  | _, .app1 o x, h => by
    simp only [Tm.netFree, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [Tm.denote, Tm.denote_setNet σ L x h.2]
    cases o <;> first | rfl | exact absurd h.1 (by simp only [Op1.isNetB]; decide)
  | _, .app2 o x y, h => by
    simp only [Tm.netFree, Bool.and_eq_true] at h
    obtain ⟨⟨hc, hx⟩, hy⟩ := h
    simp only [Tm.denote, Tm.denote_setNet σ L x hx, Tm.denote_setNet σ L y hy,
      Tm.eval_setNet σ L x hx, Tm.eval_setNet σ L y hy]
    cases o <;> first | rfl | skip
    · simp only [Op2.isCopyMem, Bool.not_true, Bool.false_eq_true] at hc
    · simp only [Op2.denote]
      generalize (eval σ x : Option (Storage C)) = a
      generalize (eval σ y : Option (Storage C)) = b
      cases a <;> cases b <;> rfl
  | _, .app3 o x y z, h => by
    simp only [Tm.netFree, Bool.and_eq_true] at h
    simp only [Tm.denote, Tm.denote_setNet σ L x h.1.1, Tm.denote_setNet σ L y h.1.2,
      Tm.denote_setNet σ L z h.2]

/-- A first-order formula that reads no ledger. -/
def Fml.netFree {Γ : Ctx} : Fml C Γ → Bool
  | .tt => true
  | .eq a b => a.netFree && b.netFree
  | .wellFormed s => s.netFree
  | .not φ => φ.netFree
  | .and φ ψ | .imp φ ψ => φ.netFree && ψ.netFree
  | .all _ _ φ => φ.netFree
  | _ => false

/-- **A formula that reads no ledger holds whatever the ledger.** -/
theorem holds_setNet : {Γ : Ctx} → (σ : State C Γ) → (L : Ledger) → (φ : Fml C Γ) →
    φ.netFree = true → (holds (σ.setNet L) φ ↔ holds σ φ)
  | _, _, _, .tt, _ => Iff.rfl
  | _, σ, L, .eq a b, h => by
    simp only [Fml.netFree, Bool.and_eq_true] at h
    rw [holds_eq, holds_eq, Tm.denote_setNet σ L a h.1, Tm.denote_setNet σ L b h.2]
  | _, σ, L, .wellFormed s, h => by
    rw [holds_wellFormed, holds_wellFormed, Tm.eval_setNet σ L s h]
  | _, σ, L, .not φ, h => not_congr (holds_setNet σ L φ h)
  | _, σ, L, .and φ ψ, h => by
    simp only [Fml.netFree, Bool.and_eq_true] at h
    exact and_congr (holds_setNet σ L φ h.1) (holds_setNet σ L ψ h.2)
  | _, σ, L, .imp φ ψ, h => by
    simp only [Fml.netFree, Bool.and_eq_true] at h
    exact imp_congr (holds_setNet σ L φ h.1) (holds_setNet σ L ψ h.2)
  | _, σ, L, .all _ p φ, h => forall_congr' fun v =>
    holds_setNet (σ.push (t := .val p) v) L φ h

/-! ## The rewriting -/

/-- The address of the `n`-th binder of KeY's `int` on a path. -/
abbrev zAddr (n : Nat) : PrimTy.uint.Denote := uintOfNat n

/-- **Each binder of KeY's `int` in a positive position read as the
starting ledger's entry at its address**, the `n`-th on a path at `n`. -/
def Fml.zT {Γ : Ctx} (n : Nat) : Fml C Γ → Fml C Γ
  | .bind _ x .kint φ =>
    .upd .box (.decl .nil x (.zint (.app1 .net (.app0 (.lit (zAddr n)))))) (φ.zT (n + 1))
  | .all x p φ => .all x p (φ.zT n)
  | .and φ ψ => .and (φ.zT n) (ψ.zT n)
  | .imp φ ψ => .imp φ (ψ.zT n)
  | φ => φ

/-- The fragment: binders of KeY's `int` under `∀`, `∧` and a consequent,
the rest first-order and reading no ledger. -/
def Fml.zOK {Γ : Ctx} : Fml C Γ → Bool
  | .bind _ _ .kint φ => φ.zOK
  | .all _ _ φ => φ.zOK
  | .and φ ψ => φ.zOK && ψ.zOK
  | .imp φ ψ => φ.netFree && ψ.zOK
  | φ => φ.netFree

/-- The most binders of KeY's `int` on a path. -/
def Fml.zDepth {Γ : Ctx} : Fml C Γ → Nat
  | .bind _ _ .kint φ => φ.zDepth + 1
  | .all _ _ φ => φ.zDepth
  | .and φ ψ => max φ.zDepth ψ.zDepth
  | .imp _ ψ => ψ.zDepth
  | _ => 0

/-- The formula binds a KeY `int` where `Fml.zT` reads it. -/
def Fml.hasZ {Γ : Ctx} : Fml C Γ → Bool
  | .bind _ _ .kint _ => true
  | .all _ _ φ => φ.hasZ
  | .and φ ψ => φ.hasZ || ψ.hasZ
  | .imp _ ψ => ψ.hasZ
  | _ => false

/-- The ledger entry at an address. -/
abbrev Ledger.at (L : Ledger) (a : PrimTy.uint.Denote) : Int := (lookupBy a L).getD 0

/-- **The declaration `{z := t}`**, `t` returning `v`, is `v` pushed. -/
theorem holds_upd_declZ {Γ : Ctx} (σ : State C Γ) (x : Var) (t : Tm C Γ .kint) {v : Int}
    (ht : t.eval σ = some v) (φ : Fml C (.kint :: Γ)) :
    holds σ (.upd .box (.decl .nil x (.zint t)) φ) ↔ holds (σ.push (t := .kint) v) φ := by
  show Upd.afterT .box σ _ _ ↔ _
  rw [Upd.afterT_applyV]
  have ha : (Upd.decl (Upd.nil (C := C) (Γ := Γ)) x (.zint t)).applyV σ =
      some (σ.globG, σ.locV.push (t := .kint) v) := by
    show (t.eval σ).bind (fun w => some (σ.globG, σ.locV.push (t := .kint) w)) = _
    rw [ht]; rfl
  rw [ha]
  constructor
  · intro h
    exact h _ rfl fun {u} i => by
      show (σ.push (t := .kint) v).locV u i = _
      rw [State.locV_push]; rfl
  · intro h σ' hg hl
    have e : σ' = σ.push (t := .kint) v := by
      apply State.eq_of_readsAs
      refine ⟨hg, fun {u} i => ?_⟩
      rw [hl i]
      show _ = (σ.push (t := .kint) v).locV u i
      rw [State.locV_push]; rfl
    rw [e]; exact h

theorem net_lit_eval {Γ : Ctx} (σ : State C Γ) (a : PrimTy.uint.Denote) :
    (Tm.app1 .net (.app0 (.lit a)) : Tm C Γ .kint).eval σ = some (σ.net.at a) := rfl

/-- **Refutation**: where the leaf holds, the rewritten leaf holds. -/
theorem Fml.holds_zT {Γ : Ctx} (n : Nat) (φ : Fml C Γ) (σ : State C Γ) (h : holds σ φ) :
    holds σ (φ.zT n) := by
  induction φ generalizing n with
  | bind m x t φ ih =>
    cases t
    case kint =>
      show holds σ (.upd .box _ _)
      rw [holds_upd_declZ σ x _ (net_lit_eval σ (zAddr n))]
      exact ih (n + 1) _ (h _)
    all_goals exact h
  | all x p φ ih => exact fun v => ih n _ (h v)
  | and φ ψ ihφ ihψ => exact ⟨ihφ n σ h.1, ihψ n σ h.2⟩
  | imp φ ψ _ ihψ => exact fun hφ => ihψ n σ (h hφ)
  | _ => exact h

/-- Two ledgers agree at the addresses of the first `n` binders. -/
def LedgerAgree (n : Nat) (L L₀ : Ledger) : Prop := ∀ k < n, L.at (zAddr k) = L₀.at (zAddr k)

theorem zAddr_inj {k n : Nat} (hk : k < 2 ^ 256) (hn : n < 2 ^ 256) (h : zAddr k = zAddr n) :
    k = n := by
  have := congrArg Subtype.val h
  rw [uintOfNat_val hk, uintOfNat_val hn] at this
  exact_mod_cast this

/-- **Soundness**, at a state: where the rewritten leaf holds with every
ledger agreeing with `L₀` at the outer binders' addresses, the leaf holds. -/
theorem Fml.zT_holds {Γ : Ctx} (n : Nat) (φ : Fml C Γ) (hok : φ.zOK = true)
    (hd : n + φ.zDepth ≤ 2 ^ 256) (σ : State C Γ) (L₀ : Ledger)
    (h : ∀ L, LedgerAgree n L L₀ → holds (σ.setNet L) (φ.zT n)) : holds σ φ := by
  induction φ generalizing n L₀ with
  | bind m x t φ ih =>
    cases t
    case kint =>
      simp only [Fml.zOK] at hok
      simp only [Fml.zDepth] at hd
      intro v
      apply ih (n + 1) hok (by omega) (σ.push (t := .kint) v) (setBy (zAddr n) v L₀)
      intro L hL
      have hv : L.at (zAddr n) = v := by
        rw [hL n (Nat.lt_succ_self n)]; simp only [Ledger.at, lookupBy_setBy_self, Option.getD_some]
      have hL' : LedgerAgree n L L₀ := fun k hk => by
        rw [hL k (Nat.lt_succ_of_lt hk)]
        have hne : zAddr k ≠ zAddr n := fun e =>
          Nat.ne_of_lt hk (zAddr_inj (by omega) (by omega) e)
        simp only [Ledger.at, lookupBy_setBy_ne hne]
      have := h L hL'
      rw [show (Fml.bind m x .kint φ).zT n = .upd .box (.decl .nil x
          (.zint (.app1 .net (.app0 (.lit (zAddr n)))))) (φ.zT (n + 1)) from rfl,
        holds_upd_declZ _ x _ (net_lit_eval _ (zAddr n))] at this
      rw [show (σ.setNet L).net.at (zAddr n) = v from hv] at this
      exact this
    all_goals simp only [Fml.zOK, Fml.netFree, Bool.false_eq_true] at hok
  | all x p φ ih =>
    exact fun v => ih n hok hd (σ.push (t := .val p) v) L₀ fun L hL => h L hL v
  | and φ ψ ihφ ihψ =>
    simp only [Fml.zOK, Bool.and_eq_true] at hok
    simp only [Fml.zDepth] at hd
    exact ⟨ihφ n hok.1 (by omega) σ L₀ fun L hL => (h L hL).1,
      ihψ n hok.2 (by omega) σ L₀ fun L hL => (h L hL).2⟩
  | imp φ ψ _ ihψ =>
    simp only [Fml.zOK, Bool.and_eq_true] at hok
    exact fun hφ => ihψ n hok.2 hd σ L₀ fun L hL => h L hL ((holds_setNet σ L φ hok.1).2 hφ)
  | tt => trivial
  | eq a b => exact (holds_setNet σ L₀ (.eq a b) hok).1 (h L₀ fun _ _ => rfl)
  | wellFormed s => exact (holds_setNet σ L₀ (.wellFormed s) hok).1 (h L₀ fun _ _ => rfl)
  | not φ _ => exact (holds_setNet σ L₀ (.not φ) hok).1 (h L₀ fun _ _ => rfl)
  | _ => simp only [Fml.zOK, Fml.netFree, Bool.false_eq_true] at hok

/-- **Soundness**: where the rewritten leaf is valid, the leaf is. -/
theorem Fml.zT_valid {φ : Fml C []} (hok : φ.zOK = true) (hd : φ.zDepth ≤ 2 ^ 256)
    (h : Fml.Valid (φ.zT 0)) : Fml.Valid φ := fun σ =>
  Fml.zT_holds 0 φ hok (by omega) σ [] fun L _ => h (σ.setNet L)

/-- info: 'Solidity.Fml.zT_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fml.zT_valid

/-- info: 'Solidity.Fml.holds_zT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fml.holds_zT

end Solidity
