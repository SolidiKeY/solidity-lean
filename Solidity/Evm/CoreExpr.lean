import Solidity.Evm.CoreSim
import Solidity.Semantics.RunErase

/-!
# Expressions over the scoped interpreter

`Evm/Correctness.lean`'s expression lemmas (`simple_sim` … `val_sim`), for
`Evm/CoreCompile.lean`'s code and `Semantics/Core.lean`'s evaluation
(`docs/intrinsic.md`, M5).  The simulation is `Evm/CoreSim.lean`'s `Sim`
with its locals read off the state: `Look.ofEnv σ.env`, each local's
denotation as `Semantics.lean` binds it (`LTy.enc`), and the global part
`σ.glob`.  A local is read at its level (`lvl b i`), never missing.

The dichotomies are the untyped compiler's: `ValOut` (a value pushed, or
both revert) and `LocOut` (a slot pushed, or both revert), stated on
`σ.glob`, whose storage both read.
-/

namespace Solidity.Evm
namespace Core

open Semantics
open SemanticsProperties
open Solidity.Core (Ctx Idx Ext Env)

variable {C : Contract}

/-! ## The locals of a state -/

/-- What the simulation reads of an environment's locals: each one's
denotation, as `Semantics.lean` binds it.  M3's instance of `Look`. -/
def Look.ofEnv {Γ : Ctx} (e : Env C Γ) : Look Γ := fun {t} i => Solidity.Core.LTy.enc C t (Env.get i e)

theorem Look.ofEnv_val {Γ : Ctx} {p : PrimTy} (e : Env C Γ) (i : Idx Γ (.val p)) :
    Look.ofEnv e i = .val (Env.get i e) := rfl

/-- An alias read through its binding is bound to the path it holds. -/
theorem Look.ofEnv_spath {Γ : Ctx} {R : RefTy} {e : Env C Γ} {i : Idx Γ (.alias R)} {r : Name}
    {segs : List Seg} (h : Look.ofEnv e i = .spath r segs) :
    (Env.get i e : Option (Name × List Seg)) = some (r, segs) := by
  unfold Look.ofEnv at h
  generalize (Env.get i e : Option (Name × List Seg)) = o at h ⊢
  rcases o with _ | ⟨r', segs'⟩
  · cases h
  · simp only [Solidity.Core.LTy.enc, Binding.spath.injEq] at h
    rw [h.1, h.2]

/-- A local declared: the pair's head. -/
theorem Look.ofEnv_cons {Γ : Ctx} {u : CLTy} (v : u.Denote C) (e : Env C Γ) {t : CLTy}
    (i : Idx (u :: Γ) t) :
    Look.ofEnv (Γ := u :: Γ) (v, e) i = Look.cons (Solidity.Core.LTy.enc C u v) (Look.ofEnv e) i := by
  cases i <;> rfl

/-- A local set. -/
theorem Look.ofEnv_set {Γ : Ctx} {u : CLTy} (i : Idx Γ u) (v : u.Denote C) (e : Env C Γ) {t : CLTy}
    (j : Idx Γ t) :
    Look.ofEnv (Env.set i v e) j = Look.set (Look.ofEnv e) i (Solidity.Core.LTy.enc C u v) j := by
  induction i with
  | here =>
    cases j with
    | here => rfl
    | there j => simp only [Look.set, Idx.toNat, Nat.add_one_ne_zero, ↓reduceIte]; rfl
  | there i ih =>
    cases j with
    | here => simp only [Look.set, Idx.toNat, Nat.zero_ne_add_one, ↓reduceIte]; rfl
    | there j =>
      have := ih v e.2 j
      simp only [Look.set, Idx.toNat, Nat.add_right_cancel_iff] at this ⊢
      exact this

/-- A scope's locals popped. -/
theorem Look.ofEnv_drop {Γ Δ : Ctx} (h : Ext Γ Δ) (e : Env C Δ) {t : CLTy} (i : Idx Γ t) :
    Look.ofEnv (Env.drop h e) i = Look.drop h (Look.ofEnv e) i := by
  induction h with
  | refl => rfl
  | push h ih => exact ih e.2

namespace Sim

variable {L b : Nat} {Γ : Ctx} {F : Frag Γ} {σ : State}

/-- `Sim` reads the locals pointwise. -/
theorem congrLook {ρ ρ' : Look Γ} {m : Machine} (h : Sim C L b F σ ρ m)
    (hρ : ∀ {t : CLTy} (i : Idx Γ t), ρ' i = ρ i) : Sim C L b F σ ρ' m := by
  refine ⟨h.store, fun i => ?_, fun i hi => ?_, h.net, h.netSelf, h.bound, fun i hi => ?_, h.env⟩
  · rw [hρ]; exact h.vals i
  · rw [hρ]; exact h.aliases i hi
  · rw [hρ]; exact h.fragile i hi

/-- `Sim` reads the global part through `storage`, `net` and `tx` only. -/
theorem congrGlob {σ' : State} {ρ : Look Γ} {m : Machine} (h : Sim C L b F σ ρ m)
    (hs : σ'.storage = σ.storage) (hn : σ'.net = σ.net) (ht : σ'.tx = σ.tx) :
    Sim C L b F σ' ρ m := by
  have hnet : ∀ a, σ'.getNet a = σ.getNet a := fun a => by simp only [State.getNet, hn]
  have hlive : ∀ r segs, σ'.findLive r segs = σ.findLive r segs := fun r segs => by
    simp only [State.findLive, hs]
  refine ⟨hs ▸ h.store, h.vals, h.aliases, fun a h1 h2 => (hnet a).trans (h.net a h1 h2),
    (hnet _).trans h.netSelf, h.bound, fun i hi => ?_, ?_⟩
  · obtain ⟨r, segs, s, h1, h2, h3, h4⟩ := h.fragile i hi
    exact ⟨r, segs, s, h1, h2, h3, by rw [hlive]; exact h4⟩
  · have := h.env; unfold EnvSim at this ⊢; rw [ht]; exact this

end Sim

/-! ## Expressions -/

variable {L b : Nat} {Γ : Ctx} {F : Frag Γ} {σ : Solidity.Core.State C Γ}

/-- A literal, a local or the environment pushes its value.

Example: `x` at level `0` is `MLOAD %0`, which pushes `x`'s word. -/
theorem simple_sim {m : Machine} (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m) :
    ∀ {p : PrimTy} (s : Solidity.Core.Simple C Γ p),
    simpleIn s = true → ValOut p (s.eval σ) (run (compileSimple b s) m) m
  | p, .lit n hr, _ => by
    cases p <;> simp only [PrimTy.inRange, decide_eq_true_eq, Bool.false_eq_true] at hr
    · exact .inl ⟨.int n, .val (toWord n), rfl,
        ⟨hr.1, hr.2, by simp only [toWord, hr.1, ↓reduceIte]⟩, rfl⟩
    · exact .inl ⟨.int n, .val (toWord n), rfl, ReprV.int hr.1 hr.2, rfl⟩
  | _, .bool b, _ => .inl ⟨.bool b, .val (bword b), rfl, rfl, rfl⟩
  | p, .local i, _ => by
    obtain ⟨v, henv, hv⟩ := hm.vals i
    rw [Look.ofEnv_val, Binding.val.injEq] at henv
    exact .inl ⟨v, m.memAt (lvl b i), by rw [← henv]; rfl, hv, rfl⟩
  | _, .env k hp, hw => by
    subst hp
    obtain ⟨h1, h2, h3, h4, w1, w2, w3, w4⟩ := hm.env
    have hn : ∀ n : Nat, n < W → ReprV .uint (.int n) (.val n) := fun n h =>
      ⟨by omega, by exact_mod_cast h, by simp⟩
    cases k
    · exact .inl ⟨_, _, by simp [Solidity.Core.Simple.eval, State.envVal, h1]; rfl, hn _ w1, rfl⟩
    · exact .inl ⟨_, _, by simp [Solidity.Core.Simple.eval, State.envVal, h2]; rfl, hn _ w2, rfl⟩
    · exact .inl ⟨_, _, by simp [Solidity.Core.Simple.eval, State.envVal, h3]; rfl, hn _ w3, rfl⟩
    · simp [simpleIn] at hw
    · exact .inl ⟨_, _, by simp [Solidity.Core.Simple.eval, State.envVal, h4]; rfl, hn _ w4, rfl⟩

mutual

/-- A storage path pushes its slot.

Example: after `Person storage p = folks[7];` (`p` at level `0`), `p.age`
compiles to `MLOAD %0; PUSH 2; ADD`, and `MLOAD %0` pushes `keccak(7, 7)`. -/
theorem spath_sim : ∀ {T : Ty} (q : Solidity.Core.SPath C Γ T) {free : Bool} {m : Machine},
    Sim C L b F σ.glob (Look.ofEnv σ.env) m → spathIn F free q = true →
      LocOut C L σ.glob free T (q.resolve σ) (run (compileSPath b q) m) m
  | _, @Solidity.Core.SPath.alias _ _ R i, free, m, hm, hw => by
    simp only [spathIn, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true'] at hw
    have hmem : ∀ {s : Slot}, m.memAt (lvl b i) = .slot s →
        run (compileSPath b (Solidity.Core.SPath.alias (C := C) i)) m = .ok (m.push (.slot s)) 0 := fun h => by
      simp only [compileSPath, run, exec_cons_zero, Instr.step, Machine.next]
      rw [show m.mem (cellOf b i) = m.memAt (lvl b i) from rfl, h]; rfl
    rcases hw with hx | ⟨rfl, hx⟩
    · obtain ⟨r, segs, s, henv, hm', hp⟩ := hm.aliases i hx
      rcases find_repr hm.store hp with ⟨sv, hsv, hr⟩ | ⟨h, _⟩
      · refine .inl ⟨r, segs, s, sv, ?_, hsv, hp.ofTrue free, hr, hmem hm'⟩
        simp only [Solidity.Core.SPath.resolve, Solidity.Core.aliasPath,
          Look.ofEnv_spath henv]; rfl
      · cases h
    · obtain ⟨r, segs, s, henv, hm', hp, sv₀, hsv₀⟩ := hm.fragile i hx
      rcases find_repr hm.store hp with ⟨sv, hsv, hr⟩ | ⟨_, hsv⟩
      · refine .inl ⟨r, segs, s, sv, ?_, hsv, hp, hr, hmem hm'⟩
        simp only [Solidity.Core.SPath.resolve, Solidity.Core.aliasPath,
          Look.ofEnv_spath henv]; rfl
      · rw [hsv₀] at hsv; cases hsv
  | _, .loc l, free, m, hm, hw => by
    simp only [Solidity.Core.SPath.resolve, compileSPath]
    exact loc_sim l hm (by simpa [spathIn] using hw)

/-- A location pushes its slot, checking every array index against the
length on the way.

Example: `folks[7].age` pushes `keccak(7, 7) + 2`; `persons[5].age` with three
persons reverts at the bounds check, as the interpreter's read does. -/
theorem loc_sim : ∀ {T : Ty} (l : Solidity.Core.Loc C Γ T) {free : Bool} {m : Machine},
    Sim C L b F σ.glob (Look.ofEnv σ.env) m → locIn F free l = true →
      LocOut C L σ.glob free T (l.resolve σ) (run (compileLoc b l) m) m
  | _, .root r h, free, m, hm, _ => by
    obtain ⟨sv, hl, hr⟩ := hm.store r _ h
    exact .inl ⟨r, [], rootSlot C r, sv, rfl, by simp [State.findLive, hl], .root h, hr, rfl⟩
  | _, @Solidity.Core.Loc.field _ _ s T q f h, free, m, hm, hw => by
    have hwb : spathIn F free q = true := by simpa [locIn] using hw
    have h' : lookupBy f (structDef s) = some T := h
    simp only [Solidity.Core.Loc.resolve, compileLoc]
    rcases spath_sim q hm hwb with ⟨r, segs, s₀, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
    · cases hr with
      | struct hex hall =>
        obtain ⟨v, hv⟩ := hex f T h'
        refine .inl ⟨r, segs ++ [.field f], s₀.add (offset s f), v, ?_, ?_, .field hp h,
          hall f T v h' hv, ?_⟩
        · simp [hres]; rfl
        · rw [findLive_append, hsv]; simp [bind, Except.bind, SVal.findLive, hv]
        · rw [run_append_ok hrun]; simp [run, Instr.step, Machine.next, Machine.push]
    · exact .inr ⟨by simp [hres]; rfl, run_append_revert hrun⟩
  | _, @Solidity.Core.Loc.index _ _ _ k V .map q i, free, m, hm, hw => by
    have ihb : ∀ {m : Machine}, Sim C L b F σ.glob (Look.ofEnv σ.env) m →
        spathIn F free q = true →
        LocOut C L σ.glob free _ (q.resolve σ) (run (compileSPath b q) m) m :=
      fun hm hw => spath_sim q hm hw
    have ihi : ∀ {m : Machine}, Sim C L b F σ.glob (Look.ofEnv σ.env) m → valIn F i = true →
        ValOut _ (i.eval σ) (run (compileVal b i) m) m := fun hm hw => val_sim i hm hw
    rw [locIn] at hw
    simp only [Bool.and_eq_true, beq_iff_eq] at hw
    obtain ⟨⟨rfl, hwb⟩, hwi⟩ := hw
    simp only [Solidity.Core.Loc.resolve, compileLoc, List.append_assoc]
    rcases ihb hm hwb with ⟨r, segs, s₀, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
    · cases hr with
      | mapOther hK => exact absurd rfl hK
      | map hall =>
        rename_i entries dflt
        rw [run_append_ok hrun]
        rcases ihi (hm.push _) hwi with ⟨v, w, hv, hrep, hrun'⟩ | ⟨hv, hrun'⟩
        · obtain ⟨n, hn, rfl, rfl⟩ := hrep.uint_inv
          have hp' := PathSlot.key hp (Int.natCast_nonneg n) (by omega)
          rw [Int.toNat_natCast] at hp'
          refine .inl ⟨r, segs ++ [.at n], .hash n s₀ 0, _, ?_, ?_, hp', hall n hn, ?_⟩
          · simp [hres, hv, Value.asInt, State.checkIndex, State.findStorage_of_findLive hsv, bind,
              Except.bind, pure, Except.pure] <;> rfl
          · rw [findLive_append, hsv]
            simp only [bind, Except.bind, SVal.findLive]
            cases lookupBy (n : Int) entries <;> simp
          · rw [run_append_ok hrun']; simp [run, Instr.step, Machine.next, Machine.push]
        · exact .inr ⟨by simp [hres, hv]; rfl, run_append_revert hrun'⟩
    · exact .inr ⟨by simp [hres]; rfl, run_append_revert hrun⟩
  | _, @Solidity.Core.Loc.index _ _ _ _ E (.arr .dyn) q i, free, m, hm, hw => by
    have ihb : ∀ {m : Machine}, Sim C L b F σ.glob (Look.ofEnv σ.env) m →
        spathIn F free q = true →
        LocOut C L σ.glob free _ (q.resolve σ) (run (compileSPath b q) m) m :=
      fun hm hw => spath_sim q hm hw
    have ihi : ∀ {m : Machine}, Sim C L b F σ.glob (Look.ofEnv σ.env) m → valIn F i = true →
        ValOut _ (i.eval σ) (run (compileVal b i) m) m := fun hm hw => val_sim i hm hw
    rw [locIn] at hw
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hw
    obtain ⟨⟨rfl, hwb⟩, hwi⟩ := hw
    simp only [compileLoc, List.append_assoc]
    rcases ihb hm hwb with ⟨r, segs, s₀, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
    · cases hr with
      | array hl hW hall =>
        rename_i elems shadow
        rw [run_append_ok hrun]
        rcases ihi (hm.push _) hwi with ⟨v, w, hv, hrep, hrun'⟩ | ⟨hv, hrun'⟩
        · obtain ⟨n, hn, rfl, rfl⟩ := hrep.uint_inv
          rw [run_append_ok hrun']
          have hsv' := State.findStorage_of_findLive hsv
          have hres' : (Solidity.Core.Loc.index (.arr .dyn) q i).resolve σ =
              (if n < elems.length then .ok (r, segs ++ [.at n]) else .error .revert) := by
            by_cases hin : n < elems.length <;>
              simp [Solidity.Core.Loc.resolve, hres, hv, Value.asInt, State.checkIndex, hsv', hin,
                bind, Except.bind, pure, Except.pure] <;> rfl
          rw [hres']
          have hb := boundsCheck_run m m.stack (elemSlot (size E)) n s₀
          simp only [Machine.push] at hb ⊢
          rw [hb, hl]
          by_cases hin : n < elems.length
          · rw [if_pos hin, if_pos hin]
            have hp' := PathSlot.elem hp (Int.natCast_nonneg n) (by omega)
            rw [Int.toNat_natCast] at hp'
            refine .inl ⟨r, segs ++ [.at n], .data s₀ (n * size E), elems[n], rfl, ?_, hp',
              hall n hin, elemSlot_run m m.stack n (size E) s₀⟩
            rw [findLive_append, hsv]
            simp [bind, Except.bind, SVal.findLive, hin]
          · rw [if_neg hin, if_neg hin]
            exact .inr ⟨rfl, rfl⟩
        · exact .inr ⟨by simp [Solidity.Core.Loc.resolve, hres, hv]; rfl,
            run_append_revert hrun'⟩
    · exact .inr ⟨by simp [Solidity.Core.Loc.resolve, hres]; rfl, run_append_revert hrun⟩
  | _, @Solidity.Core.Loc.index _ _ _ _ E (@IndexTy.arr _ _ (@ArrTy.fixed _ n)) q i, free, m,
      hm, hw => by
    have ihb : ∀ {m : Machine}, Sim C L b F σ.glob (Look.ofEnv σ.env) m →
        spathIn F free q = true →
        LocOut C L σ.glob free _ (q.resolve σ) (run (compileSPath b q) m) m :=
      fun hm hw => spath_sim q hm hw
    have ihi : ∀ {m : Machine}, Sim C L b F σ.glob (Look.ofEnv σ.env) m → valIn F i = true →
        ValOut _ (i.eval σ) (run (compileVal b i) m) m := fun hm hw => val_sim i hm hw
    rw [locIn] at hw
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hw
    obtain ⟨⟨rfl, hwb⟩, hwi⟩ := hw
    simp only [compileLoc, List.append_assoc]
    rcases ihb hm hwb with ⟨r, segs, s₀, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
    · cases hr with
      | fixed hl hall =>
        rename_i elems shadow
        rw [run_append_ok hrun]
        rcases ihi (hm.push _) hwi with ⟨v, w, hv, hrep, hrun'⟩ | ⟨hv, hrun'⟩
        · obtain ⟨k, hk, rfl, rfl⟩ := hrep.uint_inv
          rw [run_append_ok hrun']
          have hsv' := State.findStorage_of_findLive hsv
          have hres' : (Solidity.Core.Loc.index (.arr .fixed) q i).resolve σ =
              (if k < elems.length then .ok (r, segs ++ [.at k]) else .error .revert) := by
            by_cases hin : k < elems.length <;>
              simp [Solidity.Core.Loc.resolve, hres, hv, Value.asInt, State.checkIndex, hsv', hin,
                bind, Except.bind, pure, Except.pure] <;> rfl
          rw [hres']
          have hb := fixedCheck_run m m.stack (fixedSlot (size E)) n k s₀
          simp only [Machine.push] at hb ⊢
          rw [hb, ← hl]
          by_cases hin : k < elems.length
          · rw [if_pos hin, if_pos hin]
            have hp' := PathSlot.felem hp (Int.natCast_nonneg k) (by omega)
            rw [Int.toNat_natCast] at hp'
            refine .inl ⟨r, segs ++ [.at k], s₀.add (k * size E), elems[k], rfl, ?_, hp',
              hall k hin, fixedSlot_run m m.stack k (size E) s₀⟩
            rw [findLive_append, hsv]
            simp [bind, Except.bind, SVal.findLive, hin]
          · rw [if_neg hin, if_neg hin]
            exact .inr ⟨rfl, rfl⟩
        · exact .inr ⟨by simp [Solidity.Core.Loc.resolve, hres, hv]; rfl,
            run_append_revert hrun'⟩
    · exact .inr ⟨by simp [Solidity.Core.Loc.resolve, hres]; rfl, run_append_revert hrun⟩

/-- An expression pushes its value, or reverts where the interpreter does.

Example: `total * 2` pushes twice `total`'s word, and reverts with the
interpreter when that overflows; `c ? a : b` runs only the branch `c` picks. -/
theorem val_sim : ∀ {p : PrimTy} (e : Solidity.Core.Val C Γ p) {m : Machine},
    Sim C L b F σ.glob (Look.ofEnv σ.env) m → valIn F e = true →
      ValOut p (e.eval σ) (run (compileVal b e) m) m
  | _, .simple s, m, hm, hw => by
    simp only [Solidity.Core.Val.eval, compileVal]
    exact simple_sim hm s (by simpa [valIn] using hw)
  | p, .read l, m, hm, hw => by
    simp only [valIn] at hw
    simp only [Solidity.Core.Val.eval, compileVal]
    rcases loc_sim l hm hw with ⟨r, segs, s, sv, hres, hsv, _, hr, hrun⟩ | ⟨hres, hrun⟩
    · rw [run_append_ok hrun]
      obtain ⟨v, hv, hrv, _⟩ := prim_read hr
      refine .inl ⟨v, .val (m.store s), ?_, hrv, rfl⟩
      simp [hres, (State.findStorage_of_findLive hsv), hv, bind, Except.bind]
    · exact .inr ⟨by simp [hres]; rfl, run_append_revert hrun⟩
  | _, @Solidity.Core.Val.binop _ _ p q op hacc hq x y, m, hm, hw => by
    have iha : ∀ {m : Machine}, Sim C L b F σ.glob (Look.ofEnv σ.env) m → valIn F x = true →
        ValOut p (x.eval σ) (run (compileVal b x) m) m := fun hm hw => val_sim x hm hw
    have ihb : ∀ {m : Machine}, Sim C L b F σ.glob (Look.ofEnv σ.env) m → valIn F y = true →
        ValOut p (y.eval σ) (run (compileVal b y) m) m := fun hm hw => val_sim y hm hw
    subst hq
    simp only [valIn, Bool.and_eq_true] at hw
    obtain ⟨⟨hop, hwa⟩, hwb⟩ := hw
    simp only [Solidity.Core.Val.eval]
    by_cases hand : op = .and
    · subst hand
      obtain rfl : p = .bool := by cases p <;> simp [binInFrag] at hop ⊢
      simp only [compileVal, List.append_assoc]
      rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
      · obtain ⟨z, rfl, rfl⟩ := hra.bool_inv
        rw [run_append_ok hruna, hva]
        cases z
        · refine .inl ⟨.bool false, .val (bword false), rfl, rfl, ?_⟩
          rw [show [Instr.dup 1, .iszero, .jumpi ((compileVal b y).length + 1), .pop] ++
              compileVal b y = [Instr.dup 1, .iszero, .jumpi ((compileVal b y).length + 1)] ++
              ([.pop] ++ compileVal b y) from rfl,
            run_append_skip (m' := m.push (.val (bword false)))
            (k := (compileVal b y).length + 1) rfl]
          exact exec_length ([.pop] ++ compileVal b y) _
        · rw [show [Instr.dup 1, .iszero, .jumpi ((compileVal b y).length + 1), .pop] ++
              compileVal b y = [Instr.dup 1, .iszero, .jumpi ((compileVal b y).length + 1), .pop] ++
              compileVal b y from rfl, run_append_ok (m' := m) rfl]
          rcases ihb hm hwb with ⟨vb, wb, hvb, hrb, hrunb⟩ | ⟨hvb, hrunb⟩
          · obtain ⟨z, rfl, rfl⟩ := hrb.bool_inv
            refine .inl ⟨.bool z, .val (bword z), ?_, rfl, hrunb⟩
            simp [evalBinop, hvb, applyBinOp, Value.asBool, checkArith, bind, Except.bind]
          · exact .inr ⟨by simp [evalBinop, hvb, bind, Except.bind], hrunb⟩
      · exact .inr ⟨by simp [hva, bind, Except.bind], run_append_revert hruna⟩
    by_cases hor : op = .or
    · subst hor
      obtain rfl : p = .bool := by cases p <;> simp [binInFrag] at hop ⊢
      simp only [compileVal, List.append_assoc]
      rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
      · obtain ⟨z, rfl, rfl⟩ := hra.bool_inv
        rw [run_append_ok hruna, hva]
        cases z
        · rw [show [Instr.dup 1, .jumpi ((compileVal b y).length + 1), .pop] ++ compileVal b y
            = [Instr.dup 1, .jumpi ((compileVal b y).length + 1), .pop] ++ compileVal b y
            from rfl, run_append_ok (m' := m) rfl]
          rcases ihb hm hwb with ⟨vb, wb, hvb, hrb, hrunb⟩ | ⟨hvb, hrunb⟩
          · obtain ⟨z, rfl, rfl⟩ := hrb.bool_inv
            refine .inl ⟨.bool z, .val (bword z), ?_, rfl, hrunb⟩
            simp [evalBinop, hvb, applyBinOp, Value.asBool, checkArith, bind, Except.bind]
          · exact .inr ⟨by simp [evalBinop, hvb, bind, Except.bind], hrunb⟩
        · refine .inl ⟨.bool true, .val (bword true), rfl, rfl, ?_⟩
          rw [show [Instr.dup 1, .jumpi ((compileVal b y).length + 1), .pop] ++ compileVal b y
            = [Instr.dup 1, .jumpi ((compileVal b y).length + 1)] ++ ([.pop] ++ compileVal b y)
            from rfl, run_append_skip (m' := m.push (.val (bword true)))
            (k := (compileVal b y).length + 1) rfl]
          exact exec_length ([.pop] ++ compileVal b y) _
      · exact .inr ⟨by simp [hva, bind, Except.bind], run_append_revert hruna⟩
    have hcode : compileVal b (.binop op hacc rfl x y) =
        compileVal b x ++ compileVal b y ++ binTail p op := by
      cases op <;> simp_all [compileVal]
    rw [hcode, List.append_assoc]
    rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
    · rw [run_append_ok hruna, hva]
      simp only [bind, Except.bind]
      rw [evalBinop_eq hand hor]
      rcases ihb (hm.push wa) hwb with ⟨vb, wb, hvb, hrb, hrunb⟩ | ⟨hvb, hrunb⟩
      · rw [run_append_ok hrunb, hvb]
        exact tail_sim hop hand hor hra hrb m
      · exact .inr ⟨by rw [hvb]; rfl, run_append_revert hrunb⟩
    · exact .inr ⟨by simp [hva, bind, Except.bind], run_append_revert hruna⟩
  | _, @Solidity.Core.Val.unop _ _ p q op hacc hq x, m, hm, hw => by
    have iha : ∀ {m : Machine}, Sim C L b F σ.glob (Look.ofEnv σ.env) m → valIn F x = true →
        ValOut p (x.eval σ) (run (compileVal b x) m) m := fun hm hw => val_sim x hm hw
    subst hq
    simp only [valIn, Bool.and_eq_true] at hw
    obtain ⟨hop, hwa⟩ := hw
    cases op with
    | not =>
      obtain rfl : p = .bool := by cases p <;> simp [UnOp.accepts] at hacc ⊢
      simp only [Solidity.Core.Val.eval, compileVal]
      rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
      · obtain ⟨z, rfl, rfl⟩ := hra.bool_inv
        rw [run_append_ok hruna, hva]
        refine .inl ⟨.bool !z, .val (bword !z), ?_, rfl, ?_⟩
        · simp [applyUnOp, Value.asBool, unopCheck, bind, Except.bind]; rfl
        · cases z <;> rfl
      · exact .inr ⟨by simp [hva, bind, Except.bind], run_append_revert hruna⟩
    | neg =>
      obtain rfl : p = .int := by simpa [unInFrag] using hop
      simp only [Solidity.Core.Val.eval, compileVal]
      rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
      · obtain ⟨a, ha, rfl, rfl⟩ := hra.int_inv
        rw [run_append_ok hruna, hva]
        simp only [Machine.push]
        rw [neg_run m m.stack ha]
        change ValOut _ (checkArith (.prim .int) (.int (-sgn a))) _ _
        rw [checkArith_int]
        by_cases h : -(H : Int) ≤ -sgn a ∧ -sgn a < H
        · rw [if_pos h, if_pos h]; exact .inl ⟨_, _, rfl, ReprV.int h.1 h.2, rfl⟩
        · rw [if_neg h, if_neg h]; exact .inr ⟨rfl, rfl⟩
      · exact .inr ⟨by simp [hva, bind, Except.bind], run_append_revert hruna⟩
    | bnot =>
      obtain rfl : p = .uint := by simpa [unInFrag] using hop
      simp only [Solidity.Core.Val.eval, compileVal]
      rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
      · obtain ⟨a, ha, rfl, rfl⟩ := hra.uint_inv
        rw [run_append_ok hruna, hva]
        have := W_pos
        refine .inl ⟨.int ↑(W - 1 - a), .val (W - 1 - a), ?_, ReprV.uint (by omega), ?_⟩
        · simp only [applyUnOp, Value.asInt, unopCheck, bind, Except.bind, pure, Except.pure,
            uintBound_eq]
          congr 2; omega
        · simp [run, Instr.step, Machine.next]; rfl
      · exact .inr ⟨by simp [hva, bind, Except.bind], run_append_revert hruna⟩
  | p, .ternary c x y, m, hm, hw => by
    have ihc : ∀ {m : Machine}, Sim C L b F σ.glob (Look.ofEnv σ.env) m → valIn F c = true →
        ValOut .bool (c.eval σ) (run (compileVal b c) m) m := fun hm hw => val_sim c hm hw
    have iha : ∀ {m : Machine}, Sim C L b F σ.glob (Look.ofEnv σ.env) m → valIn F x = true →
        ValOut p (x.eval σ) (run (compileVal b x) m) m := fun hm hw => val_sim x hm hw
    have ihb : ∀ {m : Machine}, Sim C L b F σ.glob (Look.ofEnv σ.env) m → valIn F y = true →
        ValOut p (y.eval σ) (run (compileVal b y) m) m := fun hm hw => val_sim y hm hw
    simp only [valIn, Bool.and_eq_true] at hw
    obtain ⟨⟨hwc, hwa⟩, hwb⟩ := hw
    simp only [Solidity.Core.Val.eval, compileVal, List.append_assoc]
    rcases ihc hm hwc with ⟨vc, wc, hvc, hrc, hrunc⟩ | ⟨hvc, hrunc⟩
    · obtain ⟨z, rfl, rfl⟩ := hrc.bool_inv
      rw [run_append_ok hrunc, hvc]
      cases z
      · rw [run_append_skip (m' := m) (k := (compileVal b x).length + 1) rfl,
          show (compileVal b x).length + 1 = (compileVal b x).length + 1 from rfl, exec_append,
          exec_skip]
        simp only [Out.ok_bind]
        exact ihb hm hwb
      · rw [run_append_skip (m' := m) (k := 0) rfl]
        rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
        · refine .inl ⟨va, wa, hva, hra, ?_⟩
          change run _ m = _
          rw [run_append_ok hruna]
          exact exec_length _ _
        · exact .inr ⟨hva, run_append_revert hruna⟩
    · exact .inr ⟨by simp [hvc, bind, Except.bind], run_append_revert hrunc⟩
  | _, .len q hp, m, hm, hw => by
    cases hp
    simp only [valIn] at hw
    simp only [Solidity.Core.Val.eval, compileVal]
    rcases spath_sim q hm hw with ⟨r, segs, s, sv, hres, hsv, _, hr, hrun⟩ | ⟨hres, hrun⟩
    · cases hr with
      | @array _ _ elems shadow hl hW _ =>
        rw [run_append_ok hrun]
        have := hm.bound; have := Lmax_lt_W
        refine .inl ⟨.int elems.length, .val elems.length, ?_, ReprV.uint (by omega), ?_⟩
        · simp [hres, State.findStorage_of_findLive hsv, arrayLen, bind, Except.bind]; rfl
        · simp [run, Instr.step, Machine.next, Machine.push, hl]
    · exact .inr ⟨by simp [hres]; rfl, run_append_revert hrun⟩
  | _, .readMem _, _, _, hw => by simp [valIn] at hw
  | _, .mlen .., _, _, hw => by simp [valIn] at hw

end

end Core
end Solidity.Evm
