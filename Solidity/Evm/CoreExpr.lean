import Solidity.Evm.CoreSim

/-!
# Expressions over the typed run

`Evm/Correctness.lean`'s expression lemmas (`simple_sim` … `val_sim`), for
`Evm/CoreCompile.lean`'s code and the typed run's evaluation
(`Semantics/Core/TypedRun.lean`, `docs/intrinsic.md`, W1).  The simulation
is `Evm/CoreSim.lean`'s `Sim` with its locals read off the typed state:
`Look.ofTEnv σ.env`, each local as it is typed (a value, the reference an
alias holds), and the global part `σ.sem`, the storage erased, which the
machine-level lemmas of `Evm/Repr.lean` read.  A local is read at its level
(`lvl b i`), never missing.

The dichotomies are the untyped compiler's on typed results: `ValOutT` (a
value pushed, or both revert) and `LocOutT` (the slot of a reference
pushed, or both revert).  A typed operator's agreement with the untyped one
(`BinOp.evalT_erase`, `UnOp.evalT_erase`, `Storage.*_erase`) carries the
machine-level lemmas over (`ValOutT.ofRes`).
-/

namespace Solidity.Evm
namespace Core

open Semantics
open SemanticsProperties
open Solidity.Core (Ctx Idx Ext TEnv TState SRef TRes HTy)

variable {C : Contract}

/-! ## The global part of a typed state -/

/-- What the machine-level lemmas read of a typed state: its storage erased,
its ledger, its funds and its transaction (`ReprStore`, `EnvSim`).  Its
locals are `Look.ofTEnv`'s. -/
def _root_.Solidity.Core.TState.sem {Γ : Ctx} (σ : TState C Γ) : State :=
  { storage := σ.storage.erase, net := σ.net, selfBalance := σ.selfBalance.1, tx := σ.tx.erase }

theorem sem_storage {Γ : Ctx} (σ : TState C Γ) : σ.sem.storage = σ.storage.erase := rfl

/-- A payment is booked on the same ledger. -/
theorem sem_pay {Γ : Ctx} (σ : TState C Γ) (a x : Int) : (σ.pay a x).sem = σ.sem.pay a x := rfl

/-! ## The locals of a typed state -/

/-- A typed local, as the simulation reads it. -/
def see {H : HTy} : (t : CLTy) → t.TDenote C H → Seen C t
  | .val _, v => v
  | .alias _, a => a
  | .mem _, _ | .old, _ | .oldNet, _ => ()

/-- The locals of a typed state, as the simulation reads them. -/
def Look.ofTEnv {H : HTy} {Γ : Ctx} (e : TEnv C H Γ) : Look C Γ :=
  fun {t} i => see t (TEnv.get i e)

theorem Look.ofTEnv_val {H : HTy} {Γ : Ctx} {p : PrimTy} (e : TEnv C H Γ) (i : Idx Γ (.val p)) :
    Look.ofTEnv e i = TEnv.get i e := rfl

theorem Look.ofTEnv_alias {H : HTy} {Γ : Ctx} {R : RefTy} (e : TEnv C H Γ)
    (i : Idx Γ (.alias R)) : Look.ofTEnv e i = TEnv.get i e := rfl

/-- A local declared: the pair's head. -/
theorem Look.ofTEnv_cons {H : HTy} {Γ : Ctx} {u : CLTy} (v : u.TDenote C H) (e : TEnv C H Γ)
    {t : CLTy} (i : Idx (u :: Γ) t) :
    Look.ofTEnv (Γ := u :: Γ) (v, e) i = Look.cons (see u v) (Look.ofTEnv e) i := by
  cases i <;> rfl

/-- A local set. -/
theorem Look.ofTEnv_set {H : HTy} {Γ : Ctx} {u : CLTy} (i : Idx Γ u) (v : u.TDenote C H)
    (e : TEnv C H Γ) {t : CLTy} (j : Idx Γ t) :
    Look.ofTEnv (TEnv.set i v e) j = Look.set (Look.ofTEnv e) i (see u v) j := by
  induction i with
  | here => cases j <;> rfl
  | there i ih =>
    cases j with
    | here => rfl
    | there j => exact ih v e.2 j

/-- A scope's locals popped. -/
theorem Look.ofTEnv_drop {H : HTy} {Γ Δ : Ctx} (h : Ext Γ Δ) (e : TEnv C H Δ) {t : CLTy}
    (i : Idx Γ t) : Look.ofTEnv (TEnv.drop h e) i = Look.drop h (Look.ofTEnv e) i := by
  induction h with
  | refl => rfl
  | push h ih => exact ih e.2

theorem see_wk {H H' : HTy} (x : H <+: H') :
    (t : CLTy) → (v : t.TDenote C H) → see t (Solidity.Core.LTy.TDenote.wk x t v) = see t v
  | .val _, _ | .alias _, _ | .mem _, _ | .old, _ | .oldNet, _ => rfl

theorem TEnv.get_wk {H H' : HTy} (x : H <+: H') :
    {Γ : Ctx} → {t : CLTy} → (i : Idx Γ t) → (e : TEnv C H Γ) →
      TEnv.get i (TEnv.wk x Γ e) = Solidity.Core.LTy.TDenote.wk x t (TEnv.get i e)
  | _ :: _, _, .here, _ => rfl
  | _ :: _, _, .there i, e => TEnv.get_wk x i e.2

/-- The locals over a grown heap read as they did. -/
theorem Look.ofTEnv_wk {H H' : HTy} {Γ : Ctx} (x : H <+: H') (e : TEnv C H Γ) {t : CLTy}
    (i : Idx Γ t) : Look.ofTEnv (TEnv.wk x Γ e) i = Look.ofTEnv e i := by
  simp only [Look.ofTEnv, TEnv.get_wk, see_wk]

namespace Sim

variable {L b : Nat} {Γ : Ctx} {F : Frag Γ} {σ : State}

/-- `Sim` reads the global part through `storage`, `net` and `tx` only. -/
theorem congrGlob {σ' : State} {ρ : Look C Γ} {m : Machine} (h : Sim C L b F σ ρ m)
    (hs : σ'.storage = σ.storage) (hn : σ'.net = σ.net) (ht : σ'.tx = σ.tx) :
    Sim C L b F σ' ρ m := by
  have hnet : ∀ a, σ'.getNet a = σ.getNet a := fun a => by simp only [State.getNet, hn]
  have hlive : ∀ r segs, σ'.findLive r segs = σ.findLive r segs := fun r segs => by
    simp only [State.findLive, hs]
  refine ⟨hs ▸ h.store, h.vals, h.aliases, fun a h1 h2 => (hnet a).trans (h.net a h1 h2),
    (hnet _).trans h.netSelf, h.bound, fun i hi => ?_, ?_⟩
  · obtain ⟨r, s, h1, h2, h3, h4⟩ := h.fragile i hi
    exact ⟨r, s, h1, h2, h3, by rw [hlive]; exact h4⟩
  · have := h.env; unfold EnvSim at this ⊢; rw [ht]; exact this

end Sim

/-! ## Typed results -/

/-- A value expression's outcome: the value pushed, or both revert. -/
def ValOutT (p : PrimTy) (res : TRes p.Denote) (out : Out) (m : Machine) : Prop :=
  (∃ v w, res = .ok v ∧ ReprV p (PrimTy.erase v) w ∧ out = .ok (m.push w) 0) ∨
    (res = .error .revert ∧ out = .revert)

/-- A location's outcome: the slot of the reference pushed, the reference
live and its value laid out there; or both revert. -/
def LocOutT (C : Contract) (L : Nat) (σ : State) (free : Bool) (T : Ty) (res : TRes (SRef C T))
    (out : Out) (m : Machine) : Prop :=
  (∃ r s sv, res = .ok r ∧ σ.findLive r.root r.path.erase = .ok sv ∧
      PathSlot C free r.root r.path.erase T s ∧ ReprAt m.store L T s sv ∧
      out = .ok (m.push (.slot s)) 0) ∨
    (res = .error .revert ∧ out = .revert)

/-- The untyped outcome of an operator that agrees with a typed one. -/
theorem ValOutT.ofRes {p : PrimTy} {o : Option p.Denote} {out : Out} {m : Machine}
    (h : ValOut p (Solidity.Core.toRes PrimTy.erase o) out m) :
    ValOutT p (TRes.ofOpt o) out m := by
  cases o with
  | none =>
    rcases h with ⟨_, _, h, _⟩ | ⟨_, h⟩
    · cases h
    · exact .inr ⟨rfl, h⟩
  | some v =>
    rcases h with ⟨v', w, h, hr, hout⟩ | ⟨h, _⟩
    · cases h; exact .inl ⟨v, w, rfl, hr, hout⟩
    · cases h

/-- A reference found live is found, typed. -/
theorem find_of_findLive {Γ : Ctx} {σ : TState C Γ} {U : Ty} {r : SRef C U} {sv : SVal}
    (h : σ.sem.findLive r.root r.path.erase = .ok sv) :
    ∃ tv, σ.storage.find r = some tv ∧ tv.erase = sv := by
  have h' := State.findStorage_of_findLive h
  rw [Solidity.Core.Storage.findStorage_erase (σ := σ.sem) rfl r] at h'
  cases hf : σ.storage.find r with
  | none => rw [hf] at h'; cases h'
  | some tv => rw [hf] at h'; cases h'; exact ⟨tv, rfl, rfl⟩

theorem sref_erase_field {s f : Name} {T : Ty} (r : SRef C (.ref (.struct s)))
    (h : C.fieldType s f = some T) :
    (r.field h).root = r.root ∧ (r.field h).path.erase = r.path.erase ++ [.field f] := by
  refine ⟨rfl, ?_⟩
  simp only [SRef.field, SRef.append, Solidity.Core.Path.erase_append]
  rfl

theorem sref_erase_index {R : RefTy} {k : PrimTy} {V : Ty} (r : SRef C (.ref R))
    (it : IndexTy R k V) (i : Int) :
    (r.index it i).root = r.root ∧ (r.index it i).path.erase = r.path.erase ++ [.at i] := by
  refine ⟨rfl, ?_⟩
  simp only [SRef.index, SRef.append, Solidity.Core.Path.erase_append,
    Solidity.Core.Path.erase_index]

/-- An index check, read off the untyped one. -/
theorem checkT {Γ : Ctx} {σ : TState C Γ} {R : RefTy} {k : PrimTy} {V : Ty} (r : SRef C (.ref R))
    (it : IndexTy R k V) (n : Int) {c : Bool}
    (h : σ.sem.checkIndex r.root r.path.erase n = if c then .ok () else .error .revert) :
    TRes.ofOpt (σ.storage.checkIndex r it n) = if c then .ok () else .error .revert := by
  rw [Solidity.Core.Storage.checkIndex_erase (σ := σ.sem) rfl r it n] at h
  cases hc : σ.storage.checkIndex r it n <;> rw [hc] at h <;> cases c <;>
    simp only [Solidity.Core.toRes, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h ⊢ <;> rfl

/-- A word stored, read back at its type. -/
theorem asValue_erase_prim {p : PrimTy} (v : Solidity.Core.SVal (.prim p)) :
    v.erase.asValue = .ok (PrimTy.erase (Solidity.Core.SVal.view v)) := by
  cases v with
  | prim x => rw [Solidity.Core.SVal.erase_prim]; cases p <;> rfl

/-! ## Expressions -/

variable {L b : Nat} {Γ : Ctx} {F : Frag Γ} {σ : TState C Γ}

/-- A literal, a local or the environment pushes its value.

Example: `x` at level `0` is `MLOAD %0`, which pushes `x`'s word. -/
theorem simple_sim {m : Machine} (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) :
    ∀ {p : PrimTy} (s : Solidity.Core.Simple C Γ p), simpleIn s = true →
      ∃ w, ReprV p (PrimTy.erase (s.evalT σ)) w ∧ run (compileSimple b s) m = .ok (m.push w) 0
  | p, .lit n hr, _ => by
    cases p <;> simp only [PrimTy.inRange, decide_eq_true_eq, Bool.false_eq_true] at hr
    · exact ⟨.val (toWord n), ⟨hr.1, hr.2, by simp only [toWord, hr.1, ↓reduceIte]; rfl⟩, rfl⟩
    · exact ⟨.val (toWord n), ReprV.int hr.1 hr.2, rfl⟩
  | _, .bool b, _ => ⟨.val (bword b), rfl, rfl⟩
  | p, .local i, _ => ⟨m.memAt (lvl b i), hm.vals i, rfl⟩
  | _, .env k hp, hw => by
    subst hp
    obtain ⟨h1, h2, h3, h4, w1, w2, w3, w4⟩ := hm.env
    have hn : ∀ n : Nat, n < W → ReprV .uint (.int n) (.val n) := fun n h =>
      ⟨by omega, by exact_mod_cast h, by simp only [Int.toNat_natCast]⟩
    cases k
    · exact ⟨_, by rw [show PrimTy.erase (Solidity.Core.Simple.evalT σ (.env .msgSender rfl)) =
        .int (σ.sem.tx.msgSender) from rfl, h1]; exact hn _ w1, rfl⟩
    · exact ⟨_, by rw [show PrimTy.erase (Solidity.Core.Simple.evalT σ (.env .msgValue rfl)) =
        .int (σ.sem.tx.msgValue) from rfl, h2]; exact hn _ w2, rfl⟩
    · exact ⟨_, by rw [show PrimTy.erase (Solidity.Core.Simple.evalT σ (.env .timestamp rfl)) =
        .int (σ.sem.tx.timestamp) from rfl, h3]; exact hn _ w3, rfl⟩
    · simp only [simpleIn, bne_self_eq_false, Bool.false_eq_true] at hw
    · exact ⟨_, by rw [show PrimTy.erase (Solidity.Core.Simple.evalT σ (.env .selfAddress rfl)) =
        .int (σ.sem.tx.selfAddress) from rfl, h4]; exact hn _ w4, rfl⟩

mutual

/-- A storage path pushes its slot.

Example: after `Person storage p = folks[7];` (`p` at level `0`), `p.age`
compiles to `MLOAD %0; PUSH 2; ADD`, and `MLOAD %0` pushes `keccak(7, 7)`. -/
theorem spath_sim : ∀ {T : Ty} (q : Solidity.Core.SPath C Γ T) {free : Bool} {m : Machine},
    Sim C L b F σ.sem (Look.ofTEnv σ.env) m → spathIn F free q = true →
      LocOutT C L σ.sem free T (q.resolveT σ) (run (compileSPath b q) m) m
  | _, @Solidity.Core.SPath.alias _ _ R i, free, m, hm, hw => by
    simp only [spathIn, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true'] at hw
    have hmem : ∀ {s : Slot}, m.memAt (lvl b i) = .slot s →
        run (compileSPath b (Solidity.Core.SPath.alias (C := C) i)) m = .ok (m.push (.slot s)) 0 :=
      fun h => by
        simp only [compileSPath, run, exec_cons_zero, Instr.step, Machine.next]
        rw [show m.mem (cellOf b i) = m.memAt (lvl b i) from rfl, h]; rfl
    have hres : ∀ {r : SRef C (.ref R)}, Look.ofTEnv σ.env i = some r →
        (Solidity.Core.SPath.alias i).resolveT σ = .ok r := fun h => by
      rw [Look.ofTEnv_alias] at h
      simp only [Solidity.Core.SPath.resolveT, h]
    rcases hw with hx | ⟨rfl, hx⟩
    · obtain ⟨r, s, henv, hm', hp⟩ := hm.aliases i hx
      rcases find_repr hm.store hp with ⟨sv, hsv, hr⟩ | ⟨h, _⟩
      · exact .inl ⟨r, s, sv, hres henv, hsv, hp.ofTrue free, hr, hmem hm'⟩
      · cases h
    · obtain ⟨r, s, henv, hm', hp, sv₀, hsv₀⟩ := hm.fragile i hx
      rcases find_repr hm.store hp with ⟨sv, hsv, hr⟩ | ⟨_, hsv⟩
      · exact .inl ⟨r, s, sv, hres henv, hsv, hp, hr, hmem hm'⟩
      · rw [hsv₀] at hsv; cases hsv
  | _, .loc l, free, m, hm, hw => by
    simp only [Solidity.Core.SPath.resolveT, compileSPath]
    exact loc_sim l hm (by simpa only [spathIn] using hw)

/-- A location pushes its slot, checking every array index against the
length on the way.

Example: `folks[7].age` pushes `keccak(7, 7) + 2`; `persons[5].age` with three
persons reverts at the bounds check, as the interpreter's read does. -/
theorem loc_sim : ∀ {T : Ty} (l : Solidity.Core.Loc C Γ T) {free : Bool} {m : Machine},
    Sim C L b F σ.sem (Look.ofTEnv σ.env) m → locIn F free l = true →
      LocOutT C L σ.sem free T (l.resolveT σ) (run (compileLoc b l) m) m
  | _, .root r h, free, m, hm, _ => by
    obtain ⟨sv, hl, hr⟩ := hm.store r _ h
    exact .inl ⟨SRef.ofRoot r h, rootSlot C r, sv, rfl,
      by simp only [State.findLive, SRef.ofRoot, Solidity.Core.Path.erase, hl, SVal.findLive_nil],
      .root h, hr, rfl⟩
  | _, @Solidity.Core.Loc.field _ _ s T q f h, free, m, hm, hw => by
    have hwb : spathIn F free q = true := by simpa only [locIn] using hw
    have h' : lookupBy f (structDef s) = some T := h
    simp only [Solidity.Core.Loc.resolveT, compileLoc]
    rcases spath_sim q hm hwb with ⟨r, s₀, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
    · cases hr with
      | struct hex hall =>
        obtain ⟨v, hv⟩ := hex f T h'
        obtain ⟨hroot, hpath⟩ := sref_erase_field r h
        refine .inl ⟨r.field h, s₀.add (offset s f), v, ?_, ?_, ?_, hall f T v h' hv, ?_⟩
        · simp only [hres]; rfl
        · rw [hroot, hpath, findLive_append, hsv]
          simp only [bind, Except.bind, SVal.findLive, hv, SVal.findLive_nil]
        · rw [hroot, hpath]; exact .field hp h
        · rw [run_append_ok hrun]; simp only [run, Machine.push, exec_cons_zero, Instr.step,
            Machine.next, Out.ok_bind, exec_nil]
    · exact .inr ⟨by simp only [hres]; rfl, run_append_revert hrun⟩
  | _, @Solidity.Core.Loc.index _ _ _ k V .map q i, free, m, hm, hw => by
    have ihb : ∀ {m : Machine}, Sim C L b F σ.sem (Look.ofTEnv σ.env) m →
        spathIn F free q = true →
        LocOutT C L σ.sem free _ (q.resolveT σ) (run (compileSPath b q) m) m :=
      fun hm hw => spath_sim q hm hw
    have ihi : ∀ {m : Machine}, Sim C L b F σ.sem (Look.ofTEnv σ.env) m → valIn F i = true →
        ValOutT _ (i.evalT σ) (run (compileVal b i) m) m := fun hm hw => val_sim i hm hw
    rw [locIn] at hw
    simp only [Bool.and_eq_true, beq_iff_eq] at hw
    obtain ⟨⟨rfl, hwb⟩, hwi⟩ := hw
    simp only [compileLoc, List.append_assoc]
    rcases ihb hm hwb with ⟨r, s₀, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
    · cases hr with
      | mapOther hK => exact absurd rfl hK
      | map hall =>
        rename_i entries dflt
        rw [run_append_ok hrun]
        rcases ihi (hm.push _) hwi with ⟨v, w, hv, hrep, hrun'⟩ | ⟨hv, hrun'⟩
        · obtain ⟨n, hn, hvn, rfl⟩ := hrep.uint_inv
          have hv1 : v.1 = (n : Int) := Semantics.PrimVal.int.inj hvn
          have hsv' := State.findStorage_of_findLive hsv
          have hc : TRes.ofOpt (σ.storage.checkIndex r .map (n : Int)) =
              if true then .ok () else .error .revert :=
            checkT r .map n (by simp only [State.checkIndex, hsv', ↓reduceIte]; rfl)
          have hp' := PathSlot.key hp (Int.natCast_nonneg n) (by omega)
          rw [Int.toNat_natCast] at hp'
          obtain ⟨hroot, hpath⟩ := sref_erase_index r .map n
          have hat : r.atKey .map v = r.index .map (n : Int) := by
            unfold SRef.atKey; rw [show PrimTy.key v = (n : Int) from hv1]
          refine .inl ⟨r.atKey .map v, .hash n s₀ 0, _, ?_, ?_, ?_, hall n hn, ?_⟩
          · simp only [Solidity.Core.Loc.resolveT, hres, hv, bind, Except.bind]
            rw [show PrimTy.key v = (n : Int) from hv1, hc]; rfl
          · rw [hat, hroot, hpath, findLive_append, hsv]
            simp only [bind, Except.bind, SVal.findLive]
            cases lookupBy (n : Int) entries <;> simp only [Option.getD_none, Option.getD_some]
          · rw [hat, hroot, hpath]; exact hp'
          · rw [run_append_ok hrun']; simp only [run, Machine.push, exec_cons_zero, Instr.step,
              Machine.next, exec_nil, Out.ok_bind]
        · exact .inr ⟨by simp only [Solidity.Core.Loc.resolveT, hres, hv, bind, Except.bind],
            run_append_revert hrun'⟩
    · exact .inr ⟨by simp only [Solidity.Core.Loc.resolveT, hres, bind, Except.bind],
        run_append_revert hrun⟩
  | _, @Solidity.Core.Loc.index _ _ _ _ E (.arr .dyn) q i, free, m, hm, hw => by
    have ihb : ∀ {m : Machine}, Sim C L b F σ.sem (Look.ofTEnv σ.env) m →
        spathIn F free q = true →
        LocOutT C L σ.sem free _ (q.resolveT σ) (run (compileSPath b q) m) m :=
      fun hm hw => spath_sim q hm hw
    have ihi : ∀ {m : Machine}, Sim C L b F σ.sem (Look.ofTEnv σ.env) m → valIn F i = true →
        ValOutT _ (i.evalT σ) (run (compileVal b i) m) m := fun hm hw => val_sim i hm hw
    rw [locIn] at hw
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hw
    obtain ⟨⟨rfl, hwb⟩, hwi⟩ := hw
    simp only [compileLoc, List.append_assoc]
    rcases ihb hm hwb with ⟨r, s₀, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
    · cases hr with
      | array hl hW hall =>
        rename_i elems shadow
        rw [run_append_ok hrun]
        rcases ihi (hm.push _) hwi with ⟨v, w, hv, hrep, hrun'⟩ | ⟨hv, hrun'⟩
        · obtain ⟨n, hn, hvn, rfl⟩ := hrep.uint_inv
          have hv1 : v.1 = (n : Int) := Semantics.PrimVal.int.inj hvn
          rw [run_append_ok hrun']
          have hsv' := State.findStorage_of_findLive hsv
          have hc : TRes.ofOpt (σ.storage.checkIndex r (.arr .dyn) (n : Int)) =
              if decide (n < elems.length) then .ok () else .error .revert :=
            checkT r (.arr .dyn) n (by
              by_cases hin : n < elems.length <;>
                simp only [State.checkIndex, hsv', Int.ofNat_zero_le, Int.toNat_natCast, hin,
                  and_self, and_false, ↓reduceIte, decide_true, decide_false,
                  Bool.false_eq_true, bind, Except.bind, pure, Except.pure] <;> rfl)
          have hres' : (Solidity.Core.Loc.index (.arr .dyn) q i).resolveT σ =
              (if n < elems.length then .ok (r.atKey (.arr .dyn) v) else .error .revert) := by
            simp only [Solidity.Core.Loc.resolveT, hres, hv, bind, Except.bind]
            rw [show PrimTy.key v = (n : Int) from hv1, hc]
            by_cases hin : n < elems.length <;>
              simp only [hin, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true] <;> rfl
          rw [hres']
          have hb := boundsCheck_run m m.stack (elemSlot (size E)) n s₀
          simp only [Machine.push] at hb ⊢
          rw [hb, hl]
          by_cases hin : n < elems.length
          · rw [if_pos hin, if_pos hin]
            have hp' := PathSlot.elem hp (Int.natCast_nonneg n) (by omega)
            rw [Int.toNat_natCast] at hp'
            obtain ⟨hroot, hpath⟩ := sref_erase_index r (.arr .dyn) n
            have hat : r.atKey (.arr .dyn) v = r.index (.arr .dyn) (n : Int) := by
              unfold SRef.atKey; rw [show PrimTy.key v = (n : Int) from hv1]
            refine .inl ⟨r.atKey (.arr .dyn) v, .data s₀ (n * size E), elems[n], rfl, ?_, ?_,
              hall n hin, elemSlot_run m m.stack n (size E) s₀⟩
            · rw [hat, hroot, hpath, findLive_append, hsv]
              simp only [bind, Except.bind, SVal.findLive, Int.ofNat_zero_le, Int.toNat_natCast,
                hin, and_self, ↓reduceDIte, List.get_eq_getElem, SVal.findLive_nil]
            · rw [hat, hroot, hpath]; exact hp'
          · rw [if_neg hin, if_neg hin]
            exact .inr ⟨rfl, rfl⟩
        · exact .inr ⟨by simp only [Solidity.Core.Loc.resolveT, hres, hv, bind, Except.bind],
            run_append_revert hrun'⟩
    · exact .inr ⟨by simp only [Solidity.Core.Loc.resolveT, hres, bind, Except.bind],
        run_append_revert hrun⟩
  | _, @Solidity.Core.Loc.index _ _ _ _ E
      (@IndexTy.arr _ _ (@ArrTy.fixed _ n)) q i, free, m, hm, hw => by
    have ihb : ∀ {m : Machine}, Sim C L b F σ.sem (Look.ofTEnv σ.env) m →
        spathIn F free q = true →
        LocOutT C L σ.sem free _ (q.resolveT σ) (run (compileSPath b q) m) m :=
      fun hm hw => spath_sim q hm hw
    have ihi : ∀ {m : Machine}, Sim C L b F σ.sem (Look.ofTEnv σ.env) m → valIn F i = true →
        ValOutT _ (i.evalT σ) (run (compileVal b i) m) m := fun hm hw => val_sim i hm hw
    rw [locIn] at hw
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hw
    obtain ⟨⟨rfl, hwb⟩, hwi⟩ := hw
    simp only [compileLoc, List.append_assoc]
    rcases ihb hm hwb with ⟨r, s₀, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
    · cases hr with
      | fixed hl hall =>
        rename_i elems shadow
        rw [run_append_ok hrun]
        rcases ihi (hm.push _) hwi with ⟨v, w, hv, hrep, hrun'⟩ | ⟨hv, hrun'⟩
        · obtain ⟨k, hk, hvk, rfl⟩ := hrep.uint_inv
          have hv1 : v.1 = (k : Int) := Semantics.PrimVal.int.inj hvk
          rw [run_append_ok hrun']
          have hsv' := State.findStorage_of_findLive hsv
          have hc : TRes.ofOpt (σ.storage.checkIndex r (.arr .fixed) (k : Int)) =
              if decide (k < elems.length) then .ok () else .error .revert :=
            checkT r (.arr .fixed) k (by
              by_cases hin : k < elems.length <;>
                simp only [State.checkIndex, hsv', Int.ofNat_zero_le, Int.toNat_natCast, hin,
                  and_self, and_false, ↓reduceIte, decide_true, decide_false,
                  Bool.false_eq_true, bind, Except.bind, pure, Except.pure] <;> rfl)
          have hres' : (Solidity.Core.Loc.index (.arr .fixed) q i).resolveT σ =
              (if k < elems.length then .ok (r.atKey (.arr .fixed) v) else .error .revert) := by
            simp only [Solidity.Core.Loc.resolveT, hres, hv, bind, Except.bind]
            rw [show PrimTy.key v = (k : Int) from hv1, hc]
            by_cases hin : k < elems.length <;>
              simp only [hin, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true] <;> rfl
          rw [hres']
          have hb := fixedCheck_run m m.stack (fixedSlot (size E)) n k s₀
          simp only [Machine.push] at hb ⊢
          rw [hb]
          by_cases hin : k < elems.length
          · rw [if_pos hin, if_pos (hl ▸ hin)]
            have hp' := PathSlot.felem hp (Int.natCast_nonneg k) (by omega)
            rw [Int.toNat_natCast] at hp'
            obtain ⟨hroot, hpath⟩ := sref_erase_index r (.arr .fixed) k
            have hat : r.atKey (.arr .fixed) v = r.index (.arr .fixed) (k : Int) := by
              unfold SRef.atKey; rw [show PrimTy.key v = (k : Int) from hv1]
            refine .inl ⟨r.atKey (.arr .fixed) v, s₀.add (k * size E), elems[k], rfl, ?_, ?_,
              hall k hin, fixedSlot_run m m.stack k (size E) s₀⟩
            · rw [hat, hroot, hpath, findLive_append, hsv]
              simp only [bind, Except.bind, SVal.findLive, Int.ofNat_zero_le, Int.toNat_natCast,
                hin, and_self, ↓reduceDIte, List.get_eq_getElem, SVal.findLive_nil]
            · rw [hat, hroot, hpath]; exact hp'
          · rw [if_neg hin, if_neg (hl ▸ hin)]
            exact .inr ⟨rfl, rfl⟩
        · exact .inr ⟨by simp only [Solidity.Core.Loc.resolveT, hres, hv, bind, Except.bind],
            run_append_revert hrun'⟩
    · exact .inr ⟨by simp only [Solidity.Core.Loc.resolveT, hres, bind, Except.bind],
        run_append_revert hrun⟩

/-- An expression pushes its value, or reverts where the interpreter does.

Example: `total * 2` pushes twice `total`'s word, and reverts with the
interpreter when that overflows; `c ? a : b` runs only the branch `c` picks. -/
theorem val_sim : ∀ {p : PrimTy} (e : Solidity.Core.Val C Γ p) {m : Machine},
    Sim C L b F σ.sem (Look.ofTEnv σ.env) m → valIn F e = true →
      ValOutT p (e.evalT σ) (run (compileVal b e) m) m
  | _, .simple s, m, hm, hw => by
    simp only [Solidity.Core.Val.evalT, compileVal]
    obtain ⟨w, hr, hrun⟩ := simple_sim hm s (by simpa only [valIn] using hw)
    exact .inl ⟨_, w, rfl, hr, hrun⟩
  | p, .read l, m, hm, hw => by
    simp only [valIn] at hw
    simp only [Solidity.Core.Val.evalT, compileVal]
    rcases loc_sim l hm hw with ⟨r, s, sv, hres, hsv, _, hr, hrun⟩ | ⟨hres, hrun⟩
    · rw [run_append_ok hrun]
      obtain ⟨v, hv, hrv, _⟩ := prim_read hr
      obtain ⟨tv, hf, rfl⟩ := find_of_findLive hsv
      rw [asValue_erase_prim] at hv
      cases hv
      refine .inl ⟨Solidity.Core.SVal.view tv, .val (m.store s), ?_, hrv, rfl⟩
      simp only [hres, hf, bind, Except.bind, TRes.ofOpt, pure, Except.pure]
    · exact .inr ⟨by simp only [hres, bind, Except.bind], run_append_revert hrun⟩
  | _, @Solidity.Core.Val.binop _ _ p q op hacc hq x y, m, hm, hw => by
    have iha : ∀ {m : Machine}, Sim C L b F σ.sem (Look.ofTEnv σ.env) m → valIn F x = true →
        ValOutT p (x.evalT σ) (run (compileVal b x) m) m := fun hm hw => val_sim x hm hw
    have ihb : ∀ {m : Machine}, Sim C L b F σ.sem (Look.ofTEnv σ.env) m → valIn F y = true →
        ValOutT p (y.evalT σ) (run (compileVal b y) m) m := fun hm hw => val_sim y hm hw
    subst hq
    simp only [valIn, Bool.and_eq_true] at hw
    obtain ⟨⟨hop, hwa⟩, hwb⟩ := hw
    simp only [Solidity.Core.Val.evalT]
    by_cases hand : op = .and
    · subst hand
      obtain rfl : p = .bool := by cases p <;> simp only [binInFrag, BEq.rfl, beq_iff_eq,
          reduceCtorEq] at hop ⊢
      simp only [compileVal, List.append_assoc]
      rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
      · obtain ⟨z, hz, rfl⟩ := hra.bool_inv
        obtain rfl : va = z := Semantics.PrimVal.bool.inj hz
        rw [run_append_ok hruna, hva]
        cases va
        · refine .inl ⟨false, .val (bword false), rfl, rfl, ?_⟩
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
          · obtain ⟨z, hz, rfl⟩ := hrb.bool_inv
            obtain rfl : vb = z := Semantics.PrimVal.bool.inj hz
            refine .inl ⟨vb, .val (bword vb), ?_, rfl, hrunb⟩
            simp only [bind, Except.bind, BinOp.shortT, Solidity.Core.boolT, hvb, ↓reduceIte]
            cases vb <;> rfl
          · exact .inr ⟨by simp only [bind, Except.bind, BinOp.shortT, Solidity.Core.boolT, hvb,
              ↓reduceIte], hrunb⟩
      · exact .inr ⟨by simp only [bind, Except.bind, hva], run_append_revert hruna⟩
    by_cases hor : op = .or
    · subst hor
      obtain rfl : p = .bool := by cases p <;> simp only [binInFrag, BEq.rfl, beq_iff_eq,
          reduceCtorEq] at hop ⊢
      simp only [compileVal, List.append_assoc]
      rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
      · obtain ⟨z, hz, rfl⟩ := hra.bool_inv
        obtain rfl : va = z := Semantics.PrimVal.bool.inj hz
        rw [run_append_ok hruna, hva]
        cases va
        · rw [show [Instr.dup 1, .jumpi ((compileVal b y).length + 1), .pop] ++ compileVal b y
            = [Instr.dup 1, .jumpi ((compileVal b y).length + 1), .pop] ++ compileVal b y
            from rfl, run_append_ok (m' := m) rfl]
          rcases ihb hm hwb with ⟨vb, wb, hvb, hrb, hrunb⟩ | ⟨hvb, hrunb⟩
          · obtain ⟨z, hz, rfl⟩ := hrb.bool_inv
            obtain rfl : vb = z := Semantics.PrimVal.bool.inj hz
            refine .inl ⟨vb, .val (bword vb), ?_, rfl, hrunb⟩
            simp only [bind, Except.bind, BinOp.shortT, Solidity.Core.boolT, hvb,
              Bool.false_eq_true, ↓reduceIte]
            cases vb <;> rfl
          · exact .inr ⟨by simp only [bind, Except.bind, BinOp.shortT, Solidity.Core.boolT, hvb,
              Bool.false_eq_true, ↓reduceIte], hrunb⟩
        · refine .inl ⟨true, .val (bword true), rfl, rfl, ?_⟩
          rw [show [Instr.dup 1, .jumpi ((compileVal b y).length + 1), .pop] ++ compileVal b y
            = [Instr.dup 1, .jumpi ((compileVal b y).length + 1)] ++ ([.pop] ++ compileVal b y)
            from rfl, run_append_skip (m' := m.push (.val (bword true)))
            (k := (compileVal b y).length + 1) rfl]
          exact exec_length ([.pop] ++ compileVal b y) _
      · exact .inr ⟨by simp only [bind, Except.bind, hva], run_append_revert hruna⟩
    have hcode : compileVal b (.binop op hacc rfl x y) =
        compileVal b x ++ compileVal b y ++ binTail p op := by
      cases op <;> simp_all only [forall_const, reduceCtorEq, not_false_eq_true, compileVal,
          List.append_assoc, not_true_eq_false]
    rw [hcode, List.append_assoc]
    rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
    · rw [run_append_ok hruna, hva]
      have hs : op.shortT va = none := by
        cases op <;> cases p <;> simp_all only [BinOp.shortT, not_true_eq_false,
          reduceCtorEq, not_false_eq_true]
      simp only [bind, Except.bind, hs]
      rcases ihb (hm.push wa) hwb with ⟨vb, wb, hvb, hrb, hrunb⟩ | ⟨hvb, hrunb⟩
      · rw [run_append_ok hrunb, hvb]
        have ht := tail_sim hop hand hor hra hrb m
        have ht' : ValOut (op.ret p) (evalBinop op p (PrimTy.erase va) (.ok (PrimTy.erase vb)))
            (run (binTail p op) { m with stack := wb :: wa :: m.stack }) m := by
          rw [evalBinop_eq hand hor]; exact ht
        rw [BinOp.evalT_erase op hacc] at ht'
        exact ValOutT.ofRes ht'
      · exact .inr ⟨by rw [hvb], run_append_revert hrunb⟩
    · exact .inr ⟨by simp only [bind, Except.bind, hva], run_append_revert hruna⟩
  | _, @Solidity.Core.Val.unop _ _ p q op hacc hq x, m, hm, hw => by
    have iha : ∀ {m : Machine}, Sim C L b F σ.sem (Look.ofTEnv σ.env) m → valIn F x = true →
        ValOutT p (x.evalT σ) (run (compileVal b x) m) m := fun hm hw => val_sim x hm hw
    subst hq
    simp only [valIn, Bool.and_eq_true] at hw
    obtain ⟨hop, hwa⟩ := hw
    have key : ∀ {va : p.Denote}, x.evalT σ = .ok va →
        (Solidity.Core.Val.unop op hacc rfl x).evalT σ = TRes.ofOpt (op.evalT va) := fun h => by
      simp only [Solidity.Core.Val.evalT, h, bind, Except.bind]
    have err : ∀ {e : Solidity.Core.THalt}, x.evalT σ = .error e →
        (Solidity.Core.Val.unop op hacc rfl x).evalT σ = .error e := fun h => by
      simp only [Solidity.Core.Val.evalT, h, bind, Except.bind]
    cases op with
    | not =>
      obtain rfl : p = .bool := by cases p <;> simp only [UnOp.accepts, BEq.rfl, beq_iff_eq,
          reduceCtorEq] at hacc ⊢
      simp only [compileVal]
      rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
      · obtain ⟨z, hz, rfl⟩ := hra.bool_inv
        obtain rfl : va = z := Semantics.PrimVal.bool.inj hz
        rw [run_append_ok hruna, key hva]
        refine .inl ⟨!va, .val (bword !va), rfl, rfl, ?_⟩
        cases va <;> rfl
      · exact .inr ⟨err hva, run_append_revert hruna⟩
    | neg =>
      obtain rfl : p = .int := by simpa only [unInFrag, beq_iff_eq] using hop
      simp only [compileVal]
      rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
      · obtain ⟨a, ha, hza, rfl⟩ := hra.int_inv
        rw [run_append_ok hruna, key hva]
        apply ValOutT.ofRes
        rw [← UnOp.evalT_erase .neg hacc, hza]
        simp only [Machine.push]
        rw [neg_run m m.stack ha]
        change ValOut _ (checkArith (.prim .int) (.int (-sgn a))) _ _
        rw [checkArith_int]
        by_cases h : -(H : Int) ≤ -sgn a ∧ -sgn a < H
        · rw [if_pos h, if_pos h]; exact .inl ⟨_, _, rfl, ReprV.int h.1 h.2, rfl⟩
        · rw [if_neg h, if_neg h]; exact .inr ⟨rfl, rfl⟩
      · exact .inr ⟨err hva, run_append_revert hruna⟩
    | bnot =>
      obtain rfl : p = .uint := by simpa only [unInFrag, beq_iff_eq] using hop
      simp only [compileVal]
      rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
      · obtain ⟨a, ha, hza, rfl⟩ := hra.uint_inv
        rw [run_append_ok hruna, key hva]
        apply ValOutT.ofRes
        rw [← UnOp.evalT_erase .bnot hacc, hza]
        have := W_pos
        refine .inl ⟨.int ↑(W - 1 - a), .val (W - 1 - a), ?_, ReprV.uint (by omega), ?_⟩
        · simp only [applyUnOp, Value.asInt, unopCheck, bind, Except.bind, pure, Except.pure,
            uintBound_eq]
          congr 2; omega
        · simp only [run, exec_cons_zero, Instr.step, Machine.next, exec_nil]; rfl
      · exact .inr ⟨err hva, run_append_revert hruna⟩
  | p, .ternary c x y, m, hm, hw => by
    have ihc : ∀ {m : Machine}, Sim C L b F σ.sem (Look.ofTEnv σ.env) m → valIn F c = true →
        ValOutT .bool (c.evalT σ) (run (compileVal b c) m) m := fun hm hw => val_sim c hm hw
    have iha : ∀ {m : Machine}, Sim C L b F σ.sem (Look.ofTEnv σ.env) m → valIn F x = true →
        ValOutT p (x.evalT σ) (run (compileVal b x) m) m := fun hm hw => val_sim x hm hw
    have ihb : ∀ {m : Machine}, Sim C L b F σ.sem (Look.ofTEnv σ.env) m → valIn F y = true →
        ValOutT p (y.evalT σ) (run (compileVal b y) m) m := fun hm hw => val_sim y hm hw
    simp only [valIn, Bool.and_eq_true] at hw
    obtain ⟨⟨hwc, hwa⟩, hwb⟩ := hw
    simp only [Solidity.Core.Val.evalT, compileVal, List.append_assoc]
    rcases ihc hm hwc with ⟨vc, wc, hvc, hrc, hrunc⟩ | ⟨hvc, hrunc⟩
    · obtain ⟨z, hz, rfl⟩ := hrc.bool_inv
      obtain rfl : vc = z := Semantics.PrimVal.bool.inj hz
      rw [run_append_ok hrunc, hvc]
      simp only [bind, Except.bind, Solidity.Core.boolT]
      cases vc
      · rw [run_append_skip (m' := m) (k := (compileVal b x).length + 1) rfl,
          show (compileVal b x).length + 1 = (compileVal b x).length + 1 from rfl, exec_append,
          exec_skip]
        simp only [Out.ok_bind, Bool.false_eq_true, ↓reduceIte]
        exact ihb hm hwb
      · rw [run_append_skip (m' := m) (k := 0) rfl]
        simp only [↓reduceIte]
        rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
        · refine .inl ⟨va, wa, hva, hra, ?_⟩
          change run _ m = _
          rw [run_append_ok hruna]
          exact exec_length _ _
        · exact .inr ⟨hva, run_append_revert hruna⟩
    · exact .inr ⟨by simp only [bind, Except.bind, hvc], run_append_revert hrunc⟩
  | _, .len q hp, m, hm, hw => by
    cases hp
    simp only [valIn] at hw
    simp only [Solidity.Core.Val.evalT, compileVal]
    rcases spath_sim q hm hw with ⟨r, s, sv, hres, hsv, _, hr, hrun⟩ | ⟨hres, hrun⟩
    · cases hr with
      | @array _ _ elems shadow hl hW _ =>
        rw [run_append_ok hrun]
        have := hm.bound; have := Lmax_lt_W
        have hW' : elems.length < 2 ^ 256 := by unfold W at *; omega
        have hlen : σ.storage.len r = some (Solidity.Core.lenU elems.length hW') := by
          have h := Solidity.Core.Storage.arrayLen_erase (σ := σ.sem) rfl r
          rw [show arrayLen σ.sem r.root r.path.erase = .ok (.int elems.length) by
            simp only [arrayLen, State.findStorage_of_findLive hsv]; rfl] at h
          cases hc : σ.storage.len r with
          | none => rw [hc] at h; cases h
          | some n =>
            rw [hc] at h
            simp only [Solidity.Core.toRes, Except.ok.injEq] at h
            exact congrArg some (Subtype.ext (Semantics.PrimVal.int.inj h).symm)
        refine .inl ⟨Solidity.Core.lenU elems.length hW', .val elems.length, ?_,
          ReprV.uint (by omega), ?_⟩
        · simp only [hres, hlen, bind, Except.bind, TRes.ofOpt, pure, Except.pure]
        · simp only [run, Machine.push, exec_cons_zero, Instr.step, Machine.next, hl, exec_nil,
            Out.ok_bind]
    · exact .inr ⟨by simp only [hres, bind, Except.bind], run_append_revert hrun⟩
  | _, .readMem _, _, _, hw => by simp only [valIn, Bool.false_eq_true] at hw
  | _, .mlen .., _, _, hw => by simp only [valIn, Bool.false_eq_true] at hw

end

end Core
end Solidity.Evm
