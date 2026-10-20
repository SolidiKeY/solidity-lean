import Solidity.Evm.Sim

/-!
# Expressions over the typed run

The expression lemmas (`simple_sim` … `val_sim`), for
`Evm/Compile.lean`'s code and the typed run's evaluation
(`Semantics/Run.lean`, `docs/intrinsic.md`, W1).  The simulation is
`Evm/Sim.lean`'s `Sim` of the typed state: its locals read off it
(`Look.ofTEnv`, each local as it is typed, a value or the reference an alias
holds) and its global part, whose typed storage the machine-level lemmas of
`Evm/Repr.lean` read.  A local is read at its level (`lvl b i`), never
missing.

The dichotomies are typed results: `ValOutT` (a value pushed, or both
revert, `Evm/SimLemmas.lean`) and `LocOutT` (the slot of a reference pushed,
or both revert).  An operator's tail is `SimLemmas`' `tail_simT`.
-/

namespace Solidity.Evm

open Semantics (structDef lookupBy)
open Solidity (Ctx Idx Ext TEnv State SRef TRes HTy)

variable {C : Contract}

/-! ## Typed results -/

/-- A location's outcome: the slot of the reference pushed, the reference
live and its value laid out there; or both revert. -/
def LocOutT (C : Contract) (L : Nat) (stor : Solidity.Storage C) (free : Bool) (T : Ty)
    (res : TRes (SRef C T)) (out : Out) (m : Machine) : Prop :=
  (∃ r s sv, res = .ok r ∧ stor.findLive r = some sv ∧
      PathSlot C free r s ∧ ReprAt m.store L T s sv ∧
      out = .ok (m.push (.slot s)) 0) ∨
    (res = .error .revert ∧ out = .revert)

/-! ## Expressions -/

variable {L b : Nat} {Γ : Ctx} {F : Frag Γ} {σ : State C Γ}

/-- A literal, a local or the environment pushes its value.

Example: `x` at level `0` is `MLOAD %0`, which pushes `x`'s word. -/
theorem simple_sim {m : Machine} (hm : Sim C L b F σ m) :
    ∀ {p : PrimTy} (s : Solidity.Simple C Γ p), simpleIn s = true →
      ∃ w, ReprV p (s.evalT σ) w ∧ run (compileSimple b s) m = .ok (m.push w) 0
  | p, .lit n hr, _ => by
    cases p <;> simp only [PrimTy.inRange, decide_eq_true_eq, Bool.false_eq_true] at hr
    · have hlt : n.toNat < W := by unfold W; omega
      refine ⟨.val (wmod (toWord n)), ⟨_, rfl, ?_⟩, rfl⟩
      simp only [wmod_def, toWord, hr.1, ↓reduceIte, Nat.mod_eq_of_lt hlt]
      show n = _
      omega
    · exact ⟨.val (sword n), ReprV.int_word _, rfl⟩
  | _, .bool b, _ => ⟨.val (bword b), rfl, rfl⟩
  | p, .local i, _ => ⟨m.memAt (lvl b i), hm.vals i, rfl⟩
  | _, .env k hp, hw => by
    subst hp
    obtain ⟨h1, h2, h3, h4⟩ := hm.env
    cases k
    · exact ⟨_, ReprV.uint_of h1, rfl⟩
    · exact ⟨_, ReprV.uint_of h2, rfl⟩
    · exact ⟨_, ReprV.uint_of h3, rfl⟩
    · simp only [simpleIn, bne_self_eq_false, Bool.false_eq_true] at hw
    · exact ⟨_, ReprV.uint_of h4, rfl⟩

mutual

/-- A storage path pushes its slot.

Example: after `Person storage p = folks[7];` (`p` at level `0`), `p.age`
compiles to `MLOAD %0; PUSH 2; ADD`, and `MLOAD %0` pushes `keccak(7, 7)`. -/
theorem spath_sim : ∀ {T : Ty} (q : Solidity.SPath C Γ T) {free : Bool} {m : Machine},
    Sim C L b F σ m → spathIn F free q = true →
      LocOutT C L σ.storage free T (q.resolveT σ) (run (compileSPath b q) m) m
  | _, @Solidity.SPath.alias _ _ R i, free, m, hm, hw => by
    simp only [spathIn, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true'] at hw
    have hmem : ∀ {s : Slot}, m.memAt (lvl b i) = .slot s →
        run (compileSPath b (Solidity.SPath.alias (C := C) i)) m = .ok (m.push (.slot s)) 0 :=
      fun h => by
        simp only [compileSPath, run, exec_cons_zero, Instr.step, Machine.next]
        rw [show m.mem (cellOf b i) = m.memAt (lvl b i) from rfl, h]; rfl
    have hres : ∀ {r : SRef C (.ref R)}, Look.ofTEnv σ.env i = some r →
        (Solidity.SPath.alias i).resolveT σ = .ok r := fun h => by
      rw [Look.ofTEnv_alias] at h
      simp only [Solidity.SPath.resolveT, h]
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
    simp only [Solidity.SPath.resolveT, compileSPath]
    exact loc_sim l hm (by simpa only [spathIn] using hw)

/-- A location pushes its slot, checking every array index against the
length on the way.

Example: `folks[7].age` pushes `keccak(7, 7) + 2`; `persons[5].age` with three
persons reverts at the bounds check, as the typed run's index check does. -/
theorem loc_sim : ∀ {T : Ty} (l : Solidity.Loc C Γ T) {free : Bool} {m : Machine},
    Sim C L b F σ m → locIn F free l = true →
      LocOutT C L σ.storage free T (l.resolveT σ) (run (compileLoc b l) m) m
  | _, .root r h, free, m, hm, _ =>
    .inl ⟨SRef.ofRoot r h, rootSlot C r, _, rfl, Sto.findLive_ofRoot _ r h, PathSlot.root h,
      hm.store r _ h, rfl⟩
  | _, @Solidity.Loc.field _ _ s T q f h, free, m, hm, hw => by
    have hw' : offset s f < W ∧ spathIn F free q = true := by
      simpa only [locIn, Bool.and_eq_true, decide_eq_true_eq] using hw
    obtain ⟨hoff, hwb⟩ := hw'
    simp only [Solidity.Loc.resolveT, compileLoc]
    rcases spath_sim q hm hwb with ⟨r, s₀, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
    · cases hr with
      | @struct _ _ fs hall =>
        refine .inl ⟨r.field h, s₀.add (offset s f), _, ?_, Sto.findLive_field hsv h,
          hp.field h, hall f T h, ?_⟩
        · simp only [hres]; rfl
        · rw [run_append_ok hrun]; simp only [run, Machine.push, exec_cons_zero, Instr.step,
            Machine.next, Out.ok_bind, exec_nil, wmod_def, Nat.mod_eq_of_lt hoff]
    · exact .inr ⟨by simp only [hres]; rfl, run_append_revert hrun⟩
  | _, @Solidity.Loc.index _ _ _ k V .map q i, free, m, hm, hw => by
    have ihb : ∀ {m : Machine}, Sim C L b F σ m → spathIn F free q = true →
        LocOutT C L σ.storage free _ (q.resolveT σ) (run (compileSPath b q) m) m :=
      fun hm hw => spath_sim q hm hw
    have ihi : ∀ {m : Machine}, Sim C L b F σ m → valIn F i = true →
        ValOutT _ (i.evalT σ) (run (compileVal b i) m) m := fun hm hw => val_sim i hm hw
    rw [locIn] at hw
    simp only [Bool.and_eq_true, beq_iff_eq] at hw
    obtain ⟨⟨rfl, hwb⟩, hwi⟩ := hw
    simp only [compileLoc, List.append_assoc]
    rcases ihb hm hwb with ⟨r, s₀, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
    · cases hr with
      | @map _ _ _ mm d hall =>
        rw [run_append_ok hrun]
        rcases ihi (hm.push _) hwi with ⟨v, w, hv, hrep, hrun'⟩ | ⟨hv, hrun'⟩
        · obtain ⟨n, hn, hv1, rfl⟩ := hrep.uint_inv
          have hk : PrimTy.key v = (n : Int) := hv1
          have hvn : v.1 = (n : Int) := hk
          have hp' := PathSlot.key hp v
          rw [show v.word = ⟨n, hn⟩ from Fin.ext (by show v.word.1 = n; have := word_val v; omega)] at hp'
          have hent : ReprAt m.store L _ (.hash ⟨n, hn⟩ s₀ 0)
              ((lookupBy (n : Int) mm.hashed).getD d) := hall rfl ⟨n, hn⟩
          rw [← hk, SMap.lookupBy_hashed] at hent
          refine .inl ⟨r.index .map v, .hash ⟨n, hn⟩ s₀ 0, _, ?_, ?_, ?_, hent, ?_⟩
          · simp only [Solidity.Loc.resolveT, hres, hv, bind, Except.bind]
            rw [Sto.checkIndex_map (Sto.find_of_findLive hsv)]; rfl
          · exact Sto.findLive_key hsv _
          · exact hp'
          · rw [run_append_ok hrun']; simp only [run, Machine.push, exec_cons_zero, Instr.step,
              Machine.next, exec_nil, Out.ok_bind]
        · exact .inr ⟨by simp only [Solidity.Loc.resolveT, hres, hv, bind, Except.bind],
            run_append_revert hrun'⟩
    · exact .inr ⟨by simp only [Solidity.Loc.resolveT, hres, bind, Except.bind],
        run_append_revert hrun⟩
  | _, @Solidity.Loc.index _ _ _ _ E (.arr .dyn) q i, free, m, hm, hw => by
    have ihb : ∀ {m : Machine}, Sim C L b F σ m → spathIn F free q = true →
        LocOutT C L σ.storage free _ (q.resolveT σ) (run (compileSPath b q) m) m :=
      fun hm hw => spath_sim q hm hw
    have ihi : ∀ {m : Machine}, Sim C L b F σ m → valIn F i = true →
        ValOutT _ (i.evalT σ) (run (compileVal b i) m) m := fun hm hw => val_sim i hm hw
    rw [locIn] at hw
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hw
    obtain ⟨⟨rfl, hwb⟩, hwi⟩ := hw
    simp only [compileLoc, List.append_assoc]
    rcases ihb hm hwb with ⟨r, s₀, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
    · cases hr with
      | @array _ kk _ e sh hkk hl hW hall =>
        rw [run_append_ok hrun]
        rcases ihi (hm.push _) hwi with ⟨v, w, hv, hrep, hrun'⟩ | ⟨hv, hrun'⟩
        · obtain ⟨n, hn, hv1, rfl⟩ := hrep.uint_inv
          have hk : PrimTy.key v = (n : Int) := hv1
          have hvn : v.1.toNat = n := by have : v.1 = (n : Int) := hk; omega
          rw [run_append_ok hrun']
          have hres' : (Solidity.Loc.index (.arr .dyn) q i).resolveT σ =
              (if n < kk then .ok (r.index (.arr .dyn) v) else .error .revert) := by
            simp only [Solidity.Loc.resolveT, hres, hv, bind, Except.bind]
            rw [Sto.checkIndex_dyn (Sto.find_of_findLive hsv), hvn]
            by_cases hin : n < kk <;> simp only [hin, ↓reduceIte] <;> rfl
          rw [hres']
          have hb := boundsCheck_run m m.stack (elemSlot (size E)) n s₀ hn
          simp only [Machine.push] at hb ⊢
          rw [hb, hl]
          by_cases hin : n < kk
          · rw [if_pos hin, if_pos hin]
            have hp' := PathSlot.elem hp v
            rw [hvn] at hp'
            have hx : e.toList[n]? = some (e.toList[n]'(by rw [SVec.length_toList]; exact hin)) :=
              List.getElem?_eq_getElem _
            refine .inl ⟨r.index (.arr .dyn) v, .data s₀ (n * size E), _, rfl, ?_, ?_,
              hall n _ hx, elemSlot_run m m.stack n (size E) s₀ hn⟩
            · exact Sto.findLive_elem hsv (by rw [hvn]; exact hx)
            · exact hp'
          · rw [if_neg hin, if_neg hin]
            exact .inr ⟨rfl, rfl⟩
        · exact .inr ⟨by simp only [Solidity.Loc.resolveT, hres, hv, bind, Except.bind],
            run_append_revert hrun'⟩
    · exact .inr ⟨by simp only [Solidity.Loc.resolveT, hres, bind, Except.bind],
        run_append_revert hrun⟩
  | _, @Solidity.Loc.index _ _ _ _ E
      (@IndexTy.arr _ _ (@ArrTy.fixed _ n)) q i, free, m, hm, hw => by
    have ihb : ∀ {m : Machine}, Sim C L b F σ m → spathIn F free q = true →
        LocOutT C L σ.storage free _ (q.resolveT σ) (run (compileSPath b q) m) m :=
      fun hm hw => spath_sim q hm hw
    have ihi : ∀ {m : Machine}, Sim C L b F σ m → valIn F i = true →
        ValOutT _ (i.evalT σ) (run (compileVal b i) m) m := fun hm hw => val_sim i hm hw
    rw [locIn] at hw
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hw
    obtain ⟨⟨⟨rfl, hnW⟩, hwb⟩, hwi⟩ := hw
    simp only [compileLoc, List.append_assoc]
    rcases ihb hm hwb with ⟨r, s₀, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
    · cases hr with
      | @fixed _ _ _ e hall =>
        rw [run_append_ok hrun]
        rcases ihi (hm.push _) hwi with ⟨v, w, hv, hrep, hrun'⟩ | ⟨hv, hrun'⟩
        · obtain ⟨k, hkW, hv1, rfl⟩ := hrep.uint_inv
          have hk : PrimTy.key v = (k : Int) := hv1
          have hvk : v.1.toNat = k := by have : v.1 = (k : Int) := hk; omega
          rw [run_append_ok hrun']
          have hres' : (Solidity.Loc.index (.arr .fixed) q i).resolveT σ =
              (if k < n then .ok (r.index (.arr .fixed) v) else .error .revert) := by
            simp only [Solidity.Loc.resolveT, hres, hv, bind, Except.bind]
            rw [Sto.checkIndex_fixed (Sto.find_of_findLive hsv), hvk]
            by_cases hin : k < n <;> simp only [hin, ↓reduceIte] <;> rfl
          rw [hres']
          have hb := fixedCheck_run m m.stack (fixedSlot (size E)) n k s₀ hnW hkW
          simp only [Machine.push] at hb ⊢
          rw [hb]
          by_cases hin : k < n
          · rw [if_pos hin, if_pos hin]
            have hp' := PathSlot.felem hp (i := v)
              (by have : v.1 = (k : Int) := hk; omega)
            rw [hvk] at hp'
            have hx : e.toList[k]? = some (e.toList[k]'(by rw [SVec.length_toList]; exact hin)) :=
              List.getElem?_eq_getElem _
            refine .inl ⟨r.index (.arr .fixed) v, s₀.add (k * size E), _, rfl, ?_, ?_,
              hall k _ hx, fixedSlot_run m m.stack k (size E) s₀ hkW⟩
            · exact Sto.findLive_felem hsv (by rw [hvk]; exact hx)
            · exact hp'
          · rw [if_neg hin, if_neg hin]
            exact .inr ⟨rfl, rfl⟩
        · exact .inr ⟨by simp only [Solidity.Loc.resolveT, hres, hv, bind, Except.bind],
            run_append_revert hrun'⟩
    · exact .inr ⟨by simp only [Solidity.Loc.resolveT, hres, bind, Except.bind],
        run_append_revert hrun⟩

/-- An expression pushes its value, or reverts where the interpreter does.

Example: `total * 2` pushes twice `total`'s word, and reverts with the
interpreter when that overflows; `c ? a : b` runs only the branch `c` picks. -/
theorem val_sim : ∀ {p : PrimTy} (e : Solidity.Val C Γ p) {m : Machine},
    Sim C L b F σ m → valIn F e = true →
      ValOutT p (e.evalT σ) (run (compileVal b e) m) m
  | _, .simple s, m, hm, hw => by
    simp only [Solidity.Val.evalT, compileVal]
    obtain ⟨w, hr, hrun⟩ := simple_sim hm s (by simpa only [valIn] using hw)
    exact .inl ⟨_, w, rfl, hr, hrun⟩
  | p, .read l, m, hm, hw => by
    simp only [valIn] at hw
    simp only [Solidity.Val.evalT, compileVal]
    rcases loc_sim l hm hw with ⟨r, s, sv, hres, hsv, _, hr, hrun⟩ | ⟨hres, hrun⟩
    · rw [run_append_ok hrun]
      obtain ⟨v, rfl, hrv⟩ := prim_read hr
      refine .inl ⟨v, .val (m.store.cells s), ?_, hrv, rfl⟩
      simp only [hres, Sto.find_of_findLive hsv, bind, Except.bind, TRes.ofOpt, pure,
        Except.pure, SVal.view_prim]
    · exact .inr ⟨by simp only [hres, bind, Except.bind], run_append_revert hrun⟩
  | _, @Solidity.Val.binop _ _ p q op hacc hq x y, m, hm, hw => by
    have iha : ∀ {m : Machine}, Sim C L b F σ m → valIn F x = true →
        ValOutT p (x.evalT σ) (run (compileVal b x) m) m := fun hm hw => val_sim x hm hw
    have ihb : ∀ {m : Machine}, Sim C L b F σ m → valIn F y = true →
        ValOutT p (y.evalT σ) (run (compileVal b y) m) m := fun hm hw => val_sim y hm hw
    subst hq
    simp only [valIn, Bool.and_eq_true] at hw
    obtain ⟨⟨hop, hwa⟩, hwb⟩ := hw
    simp only [Solidity.Val.evalT]
    by_cases hand : op = .and
    · subst hand
      obtain rfl : p = .bool := by cases p <;> simp only [binInFrag, BEq.rfl, beq_iff_eq,
          reduceCtorEq] at hop ⊢
      simp only [compileVal, List.append_assoc]
      rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
      · obtain rfl := hra.bool_inv
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
          · obtain rfl := hrb.bool_inv
            refine .inl ⟨vb, .val (bword vb), ?_, rfl, hrunb⟩
            simp only [bind, Except.bind, BinOp.shortT, Solidity.boolT, hvb, ↓reduceIte]
            cases vb <;> rfl
          · exact .inr ⟨by simp only [bind, Except.bind, BinOp.shortT, Solidity.boolT, hvb,
              ↓reduceIte], hrunb⟩
      · exact .inr ⟨by simp only [bind, Except.bind, hva], run_append_revert hruna⟩
    by_cases hor : op = .or
    · subst hor
      obtain rfl : p = .bool := by cases p <;> simp only [binInFrag, BEq.rfl, beq_iff_eq,
          reduceCtorEq] at hop ⊢
      simp only [compileVal, List.append_assoc]
      rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
      · obtain rfl := hra.bool_inv
        rw [run_append_ok hruna, hva]
        cases va
        · rw [show [Instr.dup 1, .jumpi ((compileVal b y).length + 1), .pop] ++ compileVal b y
            = [Instr.dup 1, .jumpi ((compileVal b y).length + 1), .pop] ++ compileVal b y
            from rfl, run_append_ok (m' := m) rfl]
          rcases ihb hm hwb with ⟨vb, wb, hvb, hrb, hrunb⟩ | ⟨hvb, hrunb⟩
          · obtain rfl := hrb.bool_inv
            refine .inl ⟨vb, .val (bword vb), ?_, rfl, hrunb⟩
            simp only [bind, Except.bind, BinOp.shortT, Solidity.boolT, hvb,
              Bool.false_eq_true, ↓reduceIte]
            cases vb <;> rfl
          · exact .inr ⟨by simp only [bind, Except.bind, BinOp.shortT, Solidity.boolT, hvb,
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
        exact tail_simT hop hand hor hacc hra hrb m
      · exact .inr ⟨by rw [hvb], run_append_revert hrunb⟩
    · exact .inr ⟨by simp only [bind, Except.bind, hva], run_append_revert hruna⟩
  | _, @Solidity.Val.unop _ _ p q op hacc hq x, m, hm, hw => by
    have iha : ∀ {m : Machine}, Sim C L b F σ m → valIn F x = true →
        ValOutT p (x.evalT σ) (run (compileVal b x) m) m := fun hm hw => val_sim x hm hw
    subst hq
    simp only [valIn, Bool.and_eq_true] at hw
    obtain ⟨hop, hwa⟩ := hw
    have key : ∀ {va : p.Denote}, x.evalT σ = .ok va →
        (Solidity.Val.unop op hacc rfl x).evalT σ = TRes.ofOpt (op.evalT hacc va) := fun h => by
      simp only [Solidity.Val.evalT, h, bind, Except.bind]
    have err : ∀ {e : Solidity.THalt}, x.evalT σ = .error e →
        (Solidity.Val.unop op hacc rfl x).evalT σ = .error e := fun h => by
      simp only [Solidity.Val.evalT, h, bind, Except.bind]
    cases op with
    | not =>
      obtain rfl : p = .bool := by cases p <;> simp only [UnOp.accepts, BEq.rfl, beq_iff_eq,
          reduceCtorEq] at hacc ⊢
      simp only [compileVal]
      rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
      · obtain rfl := hra.bool_inv
        rw [run_append_ok hruna, key hva]
        refine .inl ⟨!va, .val (bword !va), rfl, rfl, ?_⟩
        cases va <;> rfl
      · exact .inr ⟨err hva, run_append_revert hruna⟩
    | neg =>
      obtain rfl : p = .int := by simpa only [unInFrag, beq_iff_eq] using hop
      simp only [compileVal]
      rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
      · rw [run_append_ok hruna, key hva]
        exact neg_simT hra m
      · exact .inr ⟨err hva, run_append_revert hruna⟩
    | bnot =>
      obtain rfl : p = .uint := by simpa only [unInFrag, beq_iff_eq] using hop
      simp only [compileVal]
      rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
      · rw [run_append_ok hruna, key hva]
        exact bnot_simT hra m
      · exact .inr ⟨err hva, run_append_revert hruna⟩
    | toInt =>
      obtain rfl : p = .uint := by simpa only [unInFrag, beq_iff_eq] using hop
      simp only [compileVal]
      rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
      · rw [run_append_ok hruna, key hva]
        exact toInt_simT hra m
      · exact .inr ⟨err hva, run_append_revert hruna⟩
    | toUint =>
      obtain rfl : p = .int := by simpa only [unInFrag, beq_iff_eq] using hop
      simp only [compileVal]
      rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
      · rw [run_append_ok hruna, key hva]
        exact toUint_simT hra m
      · exact .inr ⟨err hva, run_append_revert hruna⟩
  | p, .ternary c x y, m, hm, hw => by
    have ihc : ∀ {m : Machine}, Sim C L b F σ m → valIn F c = true →
        ValOutT .bool (c.evalT σ) (run (compileVal b c) m) m := fun hm hw => val_sim c hm hw
    have iha : ∀ {m : Machine}, Sim C L b F σ m → valIn F x = true →
        ValOutT p (x.evalT σ) (run (compileVal b x) m) m := fun hm hw => val_sim x hm hw
    have ihb : ∀ {m : Machine}, Sim C L b F σ m → valIn F y = true →
        ValOutT p (y.evalT σ) (run (compileVal b y) m) m := fun hm hw => val_sim y hm hw
    simp only [valIn, Bool.and_eq_true] at hw
    obtain ⟨⟨hwc, hwa⟩, hwb⟩ := hw
    simp only [Solidity.Val.evalT, compileVal, List.append_assoc]
    rcases ihc hm hwc with ⟨vc, wc, hvc, hrc, hrunc⟩ | ⟨hvc, hrunc⟩
    · obtain rfl := hrc.bool_inv
      rw [run_append_ok hrunc, hvc]
      simp only [bind, Except.bind, Solidity.boolT]
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
    simp only [Solidity.Val.evalT, compileVal]
    rcases spath_sim q hm hw with ⟨r, s, sv, hres, hsv, _, hr, hrun⟩ | ⟨hres, hrun⟩
    · cases hr with
      | @array _ kk _ e sh hk hl hW _ =>
        rw [run_append_ok hrun]
        have hlen := Sto.len_eq (Sto.find_of_findLive hsv)
        refine .inl ⟨Solidity.lenU kk hk, .val ⟨kk, hk⟩, ?_, ReprV.uint_of rfl, ?_⟩
        · simp only [hres, hlen, bind, Except.bind, TRes.ofOpt, pure, Except.pure]
        · simp only [run, Machine.push, exec_cons_zero, Instr.step, Machine.next, exec_nil,
            Out.ok_bind, show m.store.cells s = ⟨kk, hk⟩ from Fin.ext hl]
    · exact .inr ⟨by simp only [hres, bind, Except.bind], run_append_revert hrun⟩
  | _, .readMem _, _, _, hw => by simp only [valIn, Bool.false_eq_true] at hw
  | _, .mlen .., _, _, hw => by simp only [valIn, Bool.false_eq_true] at hw
  | _, .modular .., _, _, hw => by simp only [valIn, Bool.false_eq_true] at hw

end

end Solidity.Evm
