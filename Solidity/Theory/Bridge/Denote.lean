import Solidity.Update
import Solidity.Theory.Bridge.Copy
import Solidity.Theory.Bridge.Push

/-!
# The term bridge

`Tm.denote` (`Update.lean`) reads a formula's terms in the Theory algebra;
`Tm.eval` is the interpreter's reading.  The term bridge
(`Tm.denote_eval`, and per sort `Term.denote_eval` …) says the two agree wherever
`eval` returns — literally for a value and a path, up to `StValue.Equiv` for
a storage and a stored value — so an equation between terms that return
means what it meant before `holds` read it through `denote`
(`Term.holdsEq_of_eval`, `holds_eqD_iff`).

This is the only Theory module that imports `Update` (design R10).
-/

namespace Solidity

open Semantics Theory Theory.StValue

variable {C : Contract}

/-! One induction over terms, following `eval`: a symbol's step peels a bind
with `bind_ok_inv`, and each storage operation is its bridge lemma
(`Bridge/Find`, `Save`, `Copy`, `Delete`, `Push`) composed with an `Equiv`
congruence of `Observe`, since the storage below it is known only up to
`Equiv`.  `Srt.Bridge` says what agreeing means at each sort; a memory sort
denotes nothing, so there it says nothing. -/

/-- A denotation agrees with a reading that returns: the value itself, the
Theory path, the storage or stored value up to `Equiv`. -/
def Srt.Bridge : (s : Srt) → s.Den → s.Ev → Prop
  | .val => fun d r => ∀ x, r = .ok x → d = .prim x
  | .path => fun d r => ∀ n segs, r = .ok (n, segs) → d = rootPath n segs
  | .st => fun d r => ∀ τ, r = .ok τ → Struct.Equiv d τ.abs
  | .sv => fun d r => ∀ w, r = .ok w → StValue.Equiv d w.abs
  | .ident | .addr | .mem | .mv => fun _ _ => True

theorem Op0.denote_eval {σ : State} : (o : Op0 s) → Srt.Bridge s (o.denote σ) (o.eval σ)
  | .lit _ | .env _ => by intro _ h; cases h; rfl
  | .root _ => by intro _ _ h; cases h; rfl
  | .storage => by intro _ h; cases h; exact StValue.Equiv.refl _
  | .memory => trivial

theorem Op1.denote_eval {σ : State} :
    (o : Op1 a s) → {r : a.Ev} → {d : a.Den} → Srt.Bridge a d r →
      Srt.Bridge s (o.denote σ d) (o.eval σ r)
  | .unop op p, _, _, hd => by
    intro x h
    obtain ⟨va, ha, h⟩ := bind_ok_inv h
    simp only [Op1.denote]
    rw [hd va ha]
    exact congrArg Res.toSt h
  | .net, _, _, hd => by
    intro x h
    obtain ⟨va, ha, h⟩ := bind_ok_inv h
    obtain ⟨n, hn, h⟩ := bind_ok_inv h
    cases va <;> cases hn
    cases h
    simp only [Op1.denote, hd _ ha]
  | .netOf y, _, _, hd => by
    intro x h
    obtain ⟨bd, hbd, h⟩ := bind_ok_inv h
    cases bd with
    | ledger l =>
      obtain ⟨va, ha, h⟩ := bind_ok_inv h
      obtain ⟨n, hn, h⟩ := bind_ok_inv h
      cases va <;> cases hn
      cases h
      simp only [Op1.denote, hd _ ha, hbd]
    | _ => cases h
  | .field f, _, _, hd => by
    intro r segs h
    obtain ⟨⟨r0, s0⟩, hq, h⟩ := bind_ok_inv h
    cases h
    simp only [Op1.denote, hd _ _ hq]
    rfl
  | .next, _, _, hd => by
    intro r segs h
    obtain ⟨⟨r0, s0⟩, hq, h⟩ := bind_ok_inv h
    obtain ⟨w, hw, h⟩ := bind_ok_inv h
    match w, hw, h with
    | .array es sh fx, hw, h =>
      cases h
      simp only [Op1.denote]
      rw [hd _ _ hq, State.abs_lenAt_of_array hw]
      rfl
    | .prim _, _, h | .struct _, _, h | .map .., _, h => cases h
  | .select r, _, _, hd => by
    intro τ h
    obtain ⟨τ0, hs, h⟩ := bind_ok_inv h
    obtain ⟨w, hw, h⟩ := bind_ok_inv h
    match w, hw, h with
    | .struct fs, hw, h =>
      cases h
      have e1 : Struct.Equiv _ τ0.abs := hd τ0 hs
      have e3 : findSt τ0.abs (rootPath r []) = (SVal.struct fs).abs := State.abs_findStorage hw
      have e5 := Equiv.asStruct (Equiv.findSt e1 (rootPath r []))
      rw [e3] at e5
      exact e5
    | .prim _, _, h | .array .., _, h | .map .., _, h => cases h
  | .sval, _, _, hd => by
    intro w h
    obtain ⟨x, ht, h⟩ := bind_ok_inv h
    cases h
    simp only [Op1.denote]
    rw [hd x ht]
    cases x <;> exact StValue.Equiv.refl _
  | .newArr R, _, _, hd => by
    intro w h
    obtain ⟨vn, hn, h⟩ := bind_ok_inv h
    obtain ⟨k, hk, h⟩ := bind_ok_inv h
    cases h
    simp only [Op1.denote]
    rw [hd vn hn, Denote.asInt_prim_of_asInt hk]
    exact StValue.Equiv.refl _
  | .alloc _, _, _, _ | .mfield _, _, _, _ | .addM _, _, _, _ | .mval, _, _, _
  | .ref, _, _, _ => trivial

theorem Op2.denote_eval {σ : State} :
    (o : Op2 a b s) → {ra : a.Ev} → {rb : b.Ev} → {da : a.Den} → {db : b.Den} →
      Srt.Bridge a da ra → Srt.Bridge b db rb →
      Srt.Bridge s (o.denote σ ra rb da db) (o.eval σ ra rb)
  | .binop op p, _, rb, _, db, ha', hb' => by
    intro x h
    obtain ⟨va, ha, h⟩ := bind_ok_inv h
    have hb : evalBinop op p va db.toRes = .ok x := by
      cases hrb : rb with
      | error e => rw [hrb] at h; exact Denote.evalBinop_of_error _ h
      | ok vb => rw [hrb] at h; rw [hb' vb hrb]; exact h
    simp only [Op2.denote]
    rw [ha' va ha]
    exact congrArg Res.toSt hb
  | .find, _, _, _, _, hs', hq' => by
    intro x h
    obtain ⟨τ, hs, h⟩ := bind_ok_inv h
    obtain ⟨⟨r, segs⟩, hq, h⟩ := bind_ok_inv h
    obtain ⟨w, hw, h⟩ := bind_ok_inv h
    have e3 : findSt τ.abs (rootPath r segs) = w.abs := State.abs_findStorage hw
    have e4 : w.abs = .prim x := SVal.abs_of_asValue h
    simp only [Op2.denote]
    rw [hq' _ _ hq, ← Equiv.prim_iff, ← e4, ← e3]
    exact Equiv.findSt (hs' τ hs) _
  | .len, _, _, _, _, hs', hq' => by
    intro x h
    obtain ⟨τ, hs, h⟩ := bind_ok_inv h
    obtain ⟨⟨r, segs⟩, hq, h⟩ := bind_ok_inv h
    have e3 : findSt τ.abs (rootPath r segs ++ [lengthSeg]) = .prim x := State.abs_arrayLen h
    simp only [Op2.denote]
    rw [hq' _ _ hq, ← Equiv.prim_iff, ← e3]
    exact Equiv.findSt (hs' τ hs) _
  | .read, _, _, _, _, _, _ | .mlen, _, _, _, _, _, _ => by
    intro x h
    simp only [Op2.denote]
    rw [h]
    rfl
  | .at, _, _, _, _, hq', hi' => by
    intro r segs h
    obtain ⟨⟨r0, s0⟩, hq, h⟩ := bind_ok_inv h
    obtain ⟨vi, hi, h⟩ := bind_ok_inv h
    obtain ⟨k, hk, h⟩ := bind_ok_inv h
    obtain ⟨u, hu, h⟩ := bind_ok_inv h
    cases h
    simp only [Op2.denote]
    rw [hq' _ _ hq, hi' vi hi, Denote.asInt_prim_of_asInt hk]
    rfl
  | .delAt, _, _, _, _, hs', hq' => by
    intro τ h
    obtain ⟨τ0, hs, h⟩ := bind_ok_inv h
    obtain ⟨⟨r, segs⟩, hq, h⟩ := bind_ok_inv h
    obtain ⟨cur, hcur, h⟩ := bind_ok_inv h
    have e4 : Struct.Equiv (Theory.StValue.delAt τ0.abs (rootPath r segs)) τ.abs :=
      State.abs_delete hcur h
    simp only [Op2.denote]
    rw [hq' _ _ hq]
    exact StValue.Equiv.trans (Struct.Equiv.delAt (hs' τ0 hs) _) e4
  | .pushSlot E, _, _, _, _, hs', hq' => by
    intro τ h
    obtain ⟨τ0, hs, h⟩ := bind_ok_inv h
    obtain ⟨⟨r, segs⟩, hq, h⟩ := bind_ok_inv h
    have e4 : τ.abs = pushSlotT E.isPrimitive (defaultForTy E).abs τ0.abs (rootPath r segs) :=
      State.abs_pushAt_slot h
    simp only [Op2.denote]
    rw [hq' _ _ hq, e4]
    exact Struct.Equiv.pushSlotT _ _ (hs' τ0 hs) _
  | .pop, _, _, _, _, hs', hq' => by
    intro τ h
    obtain ⟨τ0, hs, h⟩ := bind_ok_inv h
    obtain ⟨⟨r, segs⟩, hq, h⟩ := bind_ok_inv h
    have e4 : Struct.Equiv (popT τ0.abs (rootPath r segs)) τ.abs := State.abs_pop h
    simp only [Op2.denote]
    rw [hq' _ _ hq]
    exact StValue.Equiv.trans (Struct.Equiv.popT (hs' τ0 hs) _) e4
  | .shrink, _, _, _, _, hs', hq' => by
    intro τ h
    obtain ⟨τ0, hs, h⟩ := bind_ok_inv h
    obtain ⟨⟨r, segs⟩, hq, h⟩ := bind_ok_inv h
    have e4 : τ.abs = shrinkT τ0.abs (rootPath r segs) := State.abs_shrink h
    simp only [Op2.denote]
    rw [hq' _ _ hq, e4]
    exact Struct.Equiv.shrinkT (hs' τ0 hs) _
  | .extend E, _, _, _, _, hs', hq' => by
    intro τ h
    obtain ⟨τ0, hs, h⟩ := bind_ok_inv h
    obtain ⟨⟨r, segs⟩, hq, h⟩ := bind_ok_inv h
    obtain ⟨⟨τ', k⟩, hp, h⟩ := bind_ok_inv h
    cases h
    have e4 : τ'.abs = pushSlotT E.isPrimitive (defaultForTy E).abs τ0.abs (rootPath r segs) :=
      (State.abs_pushPlaceAt hp).1
    simp only [Op2.denote]
    rw [hq' _ _ hq, e4]
    exact Struct.Equiv.pushSlotT _ _ (hs' τ0 hs) _
  | .sfind, _, _, _, _, hs', hq' => by
    intro w h
    obtain ⟨τ0, hs, h⟩ := bind_ok_inv h
    obtain ⟨⟨r, segs⟩, hq, h⟩ := bind_ok_inv h
    simp only [Op2.denote]
    rw [hq' _ _ hq, ← State.abs_findStorage h]
    exact Equiv.findSt (hs' τ0 hs) _
  | .copyMem, _, _, _, _, _, _ => by
    intro w h
    simp only [Op2.denote, h]
    exact StValue.Equiv.refl _
  | .iread, _, _, _, _, _, _ | .copy, _, _, _, _, _, _ | .mat, _, _, _, _, _, _
  | .copySt, _, _, _, _, _, _ => trivial

theorem Op3.denote_eval {σ : State} :
    (o : Op3 a b c s) → {ra : a.Ev} → {rb : b.Ev} → {rc : c.Ev} → {da : a.Den} → {db : b.Den} →
      {dc : c.Den} → Srt.Bridge a da ra → Srt.Bridge b db rb → Srt.Bridge c dc rc →
      Srt.Bridge s (o.denote da db dc) (o.eval σ ra rb rc)
  | .ite, _, _, _, _, _, _, hc', ha', hb' => by
    intro x h
    obtain ⟨vc, hc, h⟩ := bind_ok_inv h
    match vc, h with
    | .bool true, h =>
      simp only [Op3.denote, hc' _ hc]
      exact ha' x h
    | .bool false, h =>
      simp only [Op3.denote, hc' _ hc]
      exact hb' x h
    | .int _, h => cases h
  | .save, _, _, rv, _, _, _, hs', hq', hv' => by
    intro τ h
    obtain ⟨sv, hv, h⟩ := bind_ok_inv h
    obtain ⟨τ0, hs, h⟩ := bind_ok_inv h
    obtain ⟨⟨r, segs⟩, hq, h⟩ := bind_ok_inv h
    have e4 : Struct.Equiv (copyTo τ0.abs (rootPath r segs) sv.abs) τ.abs :=
      State.abs_writeStorage h
    simp only [Op3.denote]
    rw [hq' _ _ hq]
    exact StValue.Equiv.trans (Struct.Equiv.copyTo (hs' τ0 hs) (hv' sv hv) _) e4
  | .push, _, _, rv, _, _, _, hs', hq', hv' => by
    intro τ h
    obtain ⟨τ0, hs, h⟩ := bind_ok_inv h
    obtain ⟨⟨r, segs⟩, hq, h⟩ := bind_ok_inv h
    cases hrv : rv with
    | error e =>
      exfalso
      have h' : pushAt τ0 .uint r segs (fun _ => .error e) = .ok τ := by
        rw [hrv] at h
        exact h
      unfold pushAt at h'
      obtain ⟨w, _, h'⟩ := bind_ok_inv h'
      cases w <;> cases h'
    | ok w =>
      have h' : pushAt τ0 .uint r segs (fun _ => .ok w.strip) = .ok τ := by
        rw [hrv] at h
        exact h
      have e4 : τ.abs = pushT τ0.abs (rootPath r segs) w.strip.abs := State.abs_pushAt_const _ h'
      simp only [Op3.denote]
      rw [hq' _ _ hq, e4]
      exact Struct.Equiv.pushT (hs' τ0 hs)
        (StValue.Equiv.trans (StValue.Equiv.stripVal (hv' w hrv)) (SVal.abs_strip w)) _
  | .write, _, _, _, _, _, _, _, _, _ => trivial

/-- **The term bridge**: a term's denotation agrees with its reading
wherever the reading returns (`Srt.Bridge`). -/
theorem Tm.denote_eval {σ : State} : (t : Tm C s) → Srt.Bridge s (t.denote σ) (t.eval σ)
  | .pvV y => by
    intro x h
    obtain ⟨b, hb, h⟩ := bind_ok_inv h
    cases b <;> cases h
    simp only [Tm.denote, hb]
  | .pvP y => by
    intro r segs h
    have h' : aliasPath σ y = .ok (r, segs) := h
    simp only [Tm.denote, h']
  | .pvS y => by
    intro τ h
    obtain ⟨b, hb, h⟩ := bind_ok_inv h
    cases b with
    | store st =>
      cases h
      simp only [Tm.denote, hb]
      exact StValue.Equiv.refl _
    | _ => cases h
  | .pvI _ => trivial
  | .app0 o => o.denote_eval
  | .app1 o a => o.denote_eval a.denote_eval
  | .app2 o a b => o.denote_eval a.denote_eval b.denote_eval
  | .app3 o a b c => o.denote_eval a.denote_eval b.denote_eval c.denote_eval

/-- A value term that returns denotes its value. -/
theorem Term.denote_eval {σ : State} {t : Term C} {x : Value} (h : t.eval σ = .ok x) :
    t.denote σ = .prim x := Tm.denote_eval t x h

/-- A path that resolves denotes its Theory path. -/
theorem PTerm.denote_eval {σ : State} {p : PTerm C} {r : Name} {segs : List Seg}
    (h : p.eval σ = .ok (r, segs)) : p.denote σ = rootPath r segs := Tm.denote_eval p r segs h

/-- A storage term that returns denotes its storage, up to `Equiv`. -/
theorem STerm.denote_eval {σ τ : State} {s : STerm C} (h : s.eval σ = .ok τ) :
    Struct.Equiv (s.denote σ) τ.abs := Tm.denote_eval s τ h

/-- A stored value that returns denotes it, up to `Equiv`. -/
theorem SValT.denote_eval {σ : State} {v : SValT C} {w : SVal} (h : v.eval σ = .ok w) :
    StValue.Equiv (v.denote σ) w.abs := Tm.denote_eval v w h

/-- Between two terms that return, `Equiv` of the denotations is equality of
the values: the old meaning of `holds (a = b)`. -/
theorem Term.holdsEq_of_eval {σ : State} {a b : Term C} {x y : Value}
    (ha : a.eval σ = .ok x) (hb : b.eval σ = .ok y) :
    StValue.Equiv (a.denote σ) (b.denote σ) ↔ x = y := by
  rw [Term.denote_eval ha, Term.denote_eval hb, Equiv.prim_iff]
  exact ⟨fun h => by injection h, fun h => h ▸ rfl⟩

/-- `eqD` is the interpreter's equation: both sides return, with one value.
This is what `holds (a = b)` meant before it read `denote`. -/
theorem holds_eqD_iff {σ : State} {a b : Term C} :
    holds σ (Fml.eqD a b) ↔ ∃ x, a.eval σ = .ok x ∧ b.eval σ = .ok x := by
  simp only [holds]
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩, he⟩
    obtain rfl : x = y := (Term.holdsEq_of_eval hx hy).1 he
    exact ⟨x, hx, hy⟩
  · rintro ⟨x, hx, hy⟩
    exact ⟨⟨x, hx⟩, ⟨x, hy⟩, (Term.holdsEq_of_eval hx hy).2 rfl⟩

end Solidity
