import Solidity.Update
import Solidity.Theory.Bridge.Copy
import Solidity.Theory.Bridge.Push

/-!
# The term bridge

`Term.denote` (`Update.lean`) reads a formula's terms in the Theory algebra;
`Term.eval` is the interpreter's reading.  The term bridge
(`Term.denote_eval` and its three siblings) says the two agree wherever
`eval` returns — literally for a value and a path, up to `StValue.Equiv` for
a storage and a stored value — so an equation between terms that return
means what it meant before `holds` read it through `denote`
(`Term.holdsEq_of_eval`, `holds_eqD_iff`).

This is the only Theory module that imports `Update` (design R10).
-/

namespace Solidity

open Semantics Theory Theory.StValue

variable {C : Contract}

/-! One structural induction over the four syntactic sorts, following `eval`:
each step peels a bind with `bind_ok_inv`, and each storage operation is its
bridge lemma (`Bridge/Find`, `Save`, `Copy`, `Delete`, `Push`) composed with
an `Equiv` congruence of `Observe`, since the storage below it is known only
up to `Equiv`. -/

mutual

/-- A value term that returns denotes its value. -/
theorem Term.denote_eval {σ : State} {t : Term C} {x : Value} (h : t.eval σ = .ok x) :
    t.denote σ = .prim x := by
  match t, h with
  | .lit v, h =>
    cases h
    rfl
  | .pv y, h =>
    obtain ⟨b, hb, h⟩ := bind_ok_inv h
    cases b <;> cases h
    simp only [Term.denote, hb]
  | .binop op p a b, h =>
    obtain ⟨va, ha, h⟩ := bind_ok_inv h
    have hda : a.denote σ = .prim va := Term.denote_eval ha
    have hb' : evalBinop op p va (b.denote σ).toRes = .ok x := by
      cases hb : b.eval σ with
      | error e => rw [hb] at h; exact Denote.evalBinop_of_error _ h
      | ok vb => rw [hb] at h; rw [Term.denote_eval hb]; exact h
    simp only [Term.denote]
    rw [hda]
    exact congrArg Res.toSt hb'
  | .unop op p a, h =>
    obtain ⟨va, ha, h⟩ := bind_ok_inv h
    have hda : a.denote σ = .prim va := Term.denote_eval ha
    simp only [Term.denote]
    rw [hda]
    exact congrArg Res.toSt h
  | .find s q, h =>
    obtain ⟨τ, hs, h⟩ := bind_ok_inv h
    obtain ⟨⟨r, segs⟩, hq, h⟩ := bind_ok_inv h
    obtain ⟨w, hw, h⟩ := bind_ok_inv h
    have e1 : Struct.Equiv (s.denote σ) τ.abs := STerm.denote_eval hs
    have e2 : q.denote σ = rootPath r segs := PTerm.denote_eval hq
    have e3 : findSt τ.abs (rootPath r segs) = w.abs := State.abs_findStorage hw
    have e4 : w.abs = .prim x := SVal.abs_of_asValue h
    show findSt (s.denote σ) (q.denote σ) = .prim x
    rw [e2, ← Equiv.prim_iff, ← e4, ← e3]
    exact Equiv.findSt e1 _
  | .len s q, h =>
    obtain ⟨τ, hs, h⟩ := bind_ok_inv h
    obtain ⟨⟨r, segs⟩, hq, h⟩ := bind_ok_inv h
    have e1 : Struct.Equiv (s.denote σ) τ.abs := STerm.denote_eval hs
    have e2 : q.denote σ = rootPath r segs := PTerm.denote_eval hq
    have e3 : findSt τ.abs (rootPath r segs ++ [lengthSeg]) = .prim x := State.abs_arrayLen h
    show findSt (s.denote σ) (q.denote σ ++ [lengthSeg]) = .prim x
    rw [e2, ← Equiv.prim_iff, ← e3]
    exact Equiv.findSt e1 _
  | .read m a, h =>
    show Res.toSt _ = _
    rw [h]
    rfl
  | .ite c a b, h =>
    obtain ⟨vc, hc, h⟩ := bind_ok_inv h
    have hdc : c.denote σ = .prim vc := Term.denote_eval hc
    match vc, h with
    | .bool true, h =>
      simp only [Term.denote, hdc]
      exact Term.denote_eval (t := a) h
    | .bool false, h =>
      simp only [Term.denote, hdc]
      exact Term.denote_eval (t := b) h
    | .int _, h => cases h
  | .mlen m i, h =>
    show Res.toSt _ = _
    rw [h]
    rfl
  | .env k, h =>
    cases h
    rfl
  | .net a, h =>
    obtain ⟨va, ha, h⟩ := bind_ok_inv h
    obtain ⟨n, hn, h⟩ := bind_ok_inv h
    have hda : a.denote σ = .prim va := Term.denote_eval ha
    cases va <;> cases hn
    cases h
    simp only [Term.denote, hda]
  | .netOf y a, h =>
    obtain ⟨bd, hbd, h⟩ := bind_ok_inv h
    cases bd with
    | ledger l =>
      obtain ⟨va, ha, h⟩ := bind_ok_inv h
      obtain ⟨n, hn, h⟩ := bind_ok_inv h
      have hda : a.denote σ = .prim va := Term.denote_eval ha
      cases va <;> cases hn
      cases h
      simp only [Term.denote, hda, hbd]
    | _ => cases h

/-- A path that resolves denotes its Theory path. -/
theorem PTerm.denote_eval {σ : State} {p : PTerm C} {r : Name} {segs : List Seg}
    (h : p.eval σ = .ok (r, segs)) : p.denote σ = rootPath r segs := by
  match p, h with
  | .root r', h =>
    cases h
    rfl
  | .pv y, h =>
    have h' : aliasPath σ y = .ok (r, segs) := h
    simp only [PTerm.denote, h']
  | .field q f, h =>
    obtain ⟨⟨r0, s0⟩, hq, h⟩ := bind_ok_inv h
    cases h
    simp only [PTerm.denote, PTerm.denote_eval hq]
    rfl
  | .at q i, h =>
    obtain ⟨⟨r0, s0⟩, hq, h⟩ := bind_ok_inv h
    obtain ⟨vi, hi, h⟩ := bind_ok_inv h
    obtain ⟨k, hk, h⟩ := bind_ok_inv h
    obtain ⟨u, hu, h⟩ := bind_ok_inv h
    cases h
    simp only [PTerm.denote]
    rw [PTerm.denote_eval hq, Term.denote_eval hi, Denote.asInt_prim_of_asInt hk]
    rfl
  | .next q, h =>
    obtain ⟨⟨r0, s0⟩, hq, h⟩ := bind_ok_inv h
    obtain ⟨w, hw, h⟩ := bind_ok_inv h
    match w, hw, h with
    | .array es sh fx, hw, h =>
      cases h
      simp only [PTerm.denote]
      rw [PTerm.denote_eval hq, State.abs_lenAt_of_array hw]
      rfl
    | .prim _, _, h | .struct _, _, h | .map .., _, h => cases h

/-- A storage term that returns denotes its storage, up to `Equiv`. -/
theorem STerm.denote_eval {σ τ : State} {s : STerm C} (h : s.eval σ = .ok τ) :
    Struct.Equiv (s.denote σ) τ.abs := by
  match s, h with
  | .storage, h =>
    cases h
    exact StValue.Equiv.refl _
  | .pv y, h =>
    obtain ⟨b, hb, h⟩ := bind_ok_inv h
    cases b with
    | store st =>
      cases h
      simp only [STerm.denote, hb]
      exact StValue.Equiv.refl _
    | _ => cases h
  | .save s q v, h =>
    obtain ⟨sv, hv, h⟩ := bind_ok_inv h
    obtain ⟨τ0, hs, h⟩ := bind_ok_inv h
    obtain ⟨⟨r, segs⟩, hq, h⟩ := bind_ok_inv h
    have e1 : Struct.Equiv (s.denote σ) τ0.abs := STerm.denote_eval hs
    have e2 : q.denote σ = rootPath r segs := PTerm.denote_eval hq
    have e3 : StValue.Equiv (v.denote σ) sv.abs := SValT.denote_eval hv
    have e4 : Struct.Equiv (copyTo τ0.abs (rootPath r segs) sv.abs) τ.abs :=
      State.abs_writeStorage h
    show Struct.Equiv (copyTo (s.denote σ) (q.denote σ) (v.denote σ)) τ.abs
    rw [e2]
    exact StValue.Equiv.trans (Struct.Equiv.copyTo e1 e3 _) e4
  | .delAt s q, h =>
    obtain ⟨τ0, hs, h⟩ := bind_ok_inv h
    obtain ⟨⟨r, segs⟩, hq, h⟩ := bind_ok_inv h
    obtain ⟨cur, hcur, h⟩ := bind_ok_inv h
    have e1 : Struct.Equiv (s.denote σ) τ0.abs := STerm.denote_eval hs
    have e2 : q.denote σ = rootPath r segs := PTerm.denote_eval hq
    have e4 : Struct.Equiv (delAt τ0.abs (rootPath r segs)) τ.abs := State.abs_delete hcur h
    show Struct.Equiv (delAt (s.denote σ) (q.denote σ)) τ.abs
    rw [e2]
    exact StValue.Equiv.trans (Struct.Equiv.delAt e1 _) e4
  | .push s q v, h =>
    obtain ⟨τ0, hs, h⟩ := bind_ok_inv h
    obtain ⟨⟨r, segs⟩, hq, h⟩ := bind_ok_inv h
    have e1 : Struct.Equiv (s.denote σ) τ0.abs := STerm.denote_eval hs
    have e2 : q.denote σ = rootPath r segs := PTerm.denote_eval hq
    cases hv : v.eval σ with
    | error e =>
      exfalso
      have h' : pushAt τ0 .uint r segs (fun _ => .error e) = .ok τ := by
        rw [hv] at h
        exact h
      unfold pushAt at h'
      obtain ⟨w, _, h'⟩ := bind_ok_inv h'
      cases w <;> cases h'
    | ok w =>
      have e3 : StValue.Equiv (v.denote σ) w.abs := SValT.denote_eval hv
      have h' : pushAt τ0 .uint r segs (fun _ => .ok w.strip) = .ok τ := by
        rw [hv] at h
        exact h
      have e4 : τ.abs = pushT τ0.abs (rootPath r segs) w.strip.abs := State.abs_pushAt_const _ h'
      show Struct.Equiv (pushT (s.denote σ) (q.denote σ) (stripVal (v.denote σ))) τ.abs
      rw [e2, e4]
      exact Struct.Equiv.pushT e1
        (StValue.Equiv.trans (StValue.Equiv.stripVal e3) (SVal.abs_strip w)) _
  | .pushSlot s q E, h =>
    obtain ⟨τ0, hs, h⟩ := bind_ok_inv h
    obtain ⟨⟨r, segs⟩, hq, h⟩ := bind_ok_inv h
    have e1 : Struct.Equiv (s.denote σ) τ0.abs := STerm.denote_eval hs
    have e2 : q.denote σ = rootPath r segs := PTerm.denote_eval hq
    have e4 : τ.abs = pushSlotT E.isPrimitive (defaultForTy E).abs τ0.abs (rootPath r segs) :=
      State.abs_pushAt_slot h
    show Struct.Equiv (pushSlotT E.isPrimitive (defaultForTy E).abs (s.denote σ) (q.denote σ))
      τ.abs
    rw [e2, e4]
    exact Struct.Equiv.pushSlotT _ _ e1 _
  | .pop s q, h =>
    obtain ⟨τ0, hs, h⟩ := bind_ok_inv h
    obtain ⟨⟨r, segs⟩, hq, h⟩ := bind_ok_inv h
    have e1 : Struct.Equiv (s.denote σ) τ0.abs := STerm.denote_eval hs
    have e2 : q.denote σ = rootPath r segs := PTerm.denote_eval hq
    have e4 : Struct.Equiv (popT τ0.abs (rootPath r segs)) τ.abs := State.abs_pop h
    show Struct.Equiv (popT (s.denote σ) (q.denote σ)) τ.abs
    rw [e2]
    exact StValue.Equiv.trans (Struct.Equiv.popT e1 _) e4
  | .shrink s q, h =>
    obtain ⟨τ0, hs, h⟩ := bind_ok_inv h
    obtain ⟨⟨r, segs⟩, hq, h⟩ := bind_ok_inv h
    have e1 : Struct.Equiv (s.denote σ) τ0.abs := STerm.denote_eval hs
    have e2 : q.denote σ = rootPath r segs := PTerm.denote_eval hq
    have e4 : τ.abs = shrinkT τ0.abs (rootPath r segs) := State.abs_shrink h
    show Struct.Equiv (shrinkT (s.denote σ) (q.denote σ)) τ.abs
    rw [e2, e4]
    exact Struct.Equiv.shrinkT e1 _
  | .extend s q E, h =>
    obtain ⟨τ0, hs, h⟩ := bind_ok_inv h
    obtain ⟨⟨r, segs⟩, hq, h⟩ := bind_ok_inv h
    obtain ⟨⟨τ', k⟩, hp, h⟩ := bind_ok_inv h
    cases h
    have e1 : Struct.Equiv (s.denote σ) τ0.abs := STerm.denote_eval hs
    have e2 : q.denote σ = rootPath r segs := PTerm.denote_eval hq
    have e4 : τ'.abs = pushSlotT E.isPrimitive (defaultForTy E).abs τ0.abs (rootPath r segs) :=
      (State.abs_pushPlaceAt hp).1
    show Struct.Equiv (pushSlotT E.isPrimitive (defaultForTy E).abs (s.denote σ) (q.denote σ))
      τ'.abs
    rw [e2, e4]
    exact Struct.Equiv.pushSlotT _ _ e1 _

/-- A stored value that returns denotes it, up to `Equiv`. -/
theorem SValT.denote_eval {σ : State} {v : SValT C} {w : SVal} (h : v.eval σ = .ok w) :
    StValue.Equiv (v.denote σ) w.abs := by
  match v, h with
  | .val t, h =>
    obtain ⟨x, ht, h⟩ := bind_ok_inv h
    cases h
    show StValue.Equiv (t.denote σ) x.toSVal.abs
    rw [Term.denote_eval ht]
    cases x <;> exact StValue.Equiv.refl _
  | .find s q, h =>
    obtain ⟨τ0, hs, h⟩ := bind_ok_inv h
    obtain ⟨⟨r, segs⟩, hq, h⟩ := bind_ok_inv h
    have e1 : Struct.Equiv (s.denote σ) τ0.abs := STerm.denote_eval hs
    have e2 : q.denote σ = rootPath r segs := PTerm.denote_eval hq
    show StValue.Equiv (findSt (s.denote σ) (q.denote σ)) w.abs
    rw [e2, ← State.abs_findStorage h]
    exact Equiv.findSt e1 _
  | .copyMem m i, h =>
    simp only [SValT.denote, h]
    exact StValue.Equiv.refl _
  | .newArr R n, h =>
    obtain ⟨vn, hn, h⟩ := bind_ok_inv h
    obtain ⟨k, hk, h⟩ := bind_ok_inv h
    cases h
    show StValue.Equiv (newArrVal R (asInt (n.denote σ))).abs (newArrVal R k).abs
    rw [Term.denote_eval hn, Denote.asInt_prim_of_asInt hk]
    exact StValue.Equiv.refl _

end

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
