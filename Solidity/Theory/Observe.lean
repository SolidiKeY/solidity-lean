import Solidity.Theory.Copy

/-!
# Observational equality and congruence

`StValue.Equiv` (`Theory/Terms.lean`) says two values show the same along every
path: the same primitive, or a node of the same kind.  The laws that are not
literal equations — a copy, a delete, a pop — hold up to it, and this module
is what makes them usable under any context: every operation of the algebra
respects `Equiv`.

The congruences come from one bisimulation argument.  `Sim` is the closure of
`Equiv` under the three operations that build lazy structure (`copyVal`,
`delValue`, `storeAt`); `Sim.equiv` says it is contained in `Equiv`, because a
`copyAt`/`delSt` member is computed from kinds, lengths and members alone
(`copyRead`, `keepsOnDelete`), and kinds and lengths are what `Equiv` fixes —
`asInt` factors through `seen`.  `Equiv.of_bisim` is that coinduction step,
stated once.
-/

namespace Solidity
namespace Theory

open Semantics

namespace StValue

open Struct

/-! ## The equivalence -/

theorem Equiv.refl (v : StValue) : Equiv v v := fun _ => rfl

theorem Equiv.symm {v w : StValue} (h : Equiv v w) : Equiv w v := fun q => (h q).symm

theorem Equiv.trans {u v w : StValue} (h1 : Equiv u v) (h2 : Equiv v w) : Equiv u w :=
  fun q => (h1 q).trans (h2 q)

/-! ## Reads -/

/-- `readAt` on a struct is `findSt`. -/
theorem readAt_st (s : Struct) (q : List Seg) : (st s).readAt q = findSt s q := by
  induction q generalizing s with
  | nil => rfl
  | cons a q ih =>
      cases q with
      | nil => rfl
      | cons b q =>
          show readAt (selectSt s a) (b :: q) = findSt (asStruct (selectSt s a)) (b :: q)
          rw [← ih]
          rfl

theorem readAt_append (v : StValue) (p q : List Seg) :
    v.readAt (p ++ q) = (v.readAt p).readAt q := by
  induction p generalizing v with
  | nil => rfl
  | cons a p ih => exact ih _

/-- The `int` cast sees no more than `seen`. -/
theorem asInt_of_seen {v w : StValue} (h : v.seen = w.seen) : asInt v = asInt w := by
  cases v with
  | prim p => cases w with
    | prim p' => cases h; rfl
    | st _ => cases h
  | st _ => cases w with
    | prim _ => cases h
    | st _ => rfl

/-- The `bool` cast sees no more than `seen`. -/
theorem asBool_of_seen {v w : StValue} (h : v.seen = w.seen) : asBool v = asBool w := by
  cases v with
  | prim p => cases w with
    | prim p' => cases h; rfl
    | st _ => cases h
  | st _ => cases w with
    | prim _ => cases h
    | st _ => rfl

/-- A primitive is equivalent only to itself. -/
theorem Equiv.prim_iff {v : StValue} {p : PrimVal} : Equiv v (.prim p) ↔ v = .prim p := by
  constructor
  · intro h
    have h0 : v.seen = (prim p).seen := h []
    cases v with
    | prim p' => cases h0; rfl
    | st _ => cases h0
  · rintro rfl
    exact Equiv.refl _

theorem Equiv.asInt {v w : StValue} (h : Equiv v w) : StValue.asInt v = StValue.asInt w := by
  exact asInt_of_seen (h [])

theorem Equiv.asBool {v w : StValue} (h : Equiv v w) : StValue.asBool v = StValue.asBool w := by
  exact asBool_of_seen (h [])

theorem Equiv.asStruct {v w : StValue} (h : Equiv v w) :
    Struct.Equiv (StValue.asStruct v) (StValue.asStruct w) := by
  have h0 : v.seen = w.seen := h []
  cases v with
  | prim p => cases w with
    | prim p' => cases h0; exact Equiv.refl _
    | st _ => cases h0
  | st _ => cases w with
    | prim _ => cases h0
    | st _ => exact h

theorem Equiv.readAt {v w : StValue} (h : Equiv v w) (p : List Seg) :
    Equiv (v.readAt p) (w.readAt p) := by
  intro q
  rw [← readAt_append, ← readAt_append]
  exact h (p ++ q)

theorem Equiv.select {s t : Struct} (h : Struct.Equiv s t) (a : Seg) :
    Equiv (selectSt s a) (selectSt t a) := by
  exact fun q => h (a :: q)

theorem Equiv.findSt {s t : Struct} (h : Struct.Equiv s t) (q : List Seg) :
    Equiv (StValue.findSt s q) (StValue.findSt t q) := by
  rw [← readAt_st, ← readAt_st]
  exact StValue.Equiv.readAt h q

end StValue

theorem Struct.Equiv.kind {s t : Struct} (h : Struct.Equiv s t) : s.kind = t.kind := by
  have h0 : Seen.node s.kind = Seen.node t.kind := h []
  injection h0

theorem Struct.Equiv.lenOf {s t : Struct} (h : Struct.Equiv s t) :
    StValue.lenOf s = StValue.lenOf t := by
  exact StValue.Equiv.asInt (StValue.Equiv.select h StValue.lengthSeg)

namespace StValue

open Struct

/-! ## Bisimulation -/

/-- Coinduction for `Equiv`: a relation that shows the same at the top and whose
members are related again (or already equivalent) is contained in `Equiv`. -/
theorem Equiv.of_bisim (R : StValue -> StValue -> Prop)
    (hseen : ∀ {v w}, R v w -> v.seen = w.seen)
    (hsel : ∀ {v w} (a : Seg), R v w ->
      R (selectSt (StValue.asStruct v) a) (selectSt (StValue.asStruct w) a) ∨
      Equiv (selectSt (StValue.asStruct v) a) (selectSt (StValue.asStruct w) a))
    {v w : StValue} (h : R v w) : Equiv v w := by
  intro q
  induction q generalizing v w with
  | nil => exact hseen h
  | cons a q ih =>
      rcases hsel a h with h' | h'
      · exact ih h'
      · exact h' q

/-- `Equiv` closed under the operations that build lazy structure. -/
inductive Sim : StValue -> StValue -> Prop
  | eqv {v w : StValue} : Equiv v w -> Sim v w
  | copy {o o' n n' : StValue} : Sim o o' -> Sim n n' ->
      Sim (StValue.copyVal o n) (StValue.copyVal o' n')
  | del {v v' : StValue} : Sim v v' -> Sim (StValue.delValue v) (StValue.delValue v')
  | store {s t : Struct} {a : Seg} {v w : StValue} : Sim (.st s) (.st t) -> Sim v w ->
      Sim (.st (StValue.storeAt s a v)) (.st (StValue.storeAt t a w))

/-! ### One step of `Sim`

`Sim.step` is the induction: a `Sim` pair shows the same at the top, and at one
selector down shows the same again and is `Sim` again.  The second `seen` is
what the `copyAt` and `delSt` arms need, because their members are chosen by
the operands' lengths — a member's `asInt`. -/

/-- A copy shows what the new value shows. -/
theorem seen_copyVal (o n : StValue) : (StValue.copyVal o n).seen = n.seen := by
  cases n <;> rfl

/-- A delete keeps the node's kind. -/
theorem kind_delNode (s : Struct) : (delNode s).kind = s.kind := by
  cases s <;> rfl

/-- A delete shows what the value's `seen` fixes. -/
theorem seen_delValue {v w : StValue} (h : v.seen = w.seen) :
    (StValue.delValue v).seen = (StValue.delValue w).seen := by
  cases v with
  | prim p => cases w with
    | prim p' => cases h; rfl
    | st _ => cases h
  | st s => cases w with
    | prim _ => cases h
    | st t =>
        show Seen.node (delNode s).kind = Seen.node (delNode t).kind
        rw [kind_delNode, kind_delNode]
        exact h

/-- The same `seen` is the same kind under the `Struct` cast. -/
theorem kind_asStruct_of_seen {v w : StValue} (h : v.seen = w.seen) :
    (asStruct v).kind = (asStruct w).kind := by
  cases v with
  | prim p => cases w with
    | prim _ => rfl
    | st _ => cases h
  | st s => cases w with
    | prim _ => cases h
    | st t => injection h

/-- The two halves of `SimStep` at one member. -/
private abbrev SimSeen (v w : StValue) : Prop := v.seen = w.seen ∧ Sim v w

/-- What `Sim.step` proves of a `Sim` pair. -/
private def SimStep (v w : StValue) : Prop :=
  v.seen = w.seen ∧ ∀ a, SimSeen (selectSt (asStruct v) a) (selectSt (asStruct w) a)

private theorem SimSeen.refl (v : StValue) : SimSeen v v := ⟨rfl, Sim.eqv (Equiv.refl v)⟩

private theorem SimSeen.copy {o o' n n' : StValue} (ho : SimSeen o o') (hn : SimSeen n n') :
    SimSeen (StValue.copyVal o n) (StValue.copyVal o' n') :=
  ⟨by rw [seen_copyVal, seen_copyVal]; exact hn.1, Sim.copy ho.2 hn.2⟩

private theorem SimSeen.del {v v' : StValue} (h : SimSeen v v') :
    SimSeen (StValue.delValue v) (StValue.delValue v') :=
  ⟨seen_delValue h.1, Sim.del h.2⟩

/-- `copyRead` reads only kinds, lengths and the two members. -/
private theorem copyRead_simSeen (ko kn : Option NodeKind) (lo ln : Int) (a : Seg)
    {vo vo' vn vn' : StValue} (ho : SimSeen vo vo') (hn : SimSeen vn vn') :
    SimSeen (copyRead ko kn lo ln a vo vn) (copyRead ko kn lo ln a vo' vn') := by
  unfold copyRead
  repeat' split
  all_goals first
    | exact ho | exact hn | exact SimSeen.refl _ | exact SimSeen.del ho
    | exact SimSeen.copy ho hn | exact SimSeen.copy (SimSeen.refl _) hn

private theorem SimStep.of_equiv {v w : StValue} (h : Equiv v w) : SimStep v w :=
  ⟨h [], fun a => ⟨h [a], Sim.eqv fun q => h (a :: q)⟩⟩

private theorem Sim.step {v w : StValue} (h : Sim v w) : SimStep v w := by
  induction h with
  | eqv h => exact SimStep.of_equiv h
  | @copy o o' n n' _ _ iho ihn =>
      obtain ⟨hn0, hn1⟩ := ihn
      cases n with
      | prim p => cases n' with
        | prim p' => exact ⟨hn0, hn1⟩
        | st _ => cases hn0
      | st N => cases n' with
        | prim _ => cases hn0
        | st N' =>
            have hkN : N.kind = N'.kind := kind_asStruct_of_seen hn0
            have hkO : (asStruct o).kind = (asStruct o').kind := kind_asStruct_of_seen iho.1
            have hlO : lenOf (asStruct o) = lenOf (asStruct o') :=
              asInt_of_seen (iho.2 lengthSeg).1
            have hlN : lenOf N = lenOf N' := asInt_of_seen (hn1 lengthSeg).1
            refine ⟨hn0, fun a => ?_⟩
            show SimSeen (selectSt (.copyAt (asStruct o) N) a) (selectSt (.copyAt (asStruct o') N') a)
            rw [selectOnCopyAt, selectOnCopyAt, hkO, hkN, hlO, hlN]
            exact copyRead_simSeen _ _ _ _ _ (iho.2 a) (hn1 a)
  | @del v v' _ ih =>
      obtain ⟨h0, h1⟩ := ih
      refine ⟨seen_delValue h0, fun a => ?_⟩
      cases v with
      | prim p => cases v' with
        | prim p' => cases h0; exact SimSeen.refl _
        | st _ => cases h0
      | st S => cases v' with
        | prim _ => cases h0
        | st S' =>
            have hk : S.kind = S'.kind := kind_asStruct_of_seen h0
            have hl : lenOf S = lenOf S' := asInt_of_seen (h1 lengthSeg).1
            show SimSeen (selectSt (delNode S) a) (selectSt (delNode S') a)
            rw [selectOnDelNode, selectOnDelNode, hk, hl]
            split
            · exact h1 a
            · exact SimSeen.del (h1 a)
  | @store s t a v w _ hvw ihs ihv =>
      refine ⟨?_, fun b => ?_⟩
      · show Seen.node (storeAt s a v).kind = Seen.node (storeAt t a w).kind
        rw [kind_storeAt, kind_storeAt]
        exact ihs.1
      · show SimSeen (selectSt (storeAt s a v) b) (selectSt (storeAt t a w) b)
        rw [selectSt_storeAt, selectSt_storeAt]
        split
        · exact ⟨ihv.1, hvw⟩
        · exact ihs.2 b

theorem Sim.equiv {v w : StValue} (h : Sim v w) : Equiv v w := by
  exact Equiv.of_bisim Sim (fun h => (Sim.step h).1) (fun a h => Or.inl ((Sim.step h).2 a).2) h

/-! ## Congruence -/

theorem Equiv.copyVal {o o' n n' : StValue} (ho : Equiv o o') (hn : Equiv n n') :
    Equiv (StValue.copyVal o n) (StValue.copyVal o' n') := by
  exact Sim.equiv (Sim.copy (Sim.eqv ho) (Sim.eqv hn))

theorem Equiv.delValue {v w : StValue} (h : Equiv v w) :
    Equiv (StValue.delValue v) (StValue.delValue w) := by
  exact Sim.equiv (Sim.del (Sim.eqv h))

theorem Equiv.stripVal {v w : StValue} (h : Equiv v w) :
    Equiv (StValue.stripVal v) (StValue.stripVal w) := by
  exact StValue.Equiv.copyVal (Equiv.refl _) h

theorem Equiv.fillSlot (b : Bool) (d : StValue) {v w : StValue} (h : Equiv v w) :
    Equiv (StValue.fillSlot b d v) (StValue.fillSlot b d w) := by
  cases b with
  | true => exact Equiv.refl _
  | false =>
      have h0 : v.seen = w.seen := h []
      cases v with
      | prim p => cases w with
        | prim p' => cases h0; exact h
        | st _ => cases h0
      | st s => cases w with
        | prim _ => cases h0
        | st t =>
            have hk : s.kind = t.kind := Struct.Equiv.kind h
            simp only [StValue.fillSlot, Bool.false_eq_true, if_false, hk]
            split
            · exact Equiv.refl _
            · exact h

end StValue

theorem Struct.Equiv.storeAt {s t : Struct} {v w : StValue} (hs : Struct.Equiv s t)
    (hv : StValue.Equiv v w) (a : Seg) :
    Struct.Equiv (StValue.storeAt s a v) (StValue.storeAt t a w) := by
  exact StValue.Sim.equiv (StValue.Sim.store (StValue.Sim.eqv hs) (StValue.Sim.eqv hv))

theorem Struct.Equiv.save {s t : Struct} {v w : StValue} (hs : Struct.Equiv s t)
    (hv : StValue.Equiv v w) (p : List Seg) :
    Struct.Equiv (StValue.save s p v) (StValue.save t p w) := by
  induction p generalizing s t with
  | nil => exact StValue.Equiv.asStruct hv
  | cons a q ih =>
      cases q with
      | nil => exact Struct.Equiv.storeAt hs hv a
      | cons b q =>
          rw [StValue.save_cons_cons, StValue.save_cons_cons]
          exact Struct.Equiv.storeAt hs
            (ih (StValue.Equiv.asStruct (StValue.Equiv.select hs a))) a

theorem Struct.Equiv.copyTo {s t : Struct} {v w : StValue} (hs : Struct.Equiv s t)
    (hv : StValue.Equiv v w) (p : List Seg) :
    Struct.Equiv (StValue.copyTo s p v) (StValue.copyTo t p w) := by
  exact Struct.Equiv.save hs
    (StValue.Equiv.copyVal (StValue.Equiv.findSt hs p) hv) p

theorem Struct.Equiv.delAt {s t : Struct} (hs : Struct.Equiv s t) (p : List Seg) :
    Struct.Equiv (StValue.delAt s p) (StValue.delAt t p) := by
  exact Struct.Equiv.save hs (StValue.Equiv.delValue (StValue.Equiv.findSt hs p)) p

theorem Struct.Equiv.lenAt {s t : Struct} (hs : Struct.Equiv s t) (p : List Seg) :
    StValue.lenAt s p = StValue.lenAt t p := by
  exact StValue.Equiv.asInt (StValue.Equiv.findSt hs _)

theorem Struct.Equiv.pushT {s t : Struct} {w w' : StValue} (hs : Struct.Equiv s t)
    (hw : StValue.Equiv w w') (p : List Seg) :
    Struct.Equiv (StValue.pushT s p w) (StValue.pushT t p w') := by
  unfold StValue.pushT
  rw [Struct.Equiv.lenAt hs p]
  exact Struct.Equiv.save (Struct.Equiv.save hs hw _) (StValue.Equiv.refl _) _

theorem Struct.Equiv.pushSlotT (b : Bool) (d : StValue) {s t : Struct} (hs : Struct.Equiv s t)
    (p : List Seg) :
    Struct.Equiv (StValue.pushSlotT b d s p) (StValue.pushSlotT b d t p) := by
  unfold StValue.pushSlotT
  rw [Struct.Equiv.lenAt hs p]
  exact Struct.Equiv.pushT hs (StValue.Equiv.fillSlot b d (StValue.Equiv.findSt hs _)) p

theorem Struct.Equiv.popT {s t : Struct} (hs : Struct.Equiv s t) (p : List Seg) :
    Struct.Equiv (StValue.popT s p) (StValue.popT t p) := by
  unfold StValue.popT
  rw [Struct.Equiv.lenAt hs p]
  exact Struct.Equiv.save (Struct.Equiv.delAt hs _) (StValue.Equiv.refl _) _

theorem Struct.Equiv.shrinkT {s t : Struct} (hs : Struct.Equiv s t) (p : List Seg) :
    Struct.Equiv (StValue.shrinkT s p) (StValue.shrinkT t p) := by
  unfold StValue.shrinkT
  rw [Struct.Equiv.lenAt hs p]
  exact Struct.Equiv.save hs (StValue.Equiv.refl _) _

end Theory
end Solidity
