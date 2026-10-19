import Solidity.Calculus.ExpandLaws

/-!
# On the storage fragment, a rule writes only save-like updates

Lean only.  On a fragment of the language (`Stmt.Frag`), every rule of
`Stmt.step` writes the storage only by a term `Tm.expand?` turns into saves
(`Stmt.step_saveLike`), so after the expansion every storage right-hand side
a rule writes is a chain of `save`, `pushSlot` and `shrink` over `storage`
(`Stmt.step_saveNF`), the shape a read of the closer eliminates to a
storage-free term (`LTm.SaveNF`, `Calculus/ElimWriteFree.lean`).

**The fragment** (`Stmt.Frag`, `Prog.Frag`): storage writes of a word, of a
copy of a storage value (`Src.copy`, `Src.fixedCopy`), deletes at an
`Ty.expandable` type, a push of a word or of the default, a pop of an array
of words or of mappings, alias bindings, locals, `if`, `require`, `assert`,
`revert`, `assume(false)` and blocks; every expression free of memory
(`Val.MemFree`).  Out: memory (each memory rule writes `memory`), payments
and calls (they write the ledger or inline a frame), loops (the invariant
rule's anonymisation), `try`, compound assignment and `++`/`--` (left out to
keep the proof short: their updates are saves too, `PushSuffix.saveOp`),
copies from memory, and a push of a copy (a `push` of a reference value,
which `Tm.expand?` keeps whole).  A copy at any type is in: it is a `save`
already, expanded when its type is `Ty.expandable`, kept whole otherwise.

**Save-like** (`Tm.SaveLike`): `save`, `pushSlot` or `shrink` on `storage`,
or what `Tm.expand?` turns into those: `delAt` at an expandable type, a
`push` of a word, a `pop` of an array of words.  An element is save-like
when it writes a local, or the storage by a save-like term
(`UpdElem.SaveLike`); a premise when its updates are, and every program it
runs next is in the fragment again (`Premise.SaveLike`), so the property
holds along the strategy's whole run on a fragment program.

**The bridge to `LTm`.**  `Tm.SaveNF` is `LTm.SaveNF`'s shape on the scoped
terms: `Tm.toL ρ` (`Calculus/DecideScoped.lean`) maps each `save`,
`pushSlot`, `shrink` to its symbol and `storage` to `ρ`'s storage, so a
`Tm.SaveNF` term read at a start `ρ` whose storage is `storage` is an
`LTm.SaveNF` term once its paths and values translate to `Elimable` ones.
That last condition is about reads (memory-free, no `wt`/`cleanTail`), not
about this file's shapes, and is not proved here.

**The proof** follows `Calculus/TermSize.lean`: one lemma per arm, by cases
on the arm's own shape, under the holes' lemmas (`SHole.readStep_saveLike`,
`VHole.step_saveLike`); a capture is in the fragment because its parts are
(`Val.memFree_up`, `Prog.frag_wk`).
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3 Modality)

variable {C : Contract}

/-! ## Save-like storage terms -/

section Terms

variable {Γ : Ctx}

/-- **A save-like storage term**: a save, a slot pushed, a slot dropped on
`storage`, or what `Tm.expand?` turns into those. -/
inductive Tm.SaveLike : Tm C Γ .st → Prop where
  | save {T : Ty} (p : Tm C Γ (.path T)) (v : Tm C Γ (.sv T)) :
      Tm.SaveLike (.app3 .save (.app0 .storage) p v)
  | pushSlot {E : Ty} (p : Tm C Γ (.path (.ref (.array E)))) :
      Tm.SaveLike (.app2 .pushSlot (.app0 .storage) p)
  | shrink {E : Ty} (p : Tm C Γ (.path (.ref (.array E)))) :
      Tm.SaveLike (.app2 .shrink (.app0 .storage) p)
  | delAt {T : Ty} (p : Tm C Γ (.path T)) (hT : T.expandable = true) (hp : p.pushFree = true) :
      Tm.SaveLike (.app2 .delAt (.app0 .storage) p)
  | push {P : PrimTy} (p : Tm C Γ (.path (.ref (.array (.prim P))))) (x : Tm C Γ (.val P))
      (hp : p.pushFree = true) (hx : x.pushFree = true) :
      Tm.SaveLike (.app3 .push (.app0 .storage) p (.app1 .sval x))
  | pop {P : PrimTy} (p : Tm C Γ (.path (.ref (.array (.prim P))))) (hp : p.pushFree = true) :
      Tm.SaveLike (.app2 .pop (.app0 .storage) p)

/-- **A storage in save normal form**, on the scoped terms: `storage` with
saves, pushed slots and dropped slots on it (`LTm.SaveNF`'s shape). -/
inductive Tm.SaveNF : Tm C Γ .st → Prop where
  | storage : Tm.SaveNF (.app0 .storage)
  | save {T : Ty} {s : Tm C Γ .st} (p : Tm C Γ (.path T)) (v : Tm C Γ (.sv T)) (hs : Tm.SaveNF s) :
      Tm.SaveNF (.app3 .save s p v)
  | pushSlot {E : Ty} {s : Tm C Γ .st} (p : Tm C Γ (.path (.ref (.array E)))) (hs : Tm.SaveNF s) :
      Tm.SaveNF (.app2 .pushSlot s p)
  | shrink {E : Ty} {s : Tm C Γ .st} (p : Tm C Γ (.path (.ref (.array E)))) (hs : Tm.SaveNF s) :
      Tm.SaveNF (.app2 .shrink s p)

/-- **An element is save-like**: it writes a local, or the storage by a
save-like term. -/
def UpdElem.SaveLike {Δ : Ctx} : UpdElem C Γ Δ → Prop
  | .local _ _ => True
  | .storage s => s.SaveLike
  | _ => False

/-- Every element of the update is save-like. -/
def Upd.SaveLike : {Δ : Ctx} → Upd C Γ Δ → Prop
  | _, .nil => True
  | _, .snoc U e => U.SaveLike ∧ e.SaveLike
  | _, .decl U _ _ => U.SaveLike
  | _, .pop U _ => U.SaveLike
  | _, .drop U _ => U.SaveLike

/-- The storage right-hand sides of an update, in order. -/
def Upd.stores : {Δ : Ctx} → Upd C Γ Δ → List (Tm C Γ .st)
  | _, .nil => []
  | _, .snoc U (.storage s) => U.stores ++ [s]
  | _, .snoc U _ => U.stores
  | _, .decl U _ _ => U.stores
  | _, .pop U _ => U.stores
  | _, .drop U _ => U.stores

theorem Upd.SaveLike.stores {Δ : Ctx} :
    {U : Upd C Γ Δ} → U.SaveLike → ∀ t ∈ U.stores, t.SaveLike
  | .nil, _, t, ht => absurd ht List.not_mem_nil
  | .snoc U e, h, t, ht => by
    cases e with
    | storage s =>
      simp only [Upd.stores, List.mem_append, List.mem_singleton] at ht
      rcases ht with ht | rfl
      · exact Upd.SaveLike.stores h.1 t ht
      · exact h.2
    | «local» i r => exact Upd.SaveLike.stores h.1 t ht
    | memory _ => exact h.2.elim
    | selfBalance _ _ => exact h.2.elim
    | net _ _ _ => exact h.2.elim
    | pay _ _ => exact h.2.elim
    | netMt _ _ => exact h.2.elim
    | setBalance _ => exact h.2.elim
  | .decl U _ _, h, t, ht => Upd.SaveLike.stores (U := U) h t ht
  | .pop U _, h, t, ht => Upd.SaveLike.stores (U := U) h t ht
  | .drop U _, h, t, ht => Upd.SaveLike.stores (U := U) h t ht

end Terms

/-! ## The expansion of a save-like term is in save normal form -/

section Expand

variable {Γ : Ctx}

theorem Tm.SaveNF.saveLeaves {T : Ty} (s : Tm C Γ .st) (p : Tm C Γ (.path T))
    (val : (l : Leaf T) → Tm C Γ (.sv (.prim l.1))) :
    (ls : List (Leaf T)) → {acc : Tm C Γ .st} → acc.SaveNF → (Tm.saveLeaves s p val ls acc).SaveNF
  | [], _, h => h
  | _ :: ls, _, h => Tm.SaveNF.saveLeaves s p val ls (.save _ _ h)

/-- **After `Tm.expand?`, a save-like term is in save normal form.** -/
theorem Tm.SaveLike.saveNF_expand {t : Tm C Γ .st} (h : t.SaveLike) :
    ((t.expand?).getD t).SaveNF := by
  cases h with
  | save p v =>
    have hd : (Tm.app3 .save (.app0 .storage) p v : Tm C Γ .st).delAtExpand? = none := by
      simp only [Tm.delAtExpand?]
    have hpu : (Tm.app3 .save (.app0 .storage) p v : Tm C Γ .st).pushExpand? = none := by
      cases hq : (Tm.app3 .save (.app0 .storage) p v : Tm C Γ .st).pushExpand? with
      | none => rfl
      | some u =>
        obtain ⟨P, s, p', x, heq, -⟩ := Tm.pushExpand?_some hq
        cases heq
    have hpo : (Tm.app3 .save (.app0 .storage) p v : Tm C Γ .st).popExpand? = none := by
      simp only [Tm.popExpand?]
    cases hc : (Tm.app3 .save (.app0 .storage) p v : Tm C Γ .st).copyExpand? with
    | some t' =>
      obtain ⟨T', s, p', q, heq, rfl, -⟩ := Tm.copyExpand?_some hc
      simp only [Tm.expand?, hd, hc]
      cases heq
      exact Tm.SaveNF.saveLeaves _ _ _ _ .storage
    | none =>
      simp only [Tm.expand?, hd, hc, hpu, hpo]
      exact .save p v .storage
  | pushSlot p =>
    have he : (Tm.app2 .pushSlot (.app0 .storage) p : Tm C Γ .st).expand? = none := by
      simp only [Tm.expand?, Tm.delAtExpand?, Tm.copyExpand?, Tm.asSave?, Tm.pushExpand?,
        Tm.asPush?, Tm.popExpand?]; rfl
    simp only [he, Option.getD_none]
    exact .pushSlot p .storage
  | shrink p =>
    have he : (Tm.app2 .shrink (.app0 .storage) p : Tm C Γ .st).expand? = none := by
      simp only [Tm.expand?, Tm.delAtExpand?, Tm.copyExpand?, Tm.asSave?, Tm.pushExpand?,
        Tm.asPush?, Tm.popExpand?]; rfl
    simp only [he, Option.getD_none]
    exact .shrink p .storage
  | delAt p hT hp =>
    have he : Tm.delAtExpand? (.app2 .delAt (.app0 .storage) p) = some (Tm.delAtLeaves (.app0 .storage) p) := by
      simp only [Tm.delAtExpand?, hT, hp, Tm.pushFree, Bool.and_self, ite_true]
    simp only [Tm.expand?, he]
    exact Tm.SaveNF.saveLeaves _ _ _ _ .storage
  | @push P p x hp hx =>
    have hd : (Tm.app3 .push (.app0 .storage) p (.app1 .sval x) : Tm C Γ .st).delAtExpand? = none := by
      simp only [Tm.delAtExpand?]
    have hc : (Tm.app3 .push (.app0 .storage) p (.app1 .sval x) : Tm C Γ .st).copyExpand? = none := by
      cases hq : (Tm.app3 .push (.app0 .storage) p (.app1 .sval x) : Tm C Γ .st).copyExpand? with
      | none => rfl
      | some u =>
        obtain ⟨T, s, p', q, heq, -⟩ := Tm.copyExpand?_some hq
        cases heq
    have ha : (Tm.app3 .push (.app0 .storage) p (.app1 .sval x) : Tm C Γ .st).asPush? =
        some ⟨.prim P, .app0 .storage, p, .app1 .sval x⟩ := rfl
    have hv : (Tm.app1 .sval x : Tm C Γ (.sv (.prim P))).asSval? = some ⟨P, x⟩ := rfl
    have hpu : (Tm.app3 .push (.app0 .storage) p (.app1 .sval x) : Tm C Γ .st).pushExpand? =
        some (Tm.pushWord (.app0 .storage) p x) := by
      simp only [Tm.pushExpand?, ha, hv, hp, hx, Tm.pushFree, Bool.and_self, dite_true, ite_true]
    simp only [Tm.expand?, hd, hc, hpu]
    exact .save _ _ (.pushSlot _ .storage)
  | @pop P p hp =>
    have hd : (Tm.app2 .pop (.app0 .storage) p : Tm C Γ .st).delAtExpand? = none := by
      simp only [Tm.delAtExpand?]
    have hc : (Tm.app2 .pop (.app0 .storage) p : Tm C Γ .st).copyExpand? = none := by
      simp only [Tm.copyExpand?, Tm.asSave?]
    have hpu : (Tm.app2 .pop (.app0 .storage) p : Tm C Γ .st).pushExpand? = none := by
      simp only [Tm.pushExpand?, Tm.asPush?]
    have hpo : (Tm.app2 .pop (.app0 .storage) p : Tm C Γ .st).popExpand? =
        some (Tm.popWord (.app0 .storage) p) := by
      simp only [Tm.popExpand?, hp, Tm.pushFree, Bool.and_self, ite_true]
    simp only [Tm.expand?, hd, hc, hpu, hpo]
    exact .shrink _ (.save _ _ .storage)

end Expand

/-! ## The fragment -/

section Fragment

variable {Γ : Ctx}

mutual

/-- A storage path that reads no memory. -/
def SPath.MemFree : {T : Ty} → SPath C Γ T → Bool
  | _, .alias _ => true
  | _, .loc l => l.MemFree

/-- A storage location that reads no memory. -/
def Loc.MemFree : {T : Ty} → Loc C Γ T → Bool
  | _, .root _ _ => true
  | _, .field b _ _ => b.MemFree
  | _, .index _ b i => b.MemFree && i.MemFree

/-- **A value that reads no memory**: no `readMem`, no memory length. -/
def Val.MemFree : {p : PrimTy} → Val C Γ p → Bool
  | _, .simple _ => true
  | _, .read l => l.MemFree
  | _, .binop _ _ _ a b => a.MemFree && b.MemFree
  | _, .unop _ _ _ a => a.MemFree
  | _, .ternary c a b => c.MemFree && a.MemFree && b.MemFree
  | _, .readMem _ => false
  | _, .len b _ => b.MemFree
  | _, .mlen _ _ => false
  | _, .modular _ a b k => a.MemFree && b.MemFree && k.MemFree

end

/-- A storage write's source in the fragment: a value, a storage copy. -/
def Src.Frag {T : Ty} : Src C Γ T → Bool
  | .val v => v.MemFree
  | .copy p _ => p.MemFree
  | .fixedCopy p _ _ => p.MemFree
  | .copyMem _ => false

/-- An alias's right-hand side, reading no memory. -/
def ARhs.MemFree {R : RefTy} : ARhs C Γ R → Bool
  | .path p => p.MemFree
  | .push b _ => b.MemFree

/-- A push's argument in the fragment: none, or a word. -/
def pushArgFrag {E : Ty} : Option (Src C Γ E) → Bool
  | none => true
  | some (.val v) => v.MemFree
  | some _ => false

end Fragment

mutual

/-- **A statement of the fragment** (the module docstring). -/
def Stmt.Frag : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Bool
  | _, _, .assign l r => l.MemFree && r.Frag
  | _, _, .rebind _ r => r.MemFree
  | _, _, .assignLocal _ v => v.MemFree
  | _, _, .declLocal _ _ init => init.all (·.MemFree)
  | _, _, .declStorage _ _ init => init.all (·.MemFree)
  | _, _, .push b v _ => b.MemFree && pushArgFrag v
  | _, _, .pop b => b.MemFree && (b.elemMapping || b.elemPrim)
  | _, _, @Stmt.delete _ _ T l => T.expandable && l.MemFree
  | _, _, .ite c thn els => c.MemFree && thn.Frag && els.Frag
  | _, _, .require c => c.MemFree
  | _, _, .assert c => c.MemFree
  | _, _, .revert => true
  | _, _, .assumeFalse => true
  | _, _, .block body => body.Frag
  | _, _, .opAssign .. => false
  | _, _, .incDec .. => false
  | _, _, .assignIncDec .. => false
  | _, _, .assignLocalPush .. => false
  | _, _, .transfer .. => false
  | _, _, .send .. => false
  | _, _, .declMem .. => false
  | _, _, .rebindMem .. => false
  | _, _, .assignFromMem .. => false
  | _, _, .assignMem .. => false
  | _, _, .deleteMem .. => false
  | _, _, .assignNew .. => false
  | _, _, .call .. => false
  | _, _, .tryCall .. => false
  | _, _, .loop .. => false
  | _, _, .pushOpAssign .. => false
  | _, _, .pushIncDec .. => false
  | _, _, .callReceiver .. => false
  | _, _, .callReceiverPush .. => false

/-- A program of the fragment: every statement is. -/
def Prog.Frag : {Γ Γ' : Ctx} → Prog C Γ Γ' → Bool
  | _, _, .nil => true
  | _, _, .cons s P => s.Frag && P.Frag

end

/-! ## Weakened, a part keeps its fragment -/

section Weaken

mutual

theorem SPath.memFree_wk {Γ Δ : Ctx} (h : Thin Γ Δ) :
    {T : Ty} → (b : SPath C Γ T) → (b.wk h).MemFree = b.MemFree
  | _, .alias _ => rfl
  | _, .loc l => Loc.memFree_wk h l

theorem Loc.memFree_wk {Γ Δ : Ctx} (h : Thin Γ Δ) :
    {T : Ty} → (l : Loc C Γ T) → (l.wk h).MemFree = l.MemFree
  | _, .root _ _ => rfl
  | _, .field b _ _ => SPath.memFree_wk h b
  | _, .index _ b i => by
    simp only [Loc.wk, Loc.MemFree, SPath.memFree_wk h b, Val.memFree_wk h i]

theorem Val.memFree_wk {Γ Δ : Ctx} (h : Thin Γ Δ) :
    {p : PrimTy} → (v : Val C Γ p) → (v.wk h).MemFree = v.MemFree
  | _, .simple _ => rfl
  | _, .read l => Loc.memFree_wk h l
  | _, .binop _ _ _ a b => by
    simp only [Val.wk, Val.MemFree, Val.memFree_wk h a, Val.memFree_wk h b]
  | _, .unop _ _ _ a => Val.memFree_wk h a
  | _, .ternary c a b => by
    simp only [Val.wk, Val.MemFree, Val.memFree_wk h c, Val.memFree_wk h a, Val.memFree_wk h b]
  | _, .readMem _ => rfl
  | _, .len b _ => SPath.memFree_wk h b
  | _, .mlen _ _ => rfl
  | _, .modular _ a b k => by
    simp only [Val.wk, Val.MemFree, Val.memFree_wk h a, Val.memFree_wk h b, Val.memFree_wk h k]

end

theorem Src.frag_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {T : Ty} (r : Src C Γ T) :
    (r.wk h).Frag = r.Frag := by
  cases r with
  | val v => exact Val.memFree_wk h v
  | copy p _ => exact SPath.memFree_wk h p
  | fixedCopy p _ _ => exact SPath.memFree_wk h p
  | copyMem _ => rfl

theorem ARhs.memFree_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {R : RefTy} (r : ARhs C Γ R) :
    (r.wk h).MemFree = r.MemFree := by
  cases r with
  | path p => exact SPath.memFree_wk h p
  | push b _ => exact SPath.memFree_wk h b

theorem pushArgFrag_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {E : Ty} (v : Option (Src C Γ E)) :
    pushArgFrag (v.map (·.wk h)) = pushArgFrag v := by
  rcases v with _ | (v | _ | _ | _)
  · rfl
  · exact Val.memFree_wk h v
  all_goals rfl

theorem SPath.memFree_up {Γ : Ctx} {t : LTy} {T : Ty} (b : SPath C Γ T) :
    (b.up (t := t)).MemFree = b.MemFree := by
  rw [SPath.up_eq]; exact SPath.memFree_wk _ b

theorem Loc.memFree_up {Γ : Ctx} {t : LTy} {T : Ty} (l : Loc C Γ T) :
    (l.up (t := t)).MemFree = l.MemFree := by
  rw [Loc.up_eq]; exact Loc.memFree_wk _ l

theorem Val.memFree_up {Γ : Ctx} {t : LTy} {p : PrimTy} (v : Val C Γ p) :
    (v.up (t := t)).MemFree = v.MemFree := by
  rw [Val.up_eq]; exact Val.memFree_wk _ v

theorem ARhs.memFree_up {Γ : Ctx} {t : LTy} {R : RefTy} (r : ARhs C Γ R) :
    (r.up (t := t)).MemFree = r.MemFree := by
  rw [ARhs.up_eq]; exact ARhs.memFree_wk _ r

mutual

theorem Stmt.frag_wk : {Γ Δ : Ctx} → (h : Thin Γ Δ) → {Γ' : Ctx} → (s : Stmt C Γ Γ') →
    s.Frag = true → (s.wk h).2.2.Frag = true
  | _, _, h, _, .assign l r, hs => by
    simp only [Stmt.Frag, Bool.and_eq_true] at hs
    simp only [Stmt.wk, Stmt.Frag, Loc.memFree_wk, Src.frag_wk, hs, Bool.and_self]
  | _, _, h, _, .rebind _ r, hs => by
    simp only [Stmt.Frag] at hs
    simp only [Stmt.wk, Stmt.Frag, ARhs.memFree_wk, hs]
  | _, _, h, _, .assignLocal _ v, hs => by
    simp only [Stmt.Frag] at hs
    simp only [Stmt.wk, Stmt.Frag, Val.memFree_wk, hs]
  | _, _, h, _, .declLocal _ _ none, hs => rfl
  | _, _, h, _, .declLocal _ _ (some e), hs => by
    simp only [Stmt.Frag, Option.all_some] at hs
    simp only [Stmt.wk, Option.map_some, Stmt.Frag, Option.all_some, Val.memFree_wk, hs]
  | _, _, h, _, .declStorage _ _ none, hs => rfl
  | _, _, h, _, .declStorage _ _ (some r), hs => by
    simp only [Stmt.Frag, Option.all_some] at hs
    simp only [Stmt.wk, Option.map_some, Stmt.Frag, Option.all_some, ARhs.memFree_wk, hs]
  | _, _, h, _, .push b v _, hs => by
    simp only [Stmt.Frag, Bool.and_eq_true] at hs
    simp only [Stmt.wk, Stmt.Frag, SPath.memFree_wk, pushArgFrag_wk, hs, Bool.and_self]
  | _, _, h, _, .pop b, hs => by
    simp only [Stmt.Frag] at hs
    simp only [Stmt.wk, Stmt.Frag, SPath.memFree_wk]
    exact hs
  | _, _, h, _, .delete l, hs => by
    simp only [Stmt.Frag] at hs
    simp only [Stmt.wk, Stmt.Frag, Loc.memFree_wk]
    exact hs
  | _, _, h, _, .ite c thn els, hs => by
    simp only [Stmt.Frag, Bool.and_eq_true] at hs
    simp only [Stmt.wk, Stmt.Frag, Val.memFree_wk, hs, Prog.frag_wk h thn hs.1.2,
      Prog.frag_wk h els hs.2, Bool.and_self]
  | _, _, h, _, .require c, hs => by
    simp only [Stmt.Frag] at hs
    simp only [Stmt.wk, Stmt.Frag, Val.memFree_wk, hs]
  | _, _, h, _, .assert c, hs => by
    simp only [Stmt.Frag] at hs
    simp only [Stmt.wk, Stmt.Frag, Val.memFree_wk, hs]
  | _, _, h, _, .revert, hs => rfl
  | _, _, h, _, .assumeFalse, hs => rfl
  | _, _, h, _, .block body, hs => by
    simp only [Stmt.Frag] at hs
    simp only [Stmt.wk, Stmt.Frag, Prog.frag_wk h body hs]
  | _, _, _, _, .opAssign .., hs => by simp only [Stmt.Frag, Bool.false_eq_true] at hs
  | _, _, _, _, .incDec .., hs => by simp only [Stmt.Frag, Bool.false_eq_true] at hs
  | _, _, _, _, .assignIncDec .., hs => by simp only [Stmt.Frag, Bool.false_eq_true] at hs
  | _, _, _, _, .assignLocalPush .., hs => by simp only [Stmt.Frag, Bool.false_eq_true] at hs
  | _, _, _, _, .transfer .., hs => by simp only [Stmt.Frag, Bool.false_eq_true] at hs
  | _, _, _, _, .send .., hs => by simp only [Stmt.Frag, Bool.false_eq_true] at hs
  | _, _, _, _, .declMem .., hs => by simp only [Stmt.Frag, Bool.false_eq_true] at hs
  | _, _, _, _, .rebindMem .., hs => by simp only [Stmt.Frag, Bool.false_eq_true] at hs
  | _, _, _, _, .assignFromMem .., hs => by simp only [Stmt.Frag, Bool.false_eq_true] at hs
  | _, _, _, _, .assignMem .., hs => by simp only [Stmt.Frag, Bool.false_eq_true] at hs
  | _, _, _, _, .deleteMem .., hs => by simp only [Stmt.Frag, Bool.false_eq_true] at hs
  | _, _, _, _, .assignNew .., hs => by simp only [Stmt.Frag, Bool.false_eq_true] at hs
  | _, _, _, _, .call .., hs => by simp only [Stmt.Frag, Bool.false_eq_true] at hs
  | _, _, _, _, .tryCall .., hs => by simp only [Stmt.Frag, Bool.false_eq_true] at hs
  | _, _, _, _, .loop .., hs => by simp only [Stmt.Frag, Bool.false_eq_true] at hs
  | _, _, _, _, .pushOpAssign .., hs => by simp only [Stmt.Frag, Bool.false_eq_true] at hs
  | _, _, _, _, .pushIncDec .., hs => by simp only [Stmt.Frag, Bool.false_eq_true] at hs
  | _, _, _, _, .callReceiver .., hs => by simp only [Stmt.Frag, Bool.false_eq_true] at hs
  | _, _, _, _, .callReceiverPush .., hs => by simp only [Stmt.Frag, Bool.false_eq_true] at hs

theorem Prog.frag_wk : {Γ Δ : Ctx} → (h : Thin Γ Δ) → {Γ' : Ctx} → (P : Prog C Γ Γ') →
    P.Frag = true → (P.wk h).2.2.Frag = true
  | _, _, _, _, .nil, _ => rfl
  | _, _, h, _, .cons s P, hs => by
    simp only [Prog.Frag, Bool.and_eq_true] at hs
    show (Stmt.Frag (s.wk h).2.2 && Prog.Frag (P.wk (s.wk h).2.1).2.2) = true
    rw [Stmt.frag_wk h s hs.1, Prog.frag_wk _ P hs.2, Bool.and_self]

end

theorem Prog.frag_up {Γ Γ' : Ctx} {t : LTy} (P : Prog C Γ Γ') (h : P.Frag = true) :
    (P.wk (Solidity.up (t := t))).2.2.Frag = true :=
  Prog.frag_wk _ P h

end Weaken

/-! ## Save-like premises -/

section Premises

variable {Γ : Ctx}

/-- **A save-like premise**: every update it writes is save-like, and every
program it runs next is in the fragment.  Branches of a `try` and a loop's
invariant rule are not. -/
def Premise.SaveLike {Γ' : Ctx} : Premise C Γ Γ' → Prop
  | .update U => U.SaveLike
  | .updates U V => U.SaveLike ∧ V.SaveLike
  | .unfold P _ => P.Frag = true
  | .bind _ _ P => P.Frag = true
  | .split _ _ _ P Q => P.Frag = true ∧ Q.Frag = true
  | .check _ => True
  | .done _ => True
  | .branches _ => False
  | .cases _ us => ∀ U ∈ us, U.SaveLike
  | .inv .. => False
  | .inline P _ => P.Frag = true
  | .guardedUpdates _ U V => U.SaveLike ∧ V.SaveLike

theorem Premise.SaveLike.upds {Γ' : Ctx} {P : Premise C Γ Γ'} (h : P.SaveLike) :
    ∀ U ∈ P.upds, U.2.2.SaveLike := by
  intro W hW
  cases P with
  | update U =>
    simp only [Premise.upds, List.mem_singleton] at hW; subst hW; exact h
  | updates U V =>
    simp only [Premise.upds, List.mem_cons, List.not_mem_nil, or_false] at hW
    rcases hW with rfl | rfl
    · exact h.1
    · exact h.2
  | guardedUpdates c U V =>
    simp only [Premise.upds, List.mem_cons, List.not_mem_nil, or_false] at hW
    rcases hW with rfl | rfl
    · exact h.1
    · exact h.2
  | cases fs us =>
    simp only [Premise.upds, List.mem_map] at hW
    obtain ⟨U, hU, rfl⟩ := hW
    exact h U hU
  | inv => exact h.elim
  | _ => simp only [Premise.upds, List.not_mem_nil] at hW

end Premises

/-! ## The builders and the holes -/

section Builders

variable {Γ : Ctx}

theorem Premise.saveLike_setLocal {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p) :
    (Premise.setLocal i v).SaveLike := ⟨trivial, trivial⟩

theorem Premise.saveLike_local {t : LTy} (i : Idx Γ t) (r : Rhs C Γ t) :
    (Premise.upd1 (.local i r)).SaveLike := ⟨trivial, trivial⟩

theorem Premise.saveLike_save {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) :
    (Premise.save l r).SaveLike := ⟨trivial, .save _ _⟩

theorem Premise.saveLike_delAt {T : Ty} (l : Loc C Γ T) (hT : T.expandable = true) :
    (Premise.delAt l).SaveLike := ⟨trivial, .delAt _ hT (Loc.lower_pushFree l)⟩

theorem Premise.saveLike_capture {p : PrimTy} (x : Var) {e : Val C Γ p}
    {s : Stmt C (.val p :: Γ) (.val p :: Γ)} (he : e.MemFree = true) (hs : s.Frag = true) :
    (Premise.capture p x e s).SaveLike := by
  simp only [Premise.capture, Premise.SaveLike, Prog.Frag, Stmt.Frag, Option.all_some, he, hs,
    Bool.and_self]

theorem Premise.saveLike_captureSP {R : RefTy} (x : Var) {b : SPath C Γ (.ref R)}
    {s : Stmt C (.alias R :: Γ) (.alias R :: Γ)} (hb : b.MemFree = true) (hs : s.Frag = true) :
    (Premise.captureSP x b s).SaveLike := by
  simp only [Premise.captureSP, Premise.SaveLike, Prog.Frag, Stmt.Frag, Option.all_some,
    ARhs.MemFree, hb, hs, Bool.and_self]

/-- A hole that reads no memory. -/
def SHole.MemFree {T : Ty} : SHole C Γ T → Bool
  | .local _ => true
  | .rebind _ => true
  | .copy l _ => l.MemFree

/-- A value's hole that reads no memory: a local, a storage location. -/
def VHole.MemFree {p : PrimTy} : VHole C Γ p → Bool
  | .local _ => true
  | .store l => l.MemFree
  | .mem _ => false

theorem SHole.memFree_up {t : LTy} {T : Ty} (lhs : SHole C Γ T) (h : lhs.MemFree = true) :
    (lhs.up (t := t)).MemFree = true := by
  cases lhs with
  | «local» i => rfl
  | rebind i => rfl
  | copy l hm => simp only [SHole.up, SHole.MemFree, Loc.memFree_up] at h ⊢; exact h

theorem VHole.memFree_up {t : LTy} {p : PrimTy} (lhs : VHole C Γ p) (h : lhs.MemFree = true) :
    (lhs.up (t := t)).MemFree = true := by
  cases lhs with
  | «local» i => rfl
  | store l => simp only [VHole.up, VHole.MemFree, Loc.memFree_up] at h ⊢; exact h
  | mem l => exact absurd h Bool.false_ne_true

theorem SHole.fill_frag {T : Ty} (lhs : SHole C Γ T) (hl : lhs.MemFree = true)
    (q : SPath C Γ T) (hq : q.MemFree = true) : (lhs.fill q).Frag = true := by
  cases lhs with
  | «local» i =>
    cases q with
    | loc l => simp only [SHole.fill, Stmt.Frag, Val.MemFree]; exact hq
  | rebind i => simp only [SHole.fill, Stmt.Frag, ARhs.MemFree]; exact hq
  | copy l hm =>
    simp only [SHole.MemFree] at hl
    simp only [SHole.fill, Stmt.Frag, Src.Frag, hl, hq, Bool.and_self]

theorem VHole.fill_frag {p : PrimTy} (lhs : VHole C Γ p) (hl : lhs.MemFree = true)
    (v : Val C Γ p) (hv : v.MemFree = true) : (lhs.fill v).Frag = true := by
  cases lhs with
  | «local» i => simp only [VHole.fill, Stmt.Frag]; exact hv
  | store l =>
    simp only [VHole.MemFree] at hl
    simp only [VHole.fill, Stmt.Frag, Src.Frag, hl, hv, Bool.and_self]
  | mem l => exact absurd hl Bool.false_ne_true

end Builders

section Holes

variable (k : Nat) {Γ : Ctx}

theorem SHole.readStep_saveLike {T : Ty} (lhs : SHole C Γ T) (hl : lhs.MemFree = true)
    {root : (r : Name) → C.rootType r = some T → Premise C Γ Γ}
    {field : {s : Name} → SPath C Γ (.struct s) → (f : Name) → C.fieldType s f = some T →
      Premise C Γ Γ}
    {index : {R : RefTy} → {kp : PrimTy} → IndexTy R kp T → SPath C Γ (.ref R) →
      Simple C Γ kp → Premise C Γ Γ}
    (hr : ∀ r h, (root r h).SaveLike)
    (hf : ∀ (s : Name) (b : SPath C Γ (.struct s)) f h, b.MemFree = true → (field b f h).SaveLike)
    (hi : ∀ (R : RefTy) (kp : PrimTy) (it : IndexTy R kp T) (b : SPath C Γ (.ref R)) ie,
      b.MemFree = true → (index it b ie).SaveLike)
    (l : Loc C Γ T) (hm : l.MemFree = true) : (lhs.readStep k root field index l).SaveLike := by
  cases l with
  | root r h => exact hr r h
  | field b f h =>
    simp only [Loc.MemFree] at hm
    simp only [SHole.readStep]
    split
    · exact hf _ b f h hm
    · exact Premise.saveLike_captureSP _ hm
        (SHole.fill_frag _ (SHole.memFree_up lhs hl) _ rfl)
  | index it b i =>
    simp only [Loc.MemFree, Bool.and_eq_true] at hm
    simp only [SHole.readStep]
    split
    · cases i with
      | simple ie => exact hi _ _ it b ie hm.1
      | _ =>
        exact Premise.saveLike_capture _ hm.2 (SHole.fill_frag _ (SHole.memFree_up lhs hl) _
          (by simp only [SPath.MemFree, Loc.MemFree, SPath.memFree_up, hm.1, Val.MemFree,
            Bool.and_self]))
    · exact Premise.saveLike_captureSP _ hm.1 (SHole.fill_frag _ (SHole.memFree_up lhs hl) _
        (by simp only [SPath.MemFree, Loc.MemFree, Val.memFree_up, hm.2, Bool.and_self]))

theorem ternaryStep_saveLike {p : PrimTy} (lhs : VHole C Γ p) (hl : lhs.MemFree = true)
    (c : Val C Γ .bool) (a b : Val C Γ p) (hc : c.MemFree = true) (ha : a.MemFree = true)
    (hb : b.MemFree = true) : (ternaryStep k lhs c a b).SaveLike := by
  cases c with
  | simple se =>
    simp only [ternaryStep, Premise.SaveLike, Prog.Frag, Stmt.Frag, Val.MemFree,
      VHole.fill_frag lhs hl a ha, VHole.fill_frag lhs hl b hb, Bool.and_self]
  | _ =>
    exact Premise.saveLike_capture _ hc (VHole.fill_frag _ (VHole.memFree_up lhs hl) _
      (by simp only [Val.MemFree, Val.memFree_up, ha, hb, Bool.and_self]))

theorem VHole.step_saveLike {p : PrimTy} (lhs : VHole C Γ p) (hl : lhs.MemFree = true)
    {simple : Simple C Γ p → Premise C Γ Γ} (hs : ∀ se, (simple se).SaveLike)
    (e : Val C Γ p) (he : e.MemFree = true) : (lhs.step k simple e).SaveLike := by
  have hcap : (Premise.capture p (fse k) e (lhs.up.fill (.simple (.local .here)))).SaveLike :=
    Premise.saveLike_capture _ he (VHole.fill_frag _ (VHole.memFree_up lhs hl) _ rfl)
  cases e with
  | simple se => exact hs se
  | ternary c a b =>
    simp only [Val.MemFree, Bool.and_eq_true] at he
    exact ternaryStep_saveLike k lhs hl c a b he.1.1 he.1.2 he.2
  | read l => exact hcap
  | binop => exact hcap
  | unop => exact hcap
  | readMem l => exact absurd he Bool.false_ne_true
  | len b hp => exact hcap
  | mlen b hp => exact absurd he Bool.false_ne_true
  | modular => exact hcap

theorem VHole.lower_saveLike {p : PrimTy} (lhs : VHole C Γ p) (hl : lhs.MemFree = true)
    {other : Premise C Γ Γ} (ho : other.SaveLike) (e : Val C Γ p) (he : e.MemFree = true) :
    (lhs.lower k other e).SaveLike := by
  cases e with
  | ternary c a b =>
    simp only [Val.MemFree, Bool.and_eq_true] at he
    exact ternaryStep_saveLike k lhs hl c a b he.1.1 he.1.2 he.2
  | _ => exact ho

end Holes

/-! ## The arms -/

section Arms

variable (k : Nat) {Γ : Ctx}

theorem copyStep_saveLike {R : RefTy} (l : Loc C Γ (.ref R)) (hm : (Ty.ref R).mapFree = true)
    (hl : l.MemFree = true) (q : SPath C Γ (.ref R)) (hq : q.MemFree = true) :
    (copyStep k l hm q).SaveLike := by
  cases q with
  | alias y => exact Premise.saveLike_save _ _
  | loc l' =>
    apply SHole.readStep_saveLike k (SHole.copy l hm) hl
    · intro r h; exact Premise.saveLike_save _ _
    · intro s b f h hb
      exact Premise.saveLike_captureSP _ (by simp only [SPath.MemFree, Loc.MemFree]; exact hb)
        (by simp only [Stmt.Frag, Loc.memFree_up, Src.Frag, SPath.MemFree, hl, Bool.and_self])
    · intro R kp it b ie hb
      exact Premise.saveLike_captureSP _
        (by simp only [SPath.MemFree, Loc.MemFree, Val.MemFree, hb, Bool.and_self])
        (by simp only [Stmt.Frag, Loc.memFree_up, Src.Frag, SPath.MemFree, hl, Bool.and_self])
    · exact hq

theorem assignStep_saveLike {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) (hl : l.MemFree = true)
    (hr : r.Frag = true) : (assignStep k l r).SaveLike := by
  cases r with
  | copyMem q => exact absurd hr Bool.false_ne_true
  | fixedCopy q shape hm => cases l <;> exact Premise.saveLike_save _ _
  | val e =>
    simp only [Src.Frag] at hr
    cases l with
    | root r h =>
      exact VHole.step_saveLike k _ rfl (fun _ => Premise.saveLike_save _ _) e hr
    | field b f h =>
      simp only [Loc.MemFree] at hl
      simp only [assignStep]
      split
      · exact VHole.step_saveLike k (.store (.field b f h)) hl (fun _ => Premise.saveLike_save _ _) e hr
      · apply VHole.lower_saveLike k (.store (.field b f h)) hl _ e hr
        simp only [Premise.SaveLike, Prog.Frag, Stmt.Frag, Option.all_some, ARhs.MemFree,
          SPath.memFree_up, Loc.MemFree, SPath.MemFree, Src.Frag, Val.MemFree, hr, hl,
          Bool.and_self]
    | index it b i =>
      simp only [Loc.MemFree, Bool.and_eq_true] at hl
      have hall : (indexCaptureAll k it b i e).SaveLike := by
        simp only [indexCaptureAll, Premise.SaveLike, Prog.Frag, Stmt.Frag, Option.all_some,
          ARhs.MemFree, SPath.memFree_up, Val.memFree_up, Loc.MemFree, SPath.MemFree, Src.Frag,
          Val.MemFree, hr, hl.1, hl.2, Bool.and_self]
      simp only [assignStep]
      split
      · cases i with
        | simple ie =>
          exact VHole.step_saveLike k _ (by simp only [VHole.MemFree, Loc.MemFree, hl.1,
            Val.MemFree, Bool.and_self]) (fun _ => Premise.saveLike_save _ _) e hr
        | _ =>
          exact VHole.lower_saveLike k _ (by simp only [VHole.MemFree, Loc.MemFree, hl.1,
            hl.2, Bool.and_self]) hall e hr
      · exact VHole.lower_saveLike k _ (by simp only [VHole.MemFree, Loc.MemFree, hl.1,
            hl.2, Bool.and_self]) hall e hr
  | copy q hm =>
    simp only [Src.Frag] at hr
    cases l with
    | root r h =>
      cases q with
      | alias j => exact Premise.saveLike_save _ _
      | loc l' =>
        apply SHole.readStep_saveLike k (SHole.copy (.root r h) hm) rfl
        · intro _ _; exact Premise.saveLike_save _ _
        · intro _ _ _ _ _; exact Premise.saveLike_save _ _
        · intro _ _ _ _ _ _; exact Premise.saveLike_save _ _
        · exact hr
    | field b f h =>
      simp only [Loc.MemFree] at hl
      simp only [assignStep]
      split
      · exact copyStep_saveLike k (.field b f h) hm hl q hr
      · exact Premise.saveLike_captureSP _ hl
          (by simp only [Stmt.Frag, Loc.MemFree, SPath.MemFree, Src.Frag, SPath.memFree_up, hr,
            Bool.and_self])
    | index it b i =>
      simp only [Loc.MemFree, Bool.and_eq_true] at hl
      have hall : (indexRefCaptureAll k it b i q hm).SaveLike := by
        simp only [indexRefCaptureAll, Premise.SaveLike, Prog.Frag, Stmt.Frag, Option.all_some,
          ARhs.MemFree, SPath.memFree_up, Val.memFree_up, Loc.MemFree, SPath.MemFree, Src.Frag,
          Val.MemFree, hr, hl.1, hl.2, Bool.and_self]
      simp only [assignStep]
      split
      · cases i with
        | simple ie =>
          exact copyStep_saveLike k _ hm (by simp only [Loc.MemFree, hl.1, Val.MemFree,
            Bool.and_self]) q hr
        | _ => exact hall
      · exact hall

theorem shortStep_saveLike {p p' : PrimTy} (i : Idx Γ (.val p)) (op : BinOp)
    (ha : op.accepts p' = true) (hq : op.ret p' = p) (a : Simple C Γ p') (b : Val C Γ p')
    (hb : b.MemFree = true) : (shortStep i op ha hq a b).SaveLike := by
  unfold shortStep
  split
  · simp only [Premise.SaveLike, Prog.Frag, Stmt.Frag, Val.MemFree, hb, Bool.and_self]
  · simp only [Premise.SaveLike, Prog.Frag, Stmt.Frag, Val.MemFree, hb, Bool.and_self]
  · trivial

theorem localStep_saveLike {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p)
    (hv : v.MemFree = true) : (localStep k i v).SaveLike := by
  cases v with
  | simple s => exact Premise.saveLike_setLocal i _
  | read l =>
    apply SHole.readStep_saveLike k (SHole.local i) rfl
    · intro r h; exact Premise.saveLike_setLocal i _
    · intro s b f h _; exact Premise.saveLike_setLocal i _
    · intro R kp it b ie _; exact Premise.saveLike_setLocal i _
    · exact hv
  | binop op ha hq a b =>
    simp only [Val.MemFree, Bool.and_eq_true] at hv
    cases a with
    | simple a =>
      cases b with
      | simple b => exact Premise.saveLike_setLocal i _
      | _ =>
        simp only [localStep]
        split
        · exact shortStep_saveLike i op ha hq a _ hv.2
        · exact Premise.saveLike_capture _ hv.2
            (by simp only [Stmt.Frag, Val.MemFree, Bool.and_self])
    | _ =>
      exact Premise.saveLike_capture _ hv.1
        (by simp only [Stmt.Frag, Val.MemFree, Val.memFree_up, hv.2, Bool.and_self])
  | unop op ha hq a =>
    cases a with
    | simple a => exact Premise.saveLike_setLocal i _
    | _ =>
      exact Premise.saveLike_capture _ hv (by simp only [Stmt.Frag, Val.MemFree])
  | ternary c a b =>
    simp only [Val.MemFree, Bool.and_eq_true] at hv
    exact ternaryStep_saveLike k (.local i) rfl c a b hv.1.1 hv.1.2 hv.2
  | readMem l => exact absurd hv Bool.false_ne_true
  | len b hp =>
    simp only [Val.MemFree] at hv
    simp only [localStep]
    split
    · exact Premise.saveLike_setLocal i _
    · exact Premise.saveLike_captureSP _ hv (by simp only [Stmt.Frag, Val.MemFree, SPath.MemFree])
  | mlen b hp => exact absurd hv Bool.false_ne_true
  | modular op a b n => exact Premise.saveLike_setLocal i _

theorem rebindStep_saveLike {R : RefTy} (i : Idx Γ (.alias R)) (r : ARhs C Γ R)
    (hr : r.MemFree = true) : (rebindStep k i r).SaveLike := by
  cases r with
  | path q =>
    simp only [ARhs.MemFree] at hr
    cases q with
    | alias j => exact Premise.saveLike_local i _
    | loc l =>
      apply SHole.readStep_saveLike k (SHole.rebind i) rfl
      · intro r h; exact Premise.saveLike_local i _
      · intro s b f h _; exact Premise.saveLike_local i _
      · intro R kp it b ie _; exact Premise.saveLike_local i _
      · exact hr
  | push b hd =>
    simp only [ARhs.MemFree] at hr
    simp only [rebindStep]
    split
    · split
      · exact ⟨⟨trivial, .pushSlot _⟩, trivial⟩
      · exact ⟨⟨trivial, .pushSlot _⟩, trivial⟩
    · exact Premise.saveLike_captureSP _ hr (by simp only [Stmt.Frag, ARhs.MemFree, SPath.MemFree])

theorem deleteStep_saveLike {T : Ty} (l : Loc C Γ T) (hT : T.expandable = true)
    (hl : l.MemFree = true) : (deleteStep k l).SaveLike := by
  cases l with
  | root r h => exact Premise.saveLike_delAt _ hT
  | field b f h =>
    simp only [Loc.MemFree] at hl
    simp only [deleteStep]
    split
    · exact Premise.saveLike_delAt _ hT
    · exact Premise.saveLike_captureSP _ hl
        (by simp only [Stmt.Frag, hT, Loc.MemFree, SPath.MemFree, Bool.and_self])
  | index it b i =>
    simp only [Loc.MemFree, Bool.and_eq_true] at hl
    simp only [deleteStep]
    split
    · cases i with
      | simple ie => exact Premise.saveLike_delAt _ hT
      | _ =>
        exact Premise.saveLike_capture _ hl.2
          (by simp only [Stmt.Frag, hT, Loc.MemFree, SPath.memFree_up, hl.1, Val.MemFree,
            Bool.and_self])
    · exact Premise.saveLike_captureSP _ hl.1
        (by simp only [Stmt.Frag, hT, Loc.MemFree, SPath.MemFree, Val.memFree_up, hl.2,
          Bool.and_self])

theorem pushArgFrag_up {t : LTy} {E : Ty} (v : Option (Src C Γ E)) :
    pushArgFrag (v.map (Src.up (t := t))) = pushArgFrag v := by
  rcases v with _ | (v | _ | _ | _)
  · rfl
  · exact Val.memFree_up v
  all_goals rfl

theorem pushStep_saveLike {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E))
    (hd : (v.isSome || E.defaultOkS) = true) (hb : b.MemFree = true)
    (hv : pushArgFrag v = true) : (pushStep k b v hd).SaveLike := by
  unfold pushStep
  split
  · rcases v with _ | (e | _ | _ | _)
    · simp only
      split
      · exact ⟨trivial, .pushSlot _⟩
      · split <;> exact ⟨trivial, .pushSlot _⟩
    · simp only [pushArgFrag] at hv
      cases e with
      | simple se =>
        exact ⟨trivial, .push _ _ (SPath.lower_pushFree b) (Val.lower_pushFree _)⟩
      | _ =>
        exact Premise.saveLike_capture _ hv
          (by simp only [Stmt.Frag, SPath.memFree_up, hb, pushArgFrag, Val.MemFree,
            Bool.and_self])
    all_goals exact absurd hv Bool.false_ne_true
  · exact Premise.saveLike_captureSP _ hb
      (by simp only [Stmt.Frag, SPath.MemFree, pushArgFrag_up, hv, Bool.and_self])

theorem popStep_saveLike {E : Ty} (b : SPath C Γ (.array E)) (hb : b.MemFree = true)
    (he : (b.elemMapping || b.elemPrim) = true) : (popStep k b).SaveLike := by
  unfold popStep
  split
  · split
    · exact ⟨trivial, .shrink _⟩
    · rename_i hm
      simp only [hm, Bool.false_or, SPath.elemPrim, Ty.elemIsPrim] at he
      cases E with
      | prim P => exact ⟨trivial, .pop _ (SPath.lower_pushFree b)⟩
      | ref R => exact absurd he Bool.false_ne_true
  · exact Premise.saveLike_captureSP _ hb
      (by simp only [Stmt.Frag, SPath.MemFree, Bool.true_and]; exact he)

theorem iteStep_saveLike {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (thn : Prog C Γ Γ₁)
    (els : Prog C Γ Γ₂) (hc : c.MemFree = true) (ht : thn.Frag = true) (he : els.Frag = true) :
    (iteStep k c thn els).SaveLike := by
  cases c with
  | simple s => exact ⟨ht, he⟩
  | _ =>
    exact Premise.saveLike_capture _ hc
      (by simp only [Stmt.Frag, Val.MemFree, Prog.frag_up thn ht, Prog.frag_up els he,
        Bool.and_self])

theorem requireStep_saveLike (c : Val C Γ .bool) (hc : c.MemFree = true) :
    (requireStep k c).SaveLike := by
  cases c with
  | simple s => exact ⟨rfl, rfl⟩
  | _ => exact Premise.saveLike_capture _ hc rfl

theorem assertStep_saveLike (c : Val C Γ .bool) (hc : c.MemFree = true) :
    (assertStep k c).SaveLike := by
  cases c with
  | simple s => trivial
  | _ => exact Premise.saveLike_capture _ hc rfl

end Arms

/-! ## Every rule of the fragment -/

section Step

variable (k : Nat) (m : Modality)

/-- **On the fragment, a rule writes only save-like updates**, and the
programs it leaves are in the fragment again. -/
theorem Stmt.step_saveLike {Γ Γ' : Ctx} (s : Stmt C Γ Γ') (h : s.Frag = true) :
    (s.step k m).SaveLike := by
  cases s with
  | assign l r =>
    simp only [Stmt.Frag, Bool.and_eq_true] at h
    exact assignStep_saveLike k l r h.1 h.2
  | rebind i r => exact rebindStep_saveLike k i r h
  | assignLocal i v => exact localStep_saveLike k i v h
  | declLocal p x init =>
    cases init with
    | none => exact trivial
    | some e =>
      simp only [Stmt.Frag, Option.all_some] at h
      show Prog.Frag (.cons (.assignLocal .here e.up) .nil) = true
      simp only [Prog.Frag, Stmt.Frag, Val.memFree_up, h, Bool.and_self]
  | declStorage R x init =>
    cases init with
    | none => exact trivial
    | some r =>
      simp only [Stmt.Frag, Option.all_some] at h
      show Prog.Frag (.cons (.rebind .here r.up) .nil) = true
      simp only [Prog.Frag, Stmt.Frag, ARhs.memFree_up, h, Bool.and_self]
  | push b v hd =>
    simp only [Stmt.Frag, Bool.and_eq_true] at h
    exact pushStep_saveLike k b v hd h.1 h.2
  | pop b =>
    simp only [Stmt.Frag, Bool.and_eq_true] at h
    exact popStep_saveLike k b h.1 h.2
  | delete l =>
    simp only [Stmt.Frag, Bool.and_eq_true] at h
    exact deleteStep_saveLike k l h.1 h.2
  | ite c thn els =>
    simp only [Stmt.Frag, Bool.and_eq_true] at h
    exact iteStep_saveLike k c thn els h.1.1 h.1.2 h.2
  | require c => exact requireStep_saveLike k c h
  | assert c => exact assertStep_saveLike k c h
  | revert => cases m <;> trivial
  | assumeFalse => trivial
  | block body => exact h
  | _ => simp only [Stmt.Frag, Bool.false_eq_true] at h

/-- **On the fragment, every storage right-hand side a rule writes is, after
`Tm.expand?`, a chain of saves, pushed and dropped slots on `storage`.** -/
theorem Stmt.step_saveNF {Γ Γ' : Ctx} (s : Stmt C Γ Γ') (h : s.Frag = true) :
    ∀ U ∈ (s.step k m).upds, ∀ t ∈ U.2.2.stores, ((t.expand?).getD t).SaveNF :=
  fun U hU t ht =>
    Tm.SaveLike.saveNF_expand ((Premise.SaveLike.upds (Stmt.step_saveLike k m s h) U hU).stores t ht)

end Step

end Solidity

