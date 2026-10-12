import Solidity.Calculus.DecideErase

/-!
# The reduction's relation, by position, and its terms

`Fml.toLS` (`Calculus/DecideScoped.lean`) lowers a scoped term by position.
Its soundness is proved here on the scoped term itself, over the typed
state and the typed reading `Tm.eval`: one statement a sort (`TermOKS` to
`MValOKS`), proved together by induction on the size.

`RelU σ ρ g ℓ` is what relates the reduction's state `ρ` to a global part
`g` and the locals `ℓ` (`Locs`, by position), read in `σ`: the positions
are `ρ`'s keys (`SymS.Ok`, distinct, none from `ρ.next` on taken yet); the
storage is the stack of writes read in `σ`; each *bound* position holds
what its symbol reads in `σ` (`BindRel`, by position); the values of the
transaction are `σ`'s; and the heap and the next identity are what the
memory's run leaves.  A position no update bound (a hidden binder, until
an update binds it) is unrelated, and the fragment never reads it
(`Tm.inLS`).  At a typed state it is `RelT σ ρ τ`, at `τ.globE` and
`τ.loc`; an update's result is the pair `Upd.applyV` computes, which the
typed states it lands on read (`Upd.lands_iff_applyV`), so no typed state
is needed in between (an allocation's pair writes the local before the
heap that types it).

A term's symbols read the state's global part (`State.globE`, decision
83), so the global facts are about it; the reduction's lemmas that read no
term (the memory's runs, the storage bridges) apply to it unchanged.
-/

namespace Solidity

/-! ## Names of a thinned scope -/

section
open Semantics (Value Seg Halt Res Binding lookupBy setBy)
open Solidity (Srt Op0 Op1 Op2 Op3 Modality)
variable {C : Contract}
section Thin

theorem Thin.names_length : {Γ Δ : Ctx} → (h : Thin Γ Δ) → (ns : List Var) →
    ns.length = Δ.length → (h.names ns).length = Γ.length
  | _, _, .refl, _, hl => hl
  | _, _, .keep h, n :: ns, hl => by
    simp only [Thin.names, List.length_cons] at hl ⊢
    rw [Thin.names_length h ns (by omega)]
  | _, _, .keep _, [], hl => by simp only [List.length_nil, List.length_cons] at hl; omega
  | _, _, .drop h, ns, hl => by
    simp only [Thin.names]
    exact Thin.names_length h ns.tail (by simp only [List.length_tail, hl, List.length_cons]; omega)

theorem Thin.names_sublist : {Γ Δ : Ctx} → (h : Thin Γ Δ) → (ns : List Var) →
    (h.names ns).Sublist ns
  | _, _, .refl, _ => List.Sublist.refl _
  | _, _, .keep h, n :: ns => (Thin.names_sublist h ns).cons₂ n
  | _, _, .keep h, [] => Thin.names_sublist h []
  | _, _, .drop h, ns => (Thin.names_sublist h ns.tail).trans (List.tail_sublist ns)

/-- The locals below the innermost. -/
def Locs.tail {t : LTy} {Δ : Ctx} (ℓ : Locs C (t :: Δ)) : Locs C Δ := fun _ i => ℓ _ (.there i)

/-- The locals as `Semantics.lean`'s environment, named by `ns` (innermost
first). -/
def Locs.erase : {Γ : Ctx} → List Var → Locs C Γ → List (Var × Binding)
  | [], _, _ => []
  | _ :: _, [], _ => []
  | t :: _, x :: ns, ℓ => (x, t.enc C (ℓ t .here)) :: Locs.erase ns ℓ.tail

theorem Locs.mem_erase_key {Γ : Ctx} {ns : List Var} {ℓ : Locs C Γ} {x : Var} {b : Binding}
    (h : (x, b) ∈ Locs.erase ns ℓ) : x ∈ ns := by
  induction Γ generalizing ns with
  | nil => exact absurd h List.not_mem_nil
  | cons t Γ ih => cases ns with
    | nil => exact absurd h List.not_mem_nil
    | cons y ns =>
      rcases List.mem_cons.1 h with h | h
      · cases h; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

/-- A local's binding is among the erased ones. -/
theorem Locs.mem_erase_get {Γ : Ctx} {t : LTy} (i : Idx Γ t) :
    (ns : List Var) → (ℓ : Locs C Γ) → ns.length = Γ.length →
      (i.name ns, t.enc C (ℓ t i)) ∈ Locs.erase ns ℓ := by
  induction i with
  | here =>
    intro ns ℓ h
    cases ns with
    | nil => simp only [List.length_nil, List.length_cons, Nat.right_eq_add,
        Nat.add_one_ne_zero] at h
    | cons x ns => exact List.mem_cons_self
  | there i ih =>
    intro ns ℓ h
    cases ns with
    | nil => simp only [List.length_nil, List.length_cons, Nat.right_eq_add,
        Nat.add_one_ne_zero] at h
    | cons x ns =>
      exact List.mem_cons_of_mem _ (ih ns ℓ.tail (Nat.succ.inj h))

theorem Locs.set_here_tail {t : LTy} {Δ : Ctx} (ℓ : Locs C (t :: Δ)) (v : t.Denote C) :
    (ℓ.set .here v).tail = ℓ.tail := by
  funext u j
  exact Locs.set_ne ℓ .here (.there j) (fun h => nomatch h) v

theorem Locs.set_there_tail {t u : LTy} {Δ : Ctx} (ℓ : Locs C (u :: Δ)) (i : Idx Δ t)
    (v : t.Denote C) : (ℓ.set (.there i) v).tail = ℓ.tail.set i v := by
  funext w j
  by_cases h : i.toNat = j.toNat
  · obtain rfl := Idx.ty_eq_of_toNat h
    obtain rfl := Idx.toNat_inj i j h
    show ℓ.set (.there i) v _ (.there i) = _
    rw [Locs.set_same, Locs.set_same]
  · show ℓ.set (.there i) v _ (.there j) = _
    rw [Locs.set_ne _ _ _ h, Locs.set_ne _ (.there i) (.there j)
      (fun h' => h (Nat.add_right_cancel h'))]
    rfl

theorem Locs.set_there_here {t u : LTy} {Δ : Ctx} (ℓ : Locs C (u :: Δ)) (i : Idx Δ t)
    (v : t.Denote C) : ℓ.set (.there i) v u .here = ℓ u .here :=
  Locs.set_ne ℓ (.there i) .here (fun h => nomatch h) v

/-- A binding of a set local: the new one, or an old one of another name. -/
theorem Locs.mem_erase_set {Γ : Ctx} {t : LTy} (i : Idx Γ t) (v : t.Denote C) :
    (ns : List Var) → (ℓ : Locs C Γ) → ns.length = Γ.length → ns.Nodup →
      ∀ m ∈ Locs.erase ns (ℓ.set i v),
        m = (i.name ns, t.enc C v) ∨ (m ∈ Locs.erase ns ℓ ∧ m.1 ≠ i.name ns) := by
  induction i with
  | here =>
    intro ns ℓ h hnd m hm
    cases ns with
    | nil => simp only [List.length_nil, List.length_cons, Nat.right_eq_add,
        Nat.add_one_ne_zero] at h
    | cons x ns =>
      rcases List.mem_cons.1 hm with hm | hm
      · left; rw [hm, Locs.set_same]; rfl
      · rw [Locs.set_here_tail] at hm
        refine .inr ⟨List.mem_cons_of_mem _ hm, fun hx => ?_⟩
        have hk := Locs.mem_erase_key (b := m.2) (x := m.1) hm
        have hx' : m.1 = x := hx
        exact (List.nodup_cons.1 hnd).1 (hx' ▸ hk)
  | there i ih =>
    intro ns ℓ h hnd m hm
    cases ns with
    | nil => simp only [List.length_nil, List.length_cons, Nat.right_eq_add,
        Nat.add_one_ne_zero] at h
    | cons x ns =>
      have hnd' := List.nodup_cons.1 hnd
      rcases List.mem_cons.1 hm with hm | hm
      · subst hm
        rw [Locs.set_there_here]
        refine .inr ⟨List.mem_cons_self, fun hx => hnd'.1 ?_⟩
        have hx' : x = i.name ns := hx
        rw [hx']
        exact Idx.name_mem i ns (Nat.succ.inj h)
      · rw [Locs.set_there_tail] at hm
        rcases ih v ns ℓ.tail (Nat.succ.inj h) hnd'.2 m hm with hm' | ⟨hm', hne⟩
        · exact .inl (by rw [Idx.name_there]; exact hm')
        · exact .inr ⟨List.mem_cons_of_mem _ hm', by rw [Idx.name_there]; exact hne⟩

/-- A scope's locals popped: the rest are bound as they were. -/
theorem Locs.mem_erase_drop {Γ : Ctx} : {Δ : Ctx} → (h : Ext Γ Δ) → (qs ns : List Var) →
    (ℓ : Locs C Δ) → qs.length = h.depth →
      ∀ m ∈ Locs.erase ns (ℓ.drop h), m ∈ Locs.erase (qs ++ ns) ℓ := by
  intro Δ h
  induction h with
  | refl =>
    intro qs ns ℓ hq m hm
    cases qs with
    | nil => exact hm
    | cons _ _ =>
      change _ = 0 at hq
      simp only [List.length_cons, Nat.add_one_ne_zero] at hq
  | push h ih =>
    intro qs ns ℓ hq m hm
    change _ = h.depth + 1 at hq
    cases qs with
    | nil => simp only [List.length_nil] at hq; omega
    | cons q qs =>
      exact List.mem_cons_of_mem _ (ih qs ns ℓ.tail (by
        simp only [List.length_cons] at hq; omega) m hm)

theorem Locs.mem_erase_thin : {Γ Δ : Ctx} → (h : Thin Γ Δ) → (ns : List Var) → (ℓ : Locs C Δ) →
    ns.length = Δ.length → ∀ m ∈ Locs.erase (h.names ns) (ℓ.thin h), m ∈ Locs.erase ns ℓ
  | _, _, .refl, _, _, _, m, hm => hm
  | _, _, .keep h, n :: ns, ℓ, hl, m, hm => by
    simp only [Thin.names, Locs.erase, List.mem_cons] at hm ⊢
    rcases hm with hm | hm
    · exact .inl hm
    · exact .inr (Locs.mem_erase_thin h ns ℓ.tail (by simp only [List.length_cons] at hl; omega)
        m hm)
  | _, _, .keep _, [], _, hl, _, _ => by simp only [List.length_nil, List.length_cons] at hl; omega
  | _, _, .drop h, n :: ns, ℓ, hl, m, hm => by
    simp only [Thin.names, List.tail_cons] at hm
    simp only [Locs.erase, List.mem_cons]
    exact .inr (Locs.mem_erase_thin h ns ℓ.tail (by simp only [List.length_cons] at hl; omega) m hm)
  | _, _, .drop _, [], _, hl, _, _ => by simp only [List.length_nil, List.length_cons] at hl; omega

end Thin
end



namespace Decide

open Semantics SemanticsProperties

variable {C : Contract}

/-! ## The relation -/

section Rel

/-- What a position's binding `bd` holds, against what its symbol says
(`EnvRel`, by position), the storage `st` and the births `B` the updates
left. -/
def BindRel (σ : Semantics.State) (st : List (Name × Semantics.SVal)) (B : MemNames.Births)
    (bd : Binding) : SymB → Prop
  | .val t => ∃ v, t.eval σ = .ok v ∧ bd = .val v
  | .path q => ∃ r segs, q.eval σ = .ok (.field r :: segs) ∧ bd = .spath r segs ∧
      LiveTo (.struct st) (.field r :: segs)
  | .stale q => ∃ r segs, q.eval σ = .ok (.field r :: segs) ∧ bd = .spath r segs
  | .stor s => ∃ st', s.eval σ = .ok (.struct st') ∧ bd = .store st'
  | .mref i => ∃ n, LId.evalR B i = .ok n ∧ bd = .mref n
  | .unset => bd = .unset

variable {Γ : Ctx}

/-- The reduction's state `ρ` and the scoped state `τ` agree on everything
but the memory: each bound position holds what its symbol reads in `σ`,
its memory names read in the births `B`. -/
structure RelB (σ : Semantics.State) (ρ : SymS) (B : MemNames.Births) (g : Semantics.State)
    (ℓ : Locs C Γ) : Prop where
  ok : ρ.Ok ρ.names
  len : ρ.names.length = Γ.length
  nodup : ρ.names.Nodup
  fresh : ∀ m, ρ.next ≤ m → slotVar m ∉ ρ.names ∧ lookupBy (slotVar m) ρ.sym.env = none
  stor : ρ.sym.stor.eval σ = .ok (.struct g.storage)
  env : ∀ m ∈ Locs.erase ρ.names ℓ, ∀ b, lookupBy m.1 ρ.sym.env = some b →
    BindRel σ g.storage B m.2 b
  tx : ∀ k, g.envVal k = σ.envVal k

/-- **The reduction's state `ρ` stands for the global part `g` and the
locals `ℓ`**, read in `σ`: `RelB` in the births of `ρ`'s memory, whose run
leaves `g`'s heap. -/
structure RelU (σ : Semantics.State) (ρ : SymS) (g : Semantics.State) (ℓ : Locs C Γ) : Prop
    extends RelB σ ρ (ρ.sym.mem.births σ) g ℓ where
  mem : MemAt σ ρ.sym.mem g

/-- `RelU` at a typed state: its global part and its locals, erased. -/
abbrev RelT (σ : Semantics.State) (ρ : SymS) (τ : State C Γ) : Prop := RelU σ ρ τ.globE τ.loc

/-- A bound position of a typed state holds what its symbol reads. -/
theorem RelT.getB {σ : Semantics.State} {ρ : SymS} {τ : State C Γ} (h : RelT σ ρ τ) {t : LTy}
    (i : Idx Γ t) (b : SymB) (hb : ρ.get i.toNat = some b) :
    BindRel σ τ.globE.storage (ρ.sym.mem.births σ) (t.enc C (τ.getE i)) b :=
  h.env _ (Locs.mem_erase_get i _ τ.loc h.len) b (by rw [← SymS.get_of_ok h.ok h.len i]; exact hb)

/-- A bound position holds what its symbol reads. -/
theorem RelU.getB {σ : Semantics.State} {ρ : SymS} {g : Semantics.State} {ℓ : Locs C Γ}
    (h : RelU σ ρ g ℓ) {t : LTy} (i : Idx Γ t) (b : SymB) (hb : ρ.get i.toNat = some b) :
    BindRel σ g.storage (ρ.sym.mem.births σ) (t.enc C (ℓ t i)) b :=
  h.env _ (Locs.mem_erase_get i _ ℓ h.len) b (by rw [← SymS.get_of_ok h.ok h.len i]; exact hb)

open MemNames in
/-- A binding's relation holds in a run that allocates more. -/
theorem BindRel.grow {σ : Semantics.State} {st : List (Name × Semantics.SVal)} {B B' : Births}
    (hp : B <+: B') {bd : Binding} {b : SymB} (h : BindRel σ st B bd b) : BindRel σ st B' bd b := by
  cases b with
  | mref j =>
    obtain ⟨n, hn, he⟩ := h
    exact ⟨n, LId.evalR_prefix hp hn, he⟩
  | _ => exact h

/-- A write to the storage keeps each binding's relation, an alias through
an index made stale. -/
theorem BindRel.onWrite {σ : Semantics.State} {st st' : List (Name × Semantics.SVal)}
    {B : MemNames.Births} {bd : Binding} {b : SymB} (h : BindRel σ st B bd b) :
    BindRel σ st' B bd b.onWrite := by
  cases b with
  | path q =>
    obtain ⟨r, segs, h₁, h₂, -⟩ := h
    by_cases hn : q.noAt = true
    · simp only [SymB.onWrite, hn, if_true, BindRel]
      exact ⟨r, segs, h₁, h₂, LiveTo.of_noAt _ (LPath.noAt_eval σ hn h₁)⟩
    · simp only [SymB.onWrite, hn, if_false, BindRel, Bool.false_eq_true]
      exact ⟨r, segs, h₁, h₂⟩
  | _ => exact h

/-- The updates' memory has as many births as allocations. -/
theorem MemAt.births_length {σ g : Semantics.State} {M : LMem} (h : MemAt σ M g) :
    (M.births σ).length = M.nAlloc := by
  obtain ⟨μ, B, hr, -⟩ := h
  rw [LMem.births_of_run hr, LMem.run_nAlloc σ _ hr]

end Rel

/-! ## Terms, by position -/

section Terms

variable {Γ : Ctx}

/-- The symbols of a term, the measure the proofs below recurse on. -/
def _root_.Solidity.Tm.lsize : {s : Srt} → Tm C Γ s → Nat
  | _, .app1 _ a => a.lsize + 1
  | _, .app2 _ a b => a.lsize + b.lsize + 1
  | _, .app3 _ a b c => a.lsize + b.lsize + c.lsize + 1
  | _, .netOf _ a => a.lsize + 1
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ | _, .app0 _ => 0

/-- `x.lsize < n` for a direct subterm `x` of a term of size below `n + 1`. -/
macro "lsizeS_tac" : tactic => `(tactic| (simp only [Tm.lsize] at *; omega))

/-! The readings of the scoped symbols the proofs below unfold, on the
typed reading erased (`Tm.evalE`, `Calculus/DecideErase.lean`). -/

theorem evalS_save (τ : State C Γ) {p : PrimTy} (s : Tm C Γ .st) (q : Tm C Γ (.path (.prim p)))
    (t : Tm C Γ (.val p)) : (Tm.app3 .save s q (.app1 .sval t)).evalE τ =
    t.evalE τ >>= fun x => s.evalE τ >>= fun τ' => q.evalE τ >>= fun rs =>
      τ'.saveStorage rs.1 rs.2 x.toSVal := by
  rw [Tm.evalE_save, Tm.evalE_sval]
  simp only [bind_assoc, Res.ok_bind, State.writeStorage_toSVal]

theorem evalS_save_find (τ : State C Γ) {T : Ty} (s s' : Tm C Γ .st) (q q' : Tm C Γ (.path T)) :
    (Tm.app3 .save s q (.app2 .sfind s' q')).evalE τ =
    (Tm.app2 .sfind s' q').evalE τ >>= fun sv => s.evalE τ >>= fun τ' => q.evalE τ >>= fun rs =>
      τ'.findStorage rs.1 rs.2 >>= fun cur => τ'.saveStorage rs.1 rs.2 (cur.overlay sv) := by
  rw [Tm.evalE_save]
  simp only [Close.writeStorage_eq]

theorem evalS_save_copyMem (τ : State C Γ) {R : RefTy} (s : Tm C Γ .st) (q : Tm C Γ (.path (.ref R)))
    (m : Tm C Γ .mem) (i : Tm C Γ (.ident R)) :
    (Tm.app3 .save s q (.app2 .copyMem m i)).evalE τ =
    (Tm.app2 .copyMem m i).evalE τ >>= fun sv => s.evalE τ >>= fun τ' => q.evalE τ >>= fun rs =>
      τ'.findStorage rs.1 rs.2 >>= fun cur => τ'.saveStorage rs.1 rs.2 (cur.overlay sv) := by
  rw [Tm.evalE_save]
  simp only [Close.writeStorage_eq]

/-- `new R(nt)` reads to `R`'s array of the length `nt` reads to. -/
theorem newArrS_eval_ok {τ : State C Γ} {R : RefTy} {ho : R.newArrOk = true}
    {nt : Tm C Γ (.val .uint)} {sv : Semantics.SVal} :
    (Tm.app1 (Op1.newArr ho) nt).evalE τ = .ok sv ↔
      ∃ c, nt.evalE τ = .ok (.int c) ∧ sv = newArrVal R c :=
  Tm.evalE_newArr τ ho nt sv

/-- An identity's erased reading is its typed one. -/
theorem evalE_ident_ok {τ : State C Γ} {R : RefTy} {i : Tm C Γ (.ident R)} {id : Nat} :
    i.evalE τ = .ok id ↔ i.eval τ = some id := by
  simp only [Tm.evalE]
  cases i.eval τ with
  | none => simp only [toRes, reduceCtorEq, false_iff, reduceCtorEq]
  | some x => simp only [toRes, Except.ok.injEq, Option.some.injEq, Srt.erase]

/-! The statements below, one per sort, for the terms of fewer than `n`
symbols (`TermOK` to `MValOK`, by position).  An identity, an address and
a memory value also say that the identities they read are of their types
in `τ`'s heap (`IdOk`): where the typed reading of a memory read is the
untyped one (`Tm.evalE_read`). -/

/-- A value term reads, pushed in, what it reads in `τ`. -/
def TermOKS (σ : Semantics.State) (ρ : SymS) (τ : State C Γ) (n : Nat) : Prop :=
  ∀ {p : PrimTy} (t : Tm C Γ (.val p)), t.lsize < n → t.inLSM ρ = true →
    Sim ((t.toLSM ρ).eval σ) (t.evalE τ)

/-- A path, pushed in, is the path the program took, checked. -/
def PathOKS (σ : Semantics.State) (ρ : SymS) (τ : State C Γ) (n : Nat) : Prop :=
  ∀ {T : Ty} (p : Tm C Γ (.path T)), p.lsize < n → p.inLSM ρ = true → ∀ (qs : List Seg),
    (∃ rs, p.evalE τ = .ok rs ∧ qs = .field rs.1 :: rs.2) ↔
      ((p.toLSM ρ).eval σ = .ok qs ∧ LiveTo (.struct τ.globE.storage) qs)

/-- An identity, pushed in, is a name of the object it denotes, of its
type. -/
def IdOKS (σ : Semantics.State) (ρ : SymS) (τ : State C Γ) (n : Nat) : Prop :=
  ∀ {R : RefTy} (i : Tm C Γ (.ident R)), i.lsize < n → i.inLSM ρ = true → ∃ j g,
    i.toLSM ρ = some (j, g) ∧ (Rets (g.eval σ) → ∃ id, i.evalE τ = .ok id) ∧
    ∀ id, i.evalE τ = .ok id → Rets (g.eval σ) ∧ LId.evalR (ρ.sym.mem.births σ) j = .ok id ∧
      IdOk τ.H R id

/-- An address, pushed in, is the name of the object and what selects in it. -/
def AddrOKS (σ : Semantics.State) (ρ : SymS) (τ : State C Γ) (n : Nat) : Prop :=
  ∀ {T : Ty} (a : Tm C Γ (.addr T)), a.lsize < n → a.inLSM ρ = true →
    (∀ ad, a.eval τ = some ad → ad.Ok τ.H) ∧ ∃ j sel g, a.toLSM ρ = some (j, sel, g) ∧
    (Rets (g.eval σ) → ∃ ad, a.evalE τ = .ok ad) ∧
    ∀ ad, a.evalE τ = .ok ad → Rets (g.eval σ) ∧
      ∃ n, LId.evalR (ρ.sym.mem.births σ) j = .ok n ∧ sel.addr σ n = .ok ad

/-- A memory, pushed in, runs to the heap the term leaves. -/
def MemOKS (σ : Semantics.State) (ρ : SymS) (τ : State C Γ) (n : Nat) : Prop :=
  ∀ m : Tm C Γ .mem, m.lsize < n → m.inLSM ρ = true → ∃ M g, m.toLSM ρ = some (M, g) ∧
    (Rets (g.eval σ) → ∃ μ', m.evalE τ = .ok μ') ∧
    ∀ μ', m.evalE τ = .ok μ' → Rets (g.eval σ) ∧
      ∃ μ B, M.run σ = .ok (μ, B) ∧ μ.HeapEq μ' ∧ ρ.sym.mem.births σ <+: B

/-- A memory value, pushed in, is what the slot it writes holds. -/
def MValOKS (σ : Semantics.State) (ρ : SymS) (τ : State C Γ) (n : Nat) : Prop :=
  ∀ {T : Ty} (v : Tm C Γ (.mv T)), v.lsize < n → v.inLSM ρ = true →
    (∀ w, v.eval τ = some w → MvT.Ok τ.H T w) ∧ ∃ w g, v.toLSM ρ = some (w, g) ∧
    (Rets (g.eval σ) → ∃ mv, v.evalE τ = .ok mv) ∧
    ∀ mv, v.evalE τ = .ok mv → Rets (g.eval σ) ∧ w.eval σ (ρ.sym.mem.births σ) = .ok mv

variable {σ : Semantics.State} {ρ : SymS} {τ : State C Γ}

/-- A storage local read: the storage it holds, read where `find` reads. -/
theorem storLocalS_some {t : Tm C Γ .st} {S : LStor} (h : t.storLocalS ρ = some S) :
    ∃ i : Idx Γ .old, t = .pvS i ∧ ρ.get i.toNat = some (.stor S) := by
  cases t with
  | pvS i =>
    simp only [Tm.storLocalS, Idx.toNatR_eq] at h
    split at h
    · rename_i S' hS
      cases h
      exact ⟨i, rfl, hS⟩
    · cases h
  | _ => simp only [Tm.storLocalS, reduceCtorEq] at h

theorem isStorageS_eq {s : Srt} {t : Tm C Γ s} (h : t.isStorageS = true) :
    ∃ hs : s = .st, hs ▸ t = .app0 .storage := by
  cases t with
  | app0 o => cases o <;> simp only [Tm.isStorageS, Bool.false_eq_true] at h; exact ⟨rfl, rfl⟩
  | _ => simp only [Tm.isStorageS, Bool.false_eq_true] at h

theorem isStorageS_st {t : Tm C Γ .st} (h : t.isStorageS = true) : t = .app0 .storage := by
  obtain ⟨_, h⟩ := isStorageS_eq h
  exact h

/-- The typed facts an identity's reading carries: of its type in `τ`'s heap. -/
theorem IdOKS.typed {n : Nat} (hI : IdOKS σ ρ τ n) {R : RefTy} {i : Tm C Γ (.ident R)} (hn : i.lsize < n)
    (hf : i.inLSM ρ = true) : ∀ id, i.eval τ = some id → IdOk τ.H R id := by
  intro id hid
  obtain ⟨j, g, -, -, hie⟩ := hI i hn hf
  exact (hie id (evalE_ident_ok.2 hid)).2.2

/-- A read through an address in any memory grown from `τ`'s heap is the
untyped one. -/
theorem AddrOKS.addrOk {n : Nat} (hA : AddrOKS σ ρ τ n) {T : Ty} {a : Tm C Γ (.addr T)} (hn : a.lsize < n)
    (hf : a.inLSM ρ = true) (m : Tm C Γ .mem) : Tm.AddrOk τ m a :=
  fun μ ad _ had => MAddrT.Ok.of_prefix μ.ext ((hA a hn hf).1 ad had)

theorem IdOKS.identOk {n : Nat} (hI : IdOKS σ ρ τ n) {R : RefTy} {i : Tm C Γ (.ident R)} (hn : i.lsize < n)
    (hf : i.inLSM ρ = true) (m : Tm C Γ .mem) : Tm.IdentOk τ m i :=
  fun μ id _ hid => IdOk.of_prefix μ.ext (hI.typed hn hf id hid)

/-- **A value term reads, pushed in, what it reads in `τ`.** -/
theorem TermOKS.step (h : RelT σ ρ τ) {n : Nat}
    (hT : TermOKS σ ρ τ n) (hP : PathOKS σ ρ τ n) (hI : IdOKS σ ρ τ n)
    (hA : AddrOKS σ ρ τ n) (hM : MemOKS σ ρ τ n) (_hV : MValOKS σ ρ τ n) :
    TermOKS σ ρ τ (n + 1) := by
  intro p t hn hf
  cases t with
  | app0 o =>
    cases o with
    | lit _ => exact Sim.refl _
    | env k =>
      exact Sim.of_eq (by
        simp only [Tm.toLSM, Op0.toL, LTerm.eval, Tm.evalE_env, h.tx k])
  | pvV i =>
    simp only [Tm.inLSM] at hf
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hf
    have he := h.getB i b hb
    rw [Tm.evalE_pvV]
    simp only [Tm.toLSM, hb]
    cases b with
    | val t =>
      obtain ⟨v, h₁, h₂⟩ := he
      cases h₂
      rw [h₁]
      exact Sim.refl _
    | _ => simp only [BindRel, LTy.enc, reduceCtorEq, false_and, and_false, exists_false] at he
  | app1 o a =>
    cases o with
    | unop op hop =>
      simp only [Tm.inLSM, Op1.inL] at hf
      rw [Tm.evalE_unop]
      simp only [Tm.toLSM, Op1.toL, LTerm.mkUn_eval, LTerm.eval]
      exact Sim.bind (hT a (by lsizeS_tac) hf) fun _ => Sim.refl _
    | net | delValue | wt => simp only [Tm.inLSM, Op1.inL, Bool.false_eq_true] at hf
  | app2 o x y =>
    cases o with
    | binop op hop =>
      simp only [Tm.inLSM, Op2.inLS, Bool.and_eq_true] at hf
      simp only [Tm.toLSM, Op2.toLAtS, Op2.toL, LTerm.mkBin_eval, LTerm.eval]
      exact Sim.trans (Sim.bind (hT x (by lsizeS_tac) hf.1) fun _ =>
        evalBinop_sim (hT y (by lsizeS_tac) hf.2)) (Tm.evalE_binop τ op hop x y).symm
    | find =>
      simp only [Tm.inLSM, Op2.inLS, Bool.and_eq_true, Bool.or_eq_true] at hf
      obtain ⟨hs | hs, hf⟩ := hf
      · obtain rfl := isStorageS_st hs
        have hb := live_bridge (τ := τ.globE) (hP y (by lsizeS_tac) hf)
        rw [Tm.evalE_find, Tm.evalE_storage, Res.ok_bind]
        simp only [Tm.toLSM, Tm.storLocalS, Op2.toLAtS, Op0.toL, LTerm.eval, h.stor, Res.ok_bind]
        intro a
        simp only [Res.bind_eq_ok]
        constructor
        · rintro ⟨qs, hq, c, hc, ha⟩
          obtain ⟨rs, hrs, rfl, hfs⟩ := (hb qs c).1 ⟨hq, hc⟩
          exact ⟨rs, hrs, c, hfs, ha⟩
        · rintro ⟨rs, hrs, c, hfs, ha⟩
          obtain ⟨hq, hc⟩ := (hb _ c).2 ⟨rs, hrs, rfl, hfs⟩
          exact ⟨_, hq, c, hc, ha⟩
      · -- `find(old, y)`: the path checked against the storage the updates left,
        -- the snapshot read there
        obtain ⟨S, hS⟩ := Option.isSome_iff_exists.1 hs
        obtain ⟨i, rfl, hl⟩ := storLocalS_some hS
        obtain ⟨st, hSe, hst⟩ := h.getB i _ hl
        have hA := hP y (by lsizeS_tac) hf
        have hg := guardPath_ok h.stor (y.toLSM ρ)
        rw [Tm.evalE_find, Tm.evalE_pvS, Res.ok_bind]
        simp only [LTy.enc, Binding.store.injEq] at hst
        subst hst
        simp only [Tm.toLSM, hS, Op2.toLAtS, LTerm.eval, hSe, Res.ok_bind]
        intro a
        constructor
        · intro H
          obtain ⟨g, hgv, H⟩ := Res.bind_eq_ok.1 H
          obtain ⟨qs, hq, hlive⟩ := hg.1 ⟨g, hgv⟩
          obtain ⟨rs, hrs, rfl⟩ := (hA _).2 ⟨hq, hlive⟩
          rw [hq, Res.ok_bind] at H
          rw [hrs, Res.ok_bind, ← find_root]
          exact H
        · intro H
          obtain ⟨rs, hrs, H⟩ := Res.bind_eq_ok.1 H
          obtain ⟨hq, hlive⟩ := (hA _).1 ⟨rs, hrs, rfl⟩
          obtain ⟨g, hgv⟩ := hg.2 ⟨_, hq, hlive⟩
          rw [hgv, Res.ok_bind, hq, Res.ok_bind]
          rw [← find_root] at H
          exact H
    | len =>
      simp only [Tm.inLSM, Op2.inLS, Bool.and_eq_true] at hf
      obtain ⟨hs, hf⟩ := hf
      obtain rfl := isStorageS_st hs
      have hb := live_bridge (τ := τ.globE) (hP y (by lsizeS_tac) hf)
      rw [Tm.evalE_len, Tm.evalE_storage, Res.ok_bind]
      simp only [Tm.toLSM, Op0.toL, Op2.toLAtS, Op2.toL, LTerm.eval, h.stor, Res.ok_bind]
      intro a
      simp only [Res.bind_eq_ok]
      constructor
      · rintro ⟨qs, hq, c, hc, ha⟩
        obtain ⟨rs, hrs, rfl, hfs⟩ := (hb qs c).1 ⟨hq, hc⟩
        exact ⟨rs, hrs, c, hfs, ha⟩
      · rintro ⟨rs, hrs, c, hfs, ha⟩
        obtain ⟨hq, hc⟩ := (hb _ c).2 ⟨rs, hrs, rfl, hfs⟩
        exact ⟨_, hq, c, hc, ha⟩
    | read =>
      simp only [Tm.inLSM, Op2.inLS, Bool.and_eq_true] at hf
      obtain ⟨⟨hm, ha⟩, hr⟩ := hf
      rw [Tm.evalE_read τ x y (hA.addrOk (by lsizeS_tac) ha x)]
      obtain ⟨M, g, hM, hmr, hme⟩ := hM x (by lsizeS_tac) hm
      obtain ⟨-, j, sel, g', hA, har, hae⟩ := hA y (by lsizeS_tac) ha
      simp only [hM, hA, readM, Option.isSome_map] at hr
      obtain ⟨r, hrr⟩ := Option.isSome_iff_exists.1 hr
      simp only [Tm.toLSM, Op2.toLAtS, Op2.toL, hM, hA, readM, hrr,
        Option.map_some, Option.getD_some]
      intro w
      rw [seqL_eval, seqL_eval]
      constructor
      · intro hw
        obtain ⟨_, hg, hw⟩ := Res.bind_eq_ok.1 hw
        obtain ⟨_, hg', hw⟩ := Res.bind_eq_ok.1 hw
        obtain ⟨μ', hμ'⟩ := hmr ⟨_, hg⟩
        obtain ⟨-, μ, B, hrun, hh, hp⟩ := hme μ' hμ'
        obtain ⟨ad, had⟩ := har ⟨_, hg'⟩
        obtain ⟨-, n0, hn0, hsa⟩ := hae ad had
        have hs := LMem.readT_sim σ M j sel hrun hrr w
        rw [LId.evalR_prefix hp hn0, Res.ok_bind, LSel.read_of_addr hsa, readAddr_of_heap hh.1] at hs
        rw [hμ', Res.ok_bind, had, Res.ok_bind]
        exact hs.1 hw
      · intro hw
        obtain ⟨μ', hμ', hw⟩ := Res.bind_eq_ok.1 hw
        obtain ⟨ad, had, hw⟩ := Res.bind_eq_ok.1 hw
        obtain ⟨⟨_, hg⟩, μ, B, hrun, hh, hp⟩ := hme μ' hμ'
        obtain ⟨⟨_, hg'⟩, n0, hn0, hsa⟩ := hae ad had
        have hs := LMem.readT_sim σ M j sel hrun hrr w
        rw [LId.evalR_prefix hp hn0, Res.ok_bind, LSel.read_of_addr hsa, readAddr_of_heap hh.1] at hs
        rw [hg, Res.ok_bind, hg', Res.ok_bind]
        exact hs.2 hw
    | mlen =>
      simp only [Tm.inLSM, Op2.inLS, Bool.and_eq_true] at hf
      obtain ⟨⟨hm, hi⟩, hr⟩ := hf
      rw [Tm.evalE_mlen τ x y (hI.identOk (by lsizeS_tac) hi x)]
      obtain ⟨M, g, hM, hmr, hme⟩ := hM x (by lsizeS_tac) hm
      obtain ⟨j, g', hI, hir, hie⟩ := hI y (by lsizeS_tac) hi
      simp only [hM, hI, lenM, Option.isSome_map] at hr
      obtain ⟨r, hrr⟩ := Option.isSome_iff_exists.1 hr
      simp only [Tm.toLSM, Op2.toLAtS, Op2.toL, hM, hI, lenM, hrr,
        Option.map_some, Option.getD_some]
      intro w
      rw [seqL_eval, seqL_eval]
      constructor
      · intro hw
        obtain ⟨_, hg, hw⟩ := Res.bind_eq_ok.1 hw
        obtain ⟨_, hg', hw⟩ := Res.bind_eq_ok.1 hw
        obtain ⟨μ', hμ'⟩ := hmr ⟨_, hg⟩
        obtain ⟨-, μ, B, hrun, hh, hp⟩ := hme μ' hμ'
        obtain ⟨id, hid⟩ := hir ⟨_, hg'⟩
        obtain ⟨-, hj, -⟩ := hie id hid
        have hs := LMem.readT_sim σ M j .size hrun hrr w
        rw [LId.evalR_prefix hp hj, Res.ok_bind] at hs
        simp only [LSel.read, memArrayLen_of_heap hh.1] at hs
        rw [hμ', Res.ok_bind, hid, Res.ok_bind]
        exact hs.1 hw
      · intro hw
        obtain ⟨μ', hμ', hw⟩ := Res.bind_eq_ok.1 hw
        obtain ⟨id, hid, hw⟩ := Res.bind_eq_ok.1 hw
        obtain ⟨⟨_, hg⟩, μ, B, hrun, hh, hp⟩ := hme μ' hμ'
        obtain ⟨⟨_, hg'⟩, hj, -⟩ := hie id hid
        have hs := LMem.readT_sim σ M j .size hrun hrr w
        rw [LId.evalR_prefix hp hj, Res.ok_bind] at hs
        simp only [LSel.read, memArrayLen_of_heap hh.1] at hs
        rw [hg, Res.ok_bind, hg', Res.ok_bind]
        exact hs.2 hw
    | findIn => simp only [Tm.inLSM, Op2.inLS, Bool.false_eq_true] at hf
  | app3 o c a b =>
    cases o with
    | ite =>
      simp only [Tm.inLSM, Op3.inLS, Bool.and_eq_true] at hf
      rw [Tm.evalE_ite]
      simp only [Tm.toLSM, Op3.toLAtS, Op3.toL, LTerm.eval]
      exact Sim.bind (hT c (by lsizeS_tac) hf.1.1) fun _ =>
        pickBranch_sim (hT a (by lsizeS_tac) hf.1.2) (hT b (by lsizeS_tac) hf.2)
  | netOf _ _ => simp only [Tm.inLSM, Bool.false_eq_true] at hf

theorem glob_storage (τ : State C Γ) : τ.globE.storage = τ.globE.storage := rfl

/-- **A path, pushed in, is the path the program took**, checked. -/
theorem PathOKS.step (h : RelT σ ρ τ) {n : Nat}
    (hT : TermOKS σ ρ τ n) (hP : PathOKS σ ρ τ n) (_hI : IdOKS σ ρ τ n)
    (_hA : AddrOKS σ ρ τ n) (_hM : MemOKS σ ρ τ n) (_hV : MValOKS σ ρ τ n) :
    PathOKS σ ρ τ (n + 1) := fun p hn hf qs => match p, hn, hf, qs with
  | .app0 (.root r), hn, _, qs => by
    simp only [Tm.toLSM, Op0.toL, LPath.eval, Tm.eval, tm_eval]
    constructor
    · rintro ⟨rs, hrs, rfl⟩
      cases hrs
      exact ⟨rfl, LiveTo.of_noAt _ rfl⟩
    · rintro ⟨hq, -⟩
      cases hq
      exact ⟨(r, []), rfl, rfl⟩
  | .pvP i, hn, hf, qs => by
    simp only [Tm.inLSM] at hf
    split at hf
    · rename_i q hb
      obtain ⟨r, segs, h₁, h₂, hlive⟩ := h.getB i _ hb
      have he : τ.getE i = some (r, segs) := by
        revert h₂
        cases τ.getE i with
        | none => simp only [LTy.enc, reduceCtorEq, false_implies]
        | some p => simp only [LTy.enc, Binding.spath.injEq]; rintro ⟨rfl, rfl⟩; rfl
      simp only [Tm.toLSM, hb, Tm.eval, State.aliasPathT_getE, he, h₁]
      constructor
      · rintro ⟨rs, hrs, rfl⟩
        cases hrs
        exact ⟨rfl, hlive⟩
      · rintro ⟨hq, -⟩
        cases hq
        exact ⟨(r, segs), rfl, rfl⟩
    · rename_i t hb
      obtain ⟨v, -, h₂⟩ := h.getB i _ hb
      revert h₂
      cases τ.getE i <;> simp only [LTy.enc, reduceCtorEq, false_implies]
    all_goals cases hf
  | .app1 (.field f) _ p, hn, hf, qs => by
    simp only [Tm.inLSM, Op1.inL] at hf
    have he : ∀ ho : (Op1.field f).named = false, (Tm.app1 (.field f) ho p).evalE τ =
        p.evalE τ >>= fun rs => .ok (rs.1, rs.2 ++ [.field f]) := fun _ => rfl
    rw [he]
    simp only [Tm.toLSM, Op1.toL, LPath.eval]
    constructor
    · rintro ⟨rs', hrs', rfl⟩
      obtain ⟨rs, hrs, he⟩ := Res.bind_eq_ok.1 hrs'
      cases he
      obtain ⟨hq, hl⟩ := (hP p (by lsizeS_tac) hf _).1 ⟨rs, hrs, rfl⟩
      refine ⟨by rw [hq]; rfl, ?_⟩
      show LiveTo _ ((.field rs.1 :: rs.2) ++ [.field f])
      unfold LiveTo
      rw [lastAtSegs_field]
      exact hl
    · rintro ⟨hq, hl⟩
      obtain ⟨qs₀, hq₀, he⟩ := Res.bind_eq_ok.1 hq
      cases he
      have hl₀ : LiveTo (.struct τ.globE.storage) qs₀ := by
        unfold LiveTo at hl ⊢; rw [lastAtSegs_field] at hl; exact hl
      obtain ⟨rs, hrs, rfl⟩ := (hP p (by lsizeS_tac) hf qs₀).2 ⟨hq₀, hl₀⟩
      exact ⟨(rs.1, rs.2 ++ [.field f]), by rw [hrs]; rfl, by simp only [List.cons_append]⟩
  | .app2 .at p i, hn, hf, qs => by
    simp only [Tm.inLSM, Op2.inLS, Bool.and_eq_true] at hf
    have hi := hT i (by lsizeS_tac) hf.2
    rw [Tm.evalE_at]
    simp only [Tm.toLSM, Op2.toLAtS, Op2.toL, LPath.eval]
    constructor
    · rintro ⟨rs', hrs', rfl⟩
      obtain ⟨rs, hrs, hr⟩ := Res.bind_eq_ok.1 hrs'
      obtain ⟨k, hk, hr⟩ := Res.bind_eq_ok.1 hr
      obtain ⟨v, hv, hk⟩ := Res.bind_eq_ok.1 hk
      obtain ⟨u, hu, he⟩ := Res.bind_eq_ok.1 hr
      cases he
      rw [Close.checkIndex_eq] at hu
      obtain ⟨c, hc, hu⟩ := Res.bind_eq_ok.1 hu
      obtain ⟨hq, hl⟩ := (hP p (by lsizeS_tac) hf.1 _).1 ⟨rs, hrs, rfl⟩
      refine ⟨by rw [hq, Res.ok_bind, (hi v).2 hv, Res.ok_bind, hk]; rfl, ?_⟩
      show LiveTo _ ((.field rs.1 :: rs.2) ++ [.at k])
      unfold LiveTo
      rw [lastAtSegs_at, SVal.findLive_append, ← hl.find_eq, ← glob_storage, find_root, hc,
        Res.ok_bind]
      exact (idx_iff c k).1 (by cases u; exact hu)
    · rintro ⟨hq, hl⟩
      obtain ⟨qs₀, hq₀, hq⟩ := Res.bind_eq_ok.1 hq
      obtain ⟨k, hk, he⟩ := Res.bind_eq_ok.1 hq
      cases he
      obtain ⟨v, hv, hk⟩ := Res.bind_eq_ok.1 hk
      obtain ⟨c', hc'⟩ := hl
      rw [lastAtSegs_at, SVal.findLive_append] at hc'
      obtain ⟨c, hc, hck⟩ := Res.bind_eq_ok.1 hc'
      have hl₀ := LiveTo.of_findLive hc
      obtain ⟨rs, hrs, rfl⟩ := (hP p (by lsizeS_tac) hf.1 qs₀).2 ⟨hq₀, hl₀⟩
      refine ⟨(rs.1, rs.2 ++ [.at k]), ?_, by simp only [List.cons_append]⟩
      have hfs : τ.globE.findStorage rs.1 rs.2 = .ok c := by
        rw [← find_root, glob_storage, hl₀.find_eq]; exact hc
      rw [hrs, Res.ok_bind, (hi v).1 hv, Res.ok_bind, hk, Res.ok_bind, Close.checkIndex_eq,
        hfs, Res.ok_bind, (idx_iff c k).2 ⟨c', hck⟩, Res.ok_bind]
  | .app1 .next _ _, hn, hf, _ => by simp only [Tm.inLSM, Op1.inL, Bool.false_eq_true] at hf
  | .app2 .nextIn _ _, hn, hf, _ => by simp only [Tm.inLSM, Op2.inLS, Bool.false_eq_true] at hf
  | .app3 .atIn _ _ _, hn, hf, _ => by simp only [Tm.inLSM, Op3.inLS, Bool.false_eq_true] at hf

theorem addMOfS?_some {m : Tm C Γ .mem} {R : RefTy} (h : addMOfS? m = some R) :
    m = .app1 (.addM R) rfl (.app0 .memory) := by
  unfold addMOfS? at h
  split at h
  · cases h; rfl
  · cases h

theorem allocRefOfS?_some {v : Tm C Γ .mv} {R : RefTy} (h : allocRefOfS? v = some R) :
    v = .app1 .ref rfl (.app1 (.alloc R) rfl (.app0 .memory)) := by
  unfold allocRefOfS? at h
  split at h
  · cases h; rfl
  · cases h

/-- The value of a write is its own, or the root a `delete` allocates. -/
theorem freshRefS_cases (ρ : SymS) (m : Tm C Γ .mem) (v : Tm C Γ .mv) :
    (∀ z, freshRefS ρ m v z = z) ∨ ∃ R, m = .app1 (.addM R) rfl (.app0 .memory) ∧
      v = .app1 .ref rfl (.app1 (.alloc R) rfl (.app0 .memory)) ∧
      ∀ z, freshRefS ρ m v z = some (.ref ⟨ρ.sym.mem.nAlloc, []⟩, .lit (.bool true)) := by
  cases hm : addMOfS? m with
  | none => exact Or.inl fun _ => by simp only [freshRefS, hm]
  | some R =>
    cases hv : allocRefOfS? v with
    | none => exact Or.inl fun _ => by simp only [freshRefS, hm, hv]
    | some R' =>
      by_cases hR : R = R'
      · subst hR
        exact Or.inr ⟨R, addMOfS?_some hm, allocRefOfS?_some hv,
          fun _ => by simp only [freshRefS, hm, hv, ↓reduceIte]⟩
      · exact Or.inl fun _ => by simp only [freshRefS, hm, hv, hR, ↓reduceIte]

/-- **An identity, pushed in**: a name of the object the term denotes. -/
theorem IdOKS.step (h : RelT σ ρ τ) {n : Nat}
    (_hT : TermOKS σ ρ τ n) (_hP : PathOKS σ ρ τ n) (_hI : IdOKS σ ρ τ n)
    (hA : AddrOKS σ ρ τ n) (hM : MemOKS σ ρ τ n) (_hV : MValOKS σ ρ τ n) :
    IdOKS σ ρ τ (n + 1) := fun i hn hf => match i, hn, hf with
  | .pvI i, hn, hf => by
    simp only [Tm.inLSM] at hf
    split at hf
    · rename_i j hb
      obtain ⟨n', hn', h₂⟩ := h.getB i _ hb
      have he : τ.getE i = some n' := by
        revert h₂
        cases τ.getE i with
        | none => simp only [LTy.enc, reduceCtorEq, false_implies]
        | some p => simp only [LTy.enc, Binding.mref.injEq]; rintro rfl; rfl
      refine ⟨j, .lit (.bool true), by simp only [Tm.toLSM, hb], fun _ => ⟨n', ?_⟩,
        fun id hid => ?_⟩
      · simp only [Tm.eval, State.memRefT_getE, he, pure, Except.pure]
      · simp only [Tm.eval, State.memRefT_getE, he, pure, Except.pure, Except.ok.injEq] at hid
        subst hid
        exact ⟨⟨_, rfl⟩, hn'⟩
    · cases hf
  | .app1 (.alloc _) _ _, hn, hf => by simp only [Tm.inLSM, Op1.inL, Bool.false_eq_true] at hf
  | .app2 .copy _ _, hn, hf => by simp only [Tm.inLSM, Op2.inLS, Bool.false_eq_true] at hf
  | .app2 .iread m a, hn, hf => by
    simp only [Tm.inLSM, Op2.inLS, Bool.and_eq_true] at hf
    obtain ⟨⟨hm, ha⟩, hs⟩ := hf
    obtain ⟨M, g, hM, hmr, hme⟩ := hM m (by lsizeS_tac) hm
    obtain ⟨j, sel, g', hA, har, hae⟩ := hA a (by lsizeS_tac) ha
    simp only [hM, hA, ireadM] at hs
    have hev : (Tm.app2 .iread m a).evalE τ =
        m.evalE τ >>= fun τ' => a.evalE τ >>= fun addr => readAddr τ' addr >>= MVal.asRef := rfl
    cases hj' : M.readI j sel with
    | none => simp only [hj', Option.bind_none, irOk, Bool.false_eq_true] at hs
    | some j' =>
      cases hng : M.nameG j' with
      | none =>
        simp only [hj', hng, Option.bind_some, Option.map_none, irOk, Bool.false_eq_true] at hs
      | some ng =>
        simp only [hj', hng, Option.bind_some, Option.map_some, irOk, decide_eq_true_eq] at hs
        refine ⟨j', seqL g (seqL g' ng), by
          simp only [Tm.toLSM, Op2.toLAtS, Op2.toL, hM, hA, ireadM, hj', hng, Option.bind_some,
            Option.map_some], fun hgg => ?_, fun id hid => ?_⟩
        · obtain ⟨hg, hgg⟩ := (seqL_rets σ _ _).1 hgg
          obtain ⟨hg', hng'⟩ := (seqL_rets σ _ _).1 hgg
          obtain ⟨μ', hμ'⟩ := hmr hg
          obtain ⟨-, μ, B, hrun, hh, hp⟩ := hme μ' hμ'
          obtain ⟨ad, had⟩ := har hg'
          obtain ⟨-, n0, hn0, hsa⟩ := hae ad had
          obtain ⟨id, hid⟩ := (LMem.nameG_sim σ M j' hrun hng).1 hng'
          have hs' := (LMem.readI_sim σ M j sel hrun hj').2 id
          rw [LId.evalR_prefix hp hn0, Res.ok_bind, LSel.iread_of_addr hsa,
            readAddr_of_heap hh.1] at hs'
          refine ⟨id, ?_⟩
          rw [hev, hμ', Res.ok_bind, had, Res.ok_bind]
          exact hs'.1 hid
        · rw [hev] at hid
          obtain ⟨μ', hμ', hid⟩ := Res.bind_eq_ok.1 hid
          obtain ⟨ad, had, hid⟩ := Res.bind_eq_ok.1 hid
          obtain ⟨hg, μ, B, hrun, hh, hp⟩ := hme μ' hμ'
          obtain ⟨hg', n0, hn0, hsa⟩ := hae ad had
          have hs' := (LMem.readI_sim σ M j sel hrun hj').2 id
          rw [LId.evalR_prefix hp hn0, Res.ok_bind, LSel.iread_of_addr hsa,
            readAddr_of_heap hh.1] at hs'
          have hB : LId.evalR B j' = .ok id := hs'.2 hid
          refine ⟨(seqL_rets σ _ _).2 ⟨hg, (seqL_rets σ _ _).2
            ⟨hg', (LMem.nameG_sim σ M j' hrun hng).2 ⟨id, hB⟩⟩⟩, ?_⟩
          exact LId.evalR_prefix_lt hp (by rw [h.mem.births_length]; exact hs) hB

/-- **An address, pushed in**: the name and what selects in it. -/
theorem AddrOKS.step (_h : RelT σ ρ τ) {n : Nat}
    (hT : TermOKS σ ρ τ n) (_hP : PathOKS σ ρ τ n) (hI : IdOKS σ ρ τ n)
    (_hA : AddrOKS σ ρ τ n) (_hM : MemOKS σ ρ τ n) (_hV : MValOKS σ ρ τ n) :
    AddrOKS σ ρ τ (n + 1) := fun a hn hf => match a, hn, hf with
  | .app1 (.mfield f) _ i, hn, hf => by
    simp only [Tm.inLSM, Op1.inL] at hf
    obtain ⟨j, g, hI, hir, hie⟩ := hI i (by lsizeS_tac) hf
    have hev : ∀ ho : (Op1.mfield f).named = false, (Tm.app1 (.mfield f) ho i).evalE τ =
        i.evalE τ >>= fun id => .ok (.memoryField id f) := fun _ => rfl
    refine ⟨j, .fld f, g, by simp only [Tm.toLSM, Op1.toL, hI, Option.map_some], fun hg => ?_,
      fun ad had => ?_⟩
    · obtain ⟨id, hid⟩ := hir hg
      exact ⟨_, by rw [hev, hid, Res.ok_bind]⟩
    · rw [hev] at had
      obtain ⟨id, hid, had⟩ := Res.bind_eq_ok.1 had
      obtain ⟨hg, hj⟩ := hie id hid
      cases had
      exact ⟨hg, id, hj, rfl⟩
  | .app2 .mat i t, hn, hf => by
    simp only [Tm.inLSM, Op2.inLS, Bool.and_eq_true] at hf
    obtain ⟨j, g, hI, hir, hie⟩ := hI i (by lsizeS_tac) hf.1
    have ht := hT t (by lsizeS_tac) hf.2
    refine ⟨j, .idx (t.toLSM ρ), seqL g (isIntL (t.toLSM ρ)),
      by simp only [Tm.toLSM, Op2.toLAtS, Op2.toL, hI, Option.map_some], fun hw => ?_,
      fun ad had => ?_⟩
    · obtain ⟨hg, hi⟩ := (seqL_rets σ _ _).1 hw
      obtain ⟨k, hk⟩ := (isIntL_ret σ _).1 hi
      obtain ⟨id, hid⟩ := hir hg
      exact ⟨.memoryIndex id k, by rw [Tm.evalE_mat, hid, Res.ok_bind, (ht _).1 hk]; rfl⟩
    · rw [Tm.evalE_mat] at had
      obtain ⟨id, hid, had⟩ := Res.bind_eq_ok.1 had
      obtain ⟨hg, hj⟩ := hie id hid
      obtain ⟨k, hk, had⟩ := Res.bind_eq_ok.1 had
      obtain ⟨w, hw, hk⟩ := Res.bind_eq_ok.1 hk
      cases w with
      | bool b => cases hk
      | int k' =>
        cases hk
        cases had
        have hw' := (ht _).2 hw
        refine ⟨(seqL_rets σ _ _).2 ⟨hg, (isIntL_ret σ _).2 ⟨_, hw'⟩⟩, id, hj, ?_⟩
        simp only [LSel.addr, hw', Res.ok_bind, Value.asInt]

/-- The value a write writes, in every run of its memory that allocates
after the updates': a value of the fragment, or the root a `delete`
allocates under the write (`freshRefS`). -/
theorem writeValS_ok (h : RelT σ ρ τ) {n : Nat} (hV : MValOKS σ ρ τ n) {m : Tm C Γ .mem}
    {v : Tm C Γ .mv} (hvn : v.lsize < n) {M : LMem} {g : LTerm} (hM : m.toLSM ρ = some (M, g))
    (hv : (v.inLSM ρ || (freshRefS ρ m v none).isSome) = true) :
    ∃ w gv, freshRefS ρ m v (v.toLSM ρ) = some (w, gv) ∧
      (Rets (gv.eval σ) → ∃ mv, v.evalE τ = .ok mv) ∧
      ∀ mv, v.evalE τ = .ok mv → Rets (gv.eval σ) ∧
        ∀ μ B, M.run σ = .ok (μ, B) → ρ.sym.mem.births σ <+: B → w.eval σ B = .ok mv := by
  rcases freshRefS_cases ρ m v with hz | ⟨R, rfl, rfl, hfr⟩
  · rw [hz none, Option.isSome_none, Bool.or_false] at hv
    obtain ⟨w, gv, hw, hvr, hve⟩ := hV v hvn hv
    refine ⟨w, gv, by rw [hz, hw], hvr, fun mv hmv => ?_⟩
    obtain ⟨hg, hwe⟩ := hve mv hmv
    exact ⟨hg, fun _ _ _ hp => LMV.eval_prefix hp hwe⟩
  · simp only [Tm.toLSM, Op1.toL, Op0.toL, Option.bind_some] at hM
    split at hM
    · rename_i hR
      simp only [Option.some.injEq, Prod.mk.injEq] at hM
      obtain ⟨rfl, -⟩ := hM
      have hve : ∀ mv, (Tm.app1 (C := C) (Γ := Γ) .ref rfl
          (.app1 (.alloc R) rfl (.app0 .memory))).evalE τ = .ok mv ↔
          ∃ τ₁ id, allocDefault τ.globE R = .ok (τ₁, id) ∧ mv = .ref id := by
        intro mv
        have e : (Tm.app1 (C := C) (Γ := Γ) .ref rfl
            (.app1 (.alloc R) rfl (.app0 .memory))).evalE τ =
            (allocDefault τ.globE R >>= fun r => .ok r.2) >>= fun id => .ok (.ref id) := rfl
        rw [e]
        constructor
        · intro hmv
          obtain ⟨id, hid, hmv⟩ := Res.bind_eq_ok.1 hmv
          obtain ⟨r, hr, hid⟩ := Res.bind_eq_ok.1 hid
          cases hid; cases hmv
          exact ⟨r.1, r.2, hr, rfl⟩
        · rintro ⟨τ₁, id, hr, rfl⟩
          rw [hr]; rfl
      refine ⟨_, _, hfr _, fun _ => ?_, fun mv hmv => ⟨⟨_, rfl⟩, fun μ B hrun _ => ?_⟩⟩
      · obtain ⟨τ₁, id, hr⟩ := allocDefault_ok hR τ.globE
        exact ⟨_, (hve _).2 ⟨τ₁, id, hr, rfl⟩⟩
      · obtain ⟨τ₁, id, hr, rfl⟩ := (hve mv).1 hmv
        obtain ⟨μ₀, B₀, id₀, hr₀, hk, hc, rfl⟩ := LMem.run_addM hrun
        obtain ⟨μ₁, B₁, hr₁, hh⟩ := h.mem
        rw [hr₁, Except.ok.injEq, Prod.mk.injEq] at hr₀
        obtain ⟨rfl, rfl⟩ := hr₀
        rcases (allocDefault_heap hh R).cases with ⟨e, h₁, -⟩ | ⟨t₁, t₂, id', h₁, h₂, -⟩
        · rw [allocDefault_of_copy hc] at h₁; cases h₁
        · rw [allocDefault_of_copy hc, Except.ok.injEq, Prod.mk.injEq] at h₁
          rw [hr, Except.ok.injEq, Prod.mk.injEq] at h₂
          obtain ⟨-, rfl⟩ := h₁
          obtain ⟨-, rfl⟩ := h₂
          simp only [LMV.eval]
          rw [evalR_last _ _ hk]
          rfl
    · cases hM

/-- **A memory, pushed in**: the writes and allocations, run to the heap
the term leaves. -/
theorem MemOKS.step (h : RelT σ ρ τ) {n : Nat}
    (hT : TermOKS σ ρ τ n) (_hP : PathOKS σ ρ τ n) (_hI : IdOKS σ ρ τ n)
    (hA : AddrOKS σ ρ τ n) (hM : MemOKS σ ρ τ n) (hV : MValOKS σ ρ τ n) :
    MemOKS σ ρ τ (n + 1) := fun m hn hf => match m, hn, hf with
  | .app0 .memory, hn, _ => by
    obtain ⟨μ, B, hr, hh⟩ := h.mem
    refine ⟨ρ.sym.mem, .lit (.bool true), rfl, fun _ => ⟨τ.globE, rfl⟩, fun μ' hμ' => ?_⟩
    cases hμ'
    exact ⟨⟨_, rfl⟩, μ, B, hr, hh, by rw [LMem.births_of_run hr]; exact List.prefix_refl B⟩
  | .app1 (.addM R) _ m, hn, hf => by
    simp only [Tm.inLSM, Op1.inL, Bool.and_eq_true] at hf
    obtain ⟨hm, hs⟩ := hf
    obtain ⟨M, g, hM, hmr, hme⟩ := hM m (by lsizeS_tac) hm
    simp only [hM, Op1.toL, Option.bind_some] at hs
    have hR : allocOk R = true := by
      cases hR : allocOk R
      · simp only [hR, Bool.false_eq_true, ↓reduceIte, Option.isSome_none] at hs
      · rfl
    have hev : ∀ ho : (Op1.addM R).named = false, (Tm.app1 (.addM R) ho m).evalE τ =
        m.evalE τ >>= fun τ' => allocDefault τ' R >>= fun r => .ok r.1 := fun _ => rfl
    refine ⟨.addM M M.nAlloc R, g, by
      simp only [Tm.toLSM, Op1.toL, hM, Option.bind_some, hR, ↓reduceIte], fun hg => ?_,
      fun μ' hμ' => ?_⟩
    · obtain ⟨μ₀', hμ₀'⟩ := hmr hg
      obtain ⟨τ₁, id, ha⟩ := allocDefault_ok hR μ₀'
      exact ⟨τ₁, by rw [hev, hμ₀', Res.ok_bind, ha]; rfl⟩
    · rw [hev] at hμ'
      obtain ⟨μ₀', hμ₀', hμ'⟩ := Res.bind_eq_ok.1 hμ'
      obtain ⟨hg, μ, B, hrun, hh, hp⟩ := hme μ₀' hμ₀'
      obtain ⟨r, ha', hμ'⟩ := Res.bind_eq_ok.1 hμ'
      cases hμ'
      rcases (allocDefault_heap hh R).cases with ⟨e, -, h₂⟩ | ⟨t₁, t₂, id, h₁, h₂, ht⟩
      · rw [h₂] at ha'; cases ha'
      · rw [h₂] at ha'; cases ha'
        refine ⟨hg, t₁, B ++ [MemNames.Birth.ofCopy μ t₁ id], ?_, ht,
          hp.trans (List.prefix_append _ _)⟩
        simp only [LMem.run, hrun, Res.ok_bind, LMem.run_nAlloc σ M hrun, ↓reduceIte, h₁]
  | .app2 .copySt m v, hn, hf => by
    simp only [Tm.inLSM, Op2.inLS, Bool.and_eq_true] at hf
    obtain ⟨⟨hm, hv⟩, hs⟩ := hf
    obtain ⟨M, g, hMm, hmr, hme⟩ := hM m (by lsizeS_tac) hm
    have hev : (Tm.app2 .copySt m v).evalE τ =
        v.evalE τ >>= fun sv => m.evalE τ >>= fun τ' => copyStToM τ' sv >>= fun r => .ok r.1 := rfl
    match v, hv, hs with
    | .app1 .sval _ _, _, hs | .app2 .sfind _ _, _, hs =>
      simp only [Tm.toLSM, Op1.toL, Op2.toLAtS, Op2.toL, hMm, newM, Option.isSome_none,
        Bool.false_eq_true] at hs
    | .app2 .copyMem _ _, _, hs =>
      simp only [Tm.toLSM, Op2.toLAtS, Op2.toL, newM_memL, Option.isSome_none,
        Bool.false_eq_true] at hs
    | .app1 (.newArr R) _ nt, hv, hs =>
      simp only [Tm.inLSM, Op1.inL] at hv
      have hnt := hT nt (by lsizeS_tac) hv
      simp only [Tm.toLSM, Op1.toL, hMm, newM] at hs
      have hR : allocOk R = true := by
        cases hR : allocOk R
        · simp only [hR, Bool.false_eq_true, ↓reduceIte, Option.isSome_none] at hs
        · rfl
      refine ⟨.newArr M M.nAlloc R (nt.toLSM ρ), seqL g (isIntL (nt.toLSM ρ)), by
        simp only [Tm.toLSM, Op2.toLAtS, Op2.toL, Op1.toL, hMm, newM, hR, ↓reduceIte],
        fun hgg => ?_, fun μ' hμ' => ?_⟩
      · obtain ⟨hg, hi⟩ := (seqL_rets σ _ _).1 hgg
        obtain ⟨c, hc⟩ := (isIntL_ret σ _).1 hi
        obtain ⟨μ₀', hμ₀'⟩ := hmr hg
        obtain ⟨⟨τ₁, mv⟩, hcp⟩ := (allocOk_newArr hR c).1.at μ₀'
        refine ⟨τ₁, ?_⟩
        rw [hev, (newArrS_eval_ok.2 ⟨c, (hnt _).1 hc, rfl⟩), Res.ok_bind,
          hμ₀', Res.ok_bind, hcp]
        rfl
      · rw [hev] at hμ'
        obtain ⟨sv, hsv, hμ'⟩ := Res.bind_eq_ok.1 hμ'
        obtain ⟨μ₀', hμ₀', hμ'⟩ := Res.bind_eq_ok.1 hμ'
        obtain ⟨r, hcp, hμ'⟩ := Res.bind_eq_ok.1 hμ'
        cases hμ'
        obtain ⟨c, hc, rfl⟩ := newArrS_eval_ok.1 hsv
        obtain ⟨hg, μ, B, hrun, hh, hp⟩ := hme μ₀' hμ₀'
        have hc' : (nt.toLSM ρ).eval σ = .ok (.int c) := (hnt _).2 hc
        rcases (copyStToM_heap hh (newArrVal R c)).cases with ⟨e, -, h₂⟩ |
          ⟨t₁, t₂, mv, h₁, h₂, ht⟩
        · rw [h₂] at hcp; cases hcp
        · rw [h₂] at hcp; cases hcp
          obtain ⟨id, rfl⟩ := copy_ref h₁ (allocOk_newArr hR c).2
          refine ⟨(seqL_rets σ _ _).2 ⟨hg, (isIntL_ret σ _).2 ⟨c, hc'⟩⟩, t₁,
            B ++ [MemNames.Birth.ofCopy μ t₁ id], ?_, ht, hp.trans (List.prefix_append _ _)⟩
          simp only [LMem.run, hc', Res.ok_bind, Value.asInt, hrun, LMem.run_nAlloc σ M hrun,
            ↓reduceIte, h₁, MVal.asRef]
          rfl
  | .app3 .write m a v, hn, hf => by
    simp only [Tm.inLSM, Op3.inLS, Bool.and_eq_true] at hf
    obtain ⟨⟨⟨hm, ha⟩, hv⟩, hs⟩ := hf
    obtain ⟨M, g, hM, hmr, hme⟩ := hM m (by lsizeS_tac) hm
    obtain ⟨j, sel, g', hA, har, hae⟩ := hA a (by lsizeS_tac) ha
    obtain ⟨w, gv, hw, hvr, hve⟩ := writeValS_ok h hV (by lsizeS_tac) hM hv
    simp only [hM, hA, hw, writeM, Option.isSome_map] at hs
    obtain ⟨gw, hgw⟩ := Option.isSome_iff_exists.1 hs
    have hev : (Tm.app3 .write m a v).evalE τ = v.evalE τ >>= fun mv => m.evalE τ >>= fun τ' =>
        a.evalE τ >>= fun addr => writeAddr τ' mv addr := rfl
    refine ⟨.write M j sel w, seqL gv (seqL g (seqL g' gw)), by
      simp only [Tm.toLSM, Op3.toLAtS, hM, hA, hw, writeM, hgw, Option.map_some],
      fun hgg => ?_, fun μ' hμ' => ?_⟩
    · obtain ⟨hgv, hgg⟩ := (seqL_rets σ _ _).1 hgg
      obtain ⟨hg, hgg⟩ := (seqL_rets σ _ _).1 hgg
      obtain ⟨hg', hgw'⟩ := (seqL_rets σ _ _).1 hgg
      obtain ⟨mv, hmv⟩ := hvr hgv
      obtain ⟨μ₀', hμ₀'⟩ := hmr hg
      obtain ⟨-, μ, B, hrun, hh, hp⟩ := hme μ₀' hμ₀'
      obtain ⟨ad, had⟩ := har hg'
      obtain ⟨-, n0, hn0, hsa⟩ := hae ad had
      obtain ⟨n1, ad1, μ₁, hn1, hsa1, hwr⟩ := (LMem.writeG_sim σ hrun j sel hgw mv).1 hgw'
      rw [LId.evalR_prefix hp hn0, Except.ok.injEq] at hn1
      subst hn1
      rw [hsa, Except.ok.injEq] at hsa1
      subst hsa1
      rcases Res.memPart_cases (writeAddr_of_heap hh mv ad) with ⟨e, h₁, -⟩ |
        ⟨μ₂, μ₃, -, h₂, -⟩
      · rw [hwr] at h₁; cases h₁
      · exact ⟨μ₃, by rw [hev, hmv, Res.ok_bind, hμ₀', Res.ok_bind, had, Res.ok_bind, h₂]⟩
    · rw [hev] at hμ'
      obtain ⟨mv, hmv, hμ'⟩ := Res.bind_eq_ok.1 hμ'
      obtain ⟨μ₀', hμ₀', hμ'⟩ := Res.bind_eq_ok.1 hμ'
      obtain ⟨ad, had, hμ'⟩ := Res.bind_eq_ok.1 hμ'
      obtain ⟨hgv, hwv⟩ := hve mv hmv
      obtain ⟨hg, μ, B, hrun, hh, hp⟩ := hme μ₀' hμ₀'
      obtain ⟨hg', n0, hn0, hsa⟩ := hae ad had
      have hn0' := LId.evalR_prefix hp hn0
      rcases Res.memPart_cases (writeAddr_of_heap hh mv ad) with ⟨e, -, h₂⟩ |
        ⟨μ₂, μ₃, h₁, h₂, hh₂⟩
      · rw [h₂] at hμ'; cases hμ'
      · rw [h₂] at hμ'; cases hμ'
        refine ⟨(seqL_rets σ _ _).2 ⟨hgv, (seqL_rets σ _ _).2 ⟨hg, (seqL_rets σ _ _).2
          ⟨hg', (LMem.writeG_sim σ hrun j sel hgw mv).2 ⟨n0, ad, μ₂, hn0', hsa, h₁⟩⟩⟩⟩,
          μ₂, B, ?_, hh₂, hp⟩
        simp only [LMem.run, hrun, Res.ok_bind, hn0', hsa, hwv μ B hrun hp, h₁]

/-- **A memory value, pushed in**: what the slot holds. -/
theorem MValOKS.step (_h : RelT σ ρ τ) {n : Nat}
    (hT : TermOKS σ ρ τ n) (_hP : PathOKS σ ρ τ n) (hI : IdOKS σ ρ τ n)
    (_hA : AddrOKS σ ρ τ n) (_hM : MemOKS σ ρ τ n) (_hV : MValOKS σ ρ τ n) :
    MValOKS σ ρ τ (n + 1) := fun v hn hf => match v, hn, hf with
  | .app1 .mval _ t, hn, hf => by
    simp only [Tm.inLSM, Op1.inL] at hf
    have ht := hT t (by lsizeS_tac) hf
    have hev : ∀ ho : Op1.mval.named = false, (Tm.app1 .mval ho t).evalE τ =
        t.evalE τ >>= fun v => .ok v.toMVal := fun _ => rfl
    refine ⟨.word (t.toLSM ρ), t.toLSM ρ, by simp only [Tm.toLSM, Op1.toL], fun ⟨w, hw⟩ => ?_,
      fun mv hmv => ?_⟩
    · exact ⟨_, by rw [hev, (ht w).1 hw, Res.ok_bind]⟩
    · rw [hev] at hmv
      obtain ⟨w, hw, hmv⟩ := Res.bind_eq_ok.1 hmv
      cases hmv
      have hw' := (ht w).2 hw
      exact ⟨⟨w, hw'⟩, by simp only [LMV.eval, hw', Res.ok_bind]⟩
  | .app1 .ref _ i, hn, hf => by
    simp only [Tm.inLSM, Op1.inL] at hf
    obtain ⟨j, g, hI, hir, hie⟩ := hI i (by lsizeS_tac) hf
    have hev : ∀ ho : Op1.ref.named = false, (Tm.app1 .ref ho i).evalE τ =
        i.evalE τ >>= fun id => .ok (.ref id) := fun _ => rfl
    refine ⟨.ref j, g, by simp only [Tm.toLSM, Op1.toL, hI, Option.map_some], fun hg => ?_,
      fun mv hmv => ?_⟩
    · obtain ⟨id, hid⟩ := hir hg
      exact ⟨_, by rw [hev, hid, Res.ok_bind]⟩
    · rw [hev] at hmv
      obtain ⟨id, hid, hmv⟩ := Res.bind_eq_ok.1 hmv
      cases hmv
      obtain ⟨hg, hj⟩ := hie id hid
      exact ⟨hg, by simp only [LMV.eval, hj, Res.ok_bind]⟩

/-- All six at every size. -/
theorem RelU.all_ok (h : RelT σ ρ τ) : (n : Nat) →
    TermOKS σ ρ τ n ∧ PathOKS σ ρ τ n ∧ IdOKS σ ρ τ n ∧ AddrOKS σ ρ τ n ∧
      MemOKS σ ρ τ n ∧ MValOKS σ ρ τ n
  | 0 => ⟨fun _ hn => absurd hn (Nat.not_lt_zero _), fun _ hn => absurd hn (Nat.not_lt_zero _),
      fun _ hn => absurd hn (Nat.not_lt_zero _), fun _ hn => absurd hn (Nat.not_lt_zero _),
      fun _ hn => absurd hn (Nat.not_lt_zero _), fun _ hn => absurd hn (Nat.not_lt_zero _)⟩
  | n + 1 =>
    have ⟨hT, hP, hI, hA, hM, hV⟩ := RelU.all_ok h n
    ⟨TermOKS.step h hT hP hI hA hM hV, PathOKS.step h hT hP hI hA hM hV,
      IdOKS.step h hT hP hI hA hM hV, AddrOKS.step h hT hP hI hA hM hV,
      MemOKS.step h hT hP hI hA hM hV, MValOKS.step h hT hP hI hA hM hV⟩

/-- **A value term reads, pushed in by position, what it reads in `τ`.** -/
theorem RelU.val (h : RelT σ ρ τ) {t : Tm C Γ .val} (hf : t.inLS ρ = true) :
    Sim ((t.toLS ρ).eval σ) (t.evalE τ) := by
  rw [Tm.toLS_eq_toLSM]
  exact (h.all_ok _).1 t (Nat.lt_succ_self _) (by rw [← Tm.inLS_eq_inLSM]; exact hf)

theorem RelU.path (h : RelT σ ρ τ) {p : Tm C Γ .path} (hf : p.inLS ρ = true) (qs : List Seg) :
    (∃ rs, p.evalE τ = .ok rs ∧ qs = .field rs.1 :: rs.2) ↔
      ((p.toLS ρ).eval σ = .ok qs ∧ LiveTo (.struct τ.globE.storage) qs) := by
  rw [Tm.toLS_eq_toLSM]
  exact (h.all_ok _).2.1 p (Nat.lt_succ_self _) (by rw [← Tm.inLS_eq_inLSM]; exact hf) qs

theorem RelU.ident (h : RelT σ ρ τ) {i : Tm C Γ .ident} (hf : i.inLS ρ = true) :
    ∃ j g, i.toLS ρ = some (j, g) ∧ (Rets (g.eval σ) → ∃ id, i.evalE τ = .ok id) ∧
      ∀ id, i.evalE τ = .ok id → Rets (g.eval σ) ∧ LId.evalR (ρ.sym.mem.births σ) j = .ok id := by
  rw [Tm.toLS_eq_toLSM]
  exact (h.all_ok _).2.2.1 i (Nat.lt_succ_self _) (by rw [← Tm.inLS_eq_inLSM]; exact hf)

theorem RelU.memT (h : RelT σ ρ τ) {m : Tm C Γ .mem} (hf : m.inLS ρ = true) :
    ∃ M g, m.toLS ρ = some (M, g) ∧ (Rets (g.eval σ) → ∃ μ', m.evalE τ = .ok μ') ∧
      ∀ μ', m.evalE τ = .ok μ' → Rets (g.eval σ) ∧
        ∃ μ B, M.run σ = .ok (μ, B) ∧ μ.HeapEq μ' ∧ ρ.sym.mem.births σ <+: B := by
  rw [Tm.toLS_eq_toLSM]
  exact (h.all_ok _).2.2.2.2.1 m (Nat.lt_succ_self _) (by rw [← Tm.inLS_eq_inLSM]; exact hf)

theorem RelU.valM (h : RelT σ ρ τ) (t : Tm C Γ .val) (hf : t.inLSM ρ = true) :
    Sim ((t.toLSM ρ).eval σ) (t.evalE τ) :=
  (h.all_ok _).1 t (Nat.lt_succ_self _) hf

theorem RelU.pathM (h : RelT σ ρ τ) (p : Tm C Γ .path) (hf : p.inLSM ρ = true) (qs : List Seg) :
    (∃ rs, p.evalE τ = .ok rs ∧ qs = .field rs.1 :: rs.2) ↔
      ((p.toLSM ρ).eval σ = .ok qs ∧ LiveTo (.struct τ.globE.storage) qs) :=
  (h.all_ok _).2.1 p (Nat.lt_succ_self _) hf qs

theorem RelU.identM (h : RelT σ ρ τ) (i : Tm C Γ .ident) (hf : i.inLSM ρ = true) :
    ∃ j g, i.toLSM ρ = some (j, g) ∧ (Rets (g.eval σ) → ∃ id, i.evalE τ = .ok id) ∧
      ∀ id, i.evalE τ = .ok id → Rets (g.eval σ) ∧ LId.evalR (ρ.sym.mem.births σ) j = .ok id :=
  (h.all_ok _).2.2.1 i (Nat.lt_succ_self _) hf

theorem RelU.memM (h : RelT σ ρ τ) (m : Tm C Γ .mem) (hf : m.inLSM ρ = true) :
    ∃ M g, m.toLSM ρ = some (M, g) ∧ (Rets (g.eval σ) → ∃ μ', m.evalE τ = .ok μ') ∧
      ∀ μ', m.evalE τ = .ok μ' → Rets (g.eval σ) ∧
        ∃ μ B, M.run σ = .ok (μ, B) ∧ μ.HeapEq μ' ∧ ρ.sym.mem.births σ <+: B :=
  (h.all_ok _).2.2.2.2.1 m (Nat.lt_succ_self _) hf

theorem find_rootS (τ : State C Γ) (r : Name) (segs : List Seg) :
    (Semantics.SVal.struct τ.globE.storage).find (.field r :: segs) = τ.globE.findStorage r segs :=
  find_root τ.globE r segs

theorem save_rootS (τ : State C Γ) (r : Name) (segs : List Seg) (new : Semantics.SVal) :
    (Semantics.SVal.struct τ.globE.storage).save (.field r :: segs) new =
      τ.globE.saveStorage r segs new >>= fun τ' => .ok (.struct τ'.storage) :=
  save_root τ.globE r segs new

/-- **A storage term, pushed in, is the write it made.** -/
theorem RelU.stor_eval (h : RelT σ ρ τ) :
    (s : Tm C Γ .st) → s.inLSM ρ = true →
      Sim ((s.toLSM ρ).eval σ) (s.evalE τ >>= fun τ' => .ok (.struct τ'.storage))
  | .app0 .storage, _ => Sim.of_eq (by
      simp only [Tm.toLSM, Op0.toL, h.stor, Tm.eval, Op0.eval, pure, Except.pure, Res.ok_bind])
  | .app3 .save s p v, hf => by
    simp only [Tm.inLSM, Op3.inLS, Bool.and_eq_true] at hf
    obtain ⟨⟨⟨hs, hp⟩, hv⟩, hz⟩ := hf
    obtain rfl := isStorageS_st hs
    match v, hv, hz with
    | .app1 .sval ho t, hv, _ =>
      have ht := h.valM t hv
      have hb := live_bridge (τ := τ.globE) (h.pathM p hp)
      rw [evalS_save]
      simp only [Tm.toLSM, Op0.toL, Op1.toL, Op3.toLAtS, Op3.toL, LStor.eval, h.stor, Res.ok_bind,
          Tm.eval, Op0.eval, pure, Except.pure]
      intro a
      simp only [Res.bind_eq_ok]
      constructor
      · rintro ⟨x, hx, qs, hq, ha⟩
        obtain ⟨c, hc⟩ := findLive_of_saveLive ha
        obtain ⟨rs, hrs, rfl, hfs⟩ := (hb qs c).1 ⟨hq, hc⟩
        rw [saveLive_eq_save _ hc, save_rootS] at ha
        obtain ⟨τ'', h'', he⟩ := Res.bind_eq_ok.1 ha
        exact ⟨τ'', ⟨x, (ht x).1 hx, rs, hrs, h''⟩, he⟩
      · rintro ⟨τ'', ⟨x, hx, rs, hrs, h''⟩, he⟩
        have hsv : (Semantics.SVal.struct τ.globE.storage).save (.field rs.1 :: rs.2) x.toSVal =
            .ok a := by
          rw [save_rootS, h'', Res.ok_bind, he]
        obtain ⟨c, hc⟩ := find_of_save hsv
        rw [find_rootS] at hc
        obtain ⟨hq, hl⟩ := (hb _ c).2 ⟨rs, hrs, rfl, hc⟩
        exact ⟨x, (ht x).2 hx, _, hq, by rw [saveLive_eq_save (v := .struct τ.globE.storage) _ hl]; exact hsv⟩
    | .app2 .sfind s' p', hv, _ =>
      simp only [Tm.inLSM, Op2.inLS, Bool.and_eq_true] at hv
      obtain ⟨hs', hp'⟩ := hv
      obtain rfl := isStorageS_st hs'
      have hb := live_bridge (τ := τ.globE) (h.pathM p hp)
      have hb' := live_bridge (τ := τ.globE) (h.pathM p' hp')
      rw [evalS_save_find]
      simp only [Tm.toLSM, Op0.toL, Op2.toLAtS, Op2.toL, Op3.toLAtS, Op3.toL, LStor.eval, h.stor,
        Res.ok_bind, Tm.eval, Op0.eval, Op2.eval, pure, Except.pure, bind_assoc]
      exact read_bridge hb' fun n => write_bridge hb fun c => .ok (c.overlay n)
    | .app1 (.newArr _) _ _, _, hz =>
      simp only [Tm.toLSM, Op1.toL, LVal.storable, Bool.false_eq_true] at hz
    | .app2 .copyMem m i, hv, _ =>
      simp only [Tm.inLSM, Op2.inLS, Bool.and_eq_true] at hv
      obtain ⟨⟨hm, hi⟩, hl⟩ := hv
      obtain ⟨M, g, hMm, hmr, hme⟩ := h.memM m hm
      obtain ⟨j, g', hIi, hir, hie⟩ := h.identM i hi
      rw [hMm, hIi] at hl
      obtain ⟨⟨c, rfl⟩, c', rfl⟩ := memL_some hl
      have hb := live_bridge (τ := τ.globE) (h.pathM p hp)
      have hsrc : Sim (LMem.run σ M >>= fun r => LId.evalR r.2 j >>= fun n => copyMem r.1 (.ref n))
          ((Tm.app2 .copyMem m i).evalE τ) := by
        show Sim _ (m.evalE τ >>= fun τ' => i.evalE τ >>= fun id => copyMem τ' (.ref id))
        obtain ⟨μ', hm'⟩ := hmr ⟨c, rfl⟩
        obtain ⟨id, hi'⟩ := hir ⟨c', rfl⟩
        obtain ⟨-, μ, B, hr, hheq, hpre⟩ := hme μ' hm'
        have hj : LId.evalR B j = .ok id := LId.evalR_prefix hpre (hie id hi').2
        simp only [hr, hm', hi', hj, Res.ok_bind, copyMem_of_heap hheq.1]
        exact Sim.refl _
      rw [evalS_save_copyMem]
      simp only [Tm.toLSM, Op0.toL, Op2.toLAtS, Op2.toL, Op3.toLAtS, Op3.toL, hMm, hIi, memL,
        Option.getD_some, LStor.eval, h.stor, Res.ok_bind, Tm.eval, Op0.eval, pure, Except.pure,
        LPath.eval]
      simp only [bind_assoc, Res.ok_bind, view_findLive, SVal.findLive_nil]
      have key := Sim.bind hsrc fun n => write_bridge (τ := τ.globE) hb fun c => .ok (c.overlay n)
      simp only [bind_assoc, Res.ok_bind] at key
      exact key
  | .app2 .delAt s p, hf => by
    simp only [Tm.inLSM, Op2.inLS, Bool.and_eq_true] at hf
    obtain ⟨hs, hf⟩ := hf
    obtain rfl := isStorageS_st hs
    have hb := live_bridge (τ := τ.globE) (h.pathM p hf)
    simp only [Tm.toLSM, Op0.toL, Op2.toLAtS, Op2.toL, LStor.eval, h.stor, Res.ok_bind,
        Tm.eval, Op0.eval, Op2.eval, pure, Except.pure]
    intro a
    simp only [Res.bind_eq_ok]
    constructor
    · rintro ⟨qs, hq, c, hc, ha⟩
      obtain ⟨rs, hrs, rfl, hfs⟩ := (hb qs c).1 ⟨hq, hc⟩
      rw [saveLive_eq_save _ hc, save_rootS] at ha
      obtain ⟨τ'', h'', he⟩ := Res.bind_eq_ok.1 ha
      exact ⟨τ'', ⟨rs, hrs, c, hfs, h''⟩, he⟩
    · rintro ⟨τ'', ⟨rs, hrs, c, hfs, h''⟩, he⟩
      obtain ⟨hq, hl⟩ := (hb _ c).2 ⟨rs, hrs, rfl, hfs⟩
      refine ⟨_, hq, c, hl, ?_⟩
      rw [saveLive_eq_save (v := .struct τ.globE.storage) _ hl, save_rootS, h'', Res.ok_bind, he]
  | .pvS _, hf => by simp only [Tm.inLSM, Bool.false_eq_true] at hf
  | .app3 .push s p v, hf => by
    match v, hf with
    | .app1 .sval _ t, hf =>
      simp only [Tm.inLSM, Op3.inLS, Op1.inL, Bool.and_eq_true] at hf
      obtain ⟨⟨hs, hp⟩, ht⟩ := hf
      obtain rfl := isStorageS_st hs
      have hb := live_bridge (τ := τ.globE) (h.pathM p hp)
      have htt := h.valM t ht
      rw [evalS_push]
      simp only [Tm.toLSM, Op0.toL, Op1.toL, Op3.toLAtS, Op3.toL, LStor.eval, h.stor,
        Res.ok_bind, Tm.eval, Op0.eval, pure, Except.pure, bind_assoc]
      cases hx : t.evalE τ with
      | ok x =>
        rw [(htt x).2 hx, Res.ok_bind]
        simp only [Op1.eval, pure, Except.pure, Res.ok_bind]
        have hval : (fun _ : Semantics.SVal => (Except.ok x.toSVal.strip : Res Semantics.SVal)) =
            fun _ => .ok x.toSVal := by
          funext _; cases x <;> rfl
        rw [hval]
        simp only [pushOn_word, bind_assoc]
        exact write_bridge hb _
      | error e =>
        refine Sim.halt (fun a ha => ?_) (fun a ha => ?_)
        · obtain ⟨y, hy, -⟩ := Res.bind_eq_ok.1 ha
          have := (htt y).1 hy
          rw [hx] at this; cases this
        · obtain ⟨rs, -, ha⟩ := Res.bind_eq_ok.1 ha
          obtain ⟨c, -, ha⟩ := Res.bind_eq_ok.1 ha
          obtain ⟨τ', hτ', -⟩ := Res.bind_eq_ok.1 ha
          cases c with
          | array es sh fx =>
            simp only [Close.pushOn_array] at hτ'
            cases hτ'
          | prim _ | struct _ | map _ _ => cases hτ'
    | .app2 .sfind s' p', hf =>
      simp only [Tm.inLSM, Op3.inLS, Op2.inLS, Bool.and_eq_true] at hf
      obtain ⟨⟨hs, hp⟩, hs', hp'⟩ := hf
      obtain rfl := isStorageS_st hs
      obtain rfl := isStorageS_st hs'
      rw [evalS_push]
      simp only [Tm.toLSM, Op0.toL, Op2.toLAtS, Op2.toL, Op3.toLAtS, Op3.toL, Tm.eval, Op0.eval,
        Op2.eval, pure, Except.pure, Res.ok_bind, bind_assoc]
      exact pushCopy_bridge (τ := τ.globE) h.stor (live_bridge (h.pathM p hp))
        (live_bridge (h.pathM p' hp'))
    | .app1 (.newArr _) _ _, hf | .app2 .copyMem _ _, hf =>
      simp only [Tm.inLSM, Op3.inLS, Bool.false_eq_true] at hf
  | .app1 (.select _) _ _, hf => by simp only [Tm.inLSM, Op1.inL, Bool.false_eq_true] at hf
  | .app2 (.pushSlot E) s p, hf | .app2 (.extend E) s p, hf => by
    simp only [Tm.inLSM, Op2.inLS, Bool.and_eq_true] at hf
    obtain ⟨hs, hp⟩ := hf
    obtain rfl := isStorageS_st hs
    have hb := live_bridge (τ := τ.globE) (h.pathM p hp)
    first
      | rw [evalS_pushSlot]
      | rw [evalS_extend]
    simp only [pushOn_slot _ E _ _ (.bool true)]
    simp only [Tm.toLSM, Op0.toL, Op2.toLAtS, Op2.toL, LStor.eval, LTerm.eval, h.stor, Res.ok_bind,
      Tm.eval, Op0.eval, pure, Except.pure, bind_assoc]
    exact write_bridge hb _
  | .app2 .pop s p, hf | .app2 .shrink s p, hf => by
    simp only [Tm.inLSM, Op2.inLS, Bool.and_eq_true] at hf
    obtain ⟨hs, hp⟩ := hf
    obtain rfl := isStorageS_st hs
    have hb := live_bridge (τ := τ.globE) (h.pathM p hp)
    first
      | rw [Tm.evalE_pop]
      | rw [Tm.evalE_shrink]
    simp only [popOn_pop _ _ _ _ (.bool true)]
    simp only [Tm.toLSM, Op0.toL, Op2.toLAtS, Op2.toL, LStor.eval, LTerm.eval, h.stor, Res.ok_bind,
      Tm.eval, Op0.eval, pure, Except.pure, bind_assoc]
    exact write_bridge hb _

/-- A stale alias's slot-level path reads as the path the alias holds, and
so do its members. -/
theorem RelU.slotPath_eval (h : RelT σ ρ τ) : (p : Tm C Γ .path) → (q : LPath) →
    p.slotPathS ρ = some q → ∃ r segs, q.eval σ = .ok (.field r :: segs) ∧ p.evalE τ = .ok (r, segs)
  | .pvP i, q, hq => by
    simp only [Tm.slotPathS, Idx.toNatR_eq] at hq
    split at hq
    · rename_i q' hl
      cases hq
      obtain ⟨r, segs, h₁, h₂⟩ := h.getB i _ hl
      refine ⟨r, segs, h₁, ?_⟩
      revert h₂
      simp only [Tm.eval, State.aliasPathT_getE]
      cases τ.getE i with
      | none => simp only [LTy.enc, reduceCtorEq, false_implies]
      | some p => simp only [LTy.enc, Binding.spath.injEq]; rintro ⟨rfl, rfl⟩; rfl
    · cases hq
  | .app1 (.field f) _ p, q, hq => by
    simp only [Tm.slotPathS, Option.map_eq_some_iff] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    obtain ⟨r, segs, h₁, h₂⟩ := RelU.slotPath_eval h p q' hq'
    refine ⟨r, segs ++ [.field f], ?_, ?_⟩
    · simp only [LPath.eval, h₁, Res.ok_bind, List.cons_append]
    · show (p.evalE τ >>= fun rs => .ok (rs.1, rs.2 ++ [.field f])) = _
      rw [h₂]
      rfl
  | .app0 _, _, hq | .app1 .next _ _, _, hq | .app2 .at _ _, _, hq
  | .app2 .nextIn _ _, _, hq | .app3 .atIn _ _ _, _, hq => by
    simp only [Tm.slotPathS, reduceCtorEq] at hq

/-- What `staleWriteS` recognises: a word written or pushed at an alias's
slot-level path. -/
theorem staleWriteS_some {s : Tm C Γ .st} {op : Option AOp} {q : LPath} {t : Tm C Γ .val}
    (hw : s.staleWriteS ρ = some (op, q, t)) : ∃ p : Tm C Γ .path, p.slotPathS ρ = some q ∧
      ((op = none ∧ s = .app3 .save (.app0 .storage) p (.app1 .sval rfl t)) ∨
        (op = some .push ∧ s = .app3 .push (.app0 .storage) p (.app1 .sval rfl t))) := by
  unfold Tm.staleWriteS at hw
  split at hw
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hw
    obtain ⟨q', hq, rfl, rfl, rfl⟩ := hw
    exact ⟨_, hq, .inl ⟨rfl, rfl⟩⟩
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hw
    obtain ⟨q', hq, rfl, rfl, rfl⟩ := hw
    exact ⟨_, hq, .inr ⟨rfl, rfl⟩⟩
  · cases hw

/-- **A write through a stale alias**: the slot-level write at the path it
holds, live or not (`stale_write_bridge`). -/
theorem RelU.stale_write (h : RelT σ ρ τ) {p : Tm C Γ .path} {q : LPath}
    (hq : p.slotPathS ρ = some q) (t : Tm C Γ .val) (ht : t.inLS ρ = true) :
    Sim ((LStor.stale none ρ.sym.stor q (t.toLS ρ)).eval σ)
      ((Tm.app3 .save (.app0 .storage) p (.app1 .sval rfl t)).evalE τ >>= fun τ' =>
        .ok (.struct τ'.storage)) := by
  obtain ⟨r, segs, h₁, h₂⟩ := RelU.slotPath_eval h p q hq
  rw [evalS_save]
  simp only [LStor.eval, h.stor, h₁, Res.ok_bind, staleSave, Tm.eval, Op0.eval, pure, Except.pure,
    h₂, bind_assoc, save_rootS]
  exact Sim.bind (h.val ht) fun _ => Sim.refl _

/-- **A push through a stale alias** (`stale_push_bridge`). -/
theorem RelU.stale_push (h : RelT σ ρ τ) {p : Tm C Γ .path} {q : LPath}
    (hq : p.slotPathS ρ = some q) (t : Tm C Γ .val) (ht : t.inLS ρ = true) :
    Sim ((LStor.stale (some .push) ρ.sym.stor q (t.toLS ρ)).eval σ)
      ((Tm.app3 .push (.app0 .storage) p (.app1 .sval rfl t)).evalE τ >>= fun τ' =>
        .ok (.struct τ'.storage)) := by
  obtain ⟨r, segs, h₁, h₂⟩ := RelU.slotPath_eval h p q hq
  have htt := h.val ht
  rw [evalS_push]
  simp only [LStor.eval, h.stor, h₁, Res.ok_bind, staleSave, Tm.eval, Op0.eval, pure, Except.pure,
    h₂, bind_assoc]
  cases hx : t.evalE τ with
  | ok x =>
    rw [(htt x).2 hx, Res.ok_bind]
    simp only [Op1.eval, pure, Except.pure, Res.ok_bind]
    have hval : (fun _ : Semantics.SVal => (Except.ok x.toSVal.strip : Res Semantics.SVal)) =
        fun _ => .ok x.toSVal := by
      funext _; cases x <;> rfl
    rw [hval]
    simp only [pushOn_word, bind_assoc, find_rootS, save_rootS]
    exact Sim.refl _
  | error e =>
    refine Sim.halt (fun a ha => ?_) (fun a ha => ?_)
    · obtain ⟨y, hy, -⟩ := Res.bind_eq_ok.1 ha
      have := (htt y).1 hy
      rw [hx] at this; cases this
    · obtain ⟨c, -, ha⟩ := Res.bind_eq_ok.1 ha
      obtain ⟨τ', hτ', -⟩ := Res.bind_eq_ok.1 ha
      cases c with
      | array es sh fx =>
        simp only [Close.pushOn_array] at hτ'
        cases hτ'
      | prim _ | struct _ | map _ _ => cases hτ'

/-- **A storage update, pushed in by `toLSt`, is the write it made**:
through a stale alias at the slot level, otherwise as `RelU.stor_eval`
says. -/
theorem RelU.storT (h : RelT σ ρ τ) (s : Tm C Γ .st) (hf : s.inLSt ρ = true) :
    Sim ((s.toLSt ρ).eval σ) (s.evalE τ >>= fun τ' => .ok (.struct τ'.storage)) := by
  unfold Tm.toLSt
  unfold Tm.inLSt at hf
  cases hw : s.staleWriteS ρ with
  | none =>
    simp only [hw] at hf ⊢
    rw [Tm.toLS_eq_toLSM]
    exact RelU.stor_eval h s (by rw [← Tm.inLS_eq_inLSM]; exact hf)
  | some w =>
    obtain ⟨op, q, t⟩ := w
    simp only [hw] at hf ⊢
    obtain ⟨p, hq, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := staleWriteS_some hw
    · exact RelU.stale_write h hq t hf
    · exact RelU.stale_push h hq t hf

end Terms

/-! ## The relation through binders, pops and writes -/

section Steps

variable {Γ : Ctx} {σ : Semantics.State} {ρ : SymS} {B : MemNames.Births}

theorem slotVar_inj {m n : Nat} (h : slotVar m = slotVar n) : m = n := by
  simp only [slotVar, Var.fresh.injEq, true_and] at h
  exact h

theorem RelB.key_fresh {g : Semantics.State} {ℓ : Locs C Γ} (h : RelB σ ρ B g ℓ) :
    ρ.key ∉ ρ.names ∧ lookupBy ρ.key ρ.sym.env = none :=
  h.fresh ρ.next (Nat.le_refl _)

/-- A scope's locals popped. -/
theorem RelB.pop {Γ' : Ctx} {g : Semantics.State} {ℓ : Locs C Γ'} (h : RelB σ ρ B g ℓ)
    (hx : Ext Γ Γ') : RelB σ ⟨ρ.loc.drop hx.depth, ρ.sym, ρ.next⟩ B g (ℓ.drop hx) := by
  have hn : SymS.names ⟨ρ.loc.drop hx.depth, ρ.sym, ρ.next⟩ = ρ.names.drop hx.depth := by
    simp only [SymS.names, List.map_drop]
  have hok := h.ok
  unfold SymS.Ok at hok
  have hl : (ρ.names.take hx.depth).length = hx.depth := by
    have := hx.length_eq
    rw [List.length_take, h.len]; omega
  refine ⟨?_, ?_, ?_, fun m hm => ?_, h.stor, fun m hm b hb => ?_, h.tx⟩
  · unfold SymS.Ok
    rw [hn]
    show ρ.loc.drop hx.depth = _
    rw [hok, List.map_drop]
  · have := hx.length_eq
    rw [hn, List.length_drop, h.len]; omega
  · rw [hn]; exact h.nodup.sublist (List.drop_sublist _ _)
  · rw [hn]
    exact ⟨fun hm' => (h.fresh m hm).1 (List.mem_of_mem_drop hm'), (h.fresh m hm).2⟩
  · rw [hn] at hm
    have hm' := Locs.mem_erase_drop hx (ρ.names.take hx.depth) (ρ.names.drop hx.depth) ℓ hl
      m hm
    rw [List.take_append_drop] at hm'
    exact h.env m hm' b hb

/-- A frame dropped from under what it keeps. -/
theorem RelB.thin {Γ' : Ctx} {g : Semantics.State} {ℓ : Locs C Γ'} (h : RelB σ ρ B g ℓ)
    (hx : Thin Γ Γ') : RelB σ ⟨Thin.sel hx ρ.loc, ρ.sym, ρ.next⟩ B g (ℓ.thin hx) := by
  have hn : SymS.names ⟨Thin.sel hx ρ.loc, ρ.sym, ρ.next⟩ = hx.names ρ.names := by
    simp only [SymS.names, ← Thin.sel_map, Thin.sel_eq_names]
  have hok := h.ok
  unfold SymS.Ok at hok
  refine ⟨?_, ?_, ?_, fun m hm => ?_, h.stor, fun m hm b hb => ?_, h.tx⟩
  · unfold SymS.Ok
    rw [hn]
    show Thin.sel hx ρ.loc = _
    rw [hok, Thin.sel_map, Thin.sel_eq_names]
  · rw [hn]; exact Thin.names_length hx _ h.len
  · rw [hn]; exact (Thin.names_sublist hx _).nodup h.nodup
  · rw [hn]
    exact ⟨fun hm' => (h.fresh m hm).1 ((Thin.names_sublist hx _).subset hm'), (h.fresh m hm).2⟩
  · rw [hn] at hm
    exact h.env m (Locs.mem_erase_thin hx _ ℓ h.len m hm) b hb

/-- A local pushed under the next key, bound by the act or to nothing. -/
theorem RelB.push {g : Semantics.State} {ℓ : Locs C Γ} (h : RelB σ ρ B g ℓ) (a : Act)
    (ha : a = .keep ∨ ∃ b, a = .bind b) {t : LTy} (v : t.Denote C)
    (hb : ∀ b, a = .bind b → BindRel σ g.storage B (t.enc C v) b) :
    RelB σ (ρ.push a) B g (ℓ.push v) := by
  obtain ⟨hk, he⟩ := h.key_fresh
  have hn : (ρ.push a).names = ρ.key :: ρ.names := by
    rcases ha with rfl | ⟨b, rfl⟩ <;> simp only [SymS.push, SymS.names, List.map_cons]
  have hnx : (ρ.push a).next = ρ.next + 1 := by
    rcases ha with rfl | ⟨b, rfl⟩ <;> rfl
  have hE : ∀ y, y ≠ ρ.key → lookupBy y (ρ.push a).sym.env = lookupBy y ρ.sym.env := by
    intro y hy
    rcases ha with rfl | ⟨b, rfl⟩
    · rfl
    · simp only [SymS.push, lookupBy, hy, ↓reduceIte]
  have hst : (ρ.push a).sym.stor = ρ.sym.stor := by rcases ha with rfl | ⟨b, rfl⟩ <;> rfl
  refine ⟨?_, ?_, ?_, fun m hm => ?_, by rw [hst]; exact h.stor, fun m hm b' hb' => ?_, h.tx⟩
  · rw [hn]; exact (SymS.push_ok h.ok a ha hk).1
  · rw [hn, List.length_cons, h.len]; rfl
  · rw [hn]; exact List.nodup_cons.2 ⟨hk, h.nodup⟩
  · rw [hnx] at hm
    have hne : slotVar m ≠ ρ.key := fun hq => by
      have := slotVar_inj hq; omega
    rw [hn, hE _ hne]
    refine ⟨fun hm' => ?_, (h.fresh m (by omega)).2⟩
    rcases List.mem_cons.1 hm' with hm' | hm'
    · exact hne hm'
    · exact (h.fresh m (by omega)).1 hm'
  · rw [hn] at hm
    rcases List.mem_cons.1 hm with rfl | hm
    · rcases ha with rfl | ⟨b, rfl⟩
      · simp only [SymS.push, he, reduceCtorEq] at hb'
      · simp only [SymS.push, lookupBy, ↓reduceIte, Option.some.injEq] at hb'
        subst hb'
        exact hb _ rfl
    · have hne : m.1 ≠ ρ.key := fun hq => hk (hq ▸ Locs.mem_erase_key (b := m.2) hm)
      rw [hE _ hne] at hb'
      exact h.env m hm b' hb'

/-- A local set at its position, bound to `b`. -/
theorem RelB.setLocal {g : Semantics.State} {ℓ : Locs C Γ} (h : RelB σ ρ B g ℓ) {t : LTy}
    (i : Idx Γ t) (v : t.Denote C) (b : SymB) (hb : BindRel σ g.storage B (t.enc C v) b) :
    RelB σ (ρ.bindAt i.toNatR b) B g (ℓ.set i v) := by
  have hi : i.toNatR < ρ.names.length := by rw [Idx.toNatR_eq, h.len]; exact i.toNat_lt
  obtain ⟨hok, hsym⟩ := SymS.bindAt_ok h.ok h.nodup hi b
  have hn : (ρ.bindAt i.toNatR b).names = ρ.names := SymS.names_of_ok hok
  have hx : ρ.names.getD i.toNatR (.user "_") = i.name ρ.names := by
    rw [Idx.toNatR_eq]; rfl
  have hmem : i.name ρ.names ∈ ρ.names := Idx.name_mem i _ h.len
  rw [hx] at hsym
  refine ⟨by rw [hn]; exact hok, by rw [hn]; exact h.len, by rw [hn]; exact h.nodup,
    fun m hm => ?_, by rw [hsym]; exact h.stor, fun m hm b' hb' => ?_, h.tx⟩
  · rw [hn, hsym]
    have hne : slotVar m ≠ i.name ρ.names := fun hq => (h.fresh m hm).1 (hq ▸ hmem)
    exact ⟨(h.fresh m hm).1, by simp only [NAct.apply, lookupBy, hne, ↓reduceIte,
      (h.fresh m hm).2]⟩
  · rw [hn] at hm
    rw [hsym] at hb'
    simp only [NAct.apply, lookupBy] at hb'
    rcases Locs.mem_erase_set i v ρ.names ℓ h.len h.nodup m hm with rfl | ⟨hm, hne⟩
    · simp only [↓reduceIte, Option.some.injEq] at hb'
      subst hb'
      exact hb
    · simp only [hne, ↓reduceIte] at hb'
      exact h.env m hm b' hb'

/-- The global part replaced, its storage and the values of the
transaction kept. -/
theorem RelB.withGlob {g₀ : Semantics.State} {ℓ : Locs C Γ} (h : RelB σ ρ B g₀ ℓ)
    (g : Semantics.State) (hs : g.storage = g₀.storage) (ht : ∀ k, g.envVal k = g₀.envVal k) :
    RelB σ ρ B g ℓ :=
  ⟨h.ok, h.len, h.nodup, h.fresh, by have hst := h.stor; rw [← hs] at hst; exact hst,
    fun m hm b hb => by rw [hs]; exact h.env m hm b hb,
    fun k => by rw [← h.tx k, ← ht k]⟩

/-- A storage written: what the positions hold kept, an alias through an
index made stale. -/
theorem RelB.write {g : Semantics.State} {ℓ : Locs C Γ} (h : RelB σ ρ B g ℓ) {S : LStor}
    {st : List (Name × Semantics.SVal)} (hS : S.eval σ = .ok (.struct st)) (n? : Option Nat) :
    RelB σ (ρ.act n? (.write S)) B { g with storage := st } ℓ := by
  have hok := h.ok
  unfold SymS.Ok at hok
  have hn : (ρ.act n? (.write S)).names = ρ.names := by
    simp only [SymS.act, SymS.names, List.map_map, Function.comp_def]
  refine ⟨?_, by rw [hn]; exact h.len, by rw [hn]; exact h.nodup, fun m hm => ?_, hS,
    fun m hm b hb => ?_, fun k => by rw [← h.tx k]; cases k <;> rfl⟩
  · unfold SymS.Ok
    rw [hn]
    simp only [SymS.act, hok, List.map_map, Function.comp_def, lookupBy_map_snd]
  · rw [hn]
    refine ⟨(h.fresh m hm).1, ?_⟩
    simp only [SymS.act, lookupBy_map_snd, (h.fresh m hm).2, Option.map_none]
  · rw [hn] at hm
    simp only [SymS.act, lookupBy_map_snd, Option.map_eq_some_iff] at hb
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    exact (h.env m hm b₀ hb₀).onWrite

/-- A binding's relation holds in a run that allocates more. -/
theorem RelB.grow {g : Semantics.State} {ℓ : Locs C Γ} {B' : MemNames.Births}
    (h : RelB σ ρ B g ℓ) (hp : B <+: B') : RelB σ ρ B' g ℓ :=
  ⟨h.ok, h.len, h.nodup, h.fresh, h.stor, fun m hm b hb => (h.env m hm b hb).grow hp, h.tx⟩

/-- **A memory set**: the run of `M` leaves the heap, and allocates after
the births the positions are read in. -/
theorem RelB.setMem {g₀ : Semantics.State} {ℓ : Locs C Γ} (h : RelB σ ρ B g₀ ℓ) {M : LMem}
    {μ : Semantics.State} {B' : MemNames.Births} (hr : M.run σ = .ok (μ, B')) (hp : B <+: B')
    (n? : Option Nat) {g : Semantics.State} (hh : μ.HeapEq g) :
    RelU σ (ρ.act n? (.mem M)) { g₀ with heap := g.heap, nextId := g.nextId } ℓ := by
  have hB : (ρ.act n? (.mem M)).sym.mem.births σ = B' := by
    show M.births σ = B'
    rw [LMem.births_of_run hr]
  have h' := (h.grow hp).withGlob { g₀ with heap := g.heap, nextId := g.nextId } rfl
    (fun k => by cases k <;> rfl)
  refine ⟨?_, ⟨μ, B', hr, hh⟩⟩
  rw [hB]
  exact ⟨h'.ok, h'.len, h'.nodup, h'.fresh, h'.stor, h'.env, h'.tx⟩

/-- A quantifier's local: the atom of its position, the state read binding
it (`Rel.freePos`, by position). -/
theorem RelU.pushQ {g : Semantics.State} {ℓ : Locs C Γ} (h : RelU σ ρ g ℓ)
    (hx : ρ.sym.vars.contains ρ.key = false) (w : Value) {p : PrimTy} :
    RelU (σ.setEnv ρ.key (.val w)) ρ.pushQ g (ℓ.push (t := .val p) w) := by
  have hx' : ρ.key ∉ ρ.sym.vars := by
    simpa only [List.contains_eq_mem, decide_eq_false_iff_not] using hx
  simp only [Sym.vars, List.mem_append, not_or] at hx'
  obtain ⟨⟨hx₁, hx₂⟩, hx₃⟩ := hx'
  have hB : LMem.births (σ.setEnv ρ.key (.val w)) ρ.sym.mem = ρ.sym.mem.births σ :=
    LMem.births_setEnv hx₃
  have hset : ∀ (st : List (Name × Semantics.SVal)) (bd : Binding) (b : SymB),
      ρ.key ∉ b.vars → BindRel σ st (ρ.sym.mem.births σ) bd b →
        BindRel (σ.setEnv ρ.key (.val w)) st (ρ.sym.mem.births σ) bd b := by
    intro st bd b hv hb
    cases b with
    | val t => simp only [BindRel, SymB.vars] at hb hv ⊢; rw [LTerm.eval_setEnv _ hv]; exact hb
    | path q => simp only [BindRel, SymB.vars] at hb hv ⊢; rw [LPath.eval_setEnv _ hv]; exact hb
    | stale q => simp only [BindRel, SymB.vars] at hb hv ⊢; rw [LPath.eval_setEnv _ hv]; exact hb
    | stor s => simp only [BindRel, SymB.vars] at hb hv ⊢; rw [LStor.eval_setEnv _ hv]; exact hb
    | mref j => exact hb
    | unset => exact hb
  have hR : RelB (σ.setEnv ρ.key (.val w)) ρ (ρ.sym.mem.births σ) g ℓ :=
    ⟨h.ok, h.len, h.nodup, h.fresh, by rw [LStor.eval_setEnv _ hx₁]; exact h.stor,
      fun m hm b hb => hset _ _ _ (lookupBy_vars ρ.sym.env hb hx₂) (h.env m hm b hb),
      fun k => by rw [State.envVal_setEnv, h.tx k]⟩
  have hP := hR.push (.bind (.val (.var (.pos ρ.next)))) (.inr ⟨_, rfl⟩) (t := .val p) w
    (fun b hb => by
      cases hb
      exact ⟨w, by simp only [LTerm.eval, Atom.key, SymS.key, State.getEnv_setEnv_self]; rfl,
        rfl⟩)
  refine ⟨?_, ?_⟩
  · show RelB _ _ (LMem.births _ ρ.sym.mem) _ _
    rw [hB]
    exact hP
  · obtain ⟨μ, B', hr, hh⟩ := h.mem
    exact ⟨μ, B', by show ρ.sym.mem.run _ = _; rw [LMem.run_setEnv _ hx₃]; exact hr, hh⟩

/-- A local pushed bound to nothing: a hidden binder. -/
theorem RelU.pushFree {g : Semantics.State} {ℓ : Locs C Γ} (h : RelU σ ρ g ℓ) {t : LTy}
    (v : t.Denote C) : RelU σ (ρ.push .keep) g (ℓ.push v) :=
  ⟨h.toRelB.push .keep (.inl rfl) v (fun _ hb => nomatch hb), h.mem⟩

theorem RelU.pop {Γ' : Ctx} {g : Semantics.State} {ℓ : Locs C Γ'} (h : RelU σ ρ g ℓ)
    (hx : Ext Γ Γ') : RelU σ ⟨ρ.loc.drop hx.depth, ρ.sym, ρ.next⟩ g (ℓ.drop hx) :=
  ⟨h.toRelB.pop hx, h.mem⟩

theorem RelU.thin {Γ' : Ctx} {g : Semantics.State} {ℓ : Locs C Γ'} (h : RelU σ ρ g ℓ)
    (hx : Thin Γ Γ') : RelU σ ⟨Thin.sel hx ρ.loc, ρ.sym, ρ.next⟩ g (ℓ.thin hx) :=
  ⟨h.toRelB.thin hx, h.mem⟩

end Steps

/-! ## One element, written -/

section Elems

variable {Γ : Ctx} {σ : Semantics.State} {ρ₀ : SymS} {τ₀ : State C Γ}

/-- Two states the same storage stack stands for have one storage. -/
theorem storage_eq_of_stor {Γ' Δ : Ctx} {ρ₁ : SymS} {g₀ g₁ : Semantics.State} {ℓ₀ : Locs C Γ'}
    {ℓ₁ : Locs C Δ} {B₀ B₁ : MemNames.Births}
    (h₀ : RelB σ ρ₀ B₀ g₀ ℓ₀) (h₁ : RelB σ ρ₁ B₁ g₁ ℓ₁) (hs : ρ₁.sym.stor = ρ₀.sym.stor) :
    g₁.storage = g₀.storage := by
  have e := h₁.stor
  rw [hs, h₀.stor] at e
  simp only [Except.ok.injEq, Semantics.SVal.struct.injEq] at e
  exact e.symm

/-- **A right-hand side, read**: its guard returns exactly where it does,
and what it binds holds its value. -/
theorem RelU.rhs (h₀ : RelT σ ρ₀ τ₀) {t : LTy} (r : Rhs C Γ t) (hr : r.inLS ρ₀ = true)
    {st : List (Name × Semantics.SVal)} {B : MemNames.Births}
    (hB : r.needsMem = true → ρ₀.sym.mem.births σ <+: B)
    (hst : r.needsStor = true → st = τ₀.globE.storage) :
    ((∃ v, (r.guardS ρ₀).eval σ = .ok v) ↔ ∃ d, r.evalE τ₀ = .ok d) ∧
      ∀ d, r.evalE τ₀ = .ok d → ∃ b, r.actS ρ₀ = some b ∧ BindRel σ st B (t.enc C d) b := by
  cases r with
  | val a =>
    have ha := h₀.val (t := a) hr
    refine ⟨⟨fun ⟨v, hv⟩ => ⟨v, (ha v).1 hv⟩, fun ⟨d, hd⟩ => ⟨d, (ha d).2 hd⟩⟩,
      fun d hd => ⟨_, rfl, d, (ha d).2 hd, rfl⟩⟩
  | @path R p =>
    have hp := h₀.path (p := p) hr
    have hs := hst rfl
    subst hs
    have hg := guardPath_ok h₀.stor (p.toLS ρ₀)
    have hev : Rhs.evalE τ₀ (.path (R := R) p) = p.evalE τ₀ >>= fun rs => .ok (some rs) := rfl
    refine ⟨?_, fun d hd => ?_⟩
    · simp only [Rhs.guardS]
      rw [hg, hev]
      constructor
      · rintro ⟨qs, hq, hl⟩
        obtain ⟨rs, hrs, -⟩ := (hp qs).2 ⟨hq, hl⟩
        exact ⟨_, by rw [hrs]; rfl⟩
      · rintro ⟨d, hd⟩
        obtain ⟨rs, hrs, -⟩ := Res.bind_eq_ok.1 hd
        obtain ⟨hq, hl⟩ := (hp _).1 ⟨rs, hrs, rfl⟩
        exact ⟨_, hq, hl⟩
    · rw [hev] at hd
      obtain ⟨rs, hrs, hd⟩ := Res.bind_eq_ok.1 hd
      cases hd
      obtain ⟨hq, hl⟩ := (hp _).1 ⟨rs, hrs, rfl⟩
      exact ⟨_, rfl, rs.1, rs.2, hq, rfl, hl⟩
  | unset =>
    exact ⟨⟨fun _ => ⟨none, rfl⟩, fun _ => ⟨_, rfl⟩⟩, fun d hd => by
      cases hd; exact ⟨_, rfl, rfl⟩⟩
  | @mref R i =>
    obtain ⟨j, g, hI, hir, hie⟩ := h₀.ident (i := i) hr
    have hev : Rhs.evalE τ₀ (.mref (R := R) i) = i.evalE τ₀ >>= fun id => .ok (some id) := rfl
    refine ⟨?_, fun d hd => ?_⟩
    · simp only [Rhs.guardS, hI, hev]
      constructor
      · intro hg
        obtain ⟨id, hid⟩ := hir hg
        exact ⟨_, by rw [hid]; rfl⟩
      · rintro ⟨d, hd⟩
        obtain ⟨id, hid, -⟩ := Res.bind_eq_ok.1 hd
        exact (hie id hid).1
    · rw [hev] at hd
      obtain ⟨id, hid, hd⟩ := Res.bind_eq_ok.1 hd
      cases hd
      refine ⟨.mref j, by simp only [Rhs.actS, hI, Option.map_some], id,
        LId.evalR_prefix (hB rfl) (hie id hid).2, rfl⟩
  | store s =>
    have hs := RelU.stor_eval h₀ s (by rw [← Tm.inLS_eq_inLSM]; exact hr)
    rw [← Tm.toLS_eq_toLSM] at hs
    have hev : Rhs.evalE τ₀ (.store s) = s.evalE τ₀ >>= fun τ' => .ok τ'.storage := rfl
    refine ⟨?_, fun d hd => ?_⟩
    · simp only [Rhs.guardS, LTerm.eval, hev, Res.bind_eq_ok]
      constructor
      · rintro ⟨_, v, hv, -⟩
        obtain ⟨τ₁, h₁, -⟩ := Res.bind_eq_ok.1 ((hs v).1 hv)
        exact ⟨_, τ₁, h₁, rfl⟩
      · rintro ⟨_, τ₁, h₁, -⟩
        exact ⟨_, _, (hs _).2 (by rw [h₁]; rfl), rfl⟩
    · rw [hev] at hd
      obtain ⟨τ₁, h₁, hd⟩ := Res.bind_eq_ok.1 hd
      cases hd
      exact ⟨_, rfl, τ₁.storage, (hs _).2 (by rw [h₁]; rfl), rfl⟩
  | saveNet | saveNetMt => simp only [Rhs.inLS, Bool.false_eq_true] at hr

theorem elemV_net {Δ : Ctx} (τ : Semantics.State × Locs C Δ) (r : Tm C Γ .val) (op : IntOp)
    (a : Tm C Γ .val) : (UpdElem.net (Δ := Δ) r op a).applyVE τ₀ τ.1 τ.2 =
      r.evalE τ₀ >>= Value.asInt >>= fun addr => a.evalE τ₀ >>= Value.asInt >>= fun amt =>
        .ok ({ τ.1 with net := setBy addr (op.apply (τ.1.getNet addr) amt) τ.1.net }, τ.2) := by
  simp only [UpdElem.applyVE, UpdElem.globTE, bind, Except.bind]
  cases r.evalE τ₀ with
  | error => rfl
  | ok v =>
    cases v with
    | bool b => rfl
    | int addr =>
      cases a.evalE τ₀ with
      | error => rfl
      | ok w => cases w <;> rfl

theorem elemV_pay {Δ : Ctx} (τ : Semantics.State × Locs C Δ) (r a : Tm C Γ .val) :
    (UpdElem.pay (Δ := Δ) r a).applyVE τ₀ τ.1 τ.2 =
      r.evalE τ₀ >>= Value.asInt >>= fun addr => a.evalE τ₀ >>= Value.asInt >>= fun amt =>
        if amt < 0 then .error .revert
        else .ok ({ τ.1 with
          net := if addr = τ₀.globE.tx.selfAddress then τ.1.net
            else setBy addr (τ.1.getNet addr - amt) τ.1.net }, τ.2) := by
  simp only [UpdElem.applyVE, UpdElem.globTE, bind, Except.bind]
  cases r.evalE τ₀ with
  | error => rfl
  | ok v =>
    cases v with
    | bool b => rfl
    | int addr =>
      cases a.evalE τ₀ with
      | error => rfl
      | ok w =>
        cases w with
        | bool => rfl
        | int amt => by_cases h : amt < 0 <;> simp only [Value.asInt, h, ↓reduceIte, pure,
          Except.pure]

/-- **One element, written**, its terms read in `τ₀` (`ρ₀`) and written
into `τ₁` (`ρ₁`): its guard returns exactly where it writes, and the state
it leaves is its act's.  What
it binds reads the memory or the storage `ρ₀` left, so `ρ₁` must leave
them as they were where it does. -/
theorem RelU.elem (h₀ : RelT σ ρ₀ τ₀) {Δ : Ctx} {ρ₁ : SymS} {τ₁ : Semantics.State × Locs C Δ}
    (h₁ : RelU σ ρ₁ τ₁.1 τ₁.2) (e : UpdElem C Γ Δ) (ha : e.toElemS.inLS ρ₀ = true)
    (hm : e.toElemS.needsMem = true → ρ₁.sym.mem = ρ₀.sym.mem)
    (hs : e.toElemS.needsStor = true → ρ₁.sym.stor = ρ₀.sym.stor) :
    ((∃ v, (e.toElemS.guard ρ₀).eval σ = .ok v) ↔ ∃ τ', e.applyVE τ₀ τ₁.1 τ₁.2 = .ok τ') ∧
      ∀ τ', e.applyVE τ₀ τ₁.1 τ₁.2 = .ok τ' → RelU σ (ρ₁.act e.tgt (e.actS ρ₀)) τ'.1 τ'.2 := by
  cases e with
  | «local» i r =>
    have hr : r.inLS ρ₀ = true := ha
    obtain ⟨hg, hb⟩ := h₀.rhs r hr (st := τ₁.1.storage) (B := ρ₁.sym.mem.births σ)
      (fun hn => by rw [hm hn]; exact List.prefix_refl _)
      (fun hn => storage_eq_of_stor h₀.toRelB h₁.toRelB (hs hn))
    have hev : (UpdElem.local i r).applyVE τ₀ τ₁.1 τ₁.2 =
        r.evalE τ₀ >>= fun d => .ok (τ₁.1, τ₁.2.set i d) := rfl
    rw [hev]
    refine ⟨hg.trans ⟨fun ⟨d, hd⟩ => ⟨_, by rw [hd]; rfl⟩, fun ⟨τ', hτ'⟩ => ?_⟩, fun τ' hτ' => ?_⟩
    · obtain ⟨d, hd, -⟩ := Res.bind_eq_ok.1 hτ'
      exact ⟨d, hd⟩
    · obtain ⟨d, hd, he⟩ := Res.bind_eq_ok.1 hτ'
      cases he
      obtain ⟨b, hab, hbr⟩ := hb d hd
      have hact : (ρ₁.act (UpdElem.local i r).tgt (UpdElem.actS ρ₀ (.local i r))) =
          ρ₁.bindAt i.toNatR b := by
        simp only [UpdElem.actS, hab, Act.ofOpt, UpdElem.tgt, SymS.act]
      rw [hact]
      exact ⟨h₁.toRelB.setLocal i d b hbr, h₁.mem⟩
  | storage st =>
    have hst : st.inLSt ρ₀ = true := ha
    have hS := h₀.storT st hst
    have hev : (UpdElem.storage (Δ := Δ) st).applyVE τ₀ τ₁.1 τ₁.2 = st.evalE τ₀ >>= fun g =>
        .ok ({ τ₁.1 with storage := g.storage }, τ₁.2) := by
      simp only [UpdElem.applyVE, UpdElem.globTE, bind, Except.bind]
      cases st.evalE τ₀ <;> rfl
    rw [hev]
    refine ⟨?_, fun τ' hτ => ?_⟩
    · simp only [UpdElem.toElemS, ElemS.guard, LTerm.eval, Res.bind_eq_ok]
      constructor
      · rintro ⟨_, v, hv, -⟩
        obtain ⟨g, h₁, -⟩ := Res.bind_eq_ok.1 ((hS v).1 hv)
        exact ⟨_, g, h₁, rfl⟩
      · rintro ⟨_, g, h₁, -⟩
        exact ⟨_, _, (hS _).2 (by rw [h₁]; rfl), rfl⟩
    · obtain ⟨g, hg, he⟩ := Res.bind_eq_ok.1 hτ
      cases he
      exact ⟨h₁.toRelB.write ((hS _).2 (by rw [hg]; rfl)) _, h₁.mem.of_heap rfl rfl⟩
  | memory m =>
    have hmm : m.inLS ρ₀ = true ∧ memWithin (m.toLS ρ₀) = true := by
      simpa only [UpdElem.toElemS, ElemS.inLS, Bool.and_eq_true] using ha
    obtain ⟨M, g, hM, hmr, hme⟩ := h₀.memT hmm.1
    have hw : M.within memSize = true := by simpa only [memWithin, hM] using hmm.2
    have hev : (UpdElem.memory (Δ := Δ) m).applyVE τ₀ τ₁.1 τ₁.2 = m.evalE τ₀ >>= fun μ =>
        .ok ({ τ₁.1 with heap := μ.heap, nextId := μ.nextId }, τ₁.2) := by
      simp only [UpdElem.applyVE, UpdElem.globTE, bind, Except.bind]
      cases m.evalE τ₀ <;> rfl
    have hact : UpdElem.actS ρ₀ (UpdElem.memory (Δ := Δ) m) = .mem M := by
      simp only [UpdElem.actS, hM, hw, ↓reduceIte]
    rw [hev, hact]
    refine ⟨?_, fun τ' hτ => ?_⟩
    · simp only [UpdElem.toElemS, ElemS.guard, hM, hw, ↓reduceIte]
      constructor
      · intro hg
        obtain ⟨μ, hμ⟩ := hmr hg
        exact ⟨_, by rw [hμ, Res.ok_bind]⟩
      · rintro ⟨_, hτ⟩
        obtain ⟨μ, hμ, -⟩ := Res.bind_eq_ok.1 hτ
        exact (hme μ hμ).1
    · obtain ⟨μ', hμ', he⟩ := Res.bind_eq_ok.1 hτ
      cases he
      obtain ⟨-, μ, B, hrun, hh, hp⟩ := hme μ' hμ'
      rw [← hm rfl] at hp
      exact h₁.toRelB.setMem hrun hp _ hh
  | net r op a =>
    have hra : r.inLS ρ₀ = true ∧ a.inLS ρ₀ = true := by
      simpa only [UpdElem.toElemS, ElemS.inLS, Bool.and_eq_true] using ha
    have hr := h₀.val hra.1
    have ha' := h₀.val hra.2
    rw [elemV_net]
    refine ⟨?_, fun τ' hτ => ?_⟩
    · simp only [UpdElem.toElemS, ElemS.guard, LTerm.eval]
      constructor
      · rintro ⟨_, hv⟩
        obtain ⟨i, hi, hv⟩ := Res.bind_eq_ok.1 hv
        obtain ⟨x, hx, hi⟩ := Res.bind_eq_ok.1 hi
        obtain ⟨j, hj, -⟩ := Res.bind_eq_ok.1 hv
        obtain ⟨y, hy, hj⟩ := Res.bind_eq_ok.1 hj
        exact ⟨_, by simp only [(hr x).1 hx, (ha' y).1 hy, Res.ok_bind, hi, hj]; rfl⟩
      · rintro ⟨τ', hτ⟩
        obtain ⟨i, hi, hτ⟩ := Res.bind_eq_ok.1 hτ
        obtain ⟨x, hx, hi⟩ := Res.bind_eq_ok.1 hi
        obtain ⟨j, hj, -⟩ := Res.bind_eq_ok.1 hτ
        obtain ⟨y, hy, hj⟩ := Res.bind_eq_ok.1 hj
        refine ⟨.bool true, ?_⟩
        simp only [(hr x).2 hx, (ha' y).2 hy, Res.ok_bind, hi, hj]
        split <;> rfl
    · obtain ⟨i, -, hτ⟩ := Res.bind_eq_ok.1 hτ
      obtain ⟨j, -, hτ⟩ := Res.bind_eq_ok.1 hτ
      cases hτ
      exact ⟨h₁.toRelB.withGlob _ rfl (fun k => by cases k <;> rfl),
        h₁.mem.of_heap rfl rfl⟩
  | pay r a =>
    have hra : r.inLS ρ₀ = true ∧ a.inLS ρ₀ = true := by
      simpa only [UpdElem.toElemS, ElemS.inLS, Bool.and_eq_true] using ha
    have hr := h₀.val hra.1
    have ha' := h₀.val hra.2
    rw [elemV_pay]
    refine ⟨?_, fun τ' hτ => ?_⟩
    · simp only [UpdElem.toElemS, ElemS.guard, LTerm.eval]
      constructor
      · rintro ⟨_, hv⟩
        obtain ⟨i, hi, hv⟩ := Res.bind_eq_ok.1 hv
        obtain ⟨x, hx, hi⟩ := Res.bind_eq_ok.1 hi
        obtain ⟨j, hj, hv⟩ := Res.bind_eq_ok.1 hv
        obtain ⟨y, hy, hj⟩ := Res.bind_eq_ok.1 hj
        have hn : ¬ j < 0 := by
          intro hn
          rw [payGuard_eval σ _ hy hj, if_pos hn] at hv
          split at hv <;> cases hv
        exact ⟨_, by simp only [(hr x).1 hx, (ha' y).1 hy, Res.ok_bind, hi, hj, if_neg hn]; rfl⟩
      · rintro ⟨τ', hτ⟩
        obtain ⟨i, hi, hτ⟩ := Res.bind_eq_ok.1 hτ
        obtain ⟨x, hx, hi⟩ := Res.bind_eq_ok.1 hi
        obtain ⟨j, hj, hτ⟩ := Res.bind_eq_ok.1 hτ
        obtain ⟨y, hy, hj⟩ := Res.bind_eq_ok.1 hj
        have hn : ¬ j < 0 := by intro hn; rw [if_pos hn] at hτ; cases hτ
        refine ⟨.bool true, ?_⟩
        simp only [(hr x).2 hx, (ha' y).2 hy, Res.ok_bind, hi, hj]
        split <;> rw [payGuard_eval σ _ ((ha' y).2 hy) hj, if_neg hn]
    · obtain ⟨i, -, hτ⟩ := Res.bind_eq_ok.1 hτ
      obtain ⟨j, -, hτ⟩ := Res.bind_eq_ok.1 hτ
      split at hτ
      · cases hτ
      · cases hτ
        exact ⟨h₁.toRelB.withGlob _ rfl (fun k => by cases k <;> rfl),
          h₁.mem.of_heap rfl rfl⟩
  | selfBalance _ _ | netMt _ _ | setBalance _ =>
    simp only [UpdElem.toElemS, ElemS.inLS, Bool.false_eq_true] at ha

/-- **A declaration, written**: its guard returns exactly where its
right-hand side does, and the state it leaves binds the new position. -/
theorem RelU.decl (h₀ : RelT σ ρ₀ τ₀) {Δ : Ctx} {ρ₁ : SymS} {τ₁ : Semantics.State × Locs C Δ}
    (h₁ : RelU σ ρ₁ τ₁.1 τ₁.2) {t : LTy} (r : Rhs C Γ t) (ha : r.inLS ρ₀ = true)
    (hm : r.needsMem = true → ρ₁.sym.mem = ρ₀.sym.mem)
    (hs : r.needsStor = true → ρ₁.sym.stor = ρ₀.sym.stor) :
    ((∃ v, (r.guardS ρ₀).eval σ = .ok v) ↔ ∃ d, r.evalE τ₀ = .ok d) ∧
      ∀ d, r.evalE τ₀ = .ok d → RelU σ (ρ₁.push (.ofOpt (r.actS ρ₀))) τ₁.1 (τ₁.2.push d) := by
  obtain ⟨hg, hb⟩ := h₀.rhs r ha (st := τ₁.1.storage) (B := ρ₁.sym.mem.births σ)
    (fun hn => by rw [hm hn]; exact List.prefix_refl _)
    (fun hn => storage_eq_of_stor h₀.toRelB h₁.toRelB (hs hn))
  refine ⟨hg, fun d hd => ?_⟩
  obtain ⟨b, hab, hbr⟩ := hb d hd
  rw [hab]
  exact ⟨h₁.toRelB.push (.bind b) (.inr ⟨_, rfl⟩) d (fun b' hb' => by cases hb'; exact hbr),
    h₁.mem⟩

end Elems

/-! ## Updates -/

section Updates

variable {Γ : Ctx} {σ : Semantics.State} {ρ₀ : SymS} {τ₀ : State C Γ}

theorem applyV_pop_map {Δ Δ' : Ctx} (U : Upd C Γ Δ) (hx : Ext Δ' Δ) :
    (U.pop hx).applyVE τ₀ = (U.applyVE τ₀).map fun p => (p.1, p.2.drop hx) := by
  show (do let p ← U.applyVE τ₀; pure (p.1, p.2.drop hx)) = _
  cases U.applyVE τ₀ <;> rfl

theorem applyV_drop_map {Δ Δ' : Ctx} (U : Upd C Γ Δ) (hx : Thin Δ' Δ) :
    (U.drop hx).applyVE τ₀ = (U.applyVE τ₀).map fun p => (p.1, p.2.thin hx) := by
  show (do let p ← U.applyVE τ₀; pure (p.1, p.2.thin hx)) = _
  cases U.applyVE τ₀ <;> rfl

theorem UView.add_ne_zero (v : UView C Γ) (a : ElemS C Γ) : v.add a ≠ .zero := by
  cases v <;> simp only [UView.add, ne_eq, reduceCtorEq, not_false_eq_true]

theorem UView.add_eq_one {v : UView C Γ} {a b : ElemS C Γ} (h : v.add a = .one b) :
    v = .zero ∧ a = b := by
  cases v <;> simp only [UView.add, UView.one.injEq, reduceCtorEq] at h
  exact ⟨rfl, h⟩

theorem UView.add_eq_two {v : UView C Γ} {a b c : ElemS C Γ} (h : v.add a = .two b c) :
    v = .one b ∧ a = c := by
  cases v <;> simp only [UView.add, UView.two.injEq, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

/-- An update with no element leaves the reduction's symbols. -/
theorem replayS_sym_zero (aE : ∀ {Δ : Ctx}, UpdElem C Γ Δ → Act)
    (aR : ∀ {t : LTy}, Rhs C Γ t → Act) (ρ : SymS) : {Δ : Ctx} → (U : Upd C Γ Δ) →
      U.view = .zero → (U.replayS aE aR ρ).sym = ρ.sym
  | _, .nil, _ => rfl
  | _, .snoc U e, hv => absurd hv (UView.add_ne_zero U.view e.toElemS)
  | _, .decl U _ r, hv => absurd hv (UView.add_ne_zero U.view (.rhs r))
  | _, .pop U _, hv => replayS_sym_zero aE aR ρ U hv
  | _, .drop U _, hv => replayS_sym_zero aE aR ρ U hv

/-- An update with no element: it returns, its pops and drops applied. -/
theorem RelU.zero (aE : ∀ {Δ : Ctx}, UpdElem C Γ Δ → Act) (aR : ∀ {t : LTy}, Rhs C Γ t → Act)
    (h : RelT σ ρ₀ τ₀) : {Δ : Ctx} → (U : Upd C Γ Δ) → U.view = .zero →
      ∃ τ', U.applyVE τ₀ = .ok τ' ∧ RelU σ (U.replayS aE aR ρ₀) τ'.1 τ'.2 ∧
        (U.replayS aE aR ρ₀).sym = ρ₀.sym
  | _, .nil, _ => ⟨(τ₀.globE, τ₀.loc), rfl, h, rfl⟩
  | _, .snoc U e, hv => absurd hv (UView.add_ne_zero U.view e.toElemS)
  | _, .decl U _ r, hv => absurd hv (UView.add_ne_zero U.view (.rhs r))
  | _, .pop U hx, hv => by
    obtain ⟨τ', hτ, h', hs⟩ := RelU.zero aE aR h U hv
    exact ⟨(τ'.1, τ'.2.drop hx), by rw [applyV_pop_map, hτ]; rfl, h'.pop hx, hs⟩
  | _, .drop U hx, hv => by
    obtain ⟨τ', hτ, h', hs⟩ := RelU.zero aE aR h U hv
    exact ⟨(τ'.1, τ'.2.thin hx), by rw [applyV_drop_map, hτ]; rfl, h'.thin hx, hs⟩

/-- A pop or a drop after an update keeps what it says (both halt alike,
the relation through the pop). -/
theorem RelU.after_pop {Δ Δ' : Ctx} {U : Upd C Γ Δ} {g : LTerm} {ρ : SymS} (hx : Ext Δ' Δ)
    (hg : (∃ v, g.eval σ = .ok v) ↔ ∃ τ', U.applyVE τ₀ = .ok τ')
    (hr : ∀ τ', U.applyVE τ₀ = .ok τ' → RelU σ ρ τ'.1 τ'.2) :
    ((∃ v, g.eval σ = .ok v) ↔ ∃ τ', (Upd.pop U hx).applyVE τ₀ = .ok τ') ∧
      ∀ τ', (Upd.pop U hx).applyVE τ₀ = .ok τ' → RelU σ ⟨ρ.loc.drop hx.depth, ρ.sym, ρ.next⟩ τ'.1 τ'.2 := by
  refine ⟨hg.trans ?_, fun τ' h => ?_⟩
  · rw [applyV_pop_map]
    cases U.applyVE τ₀ with
    | error => simp only [Except.map, reduceCtorEq, exists_false]
    | ok τ₁ => exact ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩⟩
  · rw [applyV_pop_map] at h
    cases h₁ : U.applyVE τ₀ with
    | error => rw [h₁] at h; cases h
    | ok τ₁ =>
      rw [h₁] at h
      cases h
      exact (hr τ₁ h₁).pop hx

theorem RelU.after_drop {Δ Δ' : Ctx} {U : Upd C Γ Δ} {g : LTerm} {ρ : SymS} (hx : Thin Δ' Δ)
    (hg : (∃ v, g.eval σ = .ok v) ↔ ∃ τ', U.applyVE τ₀ = .ok τ')
    (hr : ∀ τ', U.applyVE τ₀ = .ok τ' → RelU σ ρ τ'.1 τ'.2) :
    ((∃ v, g.eval σ = .ok v) ↔ ∃ τ', (Upd.drop U hx).applyVE τ₀ = .ok τ') ∧
      ∀ τ', (Upd.drop U hx).applyVE τ₀ = .ok τ' → RelU σ ⟨Thin.sel hx ρ.loc, ρ.sym, ρ.next⟩ τ'.1 τ'.2 := by
  refine ⟨hg.trans ?_, fun τ' h => ?_⟩
  · rw [applyV_drop_map]
    cases U.applyVE τ₀ with
    | error => simp only [Except.map, reduceCtorEq, exists_false]
    | ok τ₁ => exact ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩⟩
  · rw [applyV_drop_map] at h
    cases h₁ : U.applyVE τ₀ with
    | error => rw [h₁] at h; cases h
    | ok τ₁ =>
      rw [h₁] at h
      cases h
      exact (hr τ₁ h₁).thin hx

/-- **An update of one element**: its guard returns exactly where the
update does, and the state it leaves is the replay's. -/
theorem RelU.one (h₀ : RelT σ ρ₀ τ₀) : {Δ : Ctx} → (U : Upd C Γ Δ) → {a : ElemS C Γ} →
    U.view = .one a → a.inLS ρ₀ = true →
    ((∃ v, (a.guard ρ₀).eval σ = .ok v) ↔ ∃ τ', U.applyVE τ₀ = .ok τ') ∧
      ∀ τ', U.applyVE τ₀ = .ok τ' →
        RelU σ (U.replayS (UpdElem.actS ρ₀) (fun r => .ofOpt (r.actS ρ₀)) ρ₀) τ'.1 τ'.2
  | _, .nil, _, hv, _ => UView.noConfusion hv
  | _, .snoc U e, _, hv, ha => by
    obtain ⟨hz, rfl⟩ := UView.add_eq_one hv
    obtain ⟨τ₁, hτ₁, h₁, hs⟩ := RelU.zero (UpdElem.actS ρ₀) (fun r => .ofOpt (r.actS ρ₀)) h₀ U hz
    have happ : (Upd.snoc U e).applyVE τ₀ = e.applyVE τ₀ τ₁.1 τ₁.2 := by
      show (do let p ← U.applyVE τ₀; e.applyVE τ₀ p.1 p.2) = _
      rw [hτ₁]; rfl
    rw [happ]
    exact RelU.elem h₀ h₁ e ha (fun _ => by rw [hs]) (fun _ => by rw [hs])
  | _, .decl U x r, _, hv, ha => by
    obtain ⟨hz, rfl⟩ := UView.add_eq_one hv
    obtain ⟨τ₁, hτ₁, h₁, hs⟩ := RelU.zero (UpdElem.actS ρ₀) (fun r => .ofOpt (r.actS ρ₀)) h₀ U hz
    obtain ⟨hg, hr⟩ := RelU.decl h₀ h₁ r ha (fun _ => by rw [hs]) (fun _ => by rw [hs])
    have happ : (Upd.decl U x r).applyVE τ₀ = (fun d => (τ₁.1, τ₁.2.push d)) <$> r.evalE τ₀ := by
      show (do let p ← U.applyVE τ₀; let v ← r.evalE τ₀; pure (p.1, p.2.push v)) = _
      rw [hτ₁]
      cases r.evalE τ₀ <;> rfl
    rw [happ]
    refine ⟨hg.trans ⟨fun ⟨d, hd⟩ => ⟨_, by rw [hd]; rfl⟩, fun ⟨τ', h⟩ => ?_⟩, fun τ' h => ?_⟩
    · cases hd : r.evalE τ₀ with
      | error => rw [hd] at h; cases h
      | ok d => exact ⟨d, rfl⟩
    · cases hd : r.evalE τ₀ with
      | error => rw [hd] at h; cases h
      | ok d =>
        rw [hd] at h
        cases h
        exact hr d hd
  | _, .pop U hx, _, hv, ha => by
    obtain ⟨hg, hr⟩ := RelU.one h₀ U hv ha
    exact RelU.after_pop hx hg hr
  | _, .drop U hx, _, hv, ha => by
    obtain ⟨hg, hr⟩ := RelU.one h₀ U hv ha
    exact RelU.after_drop hx hg hr

/-! ### Two elements, both read in the state the update is applied in -/

theorem SymS.act_mem (ρ : SymS) (n? : Option Nat) (a : Act) (ha : ∀ M, a ≠ .mem M) :
    (ρ.act n? a).sym.mem = ρ.sym.mem := by
  cases a with
  | keep => rfl
  | write _ => rfl
  | mem M => exact absurd rfl (ha M)
  | bind b => cases n? <;> rfl

theorem SymS.act_stor (ρ : SymS) (n? : Option Nat) (a : Act) (ha : ∀ S, a ≠ .write S) :
    (ρ.act n? a).sym.stor = ρ.sym.stor := by
  cases a with
  | keep => rfl
  | write S => exact absurd rfl (ha S)
  | mem _ => rfl
  | bind b => cases n? <;> rfl

theorem actS_ne_mem {Δ : Ctx} (e : UpdElem C Γ Δ) (he : e.toElemS.setsMem = false) (M : LMem) :
    e.actS ρ₀ ≠ .mem M := by
  cases e with
  | «local» i r =>
    simp only [UpdElem.actS]
    cases r.actS ρ₀ <;> simp only [Act.ofOpt, ne_eq, reduceCtorEq, not_false_eq_true]
  | memory m => simp only [UpdElem.toElemS, ElemS.setsMem, Bool.true_eq_false] at he
  | storage _ => simp only [UpdElem.actS, ne_eq, reduceCtorEq, not_false_eq_true]
  | _ => simp only [UpdElem.actS, ne_eq, reduceCtorEq, not_false_eq_true]

theorem actS_ne_write {Δ : Ctx} (e : UpdElem C Γ Δ) (he : e.toElemS.setsStor = false)
    (S : LStor) : e.actS ρ₀ ≠ .write S := by
  cases e with
  | «local» i r =>
    simp only [UpdElem.actS]
    cases r.actS ρ₀ <;> simp only [Act.ofOpt, ne_eq, reduceCtorEq, not_false_eq_true]
  | storage _ => simp only [UpdElem.toElemS, ElemS.setsStor, Bool.true_eq_false] at he
  | memory m =>
    simp only [UpdElem.actS]
    split
    · split <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true]
    · simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  | _ => simp only [UpdElem.actS, ne_eq, reduceCtorEq, not_false_eq_true]

theorem SymS.push_mem (ρ : SymS) (a : Act) : (ρ.push a).sym.mem = ρ.sym.mem := by
  cases a <;> rfl

theorem SymS.push_stor (ρ : SymS) (a : Act) : (ρ.push a).sym.stor = ρ.sym.stor := by
  cases a <;> rfl

/-- After one element that sets no memory, the memory is the one the
update is applied in; likewise the storage. -/
theorem replayS_one_mem (ρ : SymS) : {Δ : Ctx} → (U : Upd C Γ Δ) → {a : ElemS C Γ} →
    U.view = .one a → a.setsMem = false →
      (U.replayS (UpdElem.actS ρ) (fun r => .ofOpt (r.actS ρ)) ρ).sym.mem = ρ.sym.mem
  | _, .nil, _, hv, _ => UView.noConfusion hv
  | _, .snoc U e, _, hv, ha => by
    obtain ⟨hz, rfl⟩ := UView.add_eq_one hv
    show ((U.replayS _ _ ρ).act e.tgt (e.actS ρ)).sym.mem = _
    rw [SymS.act_mem _ _ _ (actS_ne_mem e ha),
      replayS_sym_zero (UpdElem.actS ρ) (fun r => .ofOpt (r.actS ρ)) ρ U hz]
  | _, .decl U x r, _, hv, _ => by
    obtain ⟨hz, rfl⟩ := UView.add_eq_one hv
    show ((U.replayS _ _ ρ).push _).sym.mem = _
    rw [SymS.push_mem, replayS_sym_zero (UpdElem.actS ρ) (fun r => .ofOpt (r.actS ρ)) ρ U hz]
  | _, .pop U _, _, hv, ha => replayS_one_mem ρ U hv ha
  | _, .drop U _, _, hv, ha => replayS_one_mem ρ U hv ha

theorem replayS_one_stor (ρ : SymS) : {Δ : Ctx} → (U : Upd C Γ Δ) → {a : ElemS C Γ} →
    U.view = .one a → a.setsStor = false →
      (U.replayS (UpdElem.actS ρ) (fun r => .ofOpt (r.actS ρ)) ρ).sym.stor = ρ.sym.stor
  | _, .nil, _, hv, _ => UView.noConfusion hv
  | _, .snoc U e, _, hv, ha => by
    obtain ⟨hz, rfl⟩ := UView.add_eq_one hv
    show ((U.replayS _ _ ρ).act e.tgt (e.actS ρ)).sym.stor = _
    rw [SymS.act_stor _ _ _ (actS_ne_write e ha),
      replayS_sym_zero (UpdElem.actS ρ) (fun r => .ofOpt (r.actS ρ)) ρ U hz]
  | _, .decl U x r, _, hv, _ => by
    obtain ⟨hz, rfl⟩ := UView.add_eq_one hv
    show ((U.replayS _ _ ρ).push _).sym.stor = _
    rw [SymS.push_stor, replayS_sym_zero (UpdElem.actS ρ) (fun r => .ofOpt (r.actS ρ)) ρ U hz]
  | _, .pop U _, _, hv, ha => replayS_one_stor ρ U hv ha
  | _, .drop U _, _, hv, ha => replayS_one_stor ρ U hv ha

/-- **Two elements, both read in the state the update is applied in**
(`{x := x + 1 ‖ storage := save(storage, p, x)}`), the second written after
the first: both guards return exactly where the update does, and the state
it leaves is the replay's, each act read in that state (`ElemS.parOk`). -/
theorem RelU.par (h₀ : RelT σ ρ₀ τ₀) : {Δ : Ctx} → (U : Upd C Γ Δ) → {a b : ElemS C Γ} →
    U.view = .two a b → ElemS.parOk ρ₀ a b = true →
    ((∃ v, (seqL (a.guard ρ₀) (b.guard ρ₀)).eval σ = .ok v) ↔ ∃ τ', U.applyVE τ₀ = .ok τ') ∧
      ∀ τ', U.applyVE τ₀ = .ok τ' →
        RelU σ (U.replayS (UpdElem.actS ρ₀) (fun r => .ofOpt (r.actS ρ₀)) ρ₀) τ'.1 τ'.2
  | _, .nil, _, _, hv, _ => UView.noConfusion hv
  | _, .snoc U e, a, b, hv, hp => by
    obtain ⟨hU, rfl⟩ := UView.add_eq_two hv
    simp only [ElemS.parOk, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff] at hp
    obtain ⟨⟨⟨ha, hb⟩, hm⟩, hs⟩ := hp
    obtain ⟨hg₁, hr₁⟩ := RelU.one h₀ U hU ha
    have hm' : e.toElemS.needsMem = true →
        (U.replayS (UpdElem.actS ρ₀) (fun r => .ofOpt (r.actS ρ₀)) ρ₀).sym.mem = ρ₀.sym.mem :=
      fun hn => replayS_one_mem ρ₀ U hU (hm.resolve_right (by rw [hn]; decide))
    have hs' : e.toElemS.needsStor = true →
        (U.replayS (UpdElem.actS ρ₀) (fun r => .ofOpt (r.actS ρ₀)) ρ₀).sym.stor = ρ₀.sym.stor :=
      fun hn => replayS_one_stor ρ₀ U hU (hs.resolve_right (by rw [hn]; decide))
    have happ : (Upd.snoc U e).applyVE τ₀ = U.applyVE τ₀ >>= fun τ₁ => e.applyVE τ₀ τ₁.1 τ₁.2 := rfl
    rw [happ]
    refine ⟨⟨fun hgg => ?_, fun ⟨τ', hτ⟩ => ?_⟩, fun τ' hτ => ?_⟩
    · obtain ⟨hA, hB⟩ := (seqL_rets σ _ _).1 hgg
      obtain ⟨τ₁, hτ₁⟩ := hg₁.1 hA
      obtain ⟨τ', hτ'⟩ := (RelU.elem h₀ (hr₁ τ₁ hτ₁) e hb hm' hs').1.1 hB
      exact ⟨τ', by rw [hτ₁, Res.ok_bind]; exact hτ'⟩
    · obtain ⟨τ₁, hτ₁, hτ⟩ := Res.bind_eq_ok.1 hτ
      exact (seqL_rets σ _ _).2 ⟨hg₁.2 ⟨τ₁, hτ₁⟩,
        (RelU.elem h₀ (hr₁ τ₁ hτ₁) e hb hm' hs').1.2 ⟨τ', hτ⟩⟩
    · obtain ⟨τ₁, hτ₁, hτ⟩ := Res.bind_eq_ok.1 hτ
      exact (RelU.elem h₀ (hr₁ τ₁ hτ₁) e hb hm' hs').2 τ' hτ
  | _, .decl U x r, a, b, hv, hp => by
    obtain ⟨hU, rfl⟩ := UView.add_eq_two hv
    simp only [ElemS.parOk, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff] at hp
    obtain ⟨⟨⟨ha, hb⟩, hm⟩, hs⟩ := hp
    obtain ⟨hg₁, hr₁⟩ := RelU.one h₀ U hU ha
    have hm' : r.needsMem = true →
        (U.replayS (UpdElem.actS ρ₀) (fun r => .ofOpt (r.actS ρ₀)) ρ₀).sym.mem = ρ₀.sym.mem :=
      fun hn => replayS_one_mem ρ₀ U hU (hm.resolve_right (by
        simp only [ElemS.needsMem, hn]; decide))
    have hs' : r.needsStor = true →
        (U.replayS (UpdElem.actS ρ₀) (fun r => .ofOpt (r.actS ρ₀)) ρ₀).sym.stor = ρ₀.sym.stor :=
      fun hn => replayS_one_stor ρ₀ U hU (hs.resolve_right (by
        simp only [ElemS.needsStor, hn]; decide))
    have happ : (Upd.decl U x r).applyVE τ₀ =
        U.applyVE τ₀ >>= fun τ₁ => r.evalE τ₀ >>= fun d => .ok (τ₁.1, τ₁.2.push d) := rfl
    rw [happ]
    refine ⟨⟨fun hgg => ?_, fun ⟨τ', hτ⟩ => ?_⟩, fun τ' hτ => ?_⟩
    · obtain ⟨hA, hB⟩ := (seqL_rets σ _ _).1 hgg
      obtain ⟨τ₁, hτ₁⟩ := hg₁.1 hA
      obtain ⟨d, hd⟩ := (RelU.decl h₀ (hr₁ τ₁ hτ₁) r hb hm' hs').1.1 hB
      exact ⟨_, by rw [hτ₁, Res.ok_bind, hd, Res.ok_bind]⟩
    · obtain ⟨τ₁, hτ₁, hτ⟩ := Res.bind_eq_ok.1 hτ
      obtain ⟨d, hd, -⟩ := Res.bind_eq_ok.1 hτ
      exact (seqL_rets σ _ _).2 ⟨hg₁.2 ⟨τ₁, hτ₁⟩,
        (RelU.decl h₀ (hr₁ τ₁ hτ₁) r hb hm' hs').1.2 ⟨d, hd⟩⟩
    · obtain ⟨τ₁, hτ₁, hτ⟩ := Res.bind_eq_ok.1 hτ
      obtain ⟨d, hd, he⟩ := Res.bind_eq_ok.1 hτ
      cases he
      exact (RelU.decl h₀ (hr₁ τ₁ hτ₁) r hb hm' hs').2 d hd
  | _, .pop U hx, a, b, hv, hp => by
    obtain ⟨hg, hr⟩ := RelU.par h₀ U hv hp
    exact RelU.after_pop hx hg hr
  | _, .drop U hx, a, b, hv, hp => by
    obtain ⟨hg, hr⟩ := RelU.par h₀ U hv hp
    exact RelU.after_drop hx hg hr

end Updates


/-! ## An allocation's pair -/

section Pair

variable {Γ : Ctx} {σ : Semantics.State} {ρ₀ : SymS} {τ₀ : State C Γ}

theorem allocPairS?_cases {i : Tm C Γ .ident} {mm : Tm C Γ .mem} (h : allocPairS? i mm = true) :
    (∃ R, i = .app1 (.alloc R) rfl (.app0 .memory) ∧ mm = .app1 (.addM R) rfl (.app0 .memory)) ∨
      ∃ v, i = .app2 .copy (.app0 .memory) v ∧ mm = .app2 .copySt (.app0 .memory) v := by
  unfold allocPairS? at h
  split at h
  · simp only [decide_eq_true_eq] at h
    subst h
    exact Or.inl ⟨_, rfl, rfl⟩
  · obtain rfl := Tm.eq_of_beqR h
    exact Or.inr ⟨_, rfl, rfl⟩
  · cases h

theorem copyOfS?_some {mm : Tm C Γ .mem} {p : Tm C Γ .path} (h : copyOfS? mm = some p) :
    mm = .app2 .copySt (.app0 .memory) (.app2 .sfind (.app0 .storage) p) := by
  unfold copyOfS? at h
  split at h
  · cases h
    rfl
  · cases h

/-- A stored value pushed in as `new R(n)` reads to `R`'s array of the
length `n` returns. -/
theorem RelU.arr_eval (h : RelT σ ρ₀ τ₀) : (v : Tm C Γ .sv) →
    v.inLSM ρ₀ = true → ∀ {R : RefTy} {n : LTerm}, v.toLSM ρ₀ = .arr R n → ∀ sv,
      v.evalE τ₀ = .ok sv ↔ ∃ c, n.eval σ = .ok (.int c) ∧ sv = newArrVal R c
  | .app1 (.newArr R) _ nt, hv, R', n, hvt, sv => by
    simp only [Tm.toLSM, Op1.toL, LVal.arr.injEq] at hvt
    obtain ⟨rfl, rfl⟩ := hvt
    simp only [Tm.inLSM, Op1.inL] at hv
    have hnt := h.valM nt hv
    rw [newArrS_eval_ok]
    exact exists_congr fun c => and_congr (hnt _).symm Iff.rfl
  | .app1 .sval _ _, _, _, _, hvt, _ => by simp only [Tm.toLSM, Op1.toL, reduceCtorEq] at hvt
  | .app2 .sfind _ _, _, _, _, hvt, _ => by
    simp only [Tm.toLSM, Op2.toLAtS, Op2.toL, reduceCtorEq] at hvt
  | .app2 .copyMem a b, _, _, _, hvt, _ => by
    simp only [Tm.toLSM, Op2.toLAtS, Op2.toL] at hvt
    rcases memL_getD (a.toLSM ρ₀) (b.toLSM ρ₀) with he | ⟨_, _, he⟩ <;>
      rw [he] at hvt <;> cases hvt

open MemNames in
/-- **A copy from storage's pair** (`pairCopy_key`, by position). -/
theorem RelU.pairCopy_key (h : RelT σ ρ₀ τ₀) {p : Tm C Γ .path} (hp : p.inLS ρ₀ = true) :
    (Rets ((copyG ρ₀.sym.stor (p.toLS ρ₀)).eval σ) ↔
      ∃ id μ', (Tm.app2 .copy (.app0 .memory) (.app2 .sfind (.app0 .storage) p)).evalE τ₀ = .ok id ∧
        (Tm.app2 .copySt (.app0 .memory) (.app2 .sfind (.app0 .storage) p)).evalE τ₀ = .ok μ') ∧
    ∀ id μ', (Tm.app2 .copy (.app0 .memory) (.app2 .sfind (.app0 .storage) p)).evalE τ₀ = .ok id →
      (Tm.app2 .copySt (.app0 .memory) (.app2 .sfind (.app0 .storage) p)).evalE τ₀ = .ok μ' →
      ∃ μ B, (LMem.copySt ρ₀.sym.mem ρ₀.sym.mem.nAlloc ρ₀.sym.stor (p.toLS ρ₀)).run σ = .ok (μ, B) ∧
        μ.HeapEq μ' ∧ ρ₀.sym.mem.births σ <+: B ∧ LId.evalR B ⟨ρ₀.sym.mem.nAlloc, []⟩ = .ok id := by
  have hb := live_bridge (τ := τ₀.globE) (h.path hp)
  have hsf : (Tm.app2 (C := C) .sfind (.app0 .storage) p).evalE τ₀ =
      p.evalE τ₀ >>= fun rs => τ₀.globE.findStorage rs.1 rs.2 := rfl
  have hv : ∀ c, (Tm.app2 (C := C) .sfind (.app0 .storage) p).evalE τ₀ = .ok c ↔
      ∃ qs, (p.toLS ρ₀).eval σ = .ok qs ∧ (Semantics.SVal.struct τ₀.globE.storage).findLive qs = .ok c := by
    intro c
    rw [hsf]
    constructor
    · intro hc
      obtain ⟨rs, hrs, hc⟩ := Res.bind_eq_ok.1 hc
      obtain ⟨hq, hl⟩ := (hb _ c).2 ⟨rs, hrs, rfl, hc⟩
      exact ⟨_, hq, hl⟩
    · rintro ⟨qs, hq, hl⟩
      obtain ⟨rs, hrs, rfl, hc⟩ := (hb qs c).1 ⟨hq, hl⟩
      rw [hrs, Res.ok_bind]
      exact hc
  have hi : (Tm.app2 (C := C) .copy (.app0 .memory) (.app2 .sfind (.app0 .storage) p)).evalE τ₀ =
      (Tm.app2 (C := C) .sfind (.app0 .storage) p).evalE τ₀ >>= fun sv =>
        copyStToM τ₀.globE sv >>= fun r => r.2.asRef := rfl
  have hmm : (Tm.app2 (C := C) .copySt (.app0 .memory) (.app2 .sfind (.app0 .storage) p)).evalE τ₀ =
      (Tm.app2 (C := C) .sfind (.app0 .storage) p).evalE τ₀ >>= fun sv =>
        copyStToM τ₀.globE sv >>= fun r => .ok r.1 := rfl
  have hG : Rets ((copyG ρ₀.sym.stor (p.toLS ρ₀)).eval σ) ↔
      ∃ c, (Tm.app2 (C := C) .sfind (.app0 .storage) p).evalE τ₀ = .ok c ∧ Cps c ∧
        ∀ pv, c ≠ .prim pv := by
    unfold copyG
    rw [seq_rets, ite_isT_rets]
    simp only [lit_rets, and_true]
    constructor
    · rintro ⟨⟨a, ha⟩, hf⟩
      simp only [LTerm.eval, h.stor, Res.ok_bind] at ha
      obtain ⟨qs, hq, ha⟩ := Res.bind_eq_ok.1 ha
      obtain ⟨c, hc, ha⟩ := Res.bind_eq_ok.1 ha
      obtain ⟨r, hr, -⟩ := Res.bind_eq_ok.1 ha
      refine ⟨c, (hv c).2 ⟨qs, hq, hc⟩, ⟨_, r, hr⟩, ?_⟩
      rintro pv rfl
      obtain ⟨a', ha'⟩ : ∃ a', (Semantics.SVal.prim pv).asValue = .ok a' := by
        cases pv <;> exact ⟨_, rfl⟩
      exact hf ⟨a', by simp only [LTerm.eval, h.stor, hq, hc, Res.ok_bind, ha']⟩
    · rintro ⟨c, hc, hcp, hnp⟩
      obtain ⟨qs, hq, hl⟩ := (hv c).1 hc
      obtain ⟨r, hr⟩ := hcp.at (memBase σ)
      refine ⟨⟨.bool true, by simp only [LTerm.eval, h.stor, hq, hl, Res.ok_bind, hr]⟩, ?_⟩
      rintro ⟨a, ha⟩
      simp only [LTerm.eval, h.stor, hq, hl, Res.ok_bind] at ha
      cases c with
      | prim pv => exact hnp pv rfl
      | struct _ | array _ _ _ | map _ _ => simp only [SVal.asValue, reduceCtorEq] at ha
  refine ⟨hG.trans ⟨fun ⟨c, hc, hcp, hnp⟩ => ?_, fun ⟨id, μ', hid, _⟩ => ?_⟩,
    fun id μ' hid hμ' => ?_⟩
  · obtain ⟨⟨τ₁, mv⟩, hcopy⟩ := hcp.at τ₀.globE
    obtain ⟨id, rfl⟩ := copy_ref hcopy hnp
    exact ⟨id, τ₁, by rw [hi, hc, Res.ok_bind, hcopy]; rfl,
      by rw [hmm, hc, Res.ok_bind, hcopy]; rfl⟩
  · rw [hi] at hid
    obtain ⟨c, hc, hid⟩ := Res.bind_eq_ok.1 hid
    obtain ⟨r, hr, hid⟩ := Res.bind_eq_ok.1 hid
    refine ⟨c, hc, ⟨τ₀.globE, r, hr⟩, ?_⟩
    rintro pv rfl
    cases pv <;> simp only [copyStToM, Except.ok.injEq] at hr <;> subst hr <;> cases hid
  · rw [hmm] at hμ'
    obtain ⟨c, hc, hμ'⟩ := Res.bind_eq_ok.1 hμ'
    obtain ⟨r, hr, hμ'⟩ := Res.bind_eq_ok.1 hμ'
    cases hμ'
    rw [hi, hc, Res.ok_bind, hr, Res.ok_bind] at hid
    obtain ⟨qs, hq, hl⟩ := (hv c).1 hc
    obtain ⟨μ₁, B₁, hr₁, hh⟩ := h.mem
    have hk : B₁.length = ρ₀.sym.mem.nAlloc := LMem.run_nAlloc σ ρ₀.sym.mem hr₁
    rcases (copyStToM_heap hh c).cases with ⟨e, -, h₂⟩ | ⟨t₁, t₂, mv, h₁, h₂, ht⟩
    · rw [hr] at h₂
      cases h₂
    · rw [hr, Except.ok.injEq] at h₂
      subst h₂
      obtain rfl : mv = .ref id := by
        cases mv <;> simp only [MVal.asRef, reduceCtorEq] at hid
        cases hid
        rfl
      refine ⟨t₁, B₁ ++ [Birth.ofCopy μ₁ t₁ id], ?_, ht, ?_, ?_⟩
      · simp only [LMem.run, h.stor, hq, hl, hr₁, Res.ok_bind, hk, ↓reduceIte, h₁, MVal.asRef]
        rfl
      · rw [LMem.births_of_run hr₁]
        exact List.prefix_append _ _
      · rw [evalR_last _ _ hk.symm]
        rfl

open MemNames in
/-- **An allocation's pair, read**: its guard returns exactly where the
identity and the memory do, and the memory's run names the identity at the
next ordinal. -/
theorem RelU.pairKey (h : RelT σ ρ₀ τ₀) {i : Tm C Γ .ident} {mm : Tm C Γ .mem} {g : LTerm}
    {M : LMem} (hq : pairLS ρ₀ i mm = some (g, M)) (hm : pairInS ρ₀ mm = true) :
    (Rets (g.eval σ) ↔ ∃ id μ', i.evalE τ₀ = .ok id ∧ mm.evalE τ₀ = .ok μ') ∧
    ∀ id μ', i.evalE τ₀ = .ok id → mm.evalE τ₀ = .ok μ' → ∃ μ B, M.run σ = .ok (μ, B) ∧
      μ.HeapEq μ' ∧ ρ₀.sym.mem.births σ <+: B ∧ LId.evalR B ⟨ρ₀.sym.mem.nAlloc, []⟩ = .ok id := by
  unfold pairLS at hq
  split at hq
  · rename_i hap
    cases hc : copyOfS? mm with
    | some p =>
      obtain rfl := copyOfS?_some hc
      simp only [pairInS, hc] at hm
      simp only [pairMemS, hc, Option.bind_some] at hq
      split at hq
      case isFalse => cases hq
      simp only [Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      rcases allocPairS?_cases hap with ⟨R, -, hmm⟩ | ⟨v, rfl, hmm⟩
      · cases hmm
      · cases hmm
        exact RelU.pairCopy_key h hm
    | none =>
      simp only [pairInS, hc] at hm
      simp only [pairMemS, hc] at hq
      obtain ⟨M', g', hM, hmr, hme⟩ := h.memT hm
      rw [hM, Option.bind_some] at hq
      split at hq
      case isFalse => cases hq
      simp only [Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      have hkey : (∀ id, i.evalE τ₀ = .ok id → ∃ μ', mm.evalE τ₀ = .ok μ') ∧
          ∀ μ', mm.evalE τ₀ = .ok μ' → ∃ id, i.evalE τ₀ = .ok id ∧
            LId.evalR (M'.births σ) ⟨ρ₀.sym.mem.nAlloc, []⟩ = .ok id := by
        rcases allocPairS?_cases hap with ⟨R, rfl, rfl⟩ | ⟨v, rfl, rfl⟩
        · rw [Tm.toLS_eq_toLSM] at hM
          simp only [Tm.toLSM, Op1.toL, Op0.toL, Option.bind_some] at hM
          split at hM
          · simp only [Option.some.injEq, Prod.mk.injEq] at hM
            obtain ⟨rfl, -⟩ := hM
            have hi : (Tm.app1 (C := C) (Γ := Γ) (.alloc R) rfl (.app0 .memory)).evalE τ₀ =
                allocDefault τ₀.globE R >>= fun r => .ok r.2 := rfl
            have hmm : (Tm.app1 (C := C) (Γ := Γ) (.addM R) rfl (.app0 .memory)).evalE τ₀ =
                allocDefault τ₀.globE R >>= fun r => .ok r.1 := rfl
            refine ⟨fun id hid => ?_, fun μ' hμ' => ?_⟩
            · rw [hi] at hid
              obtain ⟨r, hr, -⟩ := Res.bind_eq_ok.1 hid
              exact ⟨r.1, by rw [hmm, hr]; rfl⟩
            · obtain ⟨-, μ, B, hrun, -, -⟩ := hme μ' hμ'
              rw [hmm] at hμ'
              obtain ⟨r, hr, -⟩ := Res.bind_eq_ok.1 hμ'
              obtain ⟨μ₀, B₀, id₀, hr₀, hk, hc, rfl⟩ := LMem.run_addM hrun
              obtain ⟨μ₁, B₁, hr₁, hh⟩ := h.mem
              rw [hr₁, Except.ok.injEq, Prod.mk.injEq] at hr₀
              obtain ⟨rfl, rfl⟩ := hr₀
              rcases (allocDefault_heap hh R).cases with ⟨e, h₁, -⟩ | ⟨t₁, t₂, id', h₁, h₂, -⟩
              · rw [allocDefault_of_copy hc] at h₁; cases h₁
              · rw [allocDefault_of_copy hc, Except.ok.injEq, Prod.mk.injEq] at h₁
                obtain ⟨-, rfl⟩ := h₁
                rw [hr, Except.ok.injEq] at h₂
                subst h₂
                refine ⟨id₀, by rw [hi, hr]; rfl, ?_⟩
                rw [LMem.births_of_run hrun, evalR_last _ _ hk]
                rfl
          · cases hM
        · have hvi : v.inLSM ρ₀ = true := by
            rw [Tm.inLS_eq_inLSM] at hm
            simp only [Tm.inLSM, Op2.inLS, Bool.and_eq_true] at hm
            exact hm.1.2
          rw [Tm.toLS_eq_toLSM] at hM
          obtain ⟨R, n', hvt, hR, rfl, -⟩ := newM_some (by
            simpa only [Tm.toLSM, Op2.toLAtS, Op2.toL, Op0.toL] using hM)
          have hva := RelU.arr_eval h v hvi hvt
          have hi : (Tm.app2 (C := C) .copy (.app0 .memory) v).evalE τ₀ =
              v.evalE τ₀ >>= fun sv => copyStToM τ₀.globE sv >>= fun r => r.2.asRef := rfl
          have hmm : (Tm.app2 (C := C) .copySt (.app0 .memory) v).evalE τ₀ =
              v.evalE τ₀ >>= fun sv => copyStToM τ₀.globE sv >>= fun r => .ok r.1 := rfl
          refine ⟨fun id hid => ?_, fun μ' hμ' => ?_⟩
          · rw [hi] at hid
            obtain ⟨sv, hsv, hid⟩ := Res.bind_eq_ok.1 hid
            obtain ⟨r, hr, -⟩ := Res.bind_eq_ok.1 hid
            exact ⟨r.1, by rw [hmm, hsv, Res.ok_bind, hr]; rfl⟩
          · obtain ⟨-, μ, B, hrun, -, -⟩ := hme μ' hμ'
            rw [hmm] at hμ'
            obtain ⟨sv, hsv, hμ'⟩ := Res.bind_eq_ok.1 hμ'
            obtain ⟨r, hr, -⟩ := Res.bind_eq_ok.1 hμ'
            obtain ⟨c, hc, rfl⟩ := (hva sv).1 hsv
            obtain ⟨μ₀, B₀, id₀, c', hr₀, hk, hc', hcp, rfl⟩ := LMem.run_newArr hrun
            rw [hc, Except.ok.injEq, PrimVal.int.injEq] at hc'
            subst hc'
            obtain ⟨μ₁, B₁, hr₁, hh⟩ := h.mem
            rw [hr₁, Except.ok.injEq, Prod.mk.injEq] at hr₀
            obtain ⟨rfl, rfl⟩ := hr₀
            rcases (copyStToM_heap hh (newArrVal R c)).cases with ⟨e, h₁, -⟩ |
              ⟨t₁, t₂, mv, h₁, h₂, -⟩
            · rw [hcp] at h₁; cases h₁
            · rw [hcp, Except.ok.injEq, Prod.mk.injEq] at h₁
              obtain ⟨-, rfl⟩ := h₁
              rw [hr, Except.ok.injEq] at h₂
              subst h₂
              refine ⟨id₀, by rw [hi, hsv, Res.ok_bind, hr]; rfl, ?_⟩
              rw [LMem.births_of_run hrun, evalR_last _ _ hk]
              rfl
      refine ⟨⟨fun hg => ?_, fun ⟨_, μ', _, hμ'⟩ => (hme μ' hμ').1⟩, fun id μ' hid hμ' => ?_⟩
      · obtain ⟨μ', hμ'⟩ := hmr hg
        obtain ⟨id, hid, -⟩ := hkey.2 μ' hμ'
        exact ⟨id, μ', hid, hμ'⟩
      · obtain ⟨-, μ, B, hrun, hh, hp⟩ := hme μ' hμ'
        obtain ⟨id', hid', hB⟩ := hkey.2 μ' hμ'
        rw [hid, Except.ok.injEq] at hid'
        subst hid'
        exact ⟨μ, B, hrun, hh, hp, by rw [← LMem.births_of_run hrun]; exact hB⟩
  · cases hq

/-- The identity the first element of an allocation's pair binds. -/
def mrefOf : ElemS C Γ → Option (Tm C Γ .ident)
  | .rhs (.mref i) | .glob (.local _ (.mref i)) => some i
  | _ => none

theorem pairViewS_some {a b : ElemS C Γ} {i : Tm C Γ .ident} {mm : Tm C Γ .mem}
    (h : pairViewS a b = some (i, mm)) :
    mrefOf a = some i ∧ ∃ Δ : Ctx, b = @ElemS.glob C Γ Δ (.memory mm) := by
  rcases a with r | (⟨_, r⟩ | _ | _ | _ | _ | _ | _ | _) <;>
    rcases b with r' | (⟨_, r'⟩ | _ | _ | _ | _ | _ | _ | _) <;>
    (try cases r) <;> (try cases r') <;>
    first
    | (cases h; done)
    | (injection h with h; injection h with h₁ h₂; subst h₁ h₂; exact ⟨rfl, _, rfl⟩)

theorem apply_snoc_mref {Δ : Ctx} {R : RefTy} (U : Upd C Γ Δ) (j : Idx Δ (.mem R))
    (i : Tm C Γ .ident) : (Upd.snoc U (.local j (.mref i))).applyVE τ₀ =
      U.applyVE τ₀ >>= fun τ => i.evalE τ₀ >>= fun id => .ok (τ.1, τ.2.set j (some id)) := by
  simp only [Upd.applyVE, UpdElem.applyVE, Rhs.evalE, bind, Except.bind, pure, Except.pure]
  cases U.applyVE τ₀ <;> try rfl
  cases i.evalE τ₀ <;> rfl

theorem apply_decl_mref {Δ : Ctx} {R : RefTy} (U : Upd C Γ Δ) (y : Var) (i : Tm C Γ .ident) :
    (Upd.decl U y (.mref (R := R) i)).applyVE τ₀ =
      U.applyVE τ₀ >>= fun τ => i.evalE τ₀ >>= fun id => .ok (τ.1, τ.2.push (t := .mem R) (some id)) := by
  simp only [Upd.applyVE, Rhs.evalE, bind, Except.bind, pure, Except.pure]
  cases U.applyVE τ₀ <;> try rfl
  cases i.evalE τ₀ <;> rfl

/-- The first element of a pair, its pops and drops around it, written
where the identity returns. -/
theorem RelU.half_inv {i : Tm C Γ .ident} (M : LMem) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → {a : ElemS C Γ} → U.view = .one a → mrefOf a = some i →
      ∀ τ₁, U.applyVE τ₀ = .ok τ₁ → ∃ id, i.evalE τ₀ = .ok id
  | _, .nil, _, hv, _, _, _ => UView.noConfusion hv
  | _, .snoc U e, a, hv, ha, τ₁, hτ => by
    obtain ⟨-, rfl⟩ := UView.add_eq_one hv
    cases e with
    | «local» j r =>
      cases r with
      | mref i' =>
        simp only [UpdElem.toElemS, mrefOf, Option.some.injEq] at ha
        subst ha
        rw [apply_snoc_mref] at hτ
        obtain ⟨_, -, hτ⟩ := Res.bind_eq_ok.1 hτ
        obtain ⟨id, hid, -⟩ := Res.bind_eq_ok.1 hτ
        exact ⟨id, hid⟩
      | _ => simp only [UpdElem.toElemS, mrefOf, reduceCtorEq] at ha
    | _ => simp only [UpdElem.toElemS, mrefOf, reduceCtorEq] at ha
  | _, .decl U y r, a, hv, ha, τ₁, hτ => by
    obtain ⟨-, rfl⟩ := UView.add_eq_one hv
    cases r with
    | mref i' =>
      simp only [mrefOf, Option.some.injEq] at ha
      subst ha
      rw [apply_decl_mref] at hτ
      obtain ⟨_, -, hτ⟩ := Res.bind_eq_ok.1 hτ
      obtain ⟨id, hid, -⟩ := Res.bind_eq_ok.1 hτ
      exact ⟨id, hid⟩
    | _ => simp only [mrefOf, reduceCtorEq] at ha
  | _, .pop U hx, a, hv, ha, τ₁, hτ => by
    rw [applyV_pop_map] at hτ
    cases h : U.applyVE τ₀ with
    | error => rw [h] at hτ; cases hτ
    | ok τ' => exact RelU.half_inv M U hv ha τ' h
  | _, .drop U hx, a, hv, ha, τ₁, hτ => by
    rw [applyV_drop_map] at hτ
    cases h : U.applyVE τ₀ with
    | error => rw [h] at hτ; cases hτ
    | ok τ' => exact RelU.half_inv M U hv ha τ' h

/-- **The first element of an allocation's pair**, its pops and drops
around it: where the identity returns `id`, named at the next ordinal in
the births `B`, it writes, and binds its local to that root. -/
theorem RelU.half (h₀ : RelT σ ρ₀ τ₀) (M : LMem) {i : Tm C Γ .ident} {id : Nat}
    (hid : i.evalE τ₀ = .ok id) {B : MemNames.Births} (hB : ρ₀.sym.mem.births σ <+: B)
    (hj : LId.evalR B ⟨ρ₀.sym.mem.nAlloc, []⟩ = .ok id) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → {a : ElemS C Γ} → U.view = .one a → mrefOf a = some i →
      ∃ τ₁, U.applyVE τ₀ = .ok τ₁ ∧ RelB σ (U.replayS (pairActE ρ₀ M) (pairActR ρ₀) ρ₀) B τ₁.1 τ₁.2 ∧
        (U.replayS (pairActE ρ₀ M) (pairActR ρ₀) ρ₀).sym.mem = ρ₀.sym.mem
  | _, .nil, _, hv, _ => UView.noConfusion hv
  | _, .snoc U e, a, hv, ha => by
    obtain ⟨hz, rfl⟩ := UView.add_eq_one hv
    obtain ⟨τ₁, hτ₁, h₁, hs⟩ := RelU.zero (pairActE ρ₀ M) (pairActR ρ₀) h₀ U hz
    cases e with
    | «local» j r =>
      cases r with
      | mref i' =>
        simp only [UpdElem.toElemS, mrefOf, Option.some.injEq] at ha
        subst ha
        have hB₁ : (U.replayS (pairActE ρ₀ M) (pairActR ρ₀) ρ₀).sym.mem.births σ <+: B := by
          rw [hs]; exact hB
        refine ⟨(τ₁.1, τ₁.2.set j (some id)), ?_, ?_, ?_⟩
        · rw [apply_snoc_mref, hτ₁, Res.ok_bind, hid, Res.ok_bind]
        · exact (h₁.toRelB.grow hB₁).setLocal j (some id) _ ⟨id, hj, rfl⟩
        · show ((U.replayS (pairActE ρ₀ M) (pairActR ρ₀) ρ₀).bindAt _ _).sym.mem = _
          rw [← hs]; rfl
      | _ => simp only [UpdElem.toElemS, mrefOf, reduceCtorEq] at ha
    | _ => simp only [UpdElem.toElemS, mrefOf, reduceCtorEq] at ha
  | _, .decl U y r, a, hv, ha => by
    obtain ⟨hz, rfl⟩ := UView.add_eq_one hv
    obtain ⟨τ₁, hτ₁, h₁, hs⟩ := RelU.zero (pairActE ρ₀ M) (pairActR ρ₀) h₀ U hz
    cases r with
    | @mref R i' =>
      simp only [mrefOf, Option.some.injEq] at ha
      subst ha
      have hB₁ : (U.replayS (pairActE ρ₀ M) (pairActR ρ₀) ρ₀).sym.mem.births σ <+: B := by
        rw [hs]; exact hB
      refine ⟨(τ₁.1, τ₁.2.push (t := .mem R) (some id)), ?_, ?_, ?_⟩
      · rw [apply_decl_mref, hτ₁, Res.ok_bind, hid, Res.ok_bind]
      · exact (h₁.toRelB.grow hB₁).push _ (.inr ⟨_, rfl⟩) (t := .mem R) (some id)
          (fun b hb => by cases hb; exact ⟨id, hj, rfl⟩)
      · show ((U.replayS (pairActE ρ₀ M) (pairActR ρ₀) ρ₀).push _).sym.mem = _
        rw [SymS.push_mem, hs]
    | _ => simp only [mrefOf, reduceCtorEq] at ha
  | _, .pop U hx, a, hv, ha => by
    obtain ⟨τ₁, hτ₁, h₁, hs⟩ := RelU.half h₀ M hid hB hj U hv ha
    exact ⟨(τ₁.1, τ₁.2.drop hx), by rw [applyV_pop_map, hτ₁]; rfl, h₁.pop hx, hs⟩
  | _, .drop U hx, a, hv, ha => by
    obtain ⟨τ₁, hτ₁, h₁, hs⟩ := RelU.half h₀ M hid hB hj U hv ha
    exact ⟨(τ₁.1, τ₁.2.thin hx), by rw [applyV_drop_map, hτ₁]; rfl, h₁.thin hx, hs⟩

/-- **An allocation's pair**, its pops and drops around it: its guard
returns exactly where it does, and the state it leaves binds the identity
to the root of the next ordinal and the memory to the allocation. -/
theorem RelU.two (h₀ : RelT σ ρ₀ τ₀) {i : Tm C Γ .ident} {mm : Tm C Γ .mem} {g : LTerm}
    {M : LMem} (hq : pairLS ρ₀ i mm = some (g, M)) (hin : pairInS ρ₀ mm = true) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → {a b : ElemS C Γ} → U.view = .two a b →
      pairViewS a b = some (i, mm) →
      ((∃ v, g.eval σ = .ok v) ↔ ∃ τ', U.applyVE τ₀ = .ok τ') ∧
        ∀ τ', U.applyVE τ₀ = .ok τ' → RelU σ (U.replayS (pairActE ρ₀ M) (pairActR ρ₀) ρ₀) τ'.1 τ'.2
  | _, .nil, _, _, hv, _ => UView.noConfusion hv
  | _, .snoc U e, a, b, hv, hp => by
    obtain ⟨hU, rfl⟩ := UView.add_eq_two hv
    obtain ⟨hai, hb⟩ := pairViewS_some hp
    obtain ⟨Δb, hb⟩ := hb
    cases e with
    | memory mm' =>
      simp only [UpdElem.toElemS] at hb
      injection hb with hΔ hb
      subst hΔ
      injection (eq_of_heq hb) with hb
      subst mm'
      obtain ⟨H1, H2⟩ := RelU.pairKey h₀ hq hin
      have happ : (Upd.snoc U (.memory mm)).applyVE τ₀ = U.applyVE τ₀ >>= fun τ₁ =>
          mm.evalE τ₀ >>= fun μ =>
            .ok ({ τ₁.1 with heap := μ.heap, nextId := μ.nextId }, τ₁.2) := by
        show (U.applyVE τ₀ >>= fun p => (UpdElem.memory mm).applyVE τ₀ p.1 p.2) = _
        cases U.applyVE τ₀ with
        | error => rfl
        | ok p =>
          simp only [UpdElem.applyVE, UpdElem.globTE, bind, Except.bind]
          cases mm.evalE τ₀ <;> rfl
      rw [happ]
      refine ⟨H1.trans ⟨fun ⟨id, μ', hid, hμ'⟩ => ?_, fun ⟨τ', hτ⟩ => ?_⟩, fun τ' hτ => ?_⟩
      · obtain ⟨μ, B, hrun, -, hp, hj⟩ := H2 id μ' hid hμ'
        obtain ⟨τ₁, hτ₁, -⟩ := RelU.half h₀ M hid hp hj U hU hai
        exact ⟨_, by rw [hτ₁, Res.ok_bind, hμ', Res.ok_bind]⟩
      · obtain ⟨τ₁, hτ₁, hτ⟩ := Res.bind_eq_ok.1 hτ
        obtain ⟨μ', hμ', -⟩ := Res.bind_eq_ok.1 hτ
        obtain ⟨id, hid⟩ := RelU.half_inv M U hU hai τ₁ hτ₁
        exact ⟨id, μ', hid, hμ'⟩
      · obtain ⟨τ₁, hτ₁, hτ⟩ := Res.bind_eq_ok.1 hτ
        obtain ⟨μ', hμ', he⟩ := Res.bind_eq_ok.1 hτ
        cases he
        obtain ⟨id, hid⟩ := RelU.half_inv M U hU hai τ₁ hτ₁
        obtain ⟨μ, B, hrun, hh, hp, hj⟩ := H2 id μ' hid hμ'
        obtain ⟨τ₂, hτ₂, h₂, -⟩ := RelU.half h₀ M hid hp hj U hU hai
        rw [hτ₁, Except.ok.injEq] at hτ₂
        subst hτ₂
        exact h₂.setMem hrun (List.prefix_refl _) none hh
    | _ => simp only [UpdElem.toElemS] at hb; cases hb
  | _, .decl U y r, a, b, hv, hp => by
    obtain ⟨-, rfl⟩ := UView.add_eq_two hv
    obtain ⟨-, _, hb⟩ := pairViewS_some hp
    cases hb
  | _, .pop U hx, a, b, hv, hp => by
    obtain ⟨hg, hr⟩ := RelU.two h₀ hq hin U hv hp
    exact RelU.after_pop hx hg hr
  | _, .drop U hx, a, b, hv, hp => by
    obtain ⟨hg, hr⟩ := RelU.two h₀ hq hin U hv hp
    exact RelU.after_drop hx hg hr

end Pair


end Decide

end Solidity
