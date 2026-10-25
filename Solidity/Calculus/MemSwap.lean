import Solidity.Calculus.HashSwap
import Solidity.Calculus.RewritePast.Scope
import Solidity.Semantics.AllocBytes

/-!
# Fresh memory arrays read as words (M7, plan step 6)

A leaf binds fresh memory objects of any contents (`Fml.allocAll`, a
`catch` clause's data, a memory parameter).  Its reads of them are cut into
fresh atoms: at each binder of an array of primitives `x`, the binder is
read as `∀ uint n` (its length, a dynamic array's), and each read `x[e]` the
leaf makes as `∀ w` (its word, at its index), with what actual arrays make
of them in front (`MxCons`, Ackermann's reduction): two reads at equal
indices read one word.  A read is `e < n ? w : ⊥` (`⊥` halts: a read past
the length reverts), a length the binder's word (`Fml.mx`, `Tm.mx`).

`MxRel` relates a state of the leaf to one of the cut leaf: one storage,
ledger, balance and transaction, the heaps free (the cut leaf reads none),
the other locals alike, and each read the leaf makes (`MxOrig`) read by the
term that stands for it (`MxMap.tbl`).  Over it every term reads alike
(`Tm.mx_eval`, `Tm.mx_denote`) and every formula holds alike
(`Fml.mx_holds`): at a binder, from a fresh object the atoms its reads give
(`fillW`), from atoms that satisfy the premises an object that gives them
(`realizeW`).  So the cut is exact at every state (`Fml.mxTop_holds`): a
proof of the cut leaf proves the leaf, and a state refuting it refutes the
leaf, its objects any.

An index of a read must name no local bound past its array (it is read at
the binder) and be a term whose reading is its denotation (`Tm.ixOk`:
value locals, literals, the transaction's fields, operators).
-/

namespace Solidity.Decide

variable {C : Contract}

/-! ## Index terms -/

/-- A literal or a transaction field. -/
def _root_.Solidity.Op0.isIx {s : Srt} : Op0 C s → Bool
  | .lit _ => true
  | .env _ => true
  | _ => false

/-- A unary operator. -/
def _root_.Solidity.Op1.isIx {a s : Srt} : Op1 C a s → Bool
  | .unop _ _ => true
  | _ => false

/-- A binary operator. -/
def _root_.Solidity.Op2.isIx {a b s : Srt} : Op2 C a b s → Bool
  | .binop _ _ => true
  | _ => false

/-- A term whose reading in the interpreter is its denotation in the
Theory: value locals, literals, the transaction's fields, operators. -/
def _root_.Solidity.Tm.ixOk {Γ : Ctx} : {s : Srt} → Tm C Γ s → Bool
  | _, .pvV _ => true
  | _, .app0 o => o.isIx
  | _, .app1 o x => o.isIx && x.ixOk
  | _, .app2 o x y => o.isIx && x.ixOk && y.ixOk
  | _, _ => false

/-! ## The reads abstracted -/

/-- A read of the memory the leaf makes: a dynamic array's length, an
element of an array of primitives at an index term. -/
inductive MxOrig (C : Contract) (Γ : Ctx) : PrimTy → Type where
  | len {E : Ty} (i : Idx Γ (.mem (.array E))) : MxOrig C Γ .uint
  | elem {R : RefTy} {p : PrimTy} (i : Idx Γ (.mem R)) (a : ArrTy R (.prim p))
      (e : Tm C Γ (.val .uint)) (he : e.ixOk = true) : MxOrig C Γ p

/-- The read as a term. -/
def MxOrig.tm {Γ : Ctx} {p : PrimTy} : MxOrig C Γ p → Tm C Γ (.val p)
  | .len i => .app2 .mlen (.app0 .memory) (.pvI i)
  | .elem i a e _ => .app2 .read (.app0 .memory) (.app2 (.mat a) (.pvI i) e)

/-- An `ixOk` term weakened is `ixOk`. -/
theorem _root_.Solidity.Tm.ixOk_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {s : Srt} (t : Tm C Γ s) :
    t.ixOk = true → (t.wk h).ixOk = true := by
  induction t with
  | pvV _ => intro _; rfl
  | app0 o => intro ht; exact ht
  | app1 o x ih =>
    intro ht
    simp only [Tm.ixOk, Bool.and_eq_true] at ht
    rw [Tm.wk_app1]
    simp only [Tm.ixOk, ht.1, ih ht.2, Bool.and_self]
  | app2 o x y ihx ihy =>
    intro ht
    simp only [Tm.ixOk, Bool.and_eq_true] at ht
    rw [Tm.wk_app2]
    simp only [Tm.ixOk, ht.1.1, ihx ht.1.2, ihy ht.2, Bool.and_self]
  | _ => intro ht; simp only [Tm.ixOk, Bool.false_eq_true] at ht

/-- A read weakened. -/
def MxOrig.wk {Γ Δ : Ctx} (h : Thin Γ Δ) {p : PrimTy} : MxOrig C Γ p → MxOrig C Δ p
  | .len i => .len (i.wk h)
  | .elem i a e he => .elem (i.wk h) a (e.wk h) (Tm.ixOk_wk h e he)

theorem MxOrig.tm_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {p : PrimTy} :
    (o : MxOrig C Γ p) → (o.wk h).tm = o.tm.wk h
  | .len _ => rfl
  | .elem _ _ _ _ => rfl

/-- A read and the term of the cut leaf that stands for it. -/
abbrev MxEnt (C : Contract) (Γ Δ : Ctx) := (p : PrimTy) × MxOrig C Γ p × Tm C Δ (.val p)

/-- **The cut, so far**: where each local of the leaf is in the cut leaf
(`none` for a memory local), and the reads abstracted. -/
structure MxMap (C : Contract) (Γ Δ : Ctx) where
  loc : {t : LTy} → Idx Γ t → Option (Idx Δ t)
  tbl : List (MxEnt C Γ Δ)

/-- `φ₁ ∧ … ∧ φₙ`. -/
def mxConj {Γ : Ctx} : List (Fml C Γ) → Fml C Γ
  | [] => .tt
  | f :: fs => .and f (mxConj fs)

theorem holds_mxConj {Γ : Ctx} (σ : State C Γ) :
    (fs : List (Fml C Γ)) → (holds σ (mxConj fs) ↔ ∀ f ∈ fs, holds σ f)
  | [] => ⟨fun _ _ h => (nomatch h), fun _ => trivial⟩
  | f :: fs => by
    show holds σ f ∧ holds σ (mxConj fs) ↔ _
    rw [holds_mxConj σ fs]
    exact ⟨fun ⟨a, b⟩ g hg => (List.mem_cons.1 hg).elim (· ▸ a) (b g),
      fun h => ⟨h f List.mem_cons_self, fun g hg => h g (List.mem_cons_of_mem _ hg)⟩⟩

/-- The term an entry gives for `t`, where `t` is its read. -/
def MxEnt.look? {Γ Δ : Ctx} {s : Srt} (t : Tm C Γ s) (en : MxEnt C Γ Δ) : Option (Tm C Δ s) :=
  if h : Srt.val en.1 = s then
    if (h ▸ en.2.1.tm).beqR t then some (h ▸ en.2.2) else none
  else none

/-- The term the table gives for `t`. -/
def MxMap.look {Γ Δ : Ctx} (θ : MxMap C Γ Δ) {s : Srt} (t : Tm C Γ s) : Option (Tm C Δ s) :=
  θ.tbl.findSome? (MxEnt.look? t)

/-- The table's term for `t`, else `r`. -/
def MxMap.orLook {Γ Δ : Ctx} (θ : MxMap C Γ Δ) {s : Srt} (t : Tm C Γ s) (r : Option (Tm C Δ s)) :
    Option (Tm C Δ s) :=
  match θ.look t with
  | some r' => some r'
  | none => r

theorem MxMap.orLook_cases {Γ Δ : Ctx} (θ : MxMap C Γ Δ) {s : Srt} (t : Tm C Γ s)
    {r : Option (Tm C Δ s)} {t' : Tm C Δ s} (h : θ.orLook t r = some t') :
    θ.look t = some t' ∨ r = some t' := by
  unfold MxMap.orLook at h
  split at h
  · cases h; exact .inl (by assumption)
  · exact .inr h

/-- **A term, cut**: each read the table holds its term, every other symbol
kept; `none` on any other read of the memory. -/
def _root_.Solidity.Tm.mx {Γ Δ : Ctx} (θ : MxMap C Γ Δ) : {s : Srt} → Tm C Γ s → Option (Tm C Δ s)
  | _, .pvV i => θ.orLook (.pvV i) ((θ.loc i).map .pvV)
  | _, .pvP i => θ.orLook (.pvP i) ((θ.loc i).map .pvP)
  | _, .pvS i => θ.orLook (.pvS i) ((θ.loc i).map .pvS)
  | _, .pvI i => θ.orLook (.pvI i) none
  | _, .netOf i a => θ.orLook (.netOf i a) (do pure (.netOf (← θ.loc i) (← Tm.mx θ a)))
  | s, .app0 o => θ.orLook (.app0 o) (if s.isMem then none else some (.app0 o))
  | s, .app1 (a := a) o x => θ.orLook (.app1 o x)
      (if a.isMem || s.isMem then none else (Tm.mx θ x).map (.app1 o))
  | s, .app2 (a := a) (b := b) o x y => θ.orLook (.app2 o x y)
      (if a.isMem || b.isMem || s.isMem then none else
        (Tm.mx θ x).bind fun x' => (Tm.mx θ y).map fun y' => .app2 o x' y')
  | s, .app3 (a := a) (b := b) (c := c) o x y z => θ.orLook (.app3 o x y z)
      (if a.isMem || b.isMem || c.isMem || s.isMem then none else
        (Tm.mx θ x).bind fun x' => (Tm.mx θ y).bind fun y' => (Tm.mx θ z).map fun z' =>
          .app3 o x' y' z')
  | _, .pvZ i => θ.orLook (.pvZ i) ((θ.loc i).map .pvZ)

/-! ## States read alike -/

/-- **A state of the leaf and one of the cut leaf**: their global parts alike
but for the heap, each local the map places read alike, and each read the
table holds read by its term. -/
structure MxRel {Γ Δ : Ctx} (θ : MxMap C Γ Δ) (τ : State C Γ) (ρ : State C Δ) : Prop where
  glob : GAgree τ.glob ρ.glob
  loc : ∀ {t : LTy} (i : Idx Γ t) (j : Idx Δ t), θ.loc i = some j → ρ.getV j = τ.getV i
  tbl : ∀ en ∈ θ.tbl, en.2.2.eval ρ = Srt.trO (.val en.1) (en.2.1.tm.eval τ) ∧
    en.2.2.denote ρ = en.2.1.tm.denote τ

theorem MxMap.look_spec {Γ Δ : Ctx} (θ : MxMap C Γ Δ) {s : Srt} (t : Tm C Γ s) {r : Tm C Δ s}
    (h : θ.look t = some r) :
    ∃ en ∈ θ.tbl, ∃ hs : Srt.val en.1 = s, hs ▸ en.2.1.tm = t ∧ hs ▸ en.2.2 = r := by
  obtain ⟨en, hm, he⟩ := List.exists_of_findSome?_eq_some h
  refine ⟨en, hm, ?_⟩
  unfold MxEnt.look? at he
  split at he
  · rename_i hs
    split at he
    · rename_i hb
      cases he
      exact ⟨hs, Tm.eq_of_beqR hb, rfl⟩
    · cases he
  · cases he

section Terms

variable {Γ Δ : Ctx} {θ : MxMap C Γ Δ} {τ : State C Γ} {ρ : State C Δ}

theorem MxRel.look (hr : MxRel θ τ ρ) {s : Srt} (t : Tm C Γ s) {r : Tm C Δ s}
    (h : θ.look t = some r) : r.eval ρ = Srt.trO s (t.eval τ) ∧ r.denote ρ = t.denote τ := by
  obtain ⟨⟨p, o, tr⟩, hm, hs, ht, hr'⟩ := θ.look_spec t h
  subst hs ht hr'
  exact hr.tbl _ hm

/-- **A cut term reads as the term.** -/
theorem _root_.Solidity.Tm.mx_eval (hr : MxRel θ τ ρ) {s : Srt} (t : Tm C Γ s) :
    {t' : Tm C Δ s} → t.mx θ = some t' → t'.eval ρ = Srt.trO s (t.eval τ) := by
  induction t with
  | pvV i =>
    intro t' e
    rcases MxMap.orLook_cases θ _ e with e | e
    · exact (hr.look _ e).1
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 e
      exact congrArg some (hr.loc _ _ hj)
  | pvP i =>
    intro t' e
    rcases MxMap.orLook_cases θ _ e with e | e
    · exact (hr.look _ e).1
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 e
      exact hr.loc _ _ hj
  | pvS i =>
    intro t' e
    rcases MxMap.orLook_cases θ _ e with e | e
    · exact (hr.look _ e).1
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 e
      exact congrArg some (hr.loc _ _ hj)
  | pvI i =>
    intro t' e
    rcases MxMap.orLook_cases θ _ e with e | e
    · exact (hr.look _ e).1
    · cases e
  | pvZ i =>
    intro t' e
    rcases MxMap.orLook_cases θ _ e with e | e
    · exact (hr.look _ e).1
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 e
      exact congrArg some (hr.loc _ _ hj)
  | netOf i a ih =>
    intro t' e
    rcases MxMap.orLook_cases θ _ e with e | e
    · exact (hr.look _ e).1
    · obtain ⟨j, hj, e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨a', ha, e⟩ := Option.bind_eq_some_iff.1 e
      cases e
      have hl : TEnv.get j ρ.env = TEnv.get i τ.env := hr.loc _ _ hj
      show (a'.eval ρ).bind (Tm.netOfT (TEnv.get j ρ.env)) = (a.eval τ).bind (Tm.netOfT (TEnv.get i τ.env))
      rw [ih ha, hl]
      rfl
  | app0 o =>
    intro t' e
    rcases MxMap.orLook_cases θ _ e with e | e
    · exact (hr.look _ e).1
    · split at e
      · cases e
      · rename_i hs
        cases e
        exact Op0.eval_trO o (Bool.eq_false_iff.2 hs) hr.glob
  | app1 o x ih =>
    intro t' e
    rcases MxMap.orLook_cases θ _ e with e | e
    · exact (hr.look _ e).1
    · split at e
      · cases e
      · rename_i hm
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hm
        obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 e
        show o.eval ρ.glob (x'.eval ρ) = _
        rw [ih hx]
        exact Op1.eval_trO o hm.1 hm.2 hr.glob _
  | app2 o x y ihx ihy =>
    intro t' e
    rcases MxMap.orLook_cases θ _ e with e | e
    · exact (hr.look _ e).1
    · split at e
      · cases e
      · rename_i hm
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hm
        obtain ⟨x', hx, e⟩ := Option.bind_eq_some_iff.1 e
        obtain ⟨y', hy, rfl⟩ := Option.map_eq_some_iff.1 e
        show o.eval ρ.glob (x'.eval ρ) (y'.eval ρ) = _
        rw [ihx hx, ihy hy]
        exact Op2.eval_trO o hm.1.1 hm.1.2 hr.glob _ _
  | app3 o x y z ihx ihy ihz =>
    intro t' e
    rcases MxMap.orLook_cases θ _ e with e | e
    · exact (hr.look _ e).1
    · split at e
      · cases e
      · rename_i hm
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hm
        obtain ⟨x', hx, e⟩ := Option.bind_eq_some_iff.1 e
        obtain ⟨y', hy, e⟩ := Option.bind_eq_some_iff.1 e
        obtain ⟨z', hz, rfl⟩ := Option.map_eq_some_iff.1 e
        show o.eval ρ.glob (x'.eval ρ) (y'.eval ρ) (z'.eval ρ) = _
        rw [ihx hx, ihy hy, ihz hz]
        exact Op3.eval_trO (g := τ.glob) o hm.1.1.1 _ _ _

/-- **A cut term denotes as the term.** -/
theorem _root_.Solidity.Tm.mx_denote (hr : MxRel θ τ ρ) {s : Srt} (t : Tm C Γ s) :
    {t' : Tm C Δ s} → t.mx θ = some t' → t'.denote ρ = t.denote τ := by
  induction t with
  | pvV i =>
    intro t' e
    rcases MxMap.orLook_cases θ _ e with e | e
    · exact (hr.look _ e).2
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 e
      exact congrArg some (hr.loc _ _ hj)
  | pvP i =>
    intro t' e
    rcases MxMap.orLook_cases θ _ e with e | e
    · exact (hr.look _ e).2
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 e
      have hl : TEnv.get j ρ.env = TEnv.get i τ.env := hr.loc _ _ hj
      simp only [Tm.denote]
      revert hl
      generalize TEnv.get j ρ.env = a
      generalize TEnv.get i τ.env = b
      intro hl
      subst hl
      cases a <;> rfl
  | pvS i =>
    intro t' e
    rcases MxMap.orLook_cases θ _ e with e | e
    · exact (hr.look _ e).2
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 e
      have hl : TEnv.get j ρ.env = TEnv.get i τ.env := hr.loc _ _ hj
      show Storage.obs _ = Storage.obs _
      rw [hl]
  | pvI i =>
    intro t' e
    rcases MxMap.orLook_cases θ _ e with e | e
    · exact (hr.look _ e).2
    · cases e
  | pvZ i =>
    intro t' e
    rcases MxMap.orLook_cases θ _ e with e | e
    · exact (hr.look _ e).2
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 e
      exact congrArg some (hr.loc _ _ hj)
  | netOf i a ih =>
    intro t' e
    rcases MxMap.orLook_cases θ _ e with e | e
    · exact (hr.look _ e).2
    · obtain ⟨j, hj, e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨a', ha, e⟩ := Option.bind_eq_some_iff.1 e
      cases e
      have hl : TEnv.get j ρ.env = TEnv.get i τ.env := hr.loc _ _ hj
      show (a'.denote ρ).map _ = (a.denote τ).map _
      rw [ih ha, hl]
  | app0 o =>
    intro t' e
    rcases MxMap.orLook_cases θ _ e with e | e
    · exact (hr.look _ e).2
    · split at e
      · cases e
      · cases e
        exact Op0.denote_agree o hr.glob
  | app1 o x ih =>
    intro t' e
    rcases MxMap.orLook_cases θ _ e with e | e
    · exact (hr.look _ e).2
    · split at e
      · cases e
      · obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 e
        show o.denote ρ.glob (x'.denote ρ) = o.denote τ.glob (x.denote τ)
        rw [ih hx]
        exact Op1.denote_agree o hr.glob _
  | app2 o x y ihx ihy =>
    intro t' e
    rcases MxMap.orLook_cases θ _ e with e | e
    · exact (hr.look _ e).2
    · split at e
      · cases e
      · rename_i hm
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hm
        obtain ⟨x', hx, e⟩ := Option.bind_eq_some_iff.1 e
        obtain ⟨y', hy, rfl⟩ := Option.map_eq_some_iff.1 e
        show o.denote ρ.glob (x'.eval ρ) (y'.eval ρ) (x'.denote ρ) (y'.denote ρ) =
          o.denote τ.glob (x.eval τ) (y.eval τ) (x.denote τ) (y.denote τ)
        rw [ihx hx, ihy hy]
        exact Op2.denote_agree o hm.1.1 _ _ _ _ (Tm.mx_eval hr x hx) (Tm.mx_eval hr y hy) _ _
  | app3 o x y z ihx ihy ihz =>
    intro t' e
    rcases MxMap.orLook_cases θ _ e with e | e
    · exact (hr.look _ e).2
    · split at e
      · cases e
      · obtain ⟨x', hx, e⟩ := Option.bind_eq_some_iff.1 e
        obtain ⟨y', hy, e⟩ := Option.bind_eq_some_iff.1 e
        obtain ⟨z', hz, rfl⟩ := Option.map_eq_some_iff.1 e
        show o.denote (x'.denote ρ) (y'.denote ρ) (z'.denote ρ) =
          o.denote (x.denote τ) (y.denote τ) (z.denote τ)
        rw [ihx hx, ihy hy, ihz hz]

end Terms

/-! ## Binders of the atoms -/

/-- `k` locals of type `q` pushed on `Δ`, the first outermost. -/
def MxRd (q : PrimTy) : Nat → Ctx → Ctx
  | 0, Δ => Δ
  | k + 1, Δ => MxRd q k (.val q :: Δ)

/-- A thinning extended past the `k` locals. -/
def mxThinN (q : PrimTy) : (k : Nat) → {Δ₀ Δ : Ctx} → Thin Δ₀ Δ → Thin Δ₀ (MxRd q k Δ)
  | 0, _, _, h => h
  | k + 1, _, _, h => mxThinN q k (.drop h)

/-- The `j`-th of the `k` locals. -/
def mxAtom (q : PrimTy) : (k : Nat) → {Δ : Ctx} → Fin k → Idx (MxRd q k Δ) (.val q)
  | k + 1, _, ⟨0, _⟩ => Idx.wk (mxThinN q k .refl) .here
  | k + 1, _, ⟨j + 1, hj⟩ => mxAtom q k ⟨j, Nat.lt_of_succ_lt_succ hj⟩

/-- `∀ q x; … ∀ q x;` around `φ`, `k` times. -/
def mxAll (x : Var) (q : PrimTy) : (k : Nat) → {Δ : Ctx} → Fml C (MxRd q k Δ) → Fml C Δ
  | 0, _, φ => φ
  | k + 1, _, φ => .all x q (mxAll x q k φ)

/-- The `k` locals pushed, holding `ws`. -/
def mxPush (q : PrimTy) : (k : Nat) → {Δ : Ctx} → State C Δ → (Fin k → q.Denote) →
    State C (MxRd q k Δ)
  | 0, _, ρ, _ => ρ
  | k + 1, _, ρ, ws => mxPush q k (ρ.push (t := .val q) (ws 0)) (fun j => ws j.succ)

/-- `v` in front of `ws`. -/
def mxConsW {α : Type} {k : Nat} (v : α) (ws : Fin k → α) : Fin (k + 1) → α
  | ⟨0, _⟩ => v
  | ⟨j + 1, h⟩ => ws ⟨j, Nat.lt_of_succ_lt_succ h⟩

theorem holds_mxAll (x : Var) (q : PrimTy) (k : Nat) {Δ : Ctx} (ρ : State C Δ)
    (φ : Fml C (MxRd q k Δ)) : holds ρ (mxAll x q k φ) ↔ ∀ ws, holds (mxPush q k ρ ws) φ := by
  induction k generalizing Δ with
  | zero => exact ⟨fun h _ => h, fun h => h (fun j => j.elim0)⟩
  | succ k ih =>
    show (∀ v, holds (ρ.push (t := .val q) v) (mxAll x q k φ)) ↔ _
    constructor
    · intro h ws
      exact (ih _ φ).1 (h (ws 0)) _
    · intro h v
      refine (ih _ φ).2 fun ws => ?_
      exact h (mxConsW v ws)

theorem thin_mxPush (q : PrimTy) (k : Nat) {Δ₀ Δ : Ctx} (h : Thin Δ₀ Δ) (ρ : State C Δ)
    (ws : Fin k → q.Denote) : (mxPush q k ρ ws).thin (mxThinN q k h) = ρ.thin h := by
  induction k generalizing Δ with
  | zero => rfl
  | succ k ih => exact ih (.drop h) _ _

theorem glob_mxPush (q : PrimTy) (k : Nat) {Δ : Ctx} (ρ : State C Δ) (ws : Fin k → q.Denote) :
    (mxPush q k ρ ws).glob = ρ.glob := by
  induction k generalizing Δ with
  | zero => rfl
  | succ k ih => exact ih _ _

theorem mxThin_refl {Δ : Ctx} (ρ : State C Δ) : ρ.thin .refl = ρ := by
  cases ρ; rfl

theorem getV_mxAtom (q : PrimTy) (k : Nat) {Δ : Ctx} (ρ : State C Δ) (ws : Fin k → q.Denote)
    (j : Fin k) : (mxPush q k ρ ws).getV (mxAtom q k j) = ws j := by
  induction k generalizing Δ with
  | zero => exact j.elim0
  | succ k ih =>
    obtain ⟨j, hj⟩ := j
    cases j with
    | zero =>
      show (mxPush q k (ρ.push (t := .val q) (ws 0)) _).getV (Idx.wk (mxThinN q k .refl) .here) = _
      rw [← State.getV_thin, thin_mxPush, mxThin_refl]
      rfl
    | succ j => exact ih _ _ ⟨j, _⟩

theorem getV_mxLift (q : PrimTy) (k : Nat) {Δ₀ Δ : Ctx} (h : Thin Δ₀ Δ) (ρ : State C Δ)
    (ws : Fin k → q.Denote) {t : LTy} (i : Idx Δ₀ t) :
    (mxPush q k ρ ws).getV (i.wk (mxThinN q k h)) = ρ.getV (i.wk h) := by
  rw [← State.getV_thin, thin_mxPush, State.getV_thin]

theorem eval_mxLift (q : PrimTy) (k : Nat) {Δ₀ Δ : Ctx} (h : Thin Δ₀ Δ) (ρ : State C Δ)
    (ws : Fin k → q.Denote) {p : PrimTy} (t : Tm C Δ₀ (.val p)) :
    ((t.wk (mxThinN q k h)).eval (mxPush q k ρ ws) : Option p.Denote) = t.eval (ρ.thin h) := by
  rw [Tm.eval_wk]
  exact congrArg (fun (X : State C Δ₀) => (show Option p.Denote from t.eval X)) (thin_mxPush q k h ρ ws)

theorem denote_mxLift (q : PrimTy) (k : Nat) {Δ₀ Δ : Ctx} (h : Thin Δ₀ Δ) (ρ : State C Δ)
    (ws : Fin k → q.Denote) {s : Srt} (t : Tm C Δ₀ s) :
    (t.wk (mxThinN q k h)).denote (mxPush q k ρ ws) = t.denote (ρ.thin h) := by
  rw [Tm.denote_wk, thin_mxPush]

theorem mxThin_drop_push {Δ : Ctx} {t : LTy} (ρ : State C Δ) (v : t.TDenote C ρ.H) :
    (ρ.push v).thin (.drop .refl) = ρ := by
  cases ρ; rfl

/-! ## Index terms read alike -/

/-- A denotation and a reading alike at a value sort. -/
def MxDenEq {H : HTy} : (s : Srt) → s.TDen C → Option (s.Den C H) → Prop
  | .val _, d, x => d = x
  | _, _, _ => True

theorem _root_.Solidity.Tm.ixOk_denoteG {Γ : Ctx} (σ : State C Γ) {s : Srt} (t : Tm C Γ s) :
    t.ixOk = true → MxDenEq s (t.denote σ) (t.eval σ) := by
  induction t with
  | pvV _ => intro _; rfl
  | app0 o =>
    intro h
    cases o with
    | lit => rfl
    | env => rfl
    | _ => simp only [Tm.ixOk, Op0.isIx, Bool.false_eq_true] at h
  | app1 o x ih =>
    intro h
    simp only [Tm.ixOk, Bool.and_eq_true] at h
    have hx := ih h.2
    cases o with
    | unop op hp =>
      show (x.denote σ).bind (op.evalT hp) = Op1.eval σ.glob (.unop op hp) (x.eval σ)
      rw [show x.denote σ = x.eval σ from hx, Op1.eval_eq_evalM]
      rfl
    | _ => simp only [Op1.isIx, Bool.false_eq_true, false_and] at h
  | app2 o x y ihx ihy =>
    intro h
    simp only [Tm.ixOk, Bool.and_eq_true] at h
    have hx := ihx h.1.2
    have hy := ihy h.2
    cases o with
    | binop op hp =>
      show (x.denote σ).bind (fun a => binopT op hp a (y.denote σ)) =
        Op2.eval σ.glob (.binop op hp) (x.eval σ) (y.eval σ)
      rw [show x.denote σ = x.eval σ from hx, show y.denote σ = y.eval σ from hy,
        Op2.eval_eq_evalM]
      rfl
    | _ => simp only [Op2.isIx, Bool.false_eq_true, false_and] at h
  | _ => intro h; simp only [Tm.ixOk, Bool.false_eq_true] at h

/-- An index term reads its denotation. -/
theorem _root_.Solidity.Tm.ixOk_denote {Γ : Ctx} (σ : State C Γ) {p : PrimTy}
    (t : Tm C Γ (.val p)) (h : t.ixOk = true) : t.denote σ = t.eval σ :=
  Tm.ixOk_denoteG σ t h

/-- An index term reads alike in two states whose global parts agree but
for the heap and whose value locals agree. -/
theorem _root_.Solidity.Tm.ixOk_eval {Γ : Ctx} {τ τ' : State C Γ} (hg : GAgree τ.glob τ'.glob)
    (hl : ∀ {p : PrimTy} (i : Idx Γ (.val p)), τ'.getV i = τ.getV i) {s : Srt} (t : Tm C Γ s) :
    t.ixOk = true → t.eval τ' = Srt.trO s (t.eval τ) := by
  induction t with
  | pvV i => intro _; exact congrArg some (hl i)
  | app0 o =>
    intro h
    cases o with
    | lit => rfl
    | env k => exact Op0.eval_trO (Op0.env k) rfl hg
    | _ => simp only [Tm.ixOk, Op0.isIx, Bool.false_eq_true] at h
  | app1 o x ih =>
    intro h
    simp only [Tm.ixOk, Bool.and_eq_true] at h
    show Op1.eval τ'.glob o (x.eval τ') = Srt.trO _ (Op1.eval τ.glob o (x.eval τ))
    rw [ih h.2]
    cases o with
    | unop op hp => exact Op1.eval_trO _ rfl rfl hg _
    | _ => simp only [Op1.isIx, Bool.false_eq_true, false_and] at h
  | app2 o x y ihx ihy =>
    intro h
    simp only [Tm.ixOk, Bool.and_eq_true] at h
    show Op2.eval τ'.glob o (x.eval τ') (y.eval τ') = Srt.trO _ (Op2.eval τ.glob o (x.eval τ) (y.eval τ))
    rw [ihx h.1.2, ihy h.2]
    cases o with
    | binop op hp => exact Op2.eval_trO _ rfl rfl hg _ _
    | _ => simp only [Op2.isIx, Bool.false_eq_true, false_and] at h
  | _ => intro h; simp only [Tm.ixOk, Bool.false_eq_true] at h

/-! ## Past a value binder -/

/-- The cut past a value local bound on both sides. -/
def MxMap.push {Γ Δ : Ctx} (θ : MxMap C Γ Δ) (u : LTy) : MxMap C (u :: Γ) (u :: Δ) where
  loc := fun {_} i => match i with
    | .here => some .here
    | .there j => (θ.loc j).map .there
  tbl := θ.tbl.map fun en => ⟨en.1, en.2.1.wk (.drop .refl), en.2.2.wk (.drop .refl)⟩

theorem MxRel.push {Γ Δ : Ctx} {θ : MxMap C Γ Δ} {τ : State C Γ} {ρ : State C Δ}
    (hr : MxRel θ τ ρ) (p : PrimTy) (v : p.Denote) :
    MxRel (θ.push (.val p)) (τ.push (t := .val p) v) (ρ.push (t := .val p) v) where
  glob := hr.glob
  loc := fun {t} i j h => by
    cases i with
    | here => cases h; rfl
    | there i =>
      obtain ⟨j', hj', rfl⟩ := Option.map_eq_some_iff.1 h
      exact hr.loc i j' hj'
  tbl := fun en hm => by
    obtain ⟨⟨q, o, r⟩, hm', rfl⟩ := List.mem_map.1 hm
    have h := hr.tbl _ hm'
    dsimp only at h ⊢
    rw [MxOrig.tm_wk, Tm.eval_wk, Tm.eval_wk, Tm.denote_wk, Tm.denote_wk, mxThin_drop_push,
      mxThin_drop_push]
    exact h

/-! ## The reads of a fresh array -/

/-- An array of primitives: its element type and how it is indexed. -/
def _root_.Solidity.RefTy.mxArr? : (R : RefTy) → Option ((q : PrimTy) × ArrTy R (.prim q))
  | .array (.prim q) => some ⟨q, .dyn⟩
  | .fixed (.prim q) N => if N < 2 ^ 256 then some ⟨q, .fixed⟩ else none
  | _ => none

/-- The index of an element address of the local at position `hx`, read
in `Γ` (`h` drops the locals past it). -/
def _root_.Solidity.Tm.mxAt? {Γ Γc : Ctx} (h : Thin Γ Γc) (hx : Nat) {T : Ty} :
    Tm C Γc (.addr T) → Option (Tm C Γ (.val .uint))
  | .app2 (.mat _) (.pvI i) e => if i.toNat = hx then e.thinS? h else none
  | _ => none

/-- The index of a read of the memory at an element of the local at `hx`. -/
def _root_.Solidity.Op2.mxIdx {Γ Γc : Ctx} (h : Thin Γ Γc) (hx : Nat) {a b s : Srt} :
    Op2 C a b s → Tm C Γc a → Tm C Γc b → List (Tm C Γ (.val .uint))
  | .read, .app0 .memory, y => (Tm.mxAt? h hx y).toList
  | _, _, _ => []

/-- **The indices at which a term reads the local at `hx`**, read in `Γ`. -/
def _root_.Solidity.Tm.mxIdx {Γ Γc : Ctx} (h : Thin Γ Γc) (hx : Nat) :
    {s : Srt} → Tm C Γc s → List (Tm C Γ (.val .uint))
  | _, .netOf _ a => a.mxIdx h hx
  | _, .app1 _ x => x.mxIdx h hx
  | _, .app2 o x y => o.mxIdx h hx x y ++ x.mxIdx h hx ++ y.mxIdx h hx
  | _, .app3 _ x y z => x.mxIdx h hx ++ y.mxIdx h hx ++ z.mxIdx h hx
  | _, _ => []

/-- **The indices at which a formula reads the local at `hx`**, read in `Γ`. -/
def _root_.Solidity.Fml.mxIdx {Γ : Ctx} : {Γc : Ctx} → Thin Γ Γc → Nat → Fml C Γc →
    List (Tm C Γ (.val .uint))
  | _, h, hx, .eq a b => a.mxIdx h hx ++ b.mxIdx h hx
  | _, h, hx, .not φ => φ.mxIdx h hx
  | _, h, hx, .and φ ψ => φ.mxIdx h hx ++ ψ.mxIdx h hx
  | _, h, hx, .imp φ ψ => φ.mxIdx h hx ++ ψ.mxIdx h hx
  | _, h, hx, .all _ _ φ => φ.mxIdx (.drop h) (hx + 1)
  | _, h, hx, .allocAll _ _ φ => φ.mxIdx (.drop h) (hx + 1)
  | _, _, _, _ => []

/-- Terms without repeats. -/
def mxDedup {Γ : Ctx} {s : Srt} : List (Tm C Γ s) → List (Tm C Γ s)
  | [] => []
  | t :: ts => let r := mxDedup ts; if r.any (·.beqR t) then r else t :: r

/-- An index of a read, its cut. -/
structure MxIx {Γ Δ : Ctx} (θ : MxMap C Γ Δ) where
  e : Tm C Γ (.val .uint)
  he : e.ixOk = true
  e' : Tm C Δ (.val .uint)
  hmx : e.mx θ = some e'

/-- The indices `Tm.ixOk` takes and the cut reads. -/
def MxMap.ixs {Γ Δ : Ctx} (θ : MxMap C Γ Δ) (es : List (Tm C Γ (.val .uint))) : List (MxIx θ) :=
  es.filterMap fun e =>
    if he : e.ixOk = true then
      match hm : e.mx θ with
      | some e' => some ⟨e, he, e', hm⟩
      | none => none
    else none

/-- `⊥` at `q`: a term that halts (`1 / 0` decides it). -/
def mxHalt {Γ : Ctx} (q : PrimTy) : Tm C Γ (.val q) :=
  .app3 .ite (.app2 (.binop .eqB rfl) (.app2 (.binop .div rfl) (.app0 (.lit (uintOfNat 1)))
    (.app0 (.lit (uintOfNat 0)))) (.app0 (.lit (uintOfNat 0))))
    (.app0 (.lit (PrimTy.dflt q))) (.app0 (.lit (PrimTy.dflt q)))

/-- The bound of an index: the length's word, a fixed array's length. -/
def mxBound {Δ : Ctx} (n : Idx Δ (.val .uint)) {R : RefTy} {q : PrimTy} :
    ArrTy R (.prim q) → Tm C Δ (.val .uint)
  | .dyn => .pvV n
  | @ArrTy.fixed _ N => .app0 (.lit (uintOfNat N))

/-- The length's entry: a dynamic array's length is the binder's word. -/
def mxLenEnts {Γ Δ : Ctx} (n : Idx Δ (.val .uint)) {R : RefTy} {q : PrimTy} :
    ArrTy R (.prim q) → List (MxEnt C (.mem R :: Γ) Δ)
  | .dyn => [⟨.uint, .len .here, .pvV n⟩]
  | .fixed => []

/-- The `j`-th read: `e < bound ? w : ⊥`. -/
def mxReadT {Δ : Ctx} (q : PrimTy) (e bnd : Tm C Δ (.val .uint)) (w : Idx Δ (.val q)) :
    Tm C Δ (.val q) :=
  .app3 .ite (.app2 (.binop .lt rfl) e bnd) (.pvV w) (mxHalt q)

section Alloc

variable {Γ Δ : Ctx} (θ : MxMap C Γ Δ) {R : RefTy} {q : PrimTy} (a : ArrTy R (.prim q))
  (ps : List (MxIx θ))

/-- The cut leaf's context past the binder: the length's word, then one
word per read. -/
abbrev MxCtx := MxRd q ps.length (.val .uint :: Δ)

/-- The thinning from the cut leaf's context before the binder. -/
abbrev mxThin : Thin Δ (MxCtx θ (q := q) ps) := mxThinN q ps.length (.drop .refl)

/-- The length's word. -/
abbrev mxN : Idx (MxCtx θ (q := q) ps) (.val .uint) := Idx.wk (mxThinN q ps.length .refl) .here

/-- The `j`-th index, cut, past the binder. -/
abbrev mxE (j : Fin ps.length) : Tm C (MxCtx θ (q := q) ps) (.val .uint) :=
  (ps.get j).e'.wk (mxThin θ (q := q) ps)

/-- **The cut past a fresh array**: the other locals and reads moved past
the binder's words, the length and each read the term that stands for
it. -/
def MxMap.alloc : MxMap C (.mem R :: Γ) (MxCtx θ (q := q) ps) where
  loc := fun {_} i => match i with
    | .here => none
    | .there j => (θ.loc j).map (Idx.wk (mxThin θ (q := q) ps))
  tbl := θ.tbl.map (fun en => ⟨en.1, en.2.1.wk (.drop .refl), en.2.2.wk (mxThin θ (q := q) ps)⟩) ++
    mxLenEnts (mxN θ (q := q) ps) a ++
    (List.finRange ps.length).map fun j =>
      ⟨q, .elem .here a ((ps.get j).e.wk (.drop .refl)) (Tm.ixOk_wk _ _ (ps.get j).he),
        mxReadT q (mxE θ ps j) (mxBound (mxN θ (q := q) ps) a) (mxAtom q ps.length j)⟩

/-- **What actual arrays make of the reads**: two at equal indices read one
word. -/
def mxCons : Fml C (MxCtx θ (q := q) ps) :=
  mxConj ((List.finRange ps.length).flatMap fun j => (List.finRange ps.length).filterMap fun l =>
    if j.val < l.val then
      some (.imp (.eq (mxE θ ps j) (mxE θ ps l)) (.eq (.pvV (mxAtom q ps.length j)) (.pvV (mxAtom q ps.length l))))
    else none)

end Alloc

/-! ## Formulas -/

/-- **A formula, cut**: equations, the connectives, `∀`, and fresh arrays of
primitives (`allocAll`), each read as `∀ uint n` and one `∀` per read of it,
under what actual arrays make of the reads (`mxCons`). -/
def _root_.Solidity.Fml.mx : {Γ Δ : Ctx} → MxMap C Γ Δ → Fml C Γ → Option (Fml C Δ)
  | _, _, _, .tt => some .tt
  | _, _, θ, .eq a b => (a.mx θ).bind fun a' => (b.mx θ).map fun b' => .eq a' b'
  | _, _, θ, .not φ => (Fml.mx θ φ).map .not
  | _, _, θ, .and φ ψ => (Fml.mx θ φ).bind fun φ' => (Fml.mx θ ψ).map fun ψ' => .and φ' ψ'
  | _, _, θ, .imp φ ψ => (Fml.mx θ φ).bind fun φ' => (Fml.mx θ ψ).map fun ψ' => .imp φ' ψ'
  | _, _, θ, .all x p φ => (Fml.mx (θ.push (.val p)) φ).map (.all x p)
  | _, _, θ, .allocAll x R φ =>
    match R.mxArr? with
    | none => none
    | some ⟨q, a⟩ =>
      let ps := θ.ixs (mxDedup (φ.mxIdx (.drop .refl) 0))
      (Fml.mx (θ.alloc a ps) φ).map fun φ' =>
        .all x .uint (mxAll x q ps.length (.imp (mxCons θ (q := q) ps) φ'))
  | _, _, _, _ => none

/-- No local, no read. -/
def MxMap.id0 : MxMap C [] [] := ⟨fun i => some i, []⟩

/-- **A leaf, its fresh arrays cut** (`none` where a read is not cut). -/
def _root_.Solidity.Fml.mxTop (φ : Fml C []) : Option (Fml C []) := φ.mx MxMap.id0

/-! ## Reads of the heap -/

theorem _root_.Solidity.MObj.elems_wk_prim {H H' : HTy} (e : H <+: H') {R : RefTy} {q : PrimTy}
    (a : ArrTy R (.prim q)) (o : MObj H R) : MObj.elems a (MObj.wk e R o) = MObj.elems a o := by
  cases a with
  | dyn =>
    rw [MObj.elems_dyn, MObj.elems_dyn]
    show List.map (MVal.wk e (.prim q)) _ = _
    exact List.map_id' _
  | fixed =>
    rw [MObj.elems_fixed, MObj.elems_fixed]
    show List.map (MVal.wk e (.prim q)) _ = _
    exact List.map_id' _

/-- An element read by identity: the object's element, `none` past its
length. -/
theorem readAt_eval (g : State C []) {R : RefTy} {q : PrimTy} (a : ArrTy R (.prim q))
    (r : HRef g.H R) (k : PrimTy.uint.Denote) :
    (Op2.eval g (.read (p := q)) (some g.memT) (some (MAddrT.index r.id a k)) : Option q.Denote) =
      (MObj.elems a (g.heap.get r))[k.1.toNat]? := by
  rw [Op2.eval_eq_evalM]
  show (do g.memT.heap.readAddr (← (MAddrT.index r.id a k).resolve g.H) : Option (MVal g.H (.prim q))) = _
  rw [MAddrT.resolve_eq_resolveM]
  simp only [MAddrT.resolveM, HRef.ofId?_self, Option.map_some]
  rfl

/-- A dynamic array's length by identity. -/
theorem mlenAt_eval (g : State C []) {E : Ty} (r : HRef g.H (.array E)) :
    (Op2.eval g (.mlen (E := E)) (some g.memT) (some r.id) : Option PrimTy.uint.Denote) =
      some (g.heap.lenU r) := by
  rw [Op2.eval_eq_evalM]
  change (HRef.ofId? g.H (.array E) r.id).bind (fun x => some (g.heap.lenU x)) = _
  rw [HRef.ofId?_self]
  rfl

theorem _root_.Solidity.State.alloc_glob_get (τ : State C Γ') {R R' : RefTy} (o : MObj τ.H R)
    (r : HRef τ.H R') :
    HRef.ofId? (τ.alloc o).1.H R' r.id = some (r.wk (List.prefix_append τ.H [R])) := by
  have hid : r.id < τ.H.length := (List.getElem?_eq_some_iff.1 r.get?).1
  show HRef.ofId? (τ.H ++ [R]) R' r.id = _
  rw [HRef.ofId?_wk (List.prefix_append τ.H [R]) R' hid, HRef.ofId?_self]
  rfl

theorem gAgree_alloc {Γ' : Ctx} (τ : State C Γ') {R : RefTy} (o : MObj τ.H R) :
    GAgree τ.glob (τ.alloc o).1.glob := ⟨rfl, rfl, rfl, rfl⟩

/-- An allocation keeps an older array's length. -/
theorem lenU_alloc {Γ' : Ctx} (τ : State C Γ') {R : RefTy} (o : MObj τ.H R) {E : Ty}
    (r : HRef τ.H (.array E)) :
    (τ.alloc o).1.heap.lenU (r.wk (List.prefix_append τ.H [R])) = τ.heap.lenU r := by
  apply Subtype.ext
  show (((τ.heap.alloc o).1.len (r.wk _) .dyn : Nat) : Int) = ((τ.heap.len r .dyn : Nat) : Int)
  unfold Heap.len
  rw [Heap.keeps_alloc τ.heap o r, MObj.elems_dyn, MObj.elems_dyn]
  show ((List.map (MVal.wk _ E) _).length : Int) = _
  rw [List.length_map]

/-- **An allocation keeps every read the table holds.** -/
theorem MxOrig.eval_alloc {Γ' : Ctx} (τ : State C Γ') {R : RefTy} (o : MObj τ.H R) {p : PrimTy}
    (x : MxOrig C Γ' p) :
    ((x.wk (.drop .refl)).tm.eval (τ.allocPush o) : Option p.Denote) = x.tm.eval τ := by
  rw [MxOrig.tm_wk, Tm.eval_wk]
  have e1 : ((x.tm.eval ((τ.allocPush o).thin (.drop .refl))) : Option p.Denote) =
      x.tm.eval (τ.alloc o).1 :=
    congrArg (fun (X : State C Γ') => (show Option p.Denote from x.tm.eval X))
      (mxThin_drop_push (τ.alloc o).1 _)
  rw [e1]
  cases x with
  | len i =>
    show Op2.eval (τ.alloc o).1.glob .mlen (some (τ.alloc o).1.glob.memT) ((τ.alloc o).1.getV i) =
      Op2.eval τ.glob .mlen (some τ.glob.memT) (τ.getV i)
    rw [State.getV_alloc]
    have hg : τ.getV i = (TEnv.get i τ.env).map (·.id) := rfl
    rw [hg]
    cases TEnv.get i τ.env with
    | none => rw [Op2.eval_eq_evalM, Op2.eval_eq_evalM]; rfl
    | some r =>
      rw [Option.map_some, mlenAt_eval τ.glob r]
      rw [show r.id = (r.wk (List.prefix_append τ.H [R])).id from rfl]
      rw [mlenAt_eval (τ.alloc o).1.glob (r.wk (List.prefix_append τ.H [R]))]
      exact congrArg some (lenU_alloc τ o r)
  | elem i a e he =>
    have hE : (e.eval (τ.alloc o).1 : Option PrimTy.uint.Denote) = e.eval τ :=
      Tm.ixOk_eval (gAgree_alloc τ o) (fun j => State.getV_alloc τ o j) e he
    show Op2.eval (τ.alloc o).1.glob .read (some (τ.alloc o).1.glob.memT)
        (Op2.eval (τ.alloc o).1.glob (.mat a) ((τ.alloc o).1.getV i) (e.eval (τ.alloc o).1)) =
      Op2.eval τ.glob .read (some τ.glob.memT) (Op2.eval τ.glob (.mat a) (τ.getV i) (e.eval τ))
    rw [State.getV_alloc, hE]
    have hg : τ.getV i = (TEnv.get i τ.env).map (·.id) := rfl
    rw [hg]
    cases TEnv.get i τ.env with
    | none => simp only [Option.map_none, Op2.eval_eq_evalM, Op2.evalM]; rfl
    | some r =>
      cases e.eval τ with
      | none => simp only [Op2.eval_eq_evalM, Op2.evalM]; rfl
      | some k =>
        have h1 : Op2.eval (τ.alloc o).1.glob (.mat a) (some r.id) (some k) =
            some (MAddrT.index (r.wk (List.prefix_append τ.H [R])).id a k) := by
          rw [Op2.eval_eq_evalM]; rfl
        have h2 : Op2.eval τ.glob (.mat a) (some r.id) (some k) = some (MAddrT.index r.id a k) := by
          rw [Op2.eval_eq_evalM]; rfl
        rw [Option.map_some, h1, h2, readAt_eval τ.glob a r k,
          readAt_eval (τ.alloc o).1.glob a (r.wk (List.prefix_append τ.H [R])) k]
        show (MObj.elems a ((τ.heap.alloc o).1.get (r.wk _)))[k.1.toNat]? = _
        rw [Heap.keeps_alloc τ.heap o r, MObj.elems_wk_prim]
        rfl

/-! ## The terms that stand for reads -/

theorem mxHalt_eval {Δ' : Ctx} (σ : State C Δ') (q : PrimTy) :
    ((mxHalt q : Tm C Δ' (.val q)).eval σ : Option q.Denote) = none := by
  show Op3.eval σ.glob .ite (Op2.eval σ.glob (.binop .eqB rfl)
    (Op2.eval σ.glob (.binop .div rfl) (some (uintOfNat 1)) (some (uintOfNat 0))) (some (uintOfNat 0)))
    (some (PrimTy.dflt q)) (some (PrimTy.dflt q)) = none
  rw [Op3.eval_eq_evalM, Op2.eval_eq_evalM, Op2.eval_eq_evalM]
  rfl

theorem mxHalt_denote {Δ' : Ctx} (σ : State C Δ') (q : PrimTy) :
    ((mxHalt q : Tm C Δ' (.val q)).denote σ : Option q.Denote) = none := rfl

theorem mxReadT_eval {Δ' : Ctx} (σ : State C Δ') (q : PrimTy) (e bnd : Tm C Δ' (.val .uint))
    (w : Idx Δ' (.val q)) :
    ((mxReadT q e bnd w).eval σ : Option q.Denote) =
      (e.eval σ).bind fun x => (bnd.eval σ).bind fun b =>
        if x.1 < b.1 then some (σ.getV w) else none := by
  show Op3.eval σ.glob .ite (Op2.eval σ.glob (.binop .lt rfl) (e.eval σ) (bnd.eval σ))
    (some (σ.getV w)) ((mxHalt q).eval σ) = _
  rw [mxHalt_eval, Op3.eval_eq_evalM, Op2.eval_eq_evalM]
  cases e.eval σ with
  | none => rfl
  | some x =>
    cases bnd.eval σ with
    | none => rfl
    | some b =>
      show (some (decide (x.1 < b.1))).bind (fun c => cond c (some (σ.getV w)) none) = _
      by_cases h : x.1 < b.1 <;> simp [h]

theorem mxReadT_denote {Δ' : Ctx} (σ : State C Δ') (q : PrimTy) (e bnd : Tm C Δ' (.val .uint))
    (w : Idx Δ' (.val q)) :
    ((mxReadT q e bnd w).denote σ : Option q.Denote) =
      (e.denote σ).bind fun x => (bnd.denote σ).bind fun b =>
        if x.1 < b.1 then some (σ.getV w) else none := by
  show ((e.denote σ).bind fun x => binopT .lt rfl x (bnd.denote σ)).bind
    (fun c => cond c (some (σ.getV w)) ((mxHalt q).denote σ)) = _
  rw [mxHalt_denote]
  cases e.denote σ with
  | none => rfl
  | some x =>
    cases bnd.denote σ with
    | none => rfl
    | some b =>
      show (some (decide (x.1 < b.1))).bind (fun c => cond c (some (σ.getV w)) none) = _
      by_cases h : x.1 < b.1 <;> simp [h]

/-- A read of the memory reads its eval. -/
theorem MxOrig.denote_eq {Γ' : Ctx} (σ : State C Γ') {p : PrimTy} (x : MxOrig C Γ' p) :
    x.tm.denote σ = x.tm.eval σ := by
  cases x <;> rfl

/-! ## Past a fresh array -/

/-- The bound's word. -/
def mxBndV {R : RefTy} {q : PrimTy} (n : PrimTy.uint.Denote) : ArrTy R (.prim q) → PrimTy.uint.Denote
  | .dyn => n
  | @ArrTy.fixed _ N => uintOfNat N

theorem uint_nonneg (x : PrimTy.uint.Denote) : 0 ≤ x.1 := by
  have h := x.2
  simp only [PrimTy.inRange, decide_eq_true_eq] at h
  exact h.1

theorem lenU_toNat (n : PrimTy.uint.Denote) (h : n.1.toNat < 2 ^ 256) : lenU n.1.toNat h = n :=
  Subtype.ext (by show ((n.1.toNat : Nat) : Int) = n.1; exact Int.toNat_of_nonneg (uint_nonneg n))

/-- The new object's element, read at an index read before it. -/
theorem readNew_eval {Γ : Ctx} (τ : State C Γ) {R : RefTy} {q : PrimTy} (o : MObj τ.H R)
    (a : ArrTy R (.prim q)) (e : Tm C Γ (.val .uint)) (he : e.ixOk = true)
    (he' : (e.wk (.drop .refl) : Tm C (.mem R :: Γ) _).ixOk = true) :
    ((MxOrig.elem .here a (e.wk (.drop .refl)) he').tm.eval (τ.allocPush o) : Option q.Denote) =
      (e.eval τ).bind fun k => (MObj.elems a o)[k.1.toNat]? := by
  have hE : ((e.wk (.drop .refl)).eval (τ.allocPush o) : Option PrimTy.uint.Denote) = e.eval τ := by
    rw [Tm.eval_wk]
    have e1 : ((e.eval ((τ.allocPush o).thin (.drop .refl))) : Option PrimTy.uint.Denote) =
        e.eval (τ.alloc o).1 :=
      congrArg (fun (X : State C Γ) => (show Option PrimTy.uint.Denote from e.eval X))
        (mxThin_drop_push (τ.alloc o).1 _)
    rw [e1]
    exact Tm.ixOk_eval (gAgree_alloc τ o) (fun j => State.getV_alloc τ o j) e he
  show Op2.eval (τ.alloc o).1.glob .read (some (τ.alloc o).1.glob.memT)
      (Op2.eval (τ.alloc o).1.glob (.mat a) (some (τ.alloc o).2.id) ((e.wk (.drop .refl)).eval (τ.allocPush o))) = _
  rw [hE]
  cases e.eval τ with
  | none => simp only [Op2.eval_eq_evalM, Op2.evalM]; rfl
  | some k =>
    have h1 : Op2.eval (τ.alloc o).1.glob (.mat a) (some (τ.alloc o).2.id) (some k) =
        some (MAddrT.index (τ.alloc o).2.id a k) := by
      rw [Op2.eval_eq_evalM]; rfl
    rw [h1, readAt_eval (τ.alloc o).1.glob a (τ.alloc o).2 k]
    show (MObj.elems a ((τ.heap.alloc o).1.get (τ.heap.alloc o).2))[k.1.toNat]? = _
    rw [Heap.get_alloc, MObj.elems_wk_prim]
    rfl

/-- The new array's length. -/
theorem lenNew_eval {Γ : Ctx} (τ : State C Γ) {q : PrimTy} (o : MObj τ.H (.array (.prim q))) :
    ((MxOrig.len (Γ := .mem (.array (.prim q)) :: Γ) .here).tm.eval (τ.allocPush o) :
      Option PrimTy.uint.Denote) =
      some (lenU (MObj.elems .dyn o).length (by rw [MObj.elems_dyn]; exact o.2)) := by
  show Op2.eval (τ.alloc o).1.glob .mlen (some (τ.alloc o).1.glob.memT) (some (τ.alloc o).2.id) = _
  rw [mlenAt_eval (τ.alloc o).1.glob (τ.alloc o).2]
  congr 1
  apply Subtype.ext
  show (((τ.heap.alloc o).1.len (τ.heap.alloc o).2 .dyn : Nat) : Int) = _
  unfold Heap.len
  rw [Heap.get_alloc, MObj.elems_wk_prim]
  rfl

section AllocRel

variable {Γ Δ : Ctx} {θ : MxMap C Γ Δ} {τ : State C Γ} {ρ : State C Δ} {R : RefTy} {q : PrimTy}

theorem getV_mxN (ps : List (MxIx θ)) (ρ : State C Δ) (n : PrimTy.uint.Denote)
    (ws : Fin ps.length → q.Denote) :
    (mxPush q ps.length (ρ.push (t := .val .uint) n) ws).getV (mxN θ (q := q) ps) = n := by
  rw [← State.getV_thin, thin_mxPush, mxThin_refl]
  rfl

theorem mxBound_eval (ps : List (MxIx θ)) (a : ArrTy R (.prim q)) (ρ : State C Δ)
    (n : PrimTy.uint.Denote) (ws : Fin ps.length → q.Denote) :
    ((mxBound (mxN θ (q := q) ps) a).eval (mxPush q ps.length (ρ.push (t := .val .uint) n) ws) :
      Option PrimTy.uint.Denote) = some (mxBndV n a) ∧
    ((mxBound (mxN θ (q := q) ps) a).denote (mxPush q ps.length (ρ.push (t := .val .uint) n) ws) :
      Option PrimTy.uint.Denote) = some (mxBndV n a) := by
  cases a with
  | dyn => exact ⟨congrArg some (getV_mxN ps ρ n ws), congrArg some (getV_mxN ps ρ n ws)⟩
  | fixed => exact ⟨rfl, rfl⟩

theorem mxE_eval (hr : MxRel θ τ ρ) (ps : List (MxIx θ)) (n : PrimTy.uint.Denote)
    (ws : Fin ps.length → q.Denote) (j : Fin ps.length) :
    ((mxE θ (q := q) ps j).eval (mxPush q ps.length (ρ.push (t := .val .uint) n) ws) :
      Option PrimTy.uint.Denote) = (ps.get j).e.eval τ ∧
    ((mxE θ (q := q) ps j).denote (mxPush q ps.length (ρ.push (t := .val .uint) n) ws) :
      Option PrimTy.uint.Denote) = (ps.get j).e.eval τ := by
  refine ⟨?_, ?_⟩
  · rw [eval_mxLift]
    have e1 : (((ps.get j).e'.eval ((ρ.push (t := .val .uint) n).thin (.drop .refl))) :
        Option PrimTy.uint.Denote) = (ps.get j).e'.eval ρ :=
      congrArg (fun (X : State C Δ) => (show Option PrimTy.uint.Denote from (ps.get j).e'.eval X))
        (mxThin_drop_push ρ _)
    rw [e1]
    exact Tm.mx_eval hr _ (ps.get j).hmx
  · rw [denote_mxLift, mxThin_drop_push, Tm.mx_denote hr _ (ps.get j).hmx]
    exact Tm.ixOk_denote τ _ (ps.get j).he

/-- **Past a fresh array, the states read alike**, where the object's
elements are the words the reads give and, a dynamic array's, its length
the binder's word. -/
theorem MxRel.alloc (hr : MxRel θ τ ρ) (a : ArrTy R (.prim q)) (ps : List (MxIx θ))
    (o : MObj τ.H R) (n : PrimTy.uint.Denote) (ws : Fin ps.length → q.Denote)
    (hlen : (MObj.elems a o).length = (mxBndV n a).1.toNat)
    (hag : ∀ j k₀, (ps.get j).e.eval τ = some k₀ → k₀.1 < (mxBndV n a).1 →
      (MObj.elems a o)[k₀.1.toNat]? = some (ws j)) :
    MxRel (θ.alloc a ps) (τ.allocPush o) (mxPush q ps.length (ρ.push (t := .val .uint) n) ws) where
  glob := by
    have hG := glob_mxPush q ps.length (ρ.push (t := .val .uint) n) ws
    exact ⟨by rw [hG]; exact hr.glob.storage, by rw [hG]; exact hr.glob.net,
      by rw [hG]; exact hr.glob.bal, by rw [hG]; exact hr.glob.tx⟩
  loc := fun {t} i j h => by
    cases i with
    | here => cases h
    | there i =>
      obtain ⟨j', hj', rfl⟩ := Option.map_eq_some_iff.1 h
      rw [getV_mxLift, ← State.getV_thin, mxThin_drop_push, hr.loc i j' hj']
      exact (State.getV_alloc τ o i).symm
  tbl := fun en hm => by
    rcases List.mem_append.1 hm with hm | hm
    · rcases List.mem_append.1 hm with hm | hm
      · obtain ⟨⟨p, x, tr⟩, hm', rfl⟩ := List.mem_map.1 hm
        have h := hr.tbl _ hm'
        dsimp only at h ⊢
        have hx := MxOrig.eval_alloc τ o x
        refine ⟨?_, ?_⟩
        · rw [eval_mxLift]
          have e1 : ((tr.eval ((ρ.push (t := .val .uint) n).thin (.drop .refl))) : Option p.Denote) =
              tr.eval ρ :=
            congrArg (fun (X : State C Δ) => (show Option p.Denote from tr.eval X))
              (mxThin_drop_push ρ _)
          rw [e1]
          exact h.1.trans hx.symm
        · rw [denote_mxLift, mxThin_drop_push, h.2, MxOrig.denote_eq, MxOrig.denote_eq]
          exact hx.symm
      · cases a with
        | dyn =>
          simp only [mxLenEnts, List.mem_singleton] at hm
          subst hm
          have hn := getV_mxN ps ρ n ws
          have hL := lenNew_eval τ o
          have hlen' : lenU (MObj.elems .dyn o).length
              (by rw [MObj.elems_dyn]; exact o.2) = n := by
            have : (MObj.elems .dyn o).length = n.1.toNat := hlen
            apply Subtype.ext
            show (((MObj.elems .dyn o).length : Nat) : Int) = n.1
            rw [this]
            exact Int.toNat_of_nonneg (uint_nonneg n)
          refine ⟨?_, ?_⟩
          · show some _ = (MxOrig.len (Γ := .mem (.array (.prim q)) :: Γ) .here).tm.eval (τ.allocPush o)
            rw [hL, hlen']; exact congrArg some hn
          · show some _ = (MxOrig.len (Γ := .mem (.array (.prim q)) :: Γ) .here).tm.denote (τ.allocPush o)
            rw [MxOrig.denote_eq, hL, hlen']; exact congrArg some hn
        | fixed => simp only [mxLenEnts, List.not_mem_nil] at hm
    · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hm
      dsimp only
      have hR := readNew_eval τ o a (ps.get j).e (ps.get j).he (Tm.ixOk_wk _ _ (ps.get j).he)
      have hE := mxE_eval hr ps n ws j
      have hB := mxBound_eval ps a ρ n ws
      have hw : (mxPush q ps.length (ρ.push (t := .val .uint) n) ws).getV (mxAtom q ps.length j) =
          ws j := getV_mxAtom q ps.length _ ws j
      have key : ((ps.get j).e.eval τ).bind (fun x => (some (mxBndV n a)).bind fun b =>
          if x.1 < b.1 then some (ws j) else none) =
          ((ps.get j).e.eval τ).bind fun k => (MObj.elems a o)[k.1.toNat]? := by
        cases hk : (ps.get j).e.eval τ with
        | none => rfl
        | some k =>
          show (if k.1 < (mxBndV n a).1 then some (ws j) else none) = (MObj.elems a o)[k.1.toNat]?
          by_cases hlt : k.1 < (mxBndV n a).1
          · rw [if_pos hlt, hag j k hk hlt]
          · rw [if_neg hlt]
            symm
            apply List.getElem?_eq_none
            rw [hlen]
            have h0 := uint_nonneg k
            have h1 := uint_nonneg (mxBndV n a)
            omega
      refine ⟨?_, ?_⟩
      · rw [mxReadT_eval, hE.1, hB.1, hw]
        exact key.trans hR.symm
      · rw [mxReadT_denote, hE.2, hB.2, hw, MxOrig.denote_eq]
        exact key.trans hR.symm

end AllocRel

/-! ## Fresh arrays from their reads -/

/-- The fixed arrays the cut takes are shorter than `2^256`. -/
def mxArrOk {R : RefTy} {q : PrimTy} : ArrTy R (.prim q) → Prop
  | .dyn => True
  | @ArrTy.fixed _ N => N < 2 ^ 256

theorem _root_.Solidity.RefTy.mxArr?_ok : (R : RefTy) → {x : (q : PrimTy) × ArrTy R (.prim q)} →
    R.mxArr? = some x → mxArrOk x.2
  | .array (.prim _), _, h => by cases h; trivial
  | .fixed (.prim _) N, _, h => by
    simp only [RefTy.mxArr?] at h
    split at h
    · cases h; assumption
    · cases h
  | .array (.ref _), _, h | .fixed (.ref _) _, _, h | .struct _, _, h | .mapping _ _, _, h => by
    simp only [RefTy.mxArr?, reduceCtorEq] at h

theorem uintOfNat_toNat (k : PrimTy.uint.Denote) : uintOfNat k.1.toNat = k := by
  have h := k.2
  simp only [PrimTy.inRange, decide_eq_true_eq] at h
  have hl : k.1.toNat < 2 ^ 256 := by omega
  rw [uintOfNat_eq_lenU hl]
  exact lenU_toNat k hl

theorem mxBndV_lt {R : RefTy} {q : PrimTy} (n : PrimTy.uint.Denote) (a : ArrTy R (.prim q)) :
    (mxBndV n a).1.toNat < 2 ^ 256 := by
  have h := (mxBndV n a).2
  simp only [PrimTy.inRange, decide_eq_true_eq] at h
  omega

/-- An array object of the given elements. -/
def mxMk {H : HTy} {R : RefTy} {q : PrimTy} (n : PrimTy.uint.Denote) (L : List q.Denote) :
    (a : ArrTy R (.prim q)) → mxArrOk a → L.length = (mxBndV n a).1.toNat → MObj H R
  | .dyn, _, hL => (⟨L, by rw [hL]; exact mxBndV_lt n .dyn⟩ :
      {l : List (MVal H (.prim q)) // l.length < 2 ^ 256})
  | @ArrTy.fixed _ N, hok, hL => (⟨L, by rw [hL]; show (uintOfNat N).1.toNat = N; rw [uintOfNat_val hok]; rfl⟩ :
      {l : List (MVal H (.prim q)) // l.length = N})

theorem elems_mxMk {H : HTy} {R : RefTy} {q : PrimTy} (n : PrimTy.uint.Denote) (L : List q.Denote)
    (a : ArrTy R (.prim q)) (hok : mxArrOk a) (hL : L.length = (mxBndV n a).1.toNat) :
    MObj.elems a (mxMk (H := H) n L a hok hL) = L := by
  cases a with
  | dyn => rw [MObj.elems_dyn]; rfl
  | fixed => rw [MObj.elems_fixed]; rfl

theorem mem_finRange' {n : Nat} (j : Fin n) : j ∈ List.finRange n :=
  List.mem_iff_getElem.2 ⟨j.val, by simp, by simp⟩

section Realize

variable {Γ Δ : Ctx} {θ : MxMap C Γ Δ} {q : PrimTy}

/-- The word at element `i`: the first read at it, the default where none. -/
def mxPick (τ : State C Γ) (ps : List (MxIx θ)) (ws : Fin ps.length → q.Denote) (i : Nat) : q.Denote :=
  match (List.finRange ps.length).find? (fun j => decide (((ps.get j).e.eval τ).map (·.1) = some (i : Int))) with
  | some j => ws j
  | none => PrimTy.dflt q

/-- Two reads at equal indices read one word. -/
def MxConsistent (τ : State C Γ) (ps : List (MxIx θ)) (ws : Fin ps.length → q.Denote) : Prop :=
  ∀ j l : Fin ps.length, ((ps.get j).e.eval τ : Option PrimTy.uint.Denote) = (ps.get l).e.eval τ →
    ws j = ws l

theorem mxPick_spec (τ : State C Γ) (ps : List (MxIx θ)) (ws : Fin ps.length → q.Denote)
    (hc : MxConsistent τ ps ws) (j : Fin ps.length) (k : PrimTy.uint.Denote)
    (hk : (ps.get j).e.eval τ = some k) : mxPick τ ps ws k.1.toNat = ws j := by
  unfold mxPick
  have hk0 := uint_nonneg k
  have hex : ((List.finRange ps.length).find? (fun j => decide (((ps.get j).e.eval τ).map (·.1) =
      some ((k.1.toNat : Nat) : Int)))).isSome := by
    rw [List.find?_isSome]
    refine ⟨j, mem_finRange' j, ?_⟩
    simp only [hk, Option.map_some, Int.toNat_of_nonneg hk0, decide_true]
  obtain ⟨j₀, hj₀⟩ := Option.isSome_iff_exists.1 hex
  rw [hj₀]
  apply hc
  have := List.find?_some hj₀
  simp only [decide_eq_true_eq, Int.toNat_of_nonneg hk0] at this
  rw [hk]
  cases h0 : (ps.get j₀).e.eval τ with
  | none => rw [h0] at this; cases this
  | some k' =>
    rw [h0, Option.map_some, Option.some.injEq] at this
    exact congrArg some (Subtype.ext this)

/-- **The array the reads describe**: of the bound's length, each element the
word the first read at it gives. -/
def mxRealize (τ : State C Γ) {R : RefTy} (a : ArrTy R (.prim q)) (hok : mxArrOk a)
    (ps : List (MxIx θ)) (n : PrimTy.uint.Denote) (ws : Fin ps.length → q.Denote) : MObj τ.H R :=
  mxMk n (List.ofFn fun (i : Fin (mxBndV n a).1.toNat) => mxPick τ ps ws i.val) a hok
    (List.length_ofFn)

theorem mxRealize_len (τ : State C Γ) {R : RefTy} (a : ArrTy R (.prim q)) (hok : mxArrOk a)
    (ps : List (MxIx θ)) (n : PrimTy.uint.Denote) (ws : Fin ps.length → q.Denote) :
    (MObj.elems a (mxRealize τ a hok ps n ws)).length = (mxBndV n a).1.toNat := by
  rw [mxRealize, elems_mxMk, List.length_ofFn]

theorem mxRealize_ag (τ : State C Γ) {R : RefTy} (a : ArrTy R (.prim q)) (hok : mxArrOk a)
    (ps : List (MxIx θ)) (n : PrimTy.uint.Denote) (ws : Fin ps.length → q.Denote)
    (hc : MxConsistent τ ps ws) (j : Fin ps.length) (k : PrimTy.uint.Denote)
    (hk : (ps.get j).e.eval τ = some k) (hlt : k.1 < (mxBndV n a).1) :
    (MObj.elems a (mxRealize τ a hok ps n ws))[k.1.toNat]? = some (ws j) := by
  rw [mxRealize, elems_mxMk, List.getElem?_ofFn]
  have hk0 := uint_nonneg k
  have hb := uint_nonneg (mxBndV n a)
  have hi : k.1.toNat < (mxBndV n a).1.toNat := by omega
  simp only [hi, dite_true]
  exact congrArg some (mxPick_spec τ ps ws hc j k hk)

/-- The words an array's reads give. -/
def mxFill (τ : State C Γ) {R : RefTy} (a : ArrTy R (.prim q)) (ps : List (MxIx θ)) (o : MObj τ.H R) :
    Fin ps.length → q.Denote := fun j =>
  match (ps.get j).e.eval τ with
  | some k => ((MObj.elems a o)[k.1.toNat]?).getD (PrimTy.dflt q)
  | none => PrimTy.dflt q

theorem mxFill_consistent (τ : State C Γ) {R : RefTy} (a : ArrTy R (.prim q)) (ps : List (MxIx θ))
    (o : MObj τ.H R) : MxConsistent τ ps (mxFill τ a ps o) := by
  intro j l h
  simp only [mxFill, h]

theorem mxFill_ag (τ : State C Γ) {R : RefTy} (a : ArrTy R (.prim q)) (ps : List (MxIx θ))
    (o : MObj τ.H R) (n : PrimTy.uint.Denote) (hlen : (MObj.elems a o).length = (mxBndV n a).1.toNat)
    (j : Fin ps.length) (k : PrimTy.uint.Denote) (hk : (ps.get j).e.eval τ = some k)
    (hlt : k.1 < (mxBndV n a).1) :
    (MObj.elems a o)[k.1.toNat]? = some (mxFill τ a ps o j) := by
  have hk0 := uint_nonneg k
  have hi : k.1.toNat < (MObj.elems a o).length := by rw [hlen]; omega
  simp only [mxFill, hk, List.getElem?_eq_getElem hi, Option.getD_some]

/-- The binder's word a fresh array gives: its length. -/
def mxFillN {H : HTy} {R : RefTy} (a : ArrTy R (.prim q)) (o : MObj H R) : PrimTy.uint.Denote :=
  uintOfNat (MObj.elems a o).length

theorem mxFillN_len {H : HTy} {R : RefTy} (a : ArrTy R (.prim q)) (hok : mxArrOk a) (o : MObj H R) :
    (MObj.elems a o).length = (mxBndV (mxFillN a o) a).1.toNat := by
  cases a with
  | dyn =>
    have hl : (MObj.elems .dyn o).length < 2 ^ 256 := by rw [MObj.elems_dyn]; exact o.2
    show _ = (uintOfNat (MObj.elems .dyn o).length).1.toNat
    rw [uintOfNat_val hl]
    rfl
  | @fixed _ N =>
    have hl : (MObj.elems .fixed o).length = N := by rw [MObj.elems_fixed]; exact o.2
    show _ = (uintOfNat N).1.toNat
    rw [uintOfNat_val hok, hl]
    rfl

end Realize

/-! ## The cut is exact -/

section Exact

variable {Γ Δ : Ctx} {θ : MxMap C Γ Δ} {τ : State C Γ} {ρ : State C Δ} {q : PrimTy}

theorem holds_mxCons (hr : MxRel θ τ ρ) (ps : List (MxIx θ)) (n : PrimTy.uint.Denote)
    (ws : Fin ps.length → q.Denote) :
    holds (mxPush q ps.length (ρ.push (t := .val .uint) n) ws) (mxCons θ (q := q) ps) ↔
      MxConsistent τ ps ws := by
  rw [mxCons, holds_mxConj]
  have hE := mxE_eval (q := q) hr ps n ws
  have hw := getV_mxAtom q ps.length (ρ.push (t := .val .uint) n) ws
  have one : ∀ j l : Fin ps.length,
      holds (mxPush q ps.length (ρ.push (t := .val .uint) n) ws)
        (.imp (.eq (mxE θ (q := q) ps j) (mxE θ (q := q) ps l))
          (.eq (.pvV (mxAtom q ps.length j)) (.pvV (mxAtom q ps.length l)))) ↔
      (((ps.get j).e.eval τ : Option PrimTy.uint.Denote) = (ps.get l).e.eval τ → ws j = ws l) := by
    intro j l
    show ((mxE θ (q := q) ps j).denote _ = (mxE θ (q := q) ps l).denote _ →
      some (TEnv.get (mxAtom q ps.length j) _) = some (TEnv.get (mxAtom q ps.length l) _)) ↔ _
    rw [(hE j).2, (hE l).2]
    have h1 : TEnv.get (mxAtom q ps.length j) (mxPush q ps.length (ρ.push (t := .val .uint) n) ws).env =
      ws j := hw j
    have h2 : TEnv.get (mxAtom q ps.length l) (mxPush q ps.length (ρ.push (t := .val .uint) n) ws).env =
      ws l := hw l
    rw [h1, h2, Option.some.injEq]
  constructor
  · intro h j l hjl
    rcases Nat.lt_trichotomy j.val l.val with hlt | heq | hgt
    · refine (one j l).1 (h _ ?_) hjl
      refine List.mem_flatMap.2 ⟨j, mem_finRange' j, List.mem_filterMap.2 ⟨l, mem_finRange' l, ?_⟩⟩
      simp only [hlt, if_true]
    · rw [Fin.ext heq]
    · refine ((one l j).1 (h _ ?_) hjl.symm).symm
      refine List.mem_flatMap.2 ⟨l, mem_finRange' l, List.mem_filterMap.2 ⟨j, mem_finRange' j, ?_⟩⟩
      simp only [hgt, if_true]
  · intro hc f hf
    obtain ⟨j, -, hf⟩ := List.mem_flatMap.1 hf
    obtain ⟨l, -, hf⟩ := List.mem_filterMap.1 hf
    split at hf
    · cases hf
      exact (one j l).2 (hc j l)
    · cases hf

/-- **The cut formula holds exactly where the formula does**, at related
states. -/
theorem _root_.Solidity.Fml.mx_holds {Γ : Ctx} (φ : Fml C Γ) : {Δ : Ctx} → (θ : MxMap C Γ Δ) →
    {φ' : Fml C Δ} → φ.mx θ = some φ' → ∀ (τ : State C Γ) (ρ : State C Δ), MxRel θ τ ρ →
      (holds τ φ ↔ holds ρ φ') := by
  induction φ with
  | tt => intro _ _ _ e _ _ _; cases e; exact Iff.rfl
  | eq a b =>
    intro _ θ _ e τ ρ hr
    obtain ⟨a', ha, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.1 e
    show a.denote τ = b.denote τ ↔ a'.denote ρ = b'.denote ρ
    rw [Tm.mx_denote hr a ha, Tm.mx_denote hr b hb]
  | not φ ih =>
    intro _ θ _ e τ ρ hr
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact not_congr (ih θ hφ τ ρ hr)
  | and φ ψ ihφ ihψ =>
    intro _ θ _ e τ ρ hr
    obtain ⟨φ', hφ, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨ψ', hψ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact and_congr (ihφ θ hφ τ ρ hr) (ihψ θ hψ τ ρ hr)
  | imp φ ψ ihφ ihψ =>
    intro _ θ _ e τ ρ hr
    obtain ⟨φ', hφ, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨ψ', hψ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact imp_congr (ihφ θ hφ τ ρ hr) (ihψ θ hψ τ ρ hr)
  | all x p φ ih =>
    intro _ θ _ e τ ρ hr
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact forall_congr' fun v => ih (θ.push (.val p)) hφ _ _ (hr.push p v)
  | allocAll x R φ ih =>
    intro Δ θ _ e τ ρ hr
    simp only [Fml.mx] at e
    split at e
    · cases e
    · rename_i q a hR
      have hok : mxArrOk a := RefTy.mxArr?_ok R hR
      generalize θ.ixs (mxDedup (φ.mxIdx (.drop .refl) 0)) = ps at e
      obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
      show (∀ o : MObj τ.H R, holds (τ.allocPush o) φ) ↔
        ∀ n : PrimTy.uint.Denote, holds (ρ.push (t := .val .uint) n)
          (mxAll x q ps.length (.imp (mxCons θ (q := q) ps) φ'))
      constructor
      · intro h n
        rw [holds_mxAll]
        intro ws hc
        have hc' := (holds_mxCons hr ps n ws).1 hc
        let o := mxRealize τ a hok ps n ws
        have hrel := hr.alloc a ps o n ws (mxRealize_len τ a hok ps n ws)
          (mxRealize_ag τ a hok ps n ws hc')
        exact (ih _ hφ _ _ hrel).1 (h o)
      · intro h o
        let n := mxFillN a o
        let ws := mxFill τ a ps o
        have hlen := mxFillN_len a hok o
        have hrel := hr.alloc a ps o n ws hlen (mxFill_ag τ a ps o n hlen)
        refine (ih _ hφ _ _ hrel).2 ?_
        have h' := (holds_mxAll x q ps.length _ _).1 (h n) ws
        exact h' ((holds_mxCons hr ps n ws).2 (mxFill_consistent τ a ps o))
  | wellFormed | upd | modal | havoc | bind | anon | grow =>
    intro _ _ _ e; cases e

end Exact

/-- **A leaf holds exactly where its cut does**, at every state. -/
theorem _root_.Solidity.Fml.mxTop_holds {φ ψ : Fml C []} (h : φ.mxTop = some ψ) (σ : State C []) :
    holds σ φ ↔ holds σ ψ :=
  Fml.mx_holds φ MxMap.id0 h σ σ
    { glob := ⟨rfl, rfl, rfl, rfl⟩, loc := (fun i _ _ => nomatch i), tbl := (fun _ hm => nomatch hm) }

theorem _root_.Solidity.Fml.mxTop_valid {φ ψ : Fml C []} (h : φ.mxTop = some ψ) :
    Fml.Valid φ ↔ Fml.Valid ψ :=
  forall_congr' fun σ => Fml.mxTop_holds h σ

/-- info: 'Solidity.Fml.mxTop_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fml.mxTop_holds

end Solidity.Decide
