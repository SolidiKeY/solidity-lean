import Solidity.Calculus.HashComplete

/-!
# Strings hashed by two kinds (M7, plan step 7)

The hash swap (`Calculus/HashSwap.lean`) reads each fresh string as the
one word its hash of one kind returns.  A string hashed by two kinds
(`sha256(s) == sha256(t) → keccak256(s) == keccak256(t)`) stands for one
word per kind.  The second kind's words are value binders of their own,
past the prefix (`Fml.tk`): each node of the second kind of a string read
as its word (`Tm.xk`, the rest of the body read past the new binders), and
the premise per kind written as the link of the two kinds' words
(`(k₁(sᵢ) == k₁(sⱼ)) ↔ (eᵢ == eⱼ)`, which the premise makes true of every
pair of strings both kinds hash at the body's top).  The result has hashes
of the first kind only, which the one-kind swap reads:

* **valid** (`Fml.tk_validH`): a valid reading of the result is valid
  under the leaf's premise (each extra word set to its string's hash, the
  link true by the premise);
* **refuted** (`Fml.tk_refutes`): the instance at classes of strings, with
  the extra words fixed to the second kind's hashes of the family's strings
  (`Fix`), refuted, refutes the leaf in the state with the family's strings;
* **complete** (`Fml.tk_complete`): where the reading is not valid, an
  instance at some classes is not: the first kind's words relabeled by the
  one-kind completeness (`Fml.swPrefix_complete`), the second kind's
  by a relabeling of their own (`RelRL`, over the words of the second kind
  and the roots they key).
-/

namespace Solidity.Decide

variable {C : Contract}

/-! ## Reading a body past new binders -/

/-- **Where the body's locals and its strings' extra words are**: a
thinning into the new context, and each string's word of the second kind. -/
structure XMap (Γ Γ' : Ctx) where
  thin : Thin Γ Γ'
  ext : ∀ {R : RefTy}, Idx Γ (.mem R) → Option (Idx Γ' (.val .uint))

/-- Past a declared local. -/
def XMap.keep {Γ Γ' : Ctx} (θ : XMap Γ Γ') (t : LTy) : XMap (t :: Γ) (t :: Γ') where
  thin := .keep θ.thin
  ext := fun {R} i => Idx.casesOn (motive := fun Δ u _ => Δ = t :: Γ → u = .mem R →
      Option (Idx (t :: Γ') (.val .uint))) i
    (fun _ _ => none) (fun {_} {_} {_} j hΔ hu => by
      cases hΔ; cases hu; exact (θ.ext j).map .there) rfl rfl

theorem XMap.keep_ext_there {Γ Γ' : Ctx} (θ : XMap Γ Γ') (t : LTy) {R : RefTy} (j : Idx Γ (.mem R)) :
    (θ.keep t).ext (.there j) = (θ.ext j).map .there := rfl

/-- A hash node of kind `k₂` of a memory local in the starting memory: its
extra word (`some none` where the string has none). -/
def _root_.Solidity.Op2.xHash? (k₂ : HashKind) {Γ Γ' : Ctx} (θ : XMap Γ Γ') {a b s : Srt} :
    Op2 C a b s → Tm C Γ a → Tm C Γ b → Option (Option (Tm C Γ' s))
  | .hash k', .app0 .memory, .pvI i => if k' = k₂ then some ((θ.ext i).map .pvV) else none
  | _, _, _ => none

/-- **A term read past new binders**: each node of kind `k₂` of a string
its extra word, every local at its new position. -/
def _root_.Solidity.Tm.xk (k₂ : HashKind) {Γ Γ' : Ctx} (θ : XMap Γ Γ') :
    {s : Srt} → Tm C Γ s → Option (Tm C Γ' s)
  | _, .pvV i => some (.pvV (i.wk θ.thin))
  | _, .pvP i => some (.pvP (i.wk θ.thin))
  | _, .pvS i => some (.pvS (i.wk θ.thin))
  | _, .pvI i => some (.pvI (i.wk θ.thin))
  | _, .netOf i a => (a.xk k₂ θ).map (.netOf (i.wk θ.thin))
  | _, .app0 o => some (.app0 o)
  | _, .app1 o x => (x.xk k₂ θ).map (.app1 o)
  | _, .app2 o x y =>
    match o.xHash? k₂ θ x y with
    | some r => r
    | none => (x.xk k₂ θ).bind fun x' => (y.xk k₂ θ).map fun y' => .app2 o x' y'
  | _, .app3 o x y z =>
    (x.xk k₂ θ).bind fun x' => (y.xk k₂ θ).bind fun y' => (z.xk k₂ θ).map fun z' => .app3 o x' y' z'
  | _, .pvZ i => some (.pvZ (i.wk θ.thin))

/-- **The new state** (`τ` lifted along the thinning, the new binders `d`'s)
**holds each string's extra word at its hash of kind `k₂`.** -/
def XRel (k₂ : HashKind) {Γ Γ' : Ctx} (θ : XMap Γ Γ') (τ : State C Γ) (d : TEnv C τ.H Γ') : Prop :=
  ∀ {R : RefTy} (i : Idx Γ (.mem R)) (j : Idx Γ' (.val .uint)), θ.ext i = some j →
    ∃ id, (TEnv.get i τ.env).map (·.id) = some id ∧
      TEnv.get j (τ.lift θ.thin d).env = τ.glob.memT.hashId k₂ R id

section Read

variable {k₂ : HashKind} {Γ Γ' : Ctx} {θ : XMap Γ Γ'} {τ : State C Γ} {d : TEnv C τ.H Γ'}

theorem lift_glob (h : Thin Γ Γ') (τ : State C Γ) (d : TEnv C τ.H Γ') : (τ.lift h d).glob = τ.glob := rfl

/-- The hash node, evaluated. -/
theorem hashNode_eval {Δ : Ctx} (σ : State C Δ) (k : HashKind) {R : RefTy} (i : Idx Δ (.mem R))
    {id : Nat} (hv : (TEnv.get i σ.env).map (·.id) = some id) :
    (Tm.app2 (Op2.hash (R := R) k) (Tm.app0 Op0.memory) (Tm.pvI i)).eval σ =
      some (σ.glob.memT.hashId k R id) := by
  show Op2.eval σ.glob (.hash k) (Op0.eval σ.glob .memory) ((TEnv.get i σ.env).map (·.id)) = _
  rw [hv, Op2.eval_eq_evalM]
  rfl

theorem _root_.Solidity.Op2.xHash?_reads (h : XRel k₂ θ τ d) {a b s : Srt} (o : Op2 C a b s)
    (x : Tm C Γ a) (y : Tm C Γ b) {t' : Tm C Γ' s} (ht : o.xHash? k₂ θ x y = some (some t')) :
    t'.eval (τ.lift θ.thin d) = (Tm.app2 o x y).eval τ ∧
      t'.denote (τ.lift θ.thin d) = (Tm.app2 o x y).denote τ := by
  unfold Op2.xHash? at ht
  split at ht
  · rename_i R k' i
    by_cases hk : k' = k₂
    · subst hk
      simp only [if_true, Option.some.injEq] at ht
      obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
      obtain ⟨id, hid, hw⟩ := h i j hj
      have he := hashNode_eval τ k' i hid
      refine ⟨?_, ?_⟩
      · rw [he]
        show some (TEnv.get j (τ.lift θ.thin d).env) = _
        rw [hw]
      · show some (TEnv.get j (τ.lift θ.thin d).env) = Op2.eval τ.glob (.hash k') _ _
        rw [show Op2.eval τ.glob (.hash k') ((Tm.app0 (Γ := Γ) Op0.memory).eval τ)
          ((Tm.pvI i).eval τ) = some (τ.glob.memT.hashId k' R id) from he, hw]
    · simp only [hk, if_false, reduceCtorEq] at ht
  · cases ht

/-- **A term read past new binders reads as the term.** -/
theorem _root_.Solidity.Tm.xk_eval (h : XRel k₂ θ τ d) : {s : Srt} → (t : Tm C Γ s) →
    {t' : Tm C Γ' s} → t.xk k₂ θ = some t' → t'.eval (τ.lift θ.thin d) = t.eval τ
  | _, .pvV i, _, e => by
    cases e
    show some (TEnv.get (i.wk θ.thin) (τ.lift θ.thin d).env) = some (TEnv.get i τ.env)
    rw [State.get_lift]
  | _, .pvP i, _, e => by
    cases e
    show TEnv.get (i.wk θ.thin) (τ.lift θ.thin d).env = TEnv.get i τ.env
    rw [State.get_lift]
  | _, .pvS i, _, e => by
    cases e
    show some (TEnv.get (i.wk θ.thin) (τ.lift θ.thin d).env) = some (TEnv.get i τ.env)
    rw [State.get_lift]
  | _, .pvI i, _, e => by
    cases e
    show (TEnv.get (i.wk θ.thin) (τ.lift θ.thin d).env).map (·.id) = (TEnv.get i τ.env).map (·.id)
    rw [State.get_lift]
    rfl
  | _, .netOf i a, _, e => by
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 e
    show (a'.eval (τ.lift θ.thin d)).bind (Tm.netOfT (TEnv.get (i.wk θ.thin) (τ.lift θ.thin d).env)) =
      (a.eval τ).bind (Tm.netOfT (TEnv.get i τ.env))
    rw [Tm.xk_eval h a ha, State.get_lift]
  | _, .app0 o, _, e => by cases e; rfl
  | _, .app1 o x, _, e => by
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 e
    show o.eval τ.glob (x'.eval (τ.lift θ.thin d)) = o.eval τ.glob (x.eval τ)
    rw [Tm.xk_eval h x hx]
  | _, .app2 o x y, _, e => by
    simp only [Tm.xk] at e
    split at e
    · rename_i r hr
      cases r with
      | none => cases e
      | some t₀ => cases e; exact (o.xHash?_reads h x y hr).1
    · obtain ⟨x', hx, e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨y', hy, rfl⟩ := Option.map_eq_some_iff.1 e
      show o.eval τ.glob (x'.eval (τ.lift θ.thin d)) (y'.eval (τ.lift θ.thin d)) =
        o.eval τ.glob (x.eval τ) (y.eval τ)
      rw [Tm.xk_eval h x hx, Tm.xk_eval h y hy]
  | _, .app3 o x y z, _, e => by
    obtain ⟨x', hx, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨y', hy, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨z', hz, rfl⟩ := Option.map_eq_some_iff.1 e
    show o.eval τ.glob (x'.eval (τ.lift θ.thin d)) (y'.eval (τ.lift θ.thin d))
      (z'.eval (τ.lift θ.thin d)) = o.eval τ.glob (x.eval τ) (y.eval τ) (z.eval τ)
    rw [Tm.xk_eval h x hx, Tm.xk_eval h y hy, Tm.xk_eval h z hz]
  | _, .pvZ i, _, e => by
    cases e
    show some (TEnv.get (i.wk θ.thin) (τ.lift θ.thin d).env) = some (TEnv.get i τ.env)
    rw [State.get_lift]

/-- **A term read past new binders denotes as the term.** -/
theorem _root_.Solidity.Tm.xk_denote (h : XRel k₂ θ τ d) : {s : Srt} → (t : Tm C Γ s) →
    {t' : Tm C Γ' s} → t.xk k₂ θ = some t' → t'.denote (τ.lift θ.thin d) = t.denote τ
  | _, .pvV i, _, e => by
    cases e
    show some (TEnv.get (i.wk θ.thin) (τ.lift θ.thin d).env) = some (TEnv.get i τ.env)
    rw [State.get_lift]
  | _, .pvP i, _, e => by
    cases e
    have e := State.get_lift θ.thin τ d i
    simp only [Tm.denote]
    revert e
    generalize TEnv.get (i.wk θ.thin) (τ.lift θ.thin d).env = a
    generalize TEnv.get i τ.env = b
    intro e
    subst e
    cases a <;> rfl
  | _, .pvS i, _, e => by
    cases e
    show Storage.obs _ = Storage.obs _
    rw [State.get_lift]
  | _, .pvI i, _, e => by cases e; rfl
  | _, .netOf i a, _, e => by
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 e
    show (a'.denote (τ.lift θ.thin d)).map _ = (a.denote τ).map _
    rw [Tm.xk_denote h a ha, State.get_lift]
  | _, .app0 o, _, e => by cases e; rfl
  | _, .app1 o x, _, e => by
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 e
    show o.denote τ.glob (x'.denote (τ.lift θ.thin d)) = o.denote τ.glob (x.denote τ)
    rw [Tm.xk_denote h x hx]
  | _, .app2 o x y, _, e => by
    simp only [Tm.xk] at e
    split at e
    · rename_i r hr
      cases r with
      | none => cases e
      | some t₀ => cases e; exact (o.xHash?_reads h x y hr).2
    · obtain ⟨x', hx, e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨y', hy, rfl⟩ := Option.map_eq_some_iff.1 e
      show o.denote τ.glob (x'.eval (τ.lift θ.thin d)) (y'.eval (τ.lift θ.thin d))
        (x'.denote (τ.lift θ.thin d)) (y'.denote (τ.lift θ.thin d)) =
        o.denote τ.glob (x.eval τ) (y.eval τ) (x.denote τ) (y.denote τ)
      rw [Tm.xk_denote h x hx, Tm.xk_denote h y hy, Tm.xk_eval h x hx, Tm.xk_eval h y hy]
  | _, .app3 o x y z, _, e => by
    obtain ⟨x', hx, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨y', hy, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨z', hz, rfl⟩ := Option.map_eq_some_iff.1 e
    show o.denote (x'.denote (τ.lift θ.thin d)) (y'.denote (τ.lift θ.thin d))
      (z'.denote (τ.lift θ.thin d)) = o.denote (x.denote τ) (y.denote τ) (z.denote τ)
    rw [Tm.xk_denote h x hx, Tm.xk_denote h y hy, Tm.xk_denote h z hz]
  | _, .pvZ i, _, e => by
    cases e
    show some (TEnv.get (i.wk θ.thin) (τ.lift θ.thin d).env) = some (TEnv.get i τ.env)
    rw [State.get_lift]

end Read

/-! ## Formulas read past new binders -/

/-- A one-element update with no push read past new binders: a storage
write, a value local declared (its continuation past the declared local). -/
def _root_.Solidity.Upd.xk1? (k₂ : HashKind) {Γ Γ' : Ctx} (θ : XMap Γ Γ') :
    {Δ : Ctx} → Upd C Γ Δ → Option ((Δ' : Ctx) × Upd C Γ' Δ' × XMap Δ Δ')
  | _, .snoc U e =>
    match U with
    | .nil =>
      match e with
      | .storage s => (s.xk k₂ θ).bind fun s' =>
        if s.pushFree && s'.pushFree then some ⟨Γ', .snoc .nil (.storage s'), θ⟩ else none
      | _ => none
    | .snoc .. | .decl .. | .pop .. | .drop .. => none
  | _, .decl U x r =>
    match U with
    | .nil =>
      match r with
      | .val (p := p) t => (t.xk k₂ θ).bind fun t' =>
        if t.pushFree && t'.pushFree then some ⟨.val p :: Γ', .decl .nil x (.val t'), θ.keep _⟩
        else none
      | _ => none
    | .snoc .. | .decl .. | .pop .. | .drop .. => none
  | _, .nil | _, .pop .. | _, .drop .. => none

/-- **A body read past new binders**: equations, `wt`, the connectives,
and the one-element updates with no push (`Upd.xk1?`); `none` on anything
else. -/
def _root_.Solidity.Fml.xk (k₂ : HashKind) : {Γ Γ' : Ctx} → XMap Γ Γ' → Fml C Γ → Option (Fml C Γ')
  | _, _, _, .tt => some .tt
  | _, _, θ, .eq a b => (a.xk k₂ θ).bind fun a' => (b.xk k₂ θ).map fun b' => .eq a' b'
  | _, _, θ, .wellFormed s => (s.xk k₂ θ).map .wellFormed
  | _, _, θ, .not φ => (Fml.xk k₂ θ φ).map .not
  | _, _, θ, .and φ ψ => (Fml.xk k₂ θ φ).bind fun φ' => (Fml.xk k₂ θ ψ).map fun ψ' => .and φ' ψ'
  | _, _, θ, .imp φ ψ => (Fml.xk k₂ θ φ).bind fun φ' => (Fml.xk k₂ θ ψ).map fun ψ' => .imp φ' ψ'
  | _, _, θ, .upd m U φ => (U.xk1? k₂ θ).bind fun r => (Fml.xk k₂ r.2.2 φ).map (.upd m r.2.1)
  | _, _, _, _ => none

section Preserve

variable {k₂ : HashKind} {Γ Γ' : Ctx} {θ : XMap Γ Γ'}

theorem XRel.withStorage {τ : State C Γ} {d : TEnv C τ.H Γ'} (h : XRel k₂ θ τ d) (st : Storage C) :
    XRel k₂ θ (τ.withStorage st) d := fun i j hj => h i j hj

theorem lift_push (h : Thin Γ Γ') (τ : State C Γ) (d : TEnv C τ.H Γ') {t : LTy} (v : t.TDenote C τ.H)
    (v' : t.TDenote C τ.H) :
    (τ.push v).lift (.keep h) (v', d) = (τ.lift h d).push v := rfl

theorem XRel.push {τ : State C Γ} {d : TEnv C τ.H Γ'} (h : XRel k₂ θ τ d) {t : LTy}
    (v : t.TDenote C τ.H) : XRel k₂ (θ.keep t) (τ.push v) (v, d) := by
  intro R i j hj
  cases i with
  | here => cases hj
  | there i =>
    rw [XMap.keep_ext_there] at hj
    obtain ⟨j₀, hj₀, rfl⟩ := Option.map_eq_some_iff.1 hj
    exact h i j₀ hj₀

end Preserve

/-- **A one-element update read past new binders lands as the update.** -/
theorem _root_.Solidity.Upd.xk1?_afterT {k₂ : HashKind} {Γ Γ' : Ctx} {θ : XMap Γ Γ'} {Δ : Ctx}
    (U : Upd C Γ Δ) {r : (Δ' : Ctx) × Upd C Γ' Δ' × XMap Δ Δ'} (hU : U.xk1? k₂ θ = some r)
    (m : Modality) (τ : State C Γ) (d : TEnv C τ.H Γ') (h : XRel k₂ θ τ d)
    (P : State C Δ → Prop) (P' : State C r.1 → Prop)
    (hP : ∀ (σ : State C Δ) (d' : TEnv C σ.H r.1), XRel k₂ r.2.2 σ d' →
      (P' (σ.lift r.2.2.thin d') ↔ P σ)) :
    r.2.1.afterT m (τ.lift θ.thin d) P' ↔ U.afterT m τ P := by
  cases U with
  | snoc U₀ e₀ =>
    cases U₀ with
    | nil =>
      cases e₀ with
      | storage s =>
        simp only [Upd.xk1?] at hU
        obtain ⟨s', hs, e⟩ := Option.bind_eq_some_iff.1 hU
        split at e
        · rename_i hpf
          simp only [Bool.and_eq_true] at hpf
          cases e
          show (Upd.snoc .nil (.storage s')).afterT m (τ.lift θ.thin d) P' ↔
            (Upd.snoc .nil (.storage s)).afterT m τ P
          rw [Upd.afterT_storage1 m _ s' (by simp only [Upd.pushFree, UpdElem.pushFree, hpf.2,
            Bool.and_self]), Upd.afterT_storage1 m τ s (by simp only [Upd.pushFree, UpdElem.pushFree,
            hpf.1, Bool.and_self]), Tm.xk_eval h s hs]
          cases s.eval τ with
          | none => exact Iff.rfl
          | some st => exact hP (τ.withStorage st) d (h.withStorage st)
        · cases e
      | _ => simp only [Upd.xk1?, reduceCtorEq] at hU
    | _ => simp only [Upd.xk1?, reduceCtorEq] at hU
  | decl U₀ x r₀ =>
    cases U₀ with
    | nil =>
      cases r₀ with
      | val t =>
        simp only [Upd.xk1?] at hU
        obtain ⟨t', ht, e⟩ := Option.bind_eq_some_iff.1 hU
        split at e
        · rename_i hpf
          simp only [Bool.and_eq_true] at hpf
          cases e
          show (Upd.decl .nil x (.val t')).afterT m (τ.lift θ.thin d) P' ↔
            (Upd.decl .nil x (.val t)).afterT m τ P
          rw [Upd.afterT_decl1 m _ x t' (by simp only [Upd.pushFree, Rhs.pushFree, hpf.2,
            Bool.and_self, Bool.true_and]), Upd.afterT_decl1 m τ x t (by simp only [Upd.pushFree,
            Rhs.pushFree, hpf.1, Bool.and_self, Bool.true_and]), Tm.xk_eval h t ht]
          cases t.eval τ with
          | none => exact Iff.rfl
          | some v => exact hP (τ.push (t := .val _) v) (v, d) (h.push (t := .val _) v)
        · cases e
      | _ => simp only [Upd.xk1?, reduceCtorEq] at hU
    | _ => simp only [Upd.xk1?, reduceCtorEq] at hU
  | _ => simp only [Upd.xk1?, reduceCtorEq] at hU

/-- **A body read past new binders holds as the body.** -/
theorem _root_.Solidity.Fml.xk_holds {k₂ : HashKind} {Γ : Ctx} (φ : Fml C Γ) :
    ∀ {Γ' : Ctx} {θ : XMap Γ Γ'} {φ' : Fml C Γ'}, φ.xk k₂ θ = some φ' →
      ∀ (τ : State C Γ) (d : TEnv C τ.H Γ'), XRel k₂ θ τ d →
      (holds (τ.lift θ.thin d) φ' ↔ holds τ φ) := by
  induction φ with
  | tt => intro _ _ _ e _ _ _; cases e; exact Iff.rfl
  | eq a b =>
    intro _ _ _ e τ d h
    obtain ⟨a', ha, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.1 e
    rw [holds_eq, holds_eq, Tm.xk_denote h a ha, Tm.xk_denote h b hb]
  | wellFormed s =>
    intro _ _ _ e τ d h
    obtain ⟨s', hs, rfl⟩ := Option.map_eq_some_iff.1 e
    rw [holds_wellFormed, holds_wellFormed, Tm.xk_eval h s hs]
  | not φ ih =>
    intro _ _ _ e τ d h
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact not_congr (ih hφ τ d h)
  | and φ ψ ihφ ihψ =>
    intro _ _ _ e τ d h
    obtain ⟨φ', hφ, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨ψ', hψ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact and_congr (ihφ hφ τ d h) (ihψ hψ τ d h)
  | imp φ ψ ihφ ihψ =>
    intro _ _ _ e τ d h
    obtain ⟨φ', hφ, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨ψ', hψ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact imp_congr (ihφ hφ τ d h) (ihψ hψ τ d h)
  | upd m U φ ih =>
    intro _ _ _ e τ d h
    obtain ⟨r, hU, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact U.xk1?_afterT hU m τ d h _ _ fun σ d' h' => ih hφ σ d' h'
  | modal | havoc | all | bind | anon | allocAll | grow => intro _ _ _ e; cases e

/-- On a formula `Fml.xk` takes the premise is read nowhere: it has no binder. -/
theorem _root_.Solidity.Fml.holdsS_of_xk {k₂ : HashKind} {Γ : Ctx} (φ : Fml C Γ) :
    ∀ {Γ' : Ctx} {θ : XMap Γ Γ'} {φ' : Fml C Γ'}, φ.xk k₂ θ = some φ' → ∀ τ : State C Γ,
      (Fml.holdsS τ φ ↔ holds τ φ) := by
  induction φ with
  | tt | eq | wellFormed => intro _ _ _ _ _; exact Iff.rfl
  | not φ ih =>
    intro _ _ _ e τ
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact not_congr (ih hφ τ)
  | and φ ψ ihφ ihψ =>
    intro _ _ _ e τ
    obtain ⟨φ', hφ, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨ψ', hψ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact and_congr (ihφ hφ τ) (ihψ hψ τ)
  | imp φ ψ ihφ ihψ =>
    intro _ _ _ e τ
    obtain ⟨φ', hφ, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨ψ', hψ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact imp_congr (ihφ hφ τ) (ihψ hψ τ)
  | upd m U φ ih =>
    intro _ _ _ e τ
    obtain ⟨r, _, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact ⟨fun h => Upd.afterT_imp h fun σ' => (ih hφ σ').1,
      fun h => Upd.afterT_imp h fun σ' => (ih hφ σ').2⟩
  | modal | havoc | all | bind | anon | allocAll | grow => intro _ _ _ e; cases e

/-! ## The second kind's words, as new binders -/

/-- `m` new `uint` binders past `Γ`. -/
def _root_.Solidity.Thin.dropN {Γ : Ctx} : (m : Nat) → Thin Γ (List.replicate m (.val .uint) ++ Γ)
  | 0 => .refl
  | m + 1 => .drop (Thin.dropN m)

/-- The `d`-th new binder, from the innermost. -/
def topIdx {Γ : Ctx} : (m : Nat) → Fin m → Idx (List.replicate m (.val .uint) ++ Γ) (.val .uint)
  | _ + 1, ⟨0, _⟩ => .here
  | m + 1, ⟨d + 1, h⟩ => .there (topIdx m ⟨d, Nat.lt_of_succ_lt_succ h⟩)

/-- The locals with the new binders' values, `es 0` innermost. -/
def envOf {H : HTy} {Γ : Ctx} : (m : Nat) → (Fin m → PrimTy.uint.Denote) → TEnv C H Γ →
    TEnv C H (List.replicate m (.val .uint) ++ Γ)
  | 0, _, e => e
  | m + 1, es, e => (es 0, envOf m (fun i => es i.succ) e)

theorem put_dropN {H : HTy} {Γ : Ctx} : (m : Nat) → (es : Fin m → PrimTy.uint.Denote) →
    (e e' : TEnv C H Γ) → TEnv.put (Thin.dropN m) e (envOf m es e') = envOf m es e
  | 0, _, _, _ => rfl
  | m + 1, es, e, e' => by
    show (es 0, TEnv.put (Thin.dropN m) e (envOf m (fun i => es i.succ) e')) = _
    rw [put_dropN m]
    rfl

theorem get_topIdx {H : HTy} {Γ : Ctx} : (m : Nat) → (es : Fin m → PrimTy.uint.Denote) →
    (e : TEnv C H Γ) → (d : Fin m) → TEnv.get (topIdx m d) (envOf m es e) = es d
  | _ + 1, _, _, ⟨0, _⟩ => rfl
  | m + 1, es, e, ⟨d + 1, h⟩ => get_topIdx m (fun i => es i.succ) e ⟨d, Nat.lt_of_succ_lt_succ h⟩

/-- `∀ uint x₁ … xₘ. ψ`, the innermost `es 0`'s. -/
def _root_.Solidity.Fml.allN {Γ : Ctx} (x : Var) :
    (m : Nat) → Fml C (List.replicate m (.val .uint) ++ Γ) → Fml C Γ
  | 0, ψ => ψ
  | m + 1, ψ => Fml.allN x m (.all x .uint ψ)

theorem hashFree_all {Γ : Ctx} (σ : State C Γ) (x : Var) (p : PrimTy) (φ : Fml C (.val p :: Γ)) :
    (Fml.all x p φ).HashFree σ := fun _ _ _ _ _ h => h.elim

/-- **The new binders' premise and body**: what `∀ uint x₁ … xₘ. ψ` says
under its premise, `ψ` says at every value of the binders. -/
theorem holdsS_allN {Γ : Ctx} (x : Var) : (m : Nat) → (ψ : Fml C (List.replicate m (.val .uint) ++ Γ)) →
    (τ : State C Γ) → Fml.holdsS τ (Fml.allN x m ψ) → ∀ es : Fin m → PrimTy.uint.Denote,
      ψ.HashFree (τ.withEnv (envOf m es τ.env)) → Fml.holdsS (τ.withEnv (envOf m es τ.env)) ψ
  | 0, ψ, τ, h, _, _ => h
  | m + 1, ψ, τ, h, es, hf =>
    holdsS_allN x m (.all x .uint ψ) τ h (fun i => es i.succ) (hashFree_all _ _ _ _) (es 0) hf

theorem hashFree_allN {Γ : Ctx} (x : Var) (m : Nat) (ψ : Fml C (List.replicate m (.val .uint) ++ Γ))
    (τ : State C Γ)
    (h : ∀ es : Fin m → PrimTy.uint.Denote, m = 0 → ψ.HashFree (τ.withEnv (envOf m es τ.env))) :
    (Fml.allN x m ψ).HashFree τ := by
  cases m with
  | zero => exact h Fin.elim0 rfl
  | succ m =>
    show (Fml.allN x m (.all x .uint ψ)).HashFree τ
    clear h
    induction m with
    | zero => exact hashFree_all _ _ _ _
    | succ m ih => exact ih (.all x .uint ψ)

/-! ## Strings by level -/

/-- The memory local at a position. -/
def _root_.Solidity.Idx.memAt? : (Γ : Ctx) → Nat → Option ((R : RefTy) × Idx Γ (.mem R))
  | [], _ => none
  | t :: _, 0 =>
    match t with
    | .mem R => some ⟨R, .here⟩
    | _ => none
  | _ :: Γ, n + 1 => (Idx.memAt? Γ n).map fun r => ⟨r.1, .there r.2⟩

theorem _root_.Solidity.Idx.memAt?_self : {Γ : Ctx} → {R : RefTy} → (i : Idx Γ (.mem R)) →
    Idx.memAt? Γ i.toNat = some ⟨R, i⟩
  | _, _, .here => rfl
  | _ :: _, _, .there i => by
    show (Idx.memAt? _ i.toNat).map _ = _
    rw [Idx.memAt?_self i]
    rfl

/-- The memory local at a level. -/
def _root_.Solidity.Idx.memAtLevel? (Γ : Ctx) (l : Nat) : Option ((R : RefTy) × Idx Γ (.mem R)) :=
  if l < Γ.length then Idx.memAt? Γ (Γ.length - 1 - l) else none

theorem _root_.Solidity.Idx.memAtLevel?_self {Γ : Ctx} {R : RefTy} (i : Idx Γ (.mem R)) :
    Idx.memAtLevel? Γ i.level = some ⟨R, i⟩ := by
  have h := Idx.toNat_lt i
  unfold Idx.memAtLevel? Idx.level
  rw [if_pos (by omega), show Γ.length - 1 - (Γ.length - 1 - i.toNat) = i.toNat by omega,
    Idx.memAt?_self]

theorem _root_.Solidity.Idx.memAt?_toNat : {Γ : Ctx} → (n : Nat) → {R : RefTy} → {i : Idx Γ (.mem R)} →
    Idx.memAt? Γ n = some ⟨R, i⟩ → i.toNat = n
  | [], _, _, _, h => nomatch h
  | t :: Γ, 0, R, i, h => by
    cases t with
    | mem R' => cases h; rfl
    | _ => cases h
  | _ :: Γ, n + 1, R, i, h => by
    simp only [Idx.memAt?] at h
    obtain ⟨⟨R', j⟩, hj, e⟩ := Option.map_eq_some_iff.1 h
    cases e
    exact congrArg (· + 1) (Idx.memAt?_toNat n hj)

theorem _root_.Solidity.Idx.memAtLevel?_level {Γ : Ctx} {l : Nat} {R : RefTy} {i : Idx Γ (.mem R)}
    (h : Idx.memAtLevel? Γ l = some ⟨R, i⟩) : i.level = l := by
  unfold Idx.memAtLevel? at h
  split at h
  · have := Idx.memAt?_toNat _ h
    unfold Idx.level
    omega
  · cases h

/-- The first position of `x` in `l`. -/
def posIn : List Nat → Nat → Option Nat
  | [], _ => none
  | a :: l, x => if a = x then some 0 else (posIn l x).map (· + 1)

theorem posIn_spec : (l : List Nat) → (x d : Nat) → posIn l x = some d → ∃ h : d < l.length, l[d] = x
  | [], _, _, h => nomatch h
  | a :: l, x, d, h => by
    unfold posIn at h
    split at h
    · cases h; exact ⟨Nat.zero_lt_succ _, by assumption⟩
    · obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨hl, he⟩ := posIn_spec l x d' hd'
      exact ⟨Nat.succ_lt_succ hl, he⟩

theorem posIn_of_mem : (l : List Nat) → (x : Nat) → x ∈ l → ∃ d, posIn l x = some d
  | [], _, h => nomatch h
  | a :: l, x, h => by
    unfold posIn
    by_cases e : a = x
    · exact ⟨0, by rw [if_pos e]⟩
    · rw [if_neg e]
      obtain ⟨d, hd⟩ := posIn_of_mem l x ((List.mem_cons.1 h).resolve_left (Ne.symm e))
      exact ⟨d + 1, by rw [hd]; rfl⟩

/-- **The extra words of the strings at the levels `L`**: past `L.length`
new binders, the string at level `L[d]` read at the `d`-th. -/
def XMap.extras (L : List Nat) (Γ : Ctx) : XMap Γ (List.replicate L.length (.val .uint) ++ Γ) where
  thin := Thin.dropN L.length
  ext := fun i => (posIn L i.level).bind fun d =>
    if h : d < L.length then some (topIdx L.length ⟨d, h⟩) else none

/-! ## The premise past new binders -/

section HashIn

variable {k₂ : HashKind} {Γ Γ' : Ctx} {θ : XMap Γ Γ'} {τ : State C Γ} {d : TEnv C τ.H Γ'}

/-- **A hash term read past new binders is one of the term's.** -/
theorem _root_.Solidity.Tm.xk_hashIn (h : XRel k₂ θ τ d) {k : HashKind} {inp : Option (List Nat)}
    {out : PrimTy.uint.Denote} : {s : Srt} → (t : Tm C Γ s) → {t' : Tm C Γ' s} → t.xk k₂ θ = some t' →
      t'.HashIn (τ.lift θ.thin d) k inp out → t.HashIn τ k inp out
  | _, .pvV _, _, e, hi | _, .pvP _, _, e, hi | _, .pvS _, _, e, hi | _, .pvI _, _, e, hi
  | _, .pvZ _, _, e, hi => by cases e; exact hi.elim
  | _, .app0 _, _, e, hi => by cases e; exact hi.elim
  | _, .netOf i a, _, e, hi => by
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 e
    exact Tm.xk_hashIn h a ha hi
  | _, .app1 o x, _, e, hi => by
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 e
    exact Tm.xk_hashIn h x hx hi
  | _, .app2 o x y, _, e, hi => by
    simp only [Tm.xk] at e
    split at e
    · rename_i r hr
      cases r with
      | none => cases e
      | some t₀ =>
        cases e
        unfold Op2.xHash? at hr
        split at hr
        · split at hr
          · simp only [Option.some.injEq] at hr
            obtain ⟨j, -, rfl⟩ := Option.map_eq_some_iff.1 hr
            exact hi.elim
          · cases hr
        · cases hr
    · obtain ⟨x', hx, e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨y', hy, rfl⟩ := Option.map_eq_some_iff.1 e
      rcases hi with hi | hi | hi
      · refine .inl ?_
        have ex := Tm.xk_eval h x hx
        have ey := Tm.xk_eval h y hy
        revert hi
        show Op2.HashIn (H := τ.H) k inp out o (x'.eval (τ.lift θ.thin d)) (y'.eval (τ.lift θ.thin d)) →
          Op2.HashIn (H := τ.H) k inp out o (x.eval τ) (y.eval τ)
        rw [ex, ey]
        exact id
      · exact .inr (.inl (Tm.xk_hashIn h x hx hi))
      · exact .inr (.inr (Tm.xk_hashIn h y hy hi))
  | _, .app3 o x y z, _, e, hi => by
    obtain ⟨x', hx, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨y', hy, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨z', hz, rfl⟩ := Option.map_eq_some_iff.1 e
    rcases hi with hi | hi | hi
    · exact .inl (Tm.xk_hashIn h x hx hi)
    · exact .inr (.inl (Tm.xk_hashIn h y hy hi))
    · exact .inr (.inr (Tm.xk_hashIn h z hz hi))

/-- **A one-element update read past new binders lands where the update
does**, lifted, and its terms' hashes are the update's. -/
theorem _root_.Solidity.Upd.xk1?_lands {Δ : Ctx} (U : Upd C Γ Δ)
    {r : (Δ' : Ctx) × Upd C Γ' Δ' × XMap Δ Δ'} (hU : U.xk1? k₂ θ = some r) (h : XRel k₂ θ τ d) :
    (∀ {k inp out}, r.2.1.HashIn (τ.lift θ.thin d) k inp out → U.HashIn τ k inp out) ∧
    ∀ (g : GlobT C (τ.lift θ.thin d).H) (σ₂ : State C r.1), r.2.1.Lands (τ.lift θ.thin d) g σ₂ →
      ∃ (g₀ : GlobT C τ.H) (σ' : State C Δ) (d' : TEnv C σ'.H r.1), U.Lands τ g₀ σ' ∧
        σ₂ = σ'.lift r.2.2.thin d' ∧ XRel k₂ r.2.2 σ' d' := by
  cases U with
  | snoc U₀ e₀ =>
    cases U₀ with
    | nil =>
      cases e₀ with
      | storage s =>
        simp only [Upd.xk1?] at hU
        obtain ⟨s', hs, e⟩ := Option.bind_eq_some_iff.1 hU
        split at e
        · cases e
          refine ⟨fun hi => ?_, fun g σ₂ hL => ?_⟩
          · rcases hi with hi | hi
            · exact hi.elim
            · exact .inr (Tm.xk_hashIn h s hs hi)
          · have hg : (Upd.snoc .nil (.storage s') : Upd C Γ' Γ').globT (τ.lift θ.thin d) =
                (s'.eval (τ.lift θ.thin d)).bind fun st => some ((τ.lift θ.thin d).globG.withStorage st) := rfl
            rw [Tm.xk_eval h s hs] at hg
            cases hse : s.eval τ with
            | none => rw [hse] at hg; exact absurd (hL.1.symm.trans hg) (by simp only [Option.bind_none,
                reduceCtorEq, not_false_eq_true])
            | some st =>
              have hg₀ : (Upd.snoc .nil (.storage s) : Upd C Γ Γ).globT τ =
                  (s.eval τ).bind fun st => some (τ.globG.withStorage st) := rfl
              have hL₀ : (Upd.snoc .nil (.storage s) : Upd C Γ Γ).Lands τ (τ.globG.withStorage st)
                  (τ.withStorage st) := ⟨by rw [hg₀, hse]; rfl, rfl, fun _ => rfl⟩
              have hL₂ : (Upd.snoc .nil (.storage s') : Upd C Γ' Γ').Lands (τ.lift θ.thin d)
                  ((τ.lift θ.thin d).globG.withStorage st) ((τ.withStorage st).lift θ.thin d) :=
                ⟨by rw [hg, hse]; rfl, rfl, fun _ => rfl⟩
              exact ⟨τ.globG.withStorage st, τ.withStorage st, d, hL₀, Upd.Lands.eq hL hL₂, h.withStorage st⟩
        · cases e
      | _ => simp only [Upd.xk1?, reduceCtorEq] at hU
    | _ => simp only [Upd.xk1?, reduceCtorEq] at hU
  | decl U₀ x r₀ =>
    cases U₀ with
    | nil =>
      cases r₀ with
      | val t =>
        simp only [Upd.xk1?] at hU
        obtain ⟨t', ht, e⟩ := Option.bind_eq_some_iff.1 hU
        split at e
        · cases e
          refine ⟨fun hi => ?_, fun g σ₂ hL => ?_⟩
          · rcases hi with hi | hi
            · exact hi.elim
            · exact .inr (Tm.xk_hashIn h t ht hi)
          · cases hte : t.eval τ with
            | none =>
              have hg : (Upd.decl .nil x (.val t') : Upd C Γ' (_ :: Γ')).globT (τ.lift θ.thin d) =
                  (t'.eval (τ.lift θ.thin d)).bind fun _ => some (τ.lift θ.thin d).globG := rfl
              rw [Tm.xk_eval h t ht, hte] at hg
              exact absurd (hL.1.symm.trans hg) (by simp only [Option.bind_none, reduceCtorEq,
                not_false_eq_true])
            | some v =>
              have hL₀ := Upd.lands_decl (Upd.lands_nil τ) x (r := .val t) (v := (v : _)) hte
              have hte' : (t'.eval (τ.lift θ.thin d)) = some v := by rw [Tm.xk_eval h t ht, hte]
              have hL₂ := Upd.lands_decl (Upd.lands_nil (τ.lift θ.thin d)) x (r := .val t')
                (v := (v : _)) hte'
              exact ⟨τ.globG, τ.push (t := .val _) v, (v, d), hL₀, Upd.Lands.eq hL hL₂, h.push (t := .val _) v⟩
        · cases e
      | _ => simp only [Upd.xk1?, reduceCtorEq] at hU
    | _ => simp only [Upd.xk1?, reduceCtorEq] at hU
  | _ => simp only [Upd.xk1?, reduceCtorEq] at hU

end HashIn

/-- **A hash term of a body read past new binders is one of the body's.** -/
theorem _root_.Solidity.Fml.xk_hashIn {k₂ : HashKind} {Γ : Ctx} (φ : Fml C Γ) :
    ∀ {Γ' : Ctx} {θ : XMap Γ Γ'} {φ' : Fml C Γ'}, φ.xk k₂ θ = some φ' →
      ∀ (τ : State C Γ) (d : TEnv C τ.H Γ'), XRel k₂ θ τ d → ∀ {k inp out},
        Fml.HashIn k inp out (τ.lift θ.thin d) φ' → Fml.HashIn k inp out τ φ := by
  induction φ with
  | tt => intro _ _ _ e _ _ _ _ _ _ hi; cases e; exact hi.elim
  | eq a b =>
    intro _ _ _ e τ d h _ _ _ hi
    obtain ⟨a', ha, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.1 e
    rcases hi with hi | hi
    · exact .inl (Tm.xk_hashIn h a ha hi)
    · exact .inr (Tm.xk_hashIn h b hb hi)
  | wellFormed s =>
    intro _ _ _ e τ d h _ _ _ hi
    obtain ⟨s', hs, rfl⟩ := Option.map_eq_some_iff.1 e
    exact Tm.xk_hashIn h s hs hi
  | not φ ih =>
    intro _ _ _ e τ d h _ _ _ hi
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact ih hφ τ d h hi
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ =>
    intro _ _ _ e τ d h _ _ _ hi
    obtain ⟨φ', hφ, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨ψ', hψ, rfl⟩ := Option.map_eq_some_iff.1 e
    rcases hi with hi | hi
    · exact .inl (ihφ hφ τ d h hi)
    · exact .inr (ihψ hψ τ d h hi)
  | upd m U φ ih =>
    intro _ _ _ e τ d h _ _ _ hi
    obtain ⟨r, hU, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨hUi, hUl⟩ := U.xk1?_lands hU h
    rcases hi with hi | ⟨g, σ₂, -, hL, hi⟩
    · exact .inl (hUi hi)
    · obtain ⟨g₀, σ', d', hL₀, rfl, h'⟩ := hUl g σ₂ hL
      exact .inr ⟨g₀, σ', hL₀.1, hL₀, ih hφ σ' d' h' hi⟩
  | modal | havoc | all | bind | anon | allocAll | grow => intro _ _ _ e; cases e

/-! ## The leaf with the second kind's words -/

/-- `k(memory, s)`. -/
def hnode {Γ : Ctx} (k : HashKind) {R : RefTy} (i : Idx Γ (.mem R)) : Tm C Γ (.val .uint) :=
  .app2 (.hash k) (.app0 .memory) (.pvI i)

/-- `f₁ ∧ … ∧ fₙ`. -/
def _root_.Solidity.Fml.conjL {Γ : Ctx} : List (Fml C Γ) → Fml C Γ
  | [] => .tt
  | f :: fs => .and f (Fml.conjL fs)

/-- `f₁ ∨ … ∨ fₙ`. -/
def _root_.Solidity.Fml.orL {Γ : Ctx} (fs : List (Fml C Γ)) : Fml C Γ := .not (Fml.conjL (fs.map .not))

/-- `a ↔ b`. -/
def _root_.Solidity.Fml.iffF {Γ : Ctx} (a b : Fml C Γ) : Fml C Γ := .and (.imp a b) (.imp b a)

/-- The string at the level `L[d]`. -/
def strAt {Γ : Ctx} (L : List Nat) (d : Fin L.length) : Option ((R : RefTy) × Idx Γ (.mem R)) :=
  Idx.memAtLevel? Γ L[d]

/-- The pairs `a < b` of positions below `m`. -/
def pairsFin (m : Nat) : List (Fin m × Fin m) :=
  (List.finRange m).flatMap fun a => (List.finRange m).filterMap fun b =>
    if a < b then some (a, b) else none

/-- **The premise per kind, linked**, past the new binders: for each pair
of the strings `L` names, their hashes of the first kind are equal exactly
where their extra words are. -/
def linkE (k₁ : HashKind) {Γ : Ctx} (L : List Nat) :
    List (Fml C (List.replicate L.length (.val .uint) ++ Γ)) :=
  (pairsFin L.length).filterMap fun p =>
    match strAt (Γ := Γ) L p.1, strAt (Γ := Γ) L p.2 with
    | some ⟨_, i⟩, some ⟨_, j⟩ =>
      some (Fml.iffF (.eq (hnode k₁ (i.wk (Thin.dropN L.length))) (hnode k₁ (j.wk (Thin.dropN L.length))))
        (.eq (.pvV (topIdx L.length p.1)) (.pvV (topIdx L.length p.2))))
    | _, _ => none

/-- `k₁(s) == famHash k₁ j ∧ e == famHash k₂ j`, for some `j`: the string
and its extra word one of the family's. -/
def famPairE {Δ : Ctx} (k₁ k₂ : HashKind) {R : RefTy} (i : Idx Δ (.mem R)) (e : Idx Δ (.val .uint)) :
    Fml C Δ :=
  Fml.orL ((List.range famBound).map fun j =>
    .and (.eq (hnode k₁ i) (.app0 (.lit (famHash k₁ j)))) (.eq (.pvV e) (.app0 (.lit (famHash k₂ j)))))

/-- **The strings and their extra words the family's**: what fixes the
second kind's words in an instance. -/
def fixE (k₁ k₂ : HashKind) {Γ : Ctx} (L : List Nat) :
    List (Fml C (List.replicate L.length (.val .uint) ++ Γ)) :=
  (List.finRange L.length).filterMap fun d =>
    match strAt (Γ := Γ) L d with
    | some ⟨_, i⟩ => some (famPairE k₁ k₂ (i.wk (Thin.dropN L.length)) (topIdx L.length d))
    | none => none

/-- A node of kind `k` of a memory local: the local's level. -/
def _root_.Solidity.Op2.nodeLevel? (k : HashKind) {Γ : Ctx} {a b s : Srt} :
    Op2 C a b s → Tm C Γ a → Tm C Γ b → Option Nat
  | .hash k', .app0 .memory, .pvI i => if k' = k then some i.level else none
  | _, _, _ => none

/-- The levels of the strings a term hashes by `k`. -/
def _root_.Solidity.Tm.hLevels (k : HashKind) {Γ : Ctx} : {s : Srt} → Tm C Γ s → List Nat
  | _, .netOf _ a => a.hLevels k
  | _, .app1 _ a => a.hLevels k
  | _, .app2 o x y => (o.nodeLevel? k x y).toList ++ x.hLevels k ++ y.hLevels k
  | _, .app3 _ x y z => x.hLevels k ++ y.hLevels k ++ z.hLevels k
  | _, _ => []

def _root_.Solidity.Rhs.hLevels (k : HashKind) {Γ : Ctx} {t : LTy} : Rhs C Γ t → List Nat
  | .val a | .zint a => a.hLevels k
  | .path q => q.hLevels k
  | .mref i => i.hLevels k
  | .store s => s.hLevels k
  | .unset | .saveNet | .saveNetMt => []

def _root_.Solidity.UpdElem.hLevels (k : HashKind) {Γ Δ : Ctx} : UpdElem C Γ Δ → List Nat
  | .local _ r => r.hLevels k
  | .storage s | .memory s => s.hLevels k
  | .selfBalance _ a | .setBalance a => a.hLevels k
  | .net r _ a | .pay r a | .netMt r a => r.hLevels k ++ a.hLevels k

def _root_.Solidity.Upd.hLevels (k : HashKind) {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → List Nat
  | _, .nil => []
  | _, .snoc U e => U.hLevels k ++ e.hLevels k
  | _, .decl U _ r => U.hLevels k ++ r.hLevels k
  | _, .pop U _ | _, .drop U _ => U.hLevels k

/-- The levels of the strings a formula hashes by `k`, anywhere. -/
def _root_.Solidity.Fml.hLevels (k : HashKind) : {Γ : Ctx} → Fml C Γ → List Nat
  | _, .eq a b => a.hLevels k ++ b.hLevels k
  | _, .wellFormed s => s.hLevels k
  | _, .not φ | _, .all _ _ φ | _, .havoc φ | _, .bind _ _ _ φ | _, .anon _ φ | _, .allocAll _ _ φ
  | _, .grow φ => φ.hLevels k
  | _, .and φ ψ | _, .imp φ ψ => φ.hLevels k ++ ψ.hLevels k
  | _, .upd _ U φ => U.hLevels k ++ φ.hLevels k
  | _, .tt | _, .modal .. => []

/-- The levels of the strings a formula hashes by `k` where its premise
reads them: outside every update's continuation. -/
def _root_.Solidity.Fml.topLevels (k : HashKind) : {Γ : Ctx} → Fml C Γ → List Nat
  | _, .eq a b => a.hLevels k ++ b.hLevels k
  | _, .wellFormed s => s.hLevels k
  | _, .not φ => φ.topLevels k
  | _, .and φ ψ | _, .imp φ ψ => φ.topLevels k ++ ψ.topLevels k
  | _, .upd _ U _ => U.hLevels k
  | _, _ => []

/-- A hash node reads a memory local in the starting memory. -/
def _root_.Solidity.Op2.memNode {Γ : Ctx} {a b s : Srt} : Op2 C a b s → Tm C Γ a → Tm C Γ b → Bool
  | .hash _, .app0 .memory, .pvI _ => true
  | .hash _, _, _ => false
  | _, _, _ => true

/-- Every hash node of the term reads a memory local in the starting memory. -/
def _root_.Solidity.Tm.memNodes {Γ : Ctx} : {s : Srt} → Tm C Γ s → Bool
  | _, .netOf _ a | _, .app1 _ a => a.memNodes
  | _, .app2 o x y => o.memNode x y && x.memNodes && y.memNodes
  | _, .app3 _ x y z => x.memNodes && y.memNodes && z.memNodes
  | _, _ => true

/-- A one-element update (a storage write, a value local declared) whose
hash nodes read memory locals. -/
def _root_.Solidity.Upd.memNodes1 {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, .snoc U e =>
    match U with
    | .nil =>
      match e with
      | .storage s => s.memNodes
      | _ => false
    | .snoc .. | .decl .. | .pop .. | .drop .. => false
  | _, .decl U _ r =>
    match U with
    | .nil =>
      match r with
      | .val t => t.memNodes
      | _ => false
    | .snoc .. | .decl .. | .pop .. | .drop .. => false
  | _, .nil | _, .pop .. | _, .drop .. => false

/-- **Every hash node of the body reads a memory local**: equations, `wt`,
the connectives and one-element updates. -/
def _root_.Solidity.Fml.memNodes : {Γ : Ctx} → Fml C Γ → Bool
  | _, .tt => true
  | _, .eq a b => a.memNodes && b.memNodes
  | _, .wellFormed s => s.memNodes
  | _, .not φ => φ.memNodes
  | _, .and φ ψ | _, .imp φ ψ => φ.memNodes && ψ.memNodes
  | _, .upd _ U φ => U.memNodes1 && φ.memNodes
  | _, _ => false

/-- **The body with the second kind's words**: the strings `k₂` hashes
(`L`), each hashed by both kinds where the premise reads it; `m` new
binders, the link of the two kinds (`linkE`; and, for an instance,
`fixE`) assumed, the body read past them with each node of kind `k₂` its
word. -/
def _root_.Solidity.Fml.tkBody (k₁ k₂ : HashKind) (fix : Bool) {Γ : Ctx} (ψ : Fml C Γ) :
    Option (Fml C Γ) :=
  let L := (ψ.hLevels k₂).eraseDups
  if ψ.memNodes && L.all (fun l => (Idx.memAtLevel? Γ l).isSome && (ψ.topLevels k₁).contains l &&
      (ψ.topLevels k₂).contains l) then
    (ψ.xk k₂ (XMap.extras L Γ)).map fun ψ₂ =>
      Fml.allN (.user "e") L.length
        (.imp (Fml.conjL (if fix then fixE k₁ k₂ L else [])) (.imp (Fml.conjL (linkE k₁ L)) ψ₂))
  else none

/-- **The leaf with the second kind's words** (`Fml.tkBody`) past its
prefix of `∀` and fresh strings. -/
def _root_.Solidity.Fml.tk (k₁ k₂ : HashKind) (fix : Bool) : {Γ : Ctx} → Fml C Γ → Option (Fml C Γ)
  | _, .all x p φ => (Fml.tk k₁ k₂ fix φ).map (.all x p)
  | _, .allocAll x R φ => (Fml.tk k₁ k₂ fix φ).map (.allocAll x R)
  | _, .tt => Fml.tkBody k₁ k₂ fix .tt
  | _, .eq a b => Fml.tkBody k₁ k₂ fix (.eq a b)
  | _, .wellFormed s => Fml.tkBody k₁ k₂ fix (.wellFormed s)
  | _, .not φ => Fml.tkBody k₁ k₂ fix (.not φ)
  | _, .and φ ψ => Fml.tkBody k₁ k₂ fix (.and φ ψ)
  | _, .imp φ ψ => Fml.tkBody k₁ k₂ fix (.imp φ ψ)
  | _, .upd m U φ => Fml.tkBody k₁ k₂ fix (.upd m U φ)
  | _, .modal .. | _, .havoc _ | _, .bind .. | _, .anon .. | _, .grow _ => none

/-! ## Facts of the strings' hash nodes -/

section Nodes

variable {Γ : Ctx}

theorem hnode_hashIn (σ : State C Γ) (k : HashKind) {R : RefTy} (i : Idx Γ (.mem R)) {k' : HashKind}
    {inp : Option (List Nat)} {out : PrimTy.uint.Denote} (h : (hnode k i).HashIn σ k' inp out) :
    k' = k ∧ ∃ id, σ.getV i = some id ∧ inp = σ.glob.memT.hashInput R id ∧
      out = σ.glob.memT.hashId k R id := by
  rcases h with h | h | h
  · revert h
    show Op2.HashIn (H := σ.H) k' inp out (Op2.hash (R := R) k) (some σ.glob.memT)
      ((TEnv.get i σ.env).map (·.id)) → _
    cases hg : TEnv.get i σ.env with
    | none => exact fun h => h.elim
    | some r =>
      rintro ⟨rfl, h1, h2⟩
      exact ⟨rfl, r.id, by show (TEnv.get i σ.env).map (·.id) = _; rw [hg]; rfl, h1, h2⟩
  · exact h.elim
  · exact h.elim

/-- The node read where its local is set. -/
theorem hnode_hashIn_of (σ : State C Γ) (k : HashKind) {R : RefTy} (i : Idx Γ (.mem R)) {id : Nat}
    (hv : σ.getV i = some id) :
    (hnode k i).HashIn σ k (σ.glob.memT.hashInput R id) (σ.glob.memT.hashId k R id) := by
  refine .inl ?_
  show Op2.HashIn (H := σ.H) k _ _ (Op2.hash (R := R) k) (some σ.glob.memT) ((TEnv.get i σ.env).map (·.id))
  have hv' : (TEnv.get i σ.env).map (·.id) = some id := hv
  rw [hv']
  exact ⟨rfl, rfl, rfl⟩

theorem hnode_denote (σ : State C Γ) (k : HashKind) {R : RefTy} (i : Idx Γ (.mem R)) {id : Nat}
    (hv : σ.getV i = some id) : (hnode k i).denote σ = some (σ.glob.memT.hashId k R id) :=
  hashNode_eval σ k i hv

theorem _root_.Solidity.HashKind.apply_congr (k : HashKind) {bs bs' : List Int}
    (h : bs.map (fun b => b.toNat % 256) = bs'.map (fun b => b.toNat % 256)) : k.apply bs = k.apply bs' := by
  cases k <;> simp only [HashKind.apply]
  · unfold keccakBytes; simp only [h]
  · unfold sha256Bytes; rw [h]
  · unfold ripemd160Bytes; rw [h]
  · unfold ecrecoverBytes; simp only [h]

/-- **A hash is a function of its input**: equal inputs, equal hashes of
every kind. -/
theorem _root_.Solidity.Grown.hashId_of_input {H : HTy} (m : Grown H (fun _ => Unit)) (k : HashKind)
    {R R' : RefTy} {id id' : Nat} (h : m.hashInput R id = m.hashInput R' id') :
    m.hashId k R id = m.hashId k R' id' := by
  unfold Grown.hashInput at h
  unfold Grown.hashId
  cases h1 : HRef.ofId? m.H' R id with
  | none =>
    cases h2 : HRef.ofId? m.H' R' id' with
    | none => rfl
    | some r' => rw [h1, h2] at h; cases h
  | some r =>
    cases h2 : HRef.ofId? m.H' R' id' with
    | none => rw [h1, h2] at h; cases h
    | some r' =>
      rw [h1, h2] at h
      simp only [Option.map_some, Option.some.injEq, List.map_map] at h
      simp only [Option.map_some, Option.getD_some, Heap.hash]
      exact HashKind.apply_congr k h

/-- Two memory locals at one level are one. -/
theorem mem_level_eq {R R' : RefTy} {i : Idx Γ (.mem R)} {i' : Idx Γ (.mem R')} (h : i.level = i'.level) :
    (⟨R, i⟩ : (R : RefTy) × Idx Γ (.mem R)) = ⟨R', i'⟩ := by
  have a := Idx.memAtLevel?_self i
  rw [h, Idx.memAtLevel?_self i'] at a
  exact (Option.some.inj a).symm

theorem _root_.Solidity.Op2.nodeLevel?_spec {k : HashKind} {a b s : Srt} (o : Op2 C a b s)
    (x : Tm C Γ a) (y : Tm C Γ b) {l : Nat} (h : o.nodeLevel? k x y = some l) (σ : State C Γ) :
    ∃ (R : RefTy) (i : Idx Γ (.mem R)), i.level = l ∧ ∀ id, σ.getV i = some id →
      (Tm.app2 o x y).HashIn σ k (σ.glob.memT.hashInput R id) (σ.glob.memT.hashId k R id) := by
  unfold Op2.nodeLevel? at h
  split at h
  · rename_i R k' i
    by_cases hk : k' = k
    · subst hk
      rw [if_pos rfl] at h
      cases h
      exact ⟨R, i, rfl, fun id hv => hnode_hashIn_of σ k' i hv⟩
    · rw [if_neg hk] at h; cases h
  · cases h

theorem _root_.Solidity.Tm.hLevels_hashIn (σ : State C Γ) (k : HashKind) {l : Nat} :
    {s : Srt} → (t : Tm C Γ s) → l ∈ t.hLevels k → ∃ (R : RefTy) (i : Idx Γ (.mem R)), i.level = l ∧
      ∀ id, σ.getV i = some id → t.HashIn σ k (σ.glob.memT.hashInput R id) (σ.glob.memT.hashId k R id)
  | _, .netOf _ a, h | _, .app1 _ a, h => Tm.hLevels_hashIn σ k a h
  | _, .app2 o x y, h => by
    simp only [Tm.hLevels, List.mem_append] at h
    rcases h with (h | h) | h
    · obtain ⟨R, i, hl, hi⟩ := o.nodeLevel?_spec x y (Option.mem_toList.1 h) σ
      exact ⟨R, i, hl, hi⟩
    · obtain ⟨R, i, hl, hi⟩ := Tm.hLevels_hashIn σ k x h
      exact ⟨R, i, hl, fun id hv => .inr (.inl (hi id hv))⟩
    · obtain ⟨R, i, hl, hi⟩ := Tm.hLevels_hashIn σ k y h
      exact ⟨R, i, hl, fun id hv => .inr (.inr (hi id hv))⟩
  | _, .app3 _ x y z, h => by
    simp only [Tm.hLevels, List.mem_append] at h
    rcases h with (h | h) | h
    · obtain ⟨R, i, hl, hi⟩ := Tm.hLevels_hashIn σ k x h
      exact ⟨R, i, hl, fun id hv => .inl (hi id hv)⟩
    · obtain ⟨R, i, hl, hi⟩ := Tm.hLevels_hashIn σ k y h
      exact ⟨R, i, hl, fun id hv => .inr (.inl (hi id hv))⟩
    · obtain ⟨R, i, hl, hi⟩ := Tm.hLevels_hashIn σ k z h
      exact ⟨R, i, hl, fun id hv => .inr (.inr (hi id hv))⟩
  | _, .pvV _, h | _, .pvP _, h | _, .pvS _, h | _, .pvI _, h | _, .app0 _, h | _, .pvZ _, h => nomatch h

theorem _root_.Solidity.Rhs.hLevels_hashIn (σ : State C Γ) (k : HashKind) {l : Nat} {t : LTy}
    (r : Rhs C Γ t) (h : l ∈ r.hLevels k) : ∃ (R : RefTy) (i : Idx Γ (.mem R)), i.level = l ∧
      ∀ id, σ.getV i = some id → r.HashIn σ k (σ.glob.memT.hashInput R id) (σ.glob.memT.hashId k R id) := by
  cases r <;> first | exact Tm.hLevels_hashIn σ k _ h | (simp only [Rhs.hLevels, List.not_mem_nil] at h)

theorem _root_.Solidity.UpdElem.hLevels_hashIn (σ : State C Γ) (k : HashKind) {l : Nat} {Δ : Ctx}
    (e : UpdElem C Γ Δ) (h : l ∈ e.hLevels k) : ∃ (R : RefTy) (i : Idx Γ (.mem R)), i.level = l ∧
      ∀ id, σ.getV i = some id → e.HashIn σ k (σ.glob.memT.hashInput R id) (σ.glob.memT.hashId k R id) := by
  cases e with
  | «local» _ r => exact Rhs.hLevels_hashIn σ k r h
  | storage s | memory s | selfBalance _ s | setBalance s => exact Tm.hLevels_hashIn σ k s h
  | net r _ a | pay r a | netMt r a =>
    simp only [UpdElem.hLevels, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨R, i, hl, hi⟩ := Tm.hLevels_hashIn σ k r h
      exact ⟨R, i, hl, fun id hv => .inl (hi id hv)⟩
    · obtain ⟨R, i, hl, hi⟩ := Tm.hLevels_hashIn σ k a h
      exact ⟨R, i, hl, fun id hv => .inr (hi id hv)⟩

theorem _root_.Solidity.Upd.hLevels_hashIn (σ : State C Γ) (k : HashKind) {l : Nat} :
    {Δ : Ctx} → (U : Upd C Γ Δ) → l ∈ U.hLevels k → ∃ (R : RefTy) (i : Idx Γ (.mem R)), i.level = l ∧
      ∀ id, σ.getV i = some id → U.HashIn σ k (σ.glob.memT.hashInput R id) (σ.glob.memT.hashId k R id)
  | _, .nil, h => nomatch h
  | _, .snoc U e, h => by
    simp only [Upd.hLevels, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨R, i, hl, hi⟩ := Upd.hLevels_hashIn σ k U h
      exact ⟨R, i, hl, fun id hv => .inl (hi id hv)⟩
    · obtain ⟨R, i, hl, hi⟩ := UpdElem.hLevels_hashIn σ k e h
      exact ⟨R, i, hl, fun id hv => .inr (hi id hv)⟩
  | _, .decl U _ r, h => by
    simp only [Upd.hLevels, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨R, i, hl, hi⟩ := Upd.hLevels_hashIn σ k U h
      exact ⟨R, i, hl, fun id hv => .inl (hi id hv)⟩
    · obtain ⟨R, i, hl, hi⟩ := Rhs.hLevels_hashIn σ k r h
      exact ⟨R, i, hl, fun id hv => .inr (hi id hv)⟩
  | _, .pop U _, h | _, .drop U _, h => Upd.hLevels_hashIn σ k U h

/-- **A string hashed where the premise reads it is one of the premise's
hash terms.** -/
theorem _root_.Solidity.Fml.topLevels_hashIn (σ : State C Γ) (k : HashKind) {l : Nat} :
    (φ : Fml C Γ) → l ∈ φ.topLevels k → ∃ (R : RefTy) (i : Idx Γ (.mem R)), i.level = l ∧
      ∀ id, σ.getV i = some id → Fml.HashIn k (σ.glob.memT.hashInput R id) (σ.glob.memT.hashId k R id) σ φ
  | .eq a b, h => by
    simp only [Fml.topLevels, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨R, i, hl, hi⟩ := Tm.hLevels_hashIn σ k a h
      exact ⟨R, i, hl, fun id hv => .inl (hi id hv)⟩
    · obtain ⟨R, i, hl, hi⟩ := Tm.hLevels_hashIn σ k b h
      exact ⟨R, i, hl, fun id hv => .inr (hi id hv)⟩
  | .wellFormed s, h => Tm.hLevels_hashIn σ k s h
  | .not φ, h => Fml.topLevels_hashIn σ k φ h
  | .and φ ψ, h | .imp φ ψ, h => by
    simp only [Fml.topLevels, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨R, i, hl, hi⟩ := Fml.topLevels_hashIn σ k φ h
      exact ⟨R, i, hl, fun id hv => .inl (hi id hv)⟩
    · obtain ⟨R, i, hl, hi⟩ := Fml.topLevels_hashIn σ k ψ h
      exact ⟨R, i, hl, fun id hv => .inr (hi id hv)⟩
  | .upd _ U _, h => by
    obtain ⟨R, i, hl, hi⟩ := Upd.hLevels_hashIn σ k U h
    exact ⟨R, i, hl, fun id hv => .inl (hi id hv)⟩
  | .tt, h | .modal .., h | .havoc _, h | .all .., h | .bind .., h | .anon .., h | .allocAll .., h
  | .grow _, h => nomatch h

theorem holds_conjL (σ : State C Γ) : (fs : List (Fml C Γ)) → (holds σ (Fml.conjL fs) ↔ ∀ f ∈ fs, holds σ f)
  | [] => ⟨fun _ _ h => (nomatch h), fun _ => trivial⟩
  | f :: fs => by
    show holds σ f ∧ holds σ (Fml.conjL fs) ↔ _
    rw [holds_conjL σ fs]
    exact ⟨fun ⟨a, b⟩ g hg => (List.mem_cons.1 hg).elim (· ▸ a) (b g),
      fun h => ⟨h f List.mem_cons_self, fun g hg => h g (List.mem_cons_of_mem _ hg)⟩⟩

theorem hashIn_conjL (σ : State C Γ) {k : HashKind} {inp : Option (List Nat)} {out : PrimTy.uint.Denote} :
    (fs : List (Fml C Γ)) → Fml.HashIn k inp out σ (Fml.conjL fs) → ∃ f ∈ fs, Fml.HashIn k inp out σ f
  | [], h => h.elim
  | f :: fs, h => by
    rcases h with h | h
    · exact ⟨f, List.mem_cons_self, h⟩
    · obtain ⟨g, hg, h⟩ := hashIn_conjL σ fs h
      exact ⟨g, List.mem_cons_of_mem _ hg, h⟩

theorem mem_finRange' {m : Nat} (a : Fin m) : a ∈ List.finRange m :=
  List.mem_iff_getElem.2 ⟨a.1, by simp only [List.length_finRange, a.2], by simp⟩

theorem mem_pairsFin {m : Nat} {p : Fin m × Fin m} (h : p ∈ pairsFin m) : p.1 < p.2 := by
  simp only [pairsFin, List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨a, -, b, -, hb⟩ := h
  split at hb
  · cases hb; assumption
  · cases hb

theorem pairsFin_mem {m : Nat} {a b : Fin m} (h : a < b) : (a, b) ∈ pairsFin m := by
  simp only [pairsFin, List.mem_flatMap, List.mem_filterMap]
  exact ⟨a, mem_finRange' a, b, mem_finRange' b, by rw [if_pos h]⟩

theorem mem_linkE {k₁ : HashKind} {L : List Nat} {f : Fml C (List.replicate L.length (.val .uint) ++ Γ)}
    (h : f ∈ linkE k₁ (Γ := Γ) L) : ∃ (a b : Fin L.length), a < b ∧ ∃ (R₁ R₂ : RefTy)
      (i : Idx Γ (.mem R₁)) (j : Idx Γ (.mem R₂)), strAt L a = some ⟨R₁, i⟩ ∧ strAt L b = some ⟨R₂, j⟩ ∧
      f = Fml.iffF (.eq (hnode k₁ (i.wk (Thin.dropN L.length))) (hnode k₁ (j.wk (Thin.dropN L.length))))
        (.eq (.pvV (topIdx L.length a)) (.pvV (topIdx L.length b))) := by
  simp only [linkE, List.mem_filterMap] at h
  obtain ⟨⟨a, b⟩, hp, hf⟩ := h
  split at hf
  · rename_i R₁ i R₂ j ha hb
    cases hf
    exact ⟨a, b, mem_pairsFin hp, R₁, R₂, i, j, ha, hb, rfl⟩
  · cases hf

theorem linkE_mem {k₁ : HashKind} {L : List Nat} {a b : Fin L.length} (hab : a < b) {R₁ R₂ : RefTy}
    {i : Idx Γ (.mem R₁)} {j : Idx Γ (.mem R₂)} (ha : strAt L a = some ⟨R₁, i⟩)
    (hb : strAt L b = some ⟨R₂, j⟩) :
    Fml.iffF (.eq (hnode k₁ (i.wk (Thin.dropN L.length))) (hnode k₁ (j.wk (Thin.dropN L.length))))
      (.eq (.pvV (topIdx L.length a)) (.pvV (topIdx L.length b))) ∈ linkE k₁ (C := C) (Γ := Γ) L := by
  simp only [linkE, List.mem_filterMap]
  exact ⟨(a, b), pairsFin_mem hab, by simp only [ha, hb]⟩

theorem mem_fixE {k₁ k₂ : HashKind} {L : List Nat} {f : Fml C (List.replicate L.length (.val .uint) ++ Γ)}
    (h : f ∈ fixE k₁ k₂ (Γ := Γ) L) : ∃ (d : Fin L.length) (R : RefTy) (i : Idx Γ (.mem R)),
      strAt L d = some ⟨R, i⟩ ∧ f = famPairE k₁ k₂ (i.wk (Thin.dropN L.length)) (topIdx L.length d) := by
  simp only [fixE, List.mem_filterMap] at h
  obtain ⟨d, -, hf⟩ := h
  split at hf
  · rename_i R i hd
    cases hf
    exact ⟨d, R, i, hd, rfl⟩
  · cases hf

theorem fixE_mem {k₁ k₂ : HashKind} {L : List Nat} (d : Fin L.length) {R : RefTy} {i : Idx Γ (.mem R)}
    (hd : strAt L d = some ⟨R, i⟩) :
    famPairE k₁ k₂ (i.wk (Thin.dropN L.length)) (topIdx L.length d) ∈ fixE k₁ k₂ (C := C) (Γ := Γ) L := by
  simp only [fixE, List.mem_filterMap]
  exact ⟨d, mem_finRange' d, by simp only [hd]⟩

end Nodes

/-! ## Validity -/

/-- On a formula `Fml.xk` returns the premise is read nowhere either. -/
theorem _root_.Solidity.Fml.holdsS_img_xk {k₂ : HashKind} {Γ : Ctx} (φ : Fml C Γ) :
    ∀ {Γ' : Ctx} {θ : XMap Γ Γ'} {φ' : Fml C Γ'}, φ.xk k₂ θ = some φ' → ∀ τ' : State C Γ',
      (Fml.holdsS τ' φ' ↔ holds τ' φ') := by
  induction φ with
  | tt => intro _ _ _ e _; cases e; exact Iff.rfl
  | eq a b =>
    intro _ _ _ e _
    obtain ⟨a', _, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨b', _, rfl⟩ := Option.map_eq_some_iff.1 e
    exact Iff.rfl
  | wellFormed s =>
    intro _ _ _ e _
    obtain ⟨s', _, rfl⟩ := Option.map_eq_some_iff.1 e
    exact Iff.rfl
  | not φ ih =>
    intro _ _ _ e τ
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact not_congr (ih hφ τ)
  | and φ ψ ihφ ihψ =>
    intro _ _ _ e τ
    obtain ⟨φ', hφ, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨ψ', hψ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact and_congr (ihφ hφ τ) (ihψ hψ τ)
  | imp φ ψ ihφ ihψ =>
    intro _ _ _ e τ
    obtain ⟨φ', hφ, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨ψ', hψ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact imp_congr (ihφ hφ τ) (ihψ hψ τ)
  | upd m U φ ih =>
    intro _ _ _ e τ
    obtain ⟨r, _, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact ⟨fun h => Upd.afterT_imp h fun σ' => (ih hφ σ').1,
      fun h => Upd.afterT_imp h fun σ' => (ih hφ σ').2⟩
  | modal | havoc | all | bind | anon | allocAll | grow => intro _ _ _ e; cases e

section Extras

variable {Γ : Ctx}

theorem lift_dropN (τ : State C Γ) (m : Nat) (es : Fin m → PrimTy.uint.Denote) :
    τ.lift (Thin.dropN m) (envOf m es τ.env) = τ.withEnv (envOf m es τ.env) := by
  unfold State.lift
  rw [put_dropN]

/-- **The extra words set to the strings' hashes of kind `k₂`.** -/
theorem xrel_extras (k₂ : HashKind) (L : List Nat) (τ : State C Γ) (es : Fin L.length → PrimTy.uint.Denote)
    (hes : ∀ (d : Fin L.length) {R : RefTy} (i : Idx Γ (.mem R)), i.level = L[d] →
      ∃ id, τ.getV i = some id ∧ es d = τ.glob.memT.hashId k₂ R id) :
    XRel k₂ (XMap.extras L Γ) τ (envOf L.length es τ.env) := by
  intro R i j hj
  simp only [XMap.extras] at hj
  obtain ⟨d, hd, hj⟩ := Option.bind_eq_some_iff.1 hj
  obtain ⟨hlt, hL⟩ := posIn_spec L _ d hd
  rw [dif_pos hlt] at hj
  cases hj
  obtain ⟨id, hv, he⟩ := hes ⟨d, hlt⟩ i hL.symm
  refine ⟨id, hv, ?_⟩
  show TEnv.get (topIdx L.length ⟨d, hlt⟩) (TEnv.put (Thin.dropN L.length) τ.env
    (envOf L.length es τ.env)) = _
  rw [put_dropN, get_topIdx]
  exact he

/-- Past no extra words, every map holds. -/
theorem xrel_extras_nil (k₂ : HashKind) {L : List Nat} (hL : L.length = 0) (τ : State C Γ)
    (d : TEnv C τ.H (List.replicate L.length (.val .uint) ++ Γ)) : XRel k₂ (XMap.extras L Γ) τ d := by
  intro R i j hj
  simp only [XMap.extras] at hj
  obtain ⟨n, -, hj⟩ := Option.bind_eq_some_iff.1 hj
  rw [dif_neg (by omega)] at hj
  cases hj

/-- The strings' hashes of kind `k₂`, at the levels `L`. -/
def esOf (k₂ : HashKind) (L : List Nat) (τ : State C Γ) (d : Fin L.length) : PrimTy.uint.Denote :=
  match Idx.memAtLevel? Γ L[d] with
  | some ⟨R, i⟩ => τ.glob.memT.hashId k₂ R ((τ.getV i).getD 0)
  | none => PrimTy.dflt .uint

theorem esOf_spec (k₂ : HashKind) (L : List Nat) (τ : State C Γ)
    (hstr : ∀ {R : RefTy} (i : Idx Γ (.mem R)), (τ.getV i).isSome) (d : Fin L.length) {R : RefTy}
    (i : Idx Γ (.mem R)) (hl : i.level = L[d]) :
    ∃ id, τ.getV i = some id ∧ esOf k₂ L τ d = τ.glob.memT.hashId k₂ R id := by
  obtain ⟨id, hid⟩ := Option.isSome_iff_exists.1 (hstr i)
  refine ⟨id, hid, ?_⟩
  unfold esOf
  rw [← hl, Idx.memAtLevel?_self i]
  simp only [hid, Option.getD_some]

end Extras


/-! ## Formulas the premise reads no binder of -/

/-- Equations, `wt` and the connectives. -/
def _root_.Solidity.Fml.pureB {Γ : Ctx} : Fml C Γ → Bool
  | .tt | .eq .. | .wellFormed _ => true
  | .not φ => φ.pureB
  | .and φ ψ | .imp φ ψ => φ.pureB && ψ.pureB
  | _ => false

theorem _root_.Solidity.Fml.holdsS_pure {Γ : Ctx} : (φ : Fml C Γ) → φ.pureB = true → ∀ τ : State C Γ,
    (Fml.holdsS τ φ ↔ holds τ φ)
  | .tt, _, _ | .eq .., _, _ | .wellFormed _, _, _ => Iff.rfl
  | .not φ, h, τ => not_congr (Fml.holdsS_pure φ h τ)
  | .and φ ψ, h, τ => by
    simp only [Fml.pureB, Bool.and_eq_true] at h
    exact and_congr (Fml.holdsS_pure φ h.1 τ) (Fml.holdsS_pure ψ h.2 τ)
  | .imp φ ψ, h, τ => by
    simp only [Fml.pureB, Bool.and_eq_true] at h
    exact imp_congr (Fml.holdsS_pure φ h.1 τ) (Fml.holdsS_pure ψ h.2 τ)

theorem _root_.Solidity.Fml.pure_conjL {Γ : Ctx} : (fs : List (Fml C Γ)) → (∀ f ∈ fs, f.pureB = true) →
    (Fml.conjL fs).pureB = true
  | [], _ => rfl
  | f :: fs, h => by
    simp only [Fml.conjL, Fml.pureB, Bool.and_eq_true]
    exact ⟨h f List.mem_cons_self, Fml.pure_conjL fs fun g hg => h g (List.mem_cons_of_mem _ hg)⟩

theorem _root_.Solidity.Fml.pure_conjL_linkE {Γ : Ctx} (k₁ : HashKind) (L : List Nat) :
    (Fml.conjL (linkE k₁ (C := C) (Γ := Γ) L)).pureB = true :=
  Fml.pure_conjL _ fun f hf => by
    obtain ⟨a, b, -, R₁, R₂, i, j, -, -, rfl⟩ := mem_linkE hf
    rfl

theorem _root_.Solidity.Fml.pure_conjL_fixE {Γ : Ctx} (k₁ k₂ : HashKind) (L : List Nat) :
    (Fml.conjL (fixE k₁ k₂ (C := C) (Γ := Γ) L)).pureB = true :=
  Fml.pure_conjL _ fun f hf => by
    obtain ⟨d, R, i, -, rfl⟩ := mem_fixE hf
    show (Fml.conjL _).pureB = true
    exact Fml.pure_conjL _ fun g hg => by
      obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg'
      rfl

section Lifted

variable {Γ Γ' : Ctx}

theorem hnode_wk_denote (h : Thin Γ Γ') (τ : State C Γ) (d : TEnv C τ.H Γ') (k : HashKind) {R : RefTy}
    (i : Idx Γ (.mem R)) : (hnode k (i.wk h)).denote (τ.lift h d) = (hnode k i).denote τ := by
  show Op2.eval τ.glob (.hash k) (Op0.eval τ.glob .memory) ((TEnv.get (i.wk h) (τ.lift h d).env).map (·.id)) =
    Op2.eval τ.glob (.hash k) (Op0.eval τ.glob .memory) ((TEnv.get i τ.env).map (·.id))
  rw [State.get_lift]
  rfl

theorem hnode_wk_hashIn (h : Thin Γ Γ') (τ : State C Γ) (d : TEnv C τ.H Γ') (k : HashKind) {R : RefTy}
    (i : Idx Γ (.mem R)) {k' : HashKind} {inp : Option (List Nat)} {out : PrimTy.uint.Denote} :
    (hnode k (i.wk h)).HashIn (τ.lift h d) k' inp out ↔ (hnode k i).HashIn τ k' inp out := by
  show Op2.HashIn (H := τ.H) k' inp out (Op2.hash (R := R) k) (some τ.glob.memT)
      ((TEnv.get (i.wk h) (τ.lift h d).env).map (·.id)) ∨ False ∨ False ↔
    Op2.HashIn (H := τ.H) k' inp out (Op2.hash (R := R) k) (some τ.glob.memT)
      ((TEnv.get i τ.env).map (·.id)) ∨ False ∨ False
  rw [State.get_lift]
  exact Iff.rfl

theorem topIdx_denote (τ : State C Γ) (m : Nat) (es : Fin m → PrimTy.uint.Denote) (d : Fin m) :
    (Tm.pvV (C := C) (topIdx m d)).denote (τ.lift (Thin.dropN m) (envOf m es τ.env)) = some (es d) := by
  show some (TEnv.get (topIdx m d) (TEnv.put (Thin.dropN m) τ.env (envOf m es τ.env))) = _
  rw [put_dropN, get_topIdx]

end Lifted

/-- **The body with the second kind's words is sound**: where its reading
under the premise holds, the body holds under the body's premise. -/
theorem _root_.Solidity.Fml.tkBody_sound {k₁ k₂ : HashKind} (hk₁ : k₁ ≠ .ecrecover)
    (hk₂ : k₂ ≠ .ecrecover) {Γ : Ctx} (ψ : Fml C Γ) {φ₂ : Fml C Γ} (e : ψ.tkBody k₁ k₂ false = some φ₂)
    (τ : State C Γ) (hstr : ∀ {R : RefTy} (i : Idx Γ (.mem R)), (τ.getV i).isSome)
    (H : φ₂.HashFree τ → Fml.holdsS τ φ₂) (hf : ψ.HashFree τ) : Fml.holdsS τ ψ := by
  unfold Fml.tkBody at e
  simp only [Bool.false_eq_true, ↓reduceIte] at e
  split at e
  · rename_i hcov
    generalize hLd : (Fml.hLevels k₂ ψ).eraseDups = L at hcov e
    obtain ⟨ψ₂, hψ₂, rfl⟩ := Option.map_eq_some_iff.1 e
    have hcov' : ∀ l ∈ L, (Idx.memAtLevel? Γ l).isSome ∧ l ∈ ψ.topLevels k₁ ∧ l ∈ ψ.topLevels k₂ :=
      fun l hl => by
        have := List.all_eq_true.1 (Bool.and_eq_true _ _ ▸ hcov).2 l hl
        simp only [Bool.and_eq_true, List.contains_iff_mem] at this
        exact ⟨this.1.1, this.1.2, this.2⟩
    -- the strings `L` names are hashed by both kinds where the premise reads them
    have hnodeIn : ∀ {R : RefTy} (i : Idx Γ (.mem R)) (kk : HashKind), i.level ∈ L →
        (kk = k₁ ∨ kk = k₂) → ∀ id, τ.getV i = some id →
          Fml.HashIn kk (τ.glob.memT.hashInput R id) (τ.glob.memT.hashId kk R id) τ ψ := by
      intro R i kk hl hkk id hv
      have hc := hcov' _ hl
      have htop : i.level ∈ ψ.topLevels kk := by
        rcases hkk with rfl | rfl
        · exact hc.2.1
        · exact hc.2.2
      obtain ⟨R', i', hl', hin⟩ := Fml.topLevels_hashIn τ kk ψ htop
      have he := mem_level_eq hl'
      cases he
      exact hin id hv
    have strL : ∀ (a : Fin L.length) {R : RefTy} {i : Idx Γ (.mem R)}, strAt L a = some ⟨R, i⟩ →
        i.level ∈ L := fun a R i ha => by
      rw [Idx.memAtLevel?_level ha]
      exact List.getElem_mem _
    -- a hash term of the body read past the binders is one of the body's
    have hBin : ∀ (es' : Fin L.length → PrimTy.uint.Denote),
        XRel k₂ (XMap.extras L Γ) τ (envOf L.length es' τ.env) → ∀ {k inp out},
          Fml.HashIn k inp out (τ.withEnv (envOf L.length es' τ.env))
            (.imp (Fml.conjL []) (.imp (Fml.conjL (linkE k₁ L)) ψ₂)) → Fml.HashIn k inp out τ ψ := by
      intro es' hX' k inp out hi
      rw [← lift_dropN] at hi
      rcases hi with hi | hi | hi
      · exact hi.elim
      · obtain ⟨f, hf', hi⟩ := hashIn_conjL _ _ hi
        obtain ⟨a, b, -, R₁, R₂, i, j, ha, hb, rfl⟩ := mem_linkE hf'
        rcases hi with ((h | h) | (h | h)) | ((h | h) | (h | h))
        · rw [hnode_wk_hashIn] at h
          obtain ⟨rfl, id, hv, rfl, rfl⟩ := hnode_hashIn τ _ i h
          exact hnodeIn i _ (strL a ha) (.inl rfl) id hv
        · rw [hnode_wk_hashIn] at h
          obtain ⟨rfl, id, hv, rfl, rfl⟩ := hnode_hashIn τ _ j h
          exact hnodeIn j _ (strL b hb) (.inl rfl) id hv
        · exact h.elim
        · exact h.elim
        · exact h.elim
        · exact h.elim
        · rw [hnode_wk_hashIn] at h
          obtain ⟨rfl, id, hv, rfl, rfl⟩ := hnode_hashIn τ _ i h
          exact hnodeIn i _ (strL a ha) (.inl rfl) id hv
        · rw [hnode_wk_hashIn] at h
          obtain ⟨rfl, id, hv, rfl, rfl⟩ := hnode_hashIn τ _ j h
          exact hnodeIn j _ (strL b hb) (.inl rfl) id hv
      · exact Fml.xk_hashIn _ hψ₂ τ _ hX' hi
    have hfreeB : ∀ (es' : Fin L.length → PrimTy.uint.Denote),
        XRel k₂ (XMap.extras L Γ) τ (envOf L.length es' τ.env) →
          Fml.HashFree (τ.withEnv (envOf L.length es' τ.env))
            (.imp (Fml.conjL []) (.imp (Fml.conjL (linkE k₁ L)) ψ₂)) :=
      fun es' hX' k hk i₁ i₂ out h₁ h₂ => hf k hk i₁ i₂ out (hBin es' hX' h₁) (hBin es' hX' h₂)
    have hX : XRel k₂ (XMap.extras L Γ) τ (envOf L.length (esOf k₂ L τ) τ.env) :=
      xrel_extras k₂ L τ _ (esOf_spec k₂ L τ hstr)
    have hHf := hashFree_allN (.user "e") L.length _ τ fun es' hm => hfreeB es' (xrel_extras_nil k₂ hm τ _)
    have hS := holdsS_allN (.user "e") L.length _ τ (H hHf) (esOf k₂ L τ) (hfreeB _ hX)
    obtain ⟨ψ', hψ'⟩ : ∃ ψ', ψ.xk k₂ (XMap.extras L Γ) = some ψ' := ⟨ψ₂, hψ₂⟩
    rw [Fml.holdsS_of_xk ψ hψ' τ]
    -- the link holds where the extra words are the strings' hashes
    have hlink : holds (τ.lift (Thin.dropN L.length) (envOf L.length (esOf k₂ L τ) τ.env))
        (Fml.conjL (linkE k₁ L)) := by
      refine (holds_conjL _ _).2 fun f hf' => ?_
      obtain ⟨a, b, -, R₁, R₂, i, j, ha, hb, rfl⟩ := mem_linkE hf'
      obtain ⟨idi, hvi⟩ := Option.isSome_iff_exists.1 (hstr i)
      obtain ⟨idj, hvj⟩ := Option.isSome_iff_exists.1 (hstr j)
      obtain ⟨idi', hvi', hei⟩ := esOf_spec k₂ L τ hstr a i (Idx.memAtLevel?_level ha)
      obtain ⟨idj', hvj', hej⟩ := esOf_spec k₂ L τ hstr b j (Idx.memAtLevel?_level hb)
      rw [hvi] at hvi'; cases hvi'
      rw [hvj] at hvj'; cases hvj'
      have step : ∀ kk kk', (kk = k₁ ∨ kk = k₂) → kk ≠ .ecrecover →
          τ.glob.memT.hashId kk R₁ idi = τ.glob.memT.hashId kk R₂ idj →
            τ.glob.memT.hashId kk' R₁ idi = τ.glob.memT.hashId kk' R₂ idj := by
        intro kk kk' hkk hne he
        have h2 := hnodeIn j kk (strL b hb) hkk idj hvj
        rw [← he] at h2
        exact Grown.hashId_of_input _ kk' (hf kk hne _ _ _ (hnodeIn i kk (strL a ha) hkk idi hvi) h2)
      show (holds _ (.eq _ _) → holds _ (.eq _ _)) ∧ (holds _ (.eq _ _) → holds _ (.eq _ _))
      rw [holds_eq, holds_eq, hnode_wk_denote, hnode_wk_denote, hnode_denote τ k₁ i hvi,
        hnode_denote τ k₁ j hvj, topIdx_denote, topIdx_denote, hei, hej, Option.some.injEq,
        Option.some.injEq]
      exact ⟨step k₁ k₂ (.inl rfl) hk₁, step k₂ k₁ (.inr rfl) hk₂⟩
    rw [← lift_dropN] at hS
    have h3 := hS trivial ((Fml.holdsS_pure _ (Fml.pure_conjL_linkE k₁ L) _).2 hlink)
    exact (Fml.xk_holds ψ hψ₂ τ _ hX).1 ((Fml.holdsS_img_xk ψ hψ₂ _).1 h3)
  · cases e

theorem hashFree_allocAll {Γ : Ctx} (σ : State C Γ) (x : Var) (R : RefTy) (φ : Fml C (.mem R :: Γ)) :
    (Fml.allocAll x R φ).HashFree σ := fun _ _ _ _ _ h => h.elim

theorem strOK_push {Γ : Ctx} {τ : State C Γ} (h : ∀ {R : RefTy} (i : Idx Γ (.mem R)), (τ.getV i).isSome)
    {p : PrimTy} (v : p.Denote) : ∀ {R : RefTy} (i : Idx (.val p :: Γ) (.mem R)),
      ((τ.push (t := .val p) v).getV i).isSome := by
  intro R i
  cases i with
  | there j => exact h j

theorem strOK_alloc {Γ : Ctx} {τ : State C Γ} (h : ∀ {R : RefTy} (i : Idx Γ (.mem R)), (τ.getV i).isSome)
    {R₀ : RefTy} (o : MObj τ.H R₀) : ∀ {R : RefTy} (i : Idx (.mem R₀ :: Γ) (.mem R)),
      (((τ.alloc o).1.push (t := .mem R₀) (some (τ.alloc o).2)).getV i).isSome := by
  intro R i
  cases i with
  | here => rfl
  | there j =>
    show ((τ.alloc o).1.getV j).isSome = true
    rw [State.getV_alloc]
    exact h j

/-- **The leaf with the second kind's words is sound**, through its prefix. -/
theorem _root_.Solidity.Fml.tk_sound {k₁ k₂ : HashKind} (hk₁ : k₁ ≠ .ecrecover) (hk₂ : k₂ ≠ .ecrecover)
    {Γ : Ctx} (φ : Fml C Γ) : ∀ {φ₂ : Fml C Γ}, φ.tk k₁ k₂ false = some φ₂ → ∀ τ : State C Γ,
      (∀ {R : RefTy} (i : Idx Γ (.mem R)), (τ.getV i).isSome) →
      (φ₂.HashFree τ → Fml.holdsS τ φ₂) → φ.HashFree τ → Fml.holdsS τ φ := by
  induction φ with
  | all x p φ ih =>
    intro _ e τ hstr H _
    obtain ⟨φ₂, hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    intro v hv
    exact ih hφ _ (strOK_push hstr v) (fun hf => H (hashFree_all _ _ _ _) v hf) hv
  | allocAll x R φ ih =>
    intro _ e τ hstr H _
    obtain ⟨φ₂, hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    intro o ho
    exact ih hφ _ (strOK_alloc hstr o) (fun hf => H (hashFree_allocAll _ _ _ _) o hf) ho
  | tt | eq | wellFormed | not | and | imp | upd =>
    intro _ e τ hstr H hf
    exact Fml.tkBody_sound hk₁ hk₂ _ e τ hstr H hf
  | modal | havoc | bind | anon | grow => intro _ e; cases e

/-- **A valid reading with the second kind's words makes the leaf valid
under its premise.** -/
theorem _root_.Solidity.Fml.tk_validH {k₁ k₂ : HashKind} (hk₁ : k₁ ≠ .ecrecover)
    (hk₂ : k₂ ≠ .ecrecover) {φ φ₂ : Fml C []} (e : φ.tk k₁ k₂ false = some φ₂) (hv : Fml.ValidH φ₂) :
    Fml.ValidH φ :=
  fun σ hf => Fml.tk_sound hk₁ hk₂ φ e σ (fun i => nomatch i) (hv σ) hf

/-! ## Refutations -/

section MemNodes

variable {Γ : Ctx}

theorem _root_.Solidity.Tm.memNodes_hashIn (σ : State C Γ) {k : HashKind} {inp : Option (List Nat)}
    {out : PrimTy.uint.Denote} : {s : Srt} → (t : Tm C Γ s) → t.memNodes = true → t.HashIn σ k inp out →
      ∃ R id, inp = σ.glob.memT.hashInput R id ∧ out = σ.glob.memT.hashId k R id
  | _, .netOf _ a, hm, h | _, .app1 _ a, hm, h => Tm.memNodes_hashIn σ a hm h
  | _, .app2 o x y, hm, h => by
    simp only [Tm.memNodes, Bool.and_eq_true] at hm
    rcases h with h | h | h
    · cases o with
      | hash k' =>
        cases x with
        | app0 o' =>
          cases o' with
          | memory =>
            cases y with
            | pvI i =>
              obtain ⟨rfl, id, -, h1, h2⟩ := hnode_hashIn σ k' i (.inl h)
              exact ⟨_, id, h1, h2⟩
            | _ => exact absurd hm.1.1 Bool.false_ne_true
          | _ => exact absurd hm.1.1 Bool.false_ne_true
        | _ => exact absurd hm.1.1 Bool.false_ne_true
      | _ => exact h.elim
    · exact Tm.memNodes_hashIn σ x hm.1.2 h
    · exact Tm.memNodes_hashIn σ y hm.2 h
  | _, .app3 _ x y z, hm, h => by
    simp only [Tm.memNodes, Bool.and_eq_true] at hm
    rcases h with h | h | h
    · exact Tm.memNodes_hashIn σ x hm.1.1 h
    · exact Tm.memNodes_hashIn σ y hm.1.2 h
    · exact Tm.memNodes_hashIn σ z hm.2 h
  | _, .pvV _, _, h | _, .pvP _, _, h | _, .pvS _, _, h | _, .pvI _, _, h | _, .app0 _, _, h
  | _, .pvZ _, _, h => h.elim

end MemNodes

/-- **The hash nodes of a body read memory locals**, past its updates too:
of the memory it starts in. -/
theorem _root_.Solidity.Fml.memNodes_hashIn {k : HashKind} {Γ : Ctx} (φ : Fml C Γ) :
    φ.memNodes = true → ∀ (σ : State C Γ) {inp : Option (List Nat)} {out : PrimTy.uint.Denote},
      Fml.HashIn k inp out σ φ → ∃ R id, inp = σ.glob.memT.hashInput R id ∧ out = σ.glob.memT.hashId k R id := by
  induction φ with
  | tt => intro _ _ _ _ h; exact h.elim
  | eq a b =>
    intro hm σ _ _ h
    simp only [Fml.memNodes, Bool.and_eq_true] at hm
    rcases h with h | h
    · exact Tm.memNodes_hashIn σ a hm.1 h
    · exact Tm.memNodes_hashIn σ b hm.2 h
  | wellFormed s => intro hm σ _ _ h; exact Tm.memNodes_hashIn σ s hm h
  | not φ ih => intro hm σ _ _ h; exact ih hm σ h
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ =>
    intro hm σ _ _ h
    simp only [Fml.memNodes, Bool.and_eq_true] at hm
    rcases h with h | h
    · exact ihφ hm.1 σ h
    · exact ihψ hm.2 σ h
  | upd m U φ ih =>
    intro hm σ _ _ h
    simp only [Fml.memNodes, Bool.and_eq_true] at hm
    obtain ⟨hU, hφ⟩ := hm
    cases U with
    | snoc U₀ e₀ =>
      cases U₀ with
      | nil =>
        cases e₀ with
        | storage s =>
          rcases h with (h | h) | ⟨g, σ', hg, hL, h⟩
          · exact h.elim
          · exact Tm.memNodes_hashIn σ s hU h
          · have hg' : (s.eval σ).bind (fun st => some (σ.globG.withStorage st)) = some g := hg
            obtain ⟨st, -, ⟨⟩⟩ := Option.bind_eq_some_iff.1 hg'
            have hσ : σ'.glob = { σ.glob with storage := st } := hL.2.1
            obtain ⟨R, id, h1, h2⟩ := ih hφ σ' h
            refine ⟨R, id, ?_, ?_⟩
            · rw [h1, hσ]; rfl
            · rw [h2, hσ]; rfl
        | _ => simp only [Upd.memNodes1, Bool.false_eq_true] at hU
      | _ => simp only [Upd.memNodes1, Bool.false_eq_true] at hU
    | decl U₀ x r =>
      cases U₀ with
      | nil =>
        cases r with
        | val t =>
          rcases h with (h | h) | ⟨g, σ', hg, hL, h⟩
          · exact h.elim
          · exact Tm.memNodes_hashIn σ t hU h
          · have hg' : (t.eval σ).bind (fun _ => some σ.globG) = some g := hg
            obtain ⟨_, -, ⟨⟩⟩ := Option.bind_eq_some_iff.1 hg'
            have hσ : σ'.glob = σ.glob := hL.2.1
            obtain ⟨R, id, h1, h2⟩ := ih hφ σ' h
            exact ⟨R, id, by rw [h1, hσ], by rw [h2, hσ]⟩
        | _ => simp only [Upd.memNodes1, Bool.false_eq_true] at hU
      | _ => simp only [Upd.memNodes1, Bool.false_eq_true] at hU
    | _ => simp only [Upd.memNodes1, Bool.false_eq_true] at hU
  | modal | havoc | all | bind | anon | allocAll | grow => intro hm; simp only [Fml.memNodes,
      Bool.false_eq_true] at hm

/-- **A heap of the family's strings meets the premise** of a body whose
hash nodes read memory locals, of every kind. -/
theorem _root_.Solidity.Fml.hashFree_memNodes {Γ : Ctx} {φ : Fml C Γ} (hm : φ.memNodes = true)
    (σ : State C Γ) (hF : FamHeap famBound σ.glob) : φ.HashFree σ := by
  intro k hk i₁ i₂ out h₁ h₂
  have hok := famOK_bound k hk
  obtain ⟨R₁, id₁, rfl, ho₁⟩ := Fml.memNodes_hashIn φ hm σ h₁
  obtain ⟨R₂, id₂, rfl, ho₂⟩ := Fml.memNodes_hashIn φ hm σ h₂
  rcases hF.hash k R₁ id₁ with ⟨hi₁, hh₁⟩ | ⟨j₁, hj₁, hi₁, hh₁⟩ <;>
    rcases hF.hash k R₂ id₂ with ⟨hi₂, hh₂⟩ | ⟨j₂, hj₂, hi₂, hh₂⟩
  · rw [hi₁, hi₂]
  · exact absurd (congrArg Subtype.val ((hh₁.symm.trans ho₁.symm).trans (ho₂.trans hh₂))).symm
      (famOK_ne hok hj₂)
  · exact absurd (congrArg Subtype.val ((hh₂.symm.trans ho₂.symm).trans (ho₁.trans hh₁))).symm
      (famOK_ne hok hj₁)
  · rw [hi₁, hi₂, famOK_inj hok hj₁ hj₂ ((hh₁.symm.trans ho₁.symm).trans (ho₂.trans hh₂))]

/-! ### The new binders, swapped -/

/-- `v`, then `es`. -/
def finCons {α : Type} {m : Nat} (v : α) (es : Fin m → α) : Fin (m + 1) → α :=
  fun i => Fin.cases (motive := fun _ => α) v es i

@[simp] theorem finCons_zero {α : Type} {m : Nat} (v : α) (es : Fin m → α) : finCons v es 0 = v :=
  Fin.cases_zero

@[simp] theorem finCons_succ {α : Type} {m : Nat} (v : α) (es : Fin m → α) (i : Fin m) :
    finCons v es i.succ = es i := Fin.cases_succ i

section Swapped

variable {Γ : Ctx}

/-- `Fml.allN` in the swapped context. -/
def _root_.Solidity.Fml.allNsw (x : Var) :
    (m : Nat) → Fml C (Ctx.sw (List.replicate m (.val .uint) ++ Γ)) → Fml C (Ctx.sw Γ)
  | 0, ψ => ψ
  | m + 1, ψ => Fml.allNsw x m (.all x .uint ψ)

/-- `envOf` in the swapped context. -/
def envOfSw {H : HTy} : (m : Nat) → (Fin m → PrimTy.uint.Denote) → TEnv C H (Ctx.sw Γ) →
    TEnv C H (Ctx.sw (List.replicate m (.val .uint) ++ Γ))
  | 0, _, e => e
  | m + 1, es, e => (es 0, envOfSw m (fun i => es i.succ) e)

theorem _root_.Solidity.Fml.swInst_allN (k : HashKind) (cs : List Nat) (x : Var) :
    (m : Nat) → (F : Fml C (List.replicate m (.val .uint) ++ Γ)) →
      (Fml.allN x m F).swInst k cs = (F.swInst k cs).map (Fml.allNsw x m)
  | 0, F => by simp only [Fml.allN, Fml.allNsw, Option.map_id']
  | m + 1, F => by
    show (Fml.allN x m (.all x .uint F)).swInst k cs = _
    rw [Fml.swInst_allN k cs x m (.all x .uint F)]
    show ((F.swInst k cs).map (Fml.all x .uint)).map (Fml.allNsw x m) = _
    rw [Option.map_map]
    rfl

theorem holds_allNsw (x : Var) : (m : Nat) → (ψ : Fml C (Ctx.sw (List.replicate m (.val .uint) ++ Γ))) →
    (τ : State C (Ctx.sw Γ)) → (holds τ (Fml.allNsw x m ψ) ↔
      ∀ es : Fin m → PrimTy.uint.Denote, holds (τ.withEnv (envOfSw m es τ.env)) ψ)
  | 0, ψ, τ => ⟨fun h _ => h, fun h => h Fin.elim0⟩
  | m + 1, ψ, τ => by
    rw [show Fml.allNsw x (m + 1) ψ = Fml.allNsw x m (.all x .uint ψ) from rfl, holds_allNsw x m]
    constructor
    · intro h es
      exact h (fun i => es i.succ) (es 0)
    · intro h es' v
      have := h (finCons v es')
      simp only [finCons_zero, finCons_succ] at this
      exact this

theorem holds_allN (x : Var) : (m : Nat) → (ψ : Fml C (List.replicate m (.val .uint) ++ Γ)) →
    (τ : State C Γ) → (holds τ (Fml.allN x m ψ) ↔
      ∀ es : Fin m → PrimTy.uint.Denote, holds (τ.withEnv (envOf m es τ.env)) ψ)
  | 0, ψ, τ => ⟨fun h _ => h, fun h => h Fin.elim0⟩
  | m + 1, ψ, τ => by
    rw [show Fml.allN x (m + 1) ψ = Fml.allN x m (.all x .uint ψ) from rfl, holds_allN x m]
    constructor
    · intro h es
      exact h (fun i => es i.succ) (es 0)
    · intro h es' v
      have := h (finCons v es')
      simp only [finCons_zero, finCons_succ] at this
      exact this

/-- **The new binders' values pushed alike** in a state and its swapped reading. -/
theorem SwRel.envOf {k : HashKind} {τ : State C Γ} {τ' : State C (Ctx.sw Γ)} (h : SwRel k τ τ') :
    (m : Nat) → (es : Fin m → PrimTy.uint.Denote) →
      SwRel k (τ.withEnv (envOf m es τ.env)) (τ'.withEnv (envOfSw m es τ'.env))
  | 0, _ => h
  | m + 1, es => (SwRel.envOf h m (fun i => es i.succ)).push (p := .uint) (es 0)

end Swapped

theorem holds_orL {Γ : Ctx} (σ : State C Γ) (fs : List (Fml C Γ)) :
    holds σ (Fml.orL fs) ↔ ∃ f ∈ fs, holds σ f := by
  show ¬ holds σ (Fml.conjL (fs.map .not)) ↔ _
  rw [holds_conjL]
  constructor
  · intro h
    exact Classical.byContradiction fun hn => h fun g hg => by
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
      exact fun hf' => hn ⟨f, hf, hf'⟩
  · rintro ⟨f, hf, hf'⟩ h
    exact h _ (List.mem_map_of_mem hf) hf'

/-- What a hash of an identity reads and returns in a heap of the family:
nothing, or one string of the family and its hash of every kind. -/
theorem FamHeap.hashAll {N : Nat} {g : State C []} (hF : FamHeap N g) (R : RefTy) (id : Nat) :
    (g.memT.hashInput R id = none ∧ ∀ k, g.memT.hashId k R id = PrimTy.dflt .uint) ∨
      ∃ j < N, g.memT.hashInput R id = some ((famBytes j).map fun b => b.toNat % 256) ∧
        ∀ k, g.memT.hashId k R id = famHash k j := by
  unfold Grown.hashInput Grown.hashId
  cases hr : HRef.ofId? g.memT.H' R id with
  | none => exact .inl ⟨rfl, fun _ => rfl⟩
  | some r =>
    obtain ⟨j, hj, hw⟩ := hF r
    refine .inr ⟨j, hj, ?_, fun k => ?_⟩
    · show some ((MObj.words R (g.heap.get r)).map _) = some _
      rw [hw]
    · show k.apply (MObj.words R (g.heap.get r)) = _
      rw [hw]
      rfl

theorem _root_.Solidity.Fml.tkBody_memNodes {k₁ k₂ : HashKind} {fix : Bool} {Γ : Ctx} {ψ φ' : Fml C Γ}
    (e : ψ.tkBody k₁ k₂ fix = some φ') : ψ.memNodes = true := by
  unfold Fml.tkBody at e
  cases fix
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at e
    split at e
    · rename_i hcov
      exact (Bool.and_eq_true _ _ ▸ hcov).1
    · cases e

/-- **The leaf meets its premise in a heap of the family**, where it has
the second kind's words. -/
theorem _root_.Solidity.Fml.tk_hashFree {k₁ k₂ : HashKind} {fix : Bool} {Γ : Ctx} {φ φ' : Fml C Γ}
    (e : φ.tk k₁ k₂ fix = some φ') (σ : State C Γ) (hF : FamHeap famBound σ.glob) : φ.HashFree σ := by
  cases φ with
  | all | allocAll => intro _ _ _ _ _ h; exact h.elim
  | modal | havoc | bind | anon | grow => cases e
  | _ => exact Fml.hashFree_memNodes (Fml.tkBody_memNodes e) σ hF

/-- **What the body says under its premise in a heap of the family, the
instance with the second kind's words fixed says.** -/
theorem _root_.Solidity.Fml.tkBody_inst_holds {k₁ k₂ : HashKind} (hk₁ : k₁ ≠ .ecrecover)
    (hk₂ : k₂ ≠ .ecrecover) {Γ : Ctx} (ψ : Fml C Γ) {φF : Fml C Γ}
    (e : ψ.tkBody k₁ k₂ true = some φF) {cs : List Nat} {inst : Fml C (Ctx.sw Γ)}
    (ei : φF.swInst k₁ cs = some inst) (τ : State C Γ) (τ' : State C (Ctx.sw Γ)) (h : SwRel k₁ τ τ')
    (hF : FamHeap famBound τ.glob) (hstr : ∀ {R : RefTy} (i : Idx Γ (.mem R)), (τ.getV i).isSome)
    (hs : Fml.holdsS τ ψ) : holds τ' inst := by
  unfold Fml.tkBody at e
  simp only [↓reduceIte] at e
  split at e
  · rename_i hcov
    generalize hLd : (Fml.hLevels k₂ ψ).eraseDups = L at hcov e
    obtain ⟨ψ₂, hψ₂, rfl⟩ := Option.map_eq_some_iff.1 e
    rw [Fml.swInst_allN] at ei
    obtain ⟨B', hB', rfl⟩ := Option.map_eq_some_iff.1 ei
    have hB'' : Fml.sw k₁ (.imp (Fml.conjL (fixE k₁ k₂ L)) (.imp (Fml.conjL (linkE k₁ L)) ψ₂)) = some B' := hB'
    rw [holds_allNsw]
    intro es
    rw [Fml.sw_holds _ hB'' _ _ (h.envOf L.length es)]
    intro hfix _
    rw [← lift_dropN] at hfix ⊢
    have hes : ∀ (d : Fin L.length) {R : RefTy} (i : Idx Γ (.mem R)), i.level = L[d] →
        ∃ id, τ.getV i = some id ∧ es d = τ.glob.memT.hashId k₂ R id := by
      intro d R i hl
      obtain ⟨id, hid⟩ := Option.isSome_iff_exists.1 (hstr i)
      refine ⟨id, hid, ?_⟩
      have hsd : strAt (Γ := Γ) L d = some ⟨R, i⟩ := by
        unfold strAt
        rw [← hl, Idx.memAtLevel?_self]
      have hp := (holds_conjL _ _).1 hfix _ (fixE_mem (C := C) (k₁ := k₁) (k₂ := k₂) d hsd)
      obtain ⟨f, hf, hf'⟩ := (holds_orL _ _).1 hp
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hf
      obtain ⟨h1, h2⟩ := hf'
      rw [holds_eq, hnode_wk_denote, hnode_denote τ k₁ i hid] at h1
      rw [holds_eq, topIdx_denote] at h2
      have h1' := Option.some.inj h1
      have h2' := Option.some.inj h2
      have hjb := List.mem_range.1 hj
      rcases hF.hashAll R id with ⟨-, hz⟩ | ⟨j', hj', -, hk⟩
      · rw [hz k₁] at h1'
        exact absurd (congrArg Subtype.val h1'.symm) (famOK_ne (famOK_bound k₁ hk₁) hjb)
      · rw [hk k₁] at h1'
        have := famOK_inj (famOK_bound k₁ hk₁) hj' hjb h1'
        subst this
        rw [h2', hk k₂]
    have hX : XRel k₂ (XMap.extras L Γ) τ (envOf L.length es τ.env) := xrel_extras k₂ L τ es hes
    exact (Fml.xk_holds ψ hψ₂ τ _ hX).2 ((Fml.holdsS_of_xk ψ hψ₂ τ).1 hs)
  · cases e

/-- **What the leaf says under its premise, its strings chosen in the
family, the instance with the second kind's words fixed says.** -/
theorem _root_.Solidity.Fml.tk_inst_holds {k₁ k₂ : HashKind} (hk₁ : k₁ ≠ .ecrecover)
    (hk₂ : k₂ ≠ .ecrecover) {Γ : Ctx} (φ : Fml C Γ) :
    ∀ {cs : List Nat} {φF : Fml C Γ} {inst : Fml C (Ctx.sw Γ)}, φ.tk k₁ k₂ true = some φF →
      φF.swInst k₁ cs = some inst → (∀ j ∈ cs, j < famBound) →
      ∀ (τ : State C Γ) (τ' : State C (Ctx.sw Γ)), SwRel k₁ τ τ' → FamHeap famBound τ.glob →
      (∀ {R : RefTy} (i : Idx Γ (.mem R)), (τ.getV i).isSome) → Fml.holdsS τ φ → holds τ' inst := by
  induction φ with
  | all x p φ ih =>
    intro cs _ _ e ei hcs τ τ' h hF hstr hs
    obtain ⟨φF, hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨inst, hi, rfl⟩ := Option.map_eq_some_iff.1 ei
    exact fun v => ih hφ hi hcs _ _ (h.push v) hF (strOK_push hstr v)
      (hs v (Fml.tk_hashFree hφ _ hF))
  | allocAll x R φ ih =>
    intro cs _ _ e ei hcs τ τ' h hF hstr hs
    obtain ⟨φF, hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    cases cs with
    | nil => cases ei
    | cons j cs =>
      simp only [Fml.swInst] at ei
      split at ei
      · rename_i hR
        subst hR
        obtain ⟨inst, hi, rfl⟩ := Option.map_eq_some_iff.1 ei
        have hj : j < famBound := hcs j (List.mem_cons_self ..)
        intro w hw
        have hw' : w = famHash k₁ j := Option.some.inj hw
        subst hw'
        let o := famObj τ.H j
        have hF' : FamHeap famBound (τ.alloc o).1.glob := hF.alloc hj
        have h' := (h.alloc o).pushMem (τ.alloc o).2
        rw [State.alloc_hashId_self, famObj_words] at h'
        exact ih hφ hi (fun i hi => hcs i (List.mem_cons_of_mem _ hi)) _ _ h' hF' (strOK_alloc hstr o)
          (hs o (Fml.tk_hashFree hφ _ hF'))
      · cases ei
  | tt | eq | wellFormed | not | and | imp | upd =>
    intro cs _ _ e ei _ τ τ' h hF hstr hs
    exact Fml.tkBody_inst_holds hk₁ hk₂ _ e ei τ τ' h hF hstr hs
  | modal | havoc | bind | anon | grow => intro _ _ _ e; cases e

/-- **A refutation of the instance with the second kind's words fixed
refutes the leaf under its premise**: in the state with no memory, the
leaf's fresh strings allocated with the family's bytes. -/
theorem _root_.Solidity.Fml.tk_refutes {k₁ k₂ : HashKind} (hk₁ : k₁ ≠ .ecrecover) (hk₂ : k₂ ≠ .ecrecover)
    {φ φF : Fml C []} {cs : List Nat} {inst : Fml C []} (e : φ.tk k₁ k₂ true = some φF)
    (ei : φF.swInst k₁ cs = some inst) (hcs : ∀ j ∈ cs, j < famBound) {σ : State C []}
    (hr : ¬ holds σ inst) : ¬ Fml.holdsH σ.noHeap φ := by
  intro hH
  have hF : FamHeap famBound σ.noHeap.glob := FamHeap.empty famBound _ rfl
  exact hr (Fml.tk_inst_holds hk₁ hk₂ φ e ei hcs σ.noHeap σ ⟨⟨rfl, rfl, rfl, rfl⟩, fun i => nomatch i⟩
    hF (fun i => nomatch i) (hH (Fml.tk_hashFree e _ hF)))

end Solidity.Decide
