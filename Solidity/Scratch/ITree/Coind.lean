/-!
# Scratch (itree-inspection, Experiment C(ii)): a homegrown coinductive tree

No Mathlib, so no M-types: a coinductive tree is a pointed coalgebra (a
state machine whose states unfold to nodes), equality is replaced by
bisimilarity.  The minimum to state bind associativity (strong
bisimilarity) and one up-to-tau lemma (`tau t ≈ t`, weak bisimilarity
`Eutt`, inductive tau-stripping under a coinductive bisimulation).  Not for
merge: `docs/audits/itree-inspection.md`.
-/

namespace Solidity.Scratch.ITree.Co

variable {E : Type} {Ans : E → Type}

/-- One unfolding: a result, a silent step, or an event with its
continuation, over states `S`. -/
inductive Node (E : Type) (Ans : E → Type) (R S : Type) where
  | ret (r : R)
  | tau (s : S)
  | vis (e : E) (k : Ans e → S)

def Node.mapS {R S S' : Type} (f : S → S') : Node E Ans R S → Node E Ans R S'
  | .ret r => .ret r
  | .tau s => .tau (f s)
  | .vis e k => .vis e (f ∘ k)

theorem Node.mapS_mapS {R S S' S'' : Type} (f : S → S') (g : S' → S'') (n : Node E Ans R S) :
    (n.mapS f).mapS g = n.mapS (g ∘ f) := by
  cases n <;> rfl

/-- **A coinductive interaction tree**: a state machine and its start. -/
structure CoTree (E : Type) (Ans : E → Type) (R : Type) : Type 1 where
  S : Type
  step : S → Node E Ans R S
  root : S

namespace CoTree

variable {R R' R'' : Type}

/-- The tree from another state of the same machine. -/
def at_ (t : CoTree E Ans R) (s : t.S) : CoTree E Ans R := ⟨t.S, t.step, s⟩

def ret (r : R) : CoTree E Ans R := ⟨Unit, fun _ => .ret r, ()⟩

def tau (t : CoTree E Ans R) : CoTree E Ans R :=
  ⟨Option t.S, fun | none => .tau (some t.root) | some s => (t.step s).mapS some, none⟩

/-- `forever`: the silently diverging tree (`diverge` as a tree). -/
def spin : CoTree E Ans R := ⟨Unit, fun _ => .tau (), ()⟩

/-- Bind: run `t`, then at a result `r` the machine of `k r`. -/
def bind (t : CoTree E Ans R) (k : R → CoTree E Ans R') : CoTree E Ans R' where
  S := t.S ⊕ (Σ r, (k r).S)
  step
    | .inl s =>
      match t.step s with
      | .ret r => ((k r).step (k r).root).mapS (fun s' => .inr ⟨r, s'⟩)
      | .tau s' => .tau (.inl s')
      | .vis e k' => .vis e (fun a => .inl (k' a))
    | .inr ⟨r, s⟩ => ((k r).step s).mapS (fun s' => .inr ⟨r, s'⟩)
  root := .inl t.root

/-! ## Strong bisimilarity -/

/-- Nodes related by `Rel` on their states. -/
inductive NodeRel {S₁ S₂ : Type} (Rel : S₁ → S₂ → Prop) : Node E Ans R S₁ → Node E Ans R S₂ → Prop
  | ret (r : R) : NodeRel Rel (.ret r) (.ret r)
  | tau {x y} : Rel x y → NodeRel Rel (.tau x) (.tau y)
  | vis (e : E) {k₁ k₂} : (∀ a, Rel (k₁ a) (k₂ a)) → NodeRel Rel (.vis e k₁) (.vis e k₂)

/-- **Strong bisimilarity**: some relation on states relating the roots is
closed under one unfolding (the greatest fixpoint, by Knaster–Tarski). -/
def Bisim (t u : CoTree E Ans R) : Prop :=
  ∃ Rel : t.S → u.S → Prop, Rel t.root u.root ∧ ∀ x y, Rel x y → NodeRel Rel (t.step x) (u.step y)

theorem NodeRel.mapS {S₁ S₂ T₁ T₂ : Type} {Rel : S₁ → S₂ → Prop} {Rel' : T₁ → T₂ → Prop}
    {f : S₁ → T₁} {g : S₂ → T₂} (hfg : ∀ x y, Rel x y → Rel' (f x) (g y))
    {n₁ : Node E Ans R S₁} {n₂ : Node E Ans R S₂} (h : NodeRel Rel n₁ n₂) :
    NodeRel Rel' (n₁.mapS f) (n₂.mapS g) := by
  cases h with
  | ret r => exact .ret r
  | tau h => exact .tau (hfg _ _ h)
  | vis e h => exact .vis e (fun a => hfg _ _ (h a))

theorem NodeRel.refl {S : Type} (n : Node E Ans R S) : NodeRel (fun x y : S => x = y) n n := by
  cases n with
  | ret r => exact .ret r
  | tau s => exact .tau rfl
  | vis e k => exact .vis e (fun _ => rfl)

/-- **Bind is associative**, up to strong bisimilarity. -/
theorem bind_assoc (t : CoTree E Ans R) (k : R → CoTree E Ans R') (h : R' → CoTree E Ans R'') :
    Bisim ((t.bind k).bind h) (t.bind fun r => (k r).bind h) := by
  let Rel : ((t.bind k).bind h).S → (t.bind fun r => (k r).bind h).S → Prop
    | .inl (.inl s), .inl s' => s = s'
    | .inl (.inr ⟨r, s⟩), .inr ⟨r', .inl s'⟩ => r = r' ∧ HEq s s'
    | .inr ⟨q, s⟩, .inr ⟨_, .inr ⟨q', s'⟩⟩ => q = q' ∧ HEq s s'
    | _, _ => False
  refine ⟨Rel, rfl, ?_⟩
  -- the common tail: `h q`'s machine from a state, on both sides
  have tailH0 : ∀ (q : R') (s : (h q).S) (r : R),
      NodeRel Rel (((h q).step s).mapS fun s' => .inr ⟨q, s'⟩)
        (((h q).step s).mapS fun s' => .inr ⟨r, .inr ⟨q, s'⟩⟩) :=
    fun q s r => (NodeRel.refl _).mapS (fun x y hxy => by subst hxy; exact ⟨rfl, .rfl⟩)
  have tailH : ∀ (q : R') (s : (h q).S) (r : R),
      NodeRel Rel ((t.bind k).bind h |>.step (.inr ⟨q, s⟩))
        ((t.bind fun r => (k r).bind h).step (.inr ⟨r, .inr ⟨q, s⟩⟩)) := by
    intro q s r
    simp only [bind, Node.mapS_mapS]
    exact tailH0 q s r
  -- `k r`'s machine from a state, on both sides
  have tailK : ∀ (r : R) (s : (k r).S),
      NodeRel Rel ((t.bind k).bind h |>.step (.inl (.inr ⟨r, s⟩)))
        ((t.bind fun r => (k r).bind h).step (.inr ⟨r, .inl s⟩)) := by
    intro r s
    cases hs : (k r).step s <;> simp only [bind, hs, Node.mapS_mapS]
    case ret q => exact tailH0 q (h q).root r
    case tau s' => exact .tau ⟨rfl, .rfl⟩
    case vis e k' => exact .vis e (fun _ => ⟨rfl, .rfl⟩)
  intro x y hxy
  match x, y, hxy with
  | .inl (.inl s), .inl s', hss =>
    subst hss
    simp only [bind]
    cases hs : t.step s with
    | ret r =>
      have := tailK r (k r).root
      simp only [bind] at this
      exact this
    | tau s' => exact .tau rfl
    | vis e k' => exact .vis e (fun _ => rfl)
  | .inl (.inr ⟨r, s⟩), .inr ⟨r', .inl s'⟩, ⟨hr, hs⟩ =>
    subst hr; cases hs; exact tailK r s
  | .inr ⟨q, s⟩, .inr ⟨r, .inr ⟨q', s'⟩⟩, ⟨hq, hs⟩ =>
    subst hq; cases hs; exact tailH q s r

/-! ## Weak bisimilarity (`eutt`) -/

/-- One unfolding up to finitely many silent steps on either side
(inductive), the continuations related by `Rel` (coinductive). -/
inductive EuttF {S₁ S₂ : Type} (st₁ : S₁ → Node E Ans R S₁) (st₂ : S₂ → Node E Ans R S₂)
    (Rel : S₁ → S₂ → Prop) : S₁ → S₂ → Prop
  | ret {x y} (r : R) : st₁ x = .ret r → st₂ y = .ret r → EuttF st₁ st₂ Rel x y
  | vis {x y} (e : E) {k₁ k₂} : st₁ x = .vis e k₁ → st₂ y = .vis e k₂ →
      (∀ a, Rel (k₁ a) (k₂ a)) → EuttF st₁ st₂ Rel x y
  | tau {x y x' y'} : st₁ x = .tau x' → st₂ y = .tau y' → Rel x' y' → EuttF st₁ st₂ Rel x y
  | tauL {x y x'} : st₁ x = .tau x' → EuttF st₁ st₂ Rel x' y → EuttF st₁ st₂ Rel x y
  | tauR {x y y'} : st₂ y = .tau y' → EuttF st₁ st₂ Rel x y' → EuttF st₁ st₂ Rel x y

/-- **Equivalence up to tau**. -/
def Eutt (t u : CoTree E Ans R) : Prop :=
  ∃ Rel : t.S → u.S → Prop, Rel t.root u.root ∧ ∀ x y, Rel x y → EuttF t.step u.step Rel x y

/-- **Up to tau**: a silent step changes nothing. -/
theorem tau_eutt (t : CoTree E Ans R) : Eutt t.tau t := by
  let Rel : Option t.S → t.S → Prop
    | none, s => s = t.root
    | some s, s' => s = s'
  -- from a state of `t`, against itself
  have same : ∀ s, EuttF t.tau.step t.step Rel (some s) s := by
    intro s
    cases hs : t.step s with
    | ret r => exact .ret r (by simp [tau, hs, Node.mapS]) hs
    | tau s' => exact .tau (x' := some s') (by simp [tau, hs, Node.mapS]) hs rfl
    | vis e k => exact .vis e (by simp [tau, hs, Node.mapS]; rfl) hs (fun _ => rfl)
  refine ⟨Rel, rfl, ?_⟩
  intro x y hxy
  match x, hxy with
  | none, hy => subst hy; exact .tauL rfl (same _)
  | some s, hy => subst hy; exact same _

/-- Reflexivity, which the up-to-tau lemmas use. -/
theorem Eutt.refl (t : CoTree E Ans R) : Eutt t t := by
  refine ⟨fun x y => x = y, rfl, ?_⟩
  intro x y hxy; subst hxy
  cases hs : t.step x with
  | ret r => exact .ret r hs hs
  | tau s => exact .tau hs hs rfl
  | vis e k => exact .vis e hs hs (fun _ => rfl)

end CoTree

end Solidity.Scratch.ITree.Co
