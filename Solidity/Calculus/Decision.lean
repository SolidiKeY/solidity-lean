import Solidity.Calculus.AutoComplete
import Solidity.Calculus.QuantTotality

/-!
# The closer's decision, stated (M7)

The theorem the closer is held to (`docs/automation.md`, M7): on a scoped
leaf `Fml C []` it terminates with a proof (`LeafVerdict.proved`) or a
certified counterexample (`LeafVerdict.refuted σ`, a typed state that
refutes the leaf), and it may answer `unknown` only where the user allowed
it (`docs/automation.md`, M6, decisions c, c′, d and their extensions):

* a product of two non-literal terms (KeY `int` or a 256-bit type), `x ** e`
  at a literal `e ≥ 2` and `mulmod` of two symbolic factors among them;
* `/`, `%`, `**`, `<<`, `>>`, `&`, `|`, `^` with two symbolic operands, a
  symbolic divisor (`c / x`), exponent or shift amount counted as such
  (`Waivers`: each class a field, all waived by the user's answer);
* a quantified formula over array or mapping contents outside the array
  property fragment (Bradley, Manna and Sipma), negative-position
  `havoc`/`anon`/`allocAll`/`grow` and storage binders among them;
* a verdict that turns on an `ecrecover` value (an `opaque` function) or
  on a hash preimage (e3′, 2026-10-25).

Hashes are read as e3′ has it: each goal under the premise that its own
hash terms are free of collisions (`Fml.HashFree`, `Fml.holdsH`,
`Fml.ValidH`), no axiom and no global assumption; the premise is taken
per scope, each binder's instance under its own.  In the fragment a hash
term stands where that premise settles it: against a hash of its kind
(`==`, `!=`), or as the key of a mapping at a root whose keys are all
hashes (`Fml.inTarget`); `ecrecover` stands nowhere.

The fragment is `Fml.inTarget`, the statement `DecisionTheorem`, both
about the one decision function `decideGoal` (`decideLeaf` on a leaf
without a hash).  The statement is the goal of the rounds to come, not true
today: `Examples/Decision.lean`'s `apf` is in the fragment and answered
`unknown`.  A statement of the form "some decider is complete" would
be vacuous: a classical function deciding validity by `Classical.choice`
exists, so the statement is about this computable function, which later
rounds extend.

What is proved: `decideLeaf` is sound (`decideLeaf_sound`), its refutations
are refutations (`decideLeaf_refutes`), and it answers on `Fml.Covered`
(`decideLeaf_complete`), the fragment M4 proves total
(`dependentReduction?_isSome`) as extended since; `decideGoal` likewise
under the hash premise (`decideGoal_sound`, `decideGoal_refutes`,
`decideGoal_complete`, on covered leaves without a hash).  `Fml.Covered`
also holds of formulas with programs, which `Fml.inTarget` (on leaves)
excludes; on program-free leaves the inclusion `Fml.Covered ⊆
Fml.inTarget` is not proved (`Fml.Covered` is read on the eliminated leaf,
`Fml.inTarget` on the source).

The array-property check is syntactic and conservative: an update or a
program under a quantifier counts as reading at its variable, the body of a
negative-position block must be quantifier-free, and an index guard is an
`&&`/`||` of comparisons (never `!=`) of index terms, a bound variable or a
term mentioning none; a hash stored by an update, a hash key of a nested
mapping and an `ecrecover` term are outside.  So
`Fml.inTarget` is a subset of the fragment the user named, never a
superset.
-/

namespace Solidity.Decide

open Linear

variable {C : Contract}

/-! ## Verdicts and the decision -/

/-- What the closer answers on a leaf. -/
inductive LeafVerdict (C : Contract) where
  /-- The leaf is valid. -/
  | proved
  /-- The typed state refutes the leaf. -/
  | refuted (σ : State C [])
  /-- Neither: allowed only outside the fragment. -/
  | unknown

/-- **The decision**: the automatic pipeline (`dependentReduction?`), its
arithmetic decided by the verified procedure (`AFml.decide_iff`), a `false`
answer turned into a typed countermodel (`DependentReduction.verify`); on a
leaf it refuses, the quantified pipeline (`quantReduction?`), decided by
the verified projection procedure (`QFml.decide_iff`, `QuantReduction.verify`). -/
def decideLeaf (φ : Fml C []) : LeafVerdict C :=
  match dependentReduction? φ with
  | some r =>
    match r.verify with
    | .inl _ => .proved
    | .inr cm => .refuted cm.state
  | none =>
    match quantReduction? φ with
    | some q =>
      match q.verify with
      | .inl _ => .proved
      | .inr cm => .refuted cm.1
    | none => .unknown

/-- **Soundness.** -/
theorem decideLeaf_sound {φ : Fml C []} (h : decideLeaf φ = .proved) : Fml.Valid φ := by
  unfold decideLeaf at h
  split at h
  · split at h
    · rename_i hv _
      exact hv.down
    · cases h
  · split at h
    · split at h
      · rename_i hv _
        exact hv.down
      · cases h
    · cases h

/-- **Refutations are certified**: the state returned refutes the leaf. -/
theorem decideLeaf_refutes {φ : Fml C []} {σ : State C []} (h : decideLeaf φ = .refuted σ) :
    ¬ holds σ φ := by
  unfold decideLeaf at h
  split at h
  · split at h
    · cases h
    · rename_i cm _
      cases h
      exact cm.refutes
  · split at h
    · split at h
      · cases h
      · rename_i cm _
        cases h
        exact cm.2
    · cases h

theorem decideLeaf_not_valid {φ : Fml C []} {σ : State C []} (h : decideLeaf φ = .refuted σ) :
    ¬ Fml.Valid φ :=
  fun hv => decideLeaf_refutes h (hv σ)

/-- **The fragment proved complete**: M4's, on the eliminated leaf, and the
quantified one (`Fml.quantCovered`, M7 step 4). -/
def _root_.Solidity.Fml.Covered (φ : Fml C []) : Bool :=
  φ.inExact && φ.exactBounded || φ.quantCovered

/-- **Completeness on `Fml.Covered`.** -/
theorem decideLeaf_complete {φ : Fml C []} (h : φ.Covered = true) : decideLeaf φ ≠ .unknown := by
  simp only [Fml.Covered, Bool.or_eq_true, Bool.and_eq_true] at h
  unfold decideLeaf
  cases hd : dependentReduction? φ with
  | some r =>
    dsimp only
    split <;> exact fun h => nomatch h
  | none =>
    rcases h with h | h
    · have := dependentReduction?_isSome φ h.1 h.2
      rw [hd] at this
      cases this
    · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (quantReduction?_isSome φ h)
      dsimp only
      rw [hq]
      dsimp only
      split <;> exact fun h => nomatch h

/-- On the fragment the verdict is exact. -/
theorem decideLeaf_proved_iff {φ : Fml C []} (h : φ.Covered = true) :
    decideLeaf φ = .proved ↔ Fml.Valid φ := by
  refine ⟨decideLeaf_sound, fun hv => ?_⟩
  cases hd : decideLeaf φ with
  | proved => rfl
  | refuted σ => exact absurd hv (decideLeaf_not_valid hd)
  | unknown => exact absurd hd (decideLeaf_complete h)

/-! ## The goal under its own hash premise (e3′)

A hash is the real function of its bytes (`Heap.hash`), so a leaf may turn
on a collision no one can exhibit.  The user's reading (2026-10-25, e3′):
each goal is read under the premise that *its own* hash terms are free of
collisions, distinct inputs giving distinct outputs.  The premise is part
of the goal's reading, not an axiom and not a global assumption.

`Fml.HashIn k inp out σ φ`: some hash term of `φ`, of kind `k`, outside
`φ`'s binders, evaluated at `σ` (or past `φ`'s updates), reads the bytes
`inp` and returns `out`.  The premise is taken at every scope: `Fml.holdsH`
is `holds` with each binder's body read under the premise of that
instance, so a premise is about finitely many hash evaluations, false only
at an actual collision among them.  `ecrecover` is no hash of the premise:
it is `0` on every invalid signature. -/

/-- The bytes a hash of the object `id` reads, each word modulo `256` as
`HashKind.apply` reads it: `none` where `id` names no object of type `R`
(the hash is then `0`). -/
def _root_.Solidity.Grown.hashInput {H : HTy} (m : Grown H (fun _ => Unit)) (R : RefTy) (id : Nat) :
    Option (List Nat) :=
  (HRef.ofId? m.H' R id).map fun r => (MObj.words R (m.heap.get r)).map fun b => b.toNat % 256

/-- A hash node, evaluated: kind `k`, input `inp`, output `out`. -/
def _root_.Solidity.Op2.HashIn {H : HTy} (k : HashKind) (inp : Option (List Nat))
    (out : PrimTy.uint.Denote) {a b s : Srt} :
    Op2 C a b s → Option (a.Den C H) → Option (b.Den C H) → Prop
  | @Op2.hash _ R k', some m, some id => k' = k ∧ inp = m.hashInput R id ∧ out = m.hashId k' R id
  | _, _, _ => False

def _root_.Solidity.Tm.HashIn {Γ : Ctx} (σ : State C Γ) (k : HashKind) (inp : Option (List Nat))
    (out : PrimTy.uint.Denote) : {s : Srt} → Tm C Γ s → Prop
  | _, .netOf _ a | _, .app1 _ a => a.HashIn σ k inp out
  | _, .app2 o x y => o.HashIn (H := σ.H) k inp out (x.eval σ) (y.eval σ) ∨ x.HashIn σ k inp out ∨
      y.HashIn σ k inp out
  | _, .app3 _ x y z => x.HashIn σ k inp out ∨ y.HashIn σ k inp out ∨ z.HashIn σ k inp out
  | _, _ => False

def _root_.Solidity.Rhs.HashIn {Γ : Ctx} (σ : State C Γ) (k : HashKind) (inp : Option (List Nat))
    (out : PrimTy.uint.Denote) {t : LTy} : Rhs C Γ t → Prop
  | .val a | .zint a => a.HashIn σ k inp out
  | .path q => q.HashIn σ k inp out
  | .mref i => i.HashIn σ k inp out
  | .store s => s.HashIn σ k inp out
  | .unset | .saveNet | .saveNetMt => False

def _root_.Solidity.UpdElem.HashIn {Γ Δ : Ctx} (σ : State C Γ) (k : HashKind)
    (inp : Option (List Nat)) (out : PrimTy.uint.Denote) : UpdElem C Γ Δ → Prop
  | .local _ r => r.HashIn σ k inp out
  | .storage s => s.HashIn σ k inp out
  | .memory m => m.HashIn σ k inp out
  | .selfBalance _ a | .setBalance a => a.HashIn σ k inp out
  | .net r _ a | .pay r a | .netMt r a => r.HashIn σ k inp out ∨ a.HashIn σ k inp out

def _root_.Solidity.Upd.HashIn {Γ : Ctx} (σ : State C Γ) (k : HashKind) (inp : Option (List Nat))
    (out : PrimTy.uint.Denote) : {Δ : Ctx} → Upd C Γ Δ → Prop
  | _, .nil => False
  | _, .snoc U e => U.HashIn σ k inp out ∨ e.HashIn σ k inp out
  | _, .decl U _ r => U.HashIn σ k inp out ∨ r.HashIn σ k inp out
  | _, .pop U _ | _, .drop U _ => U.HashIn σ k inp out

def _root_.Solidity.Fml.HashIn (k : HashKind) (inp : Option (List Nat)) (out : PrimTy.uint.Denote) :
    {Γ : Ctx} → State C Γ → Fml C Γ → Prop
  | _, _, .tt => False
  | _, σ, .eq a b => a.HashIn σ k inp out ∨ b.HashIn σ k inp out
  | _, σ, .wellFormed s => s.HashIn σ k inp out
  | _, σ, .not φ => Fml.HashIn k inp out σ φ
  | _, σ, .and φ ψ | _, σ, .imp φ ψ => Fml.HashIn k inp out σ φ ∨ Fml.HashIn k inp out σ ψ
  | _, σ, .upd _ U φ => U.HashIn σ k inp out ∨
      ∃ g σ', U.globT σ = some g ∧ U.Lands σ g σ' ∧ Fml.HashIn k inp out σ' φ
  | _, _, .modal .. | _, _, .havoc _ | _, _, .all .. | _, _, .bind .. | _, _, .anon .. | _, _, .allocAll ..
  | _, _, .grow _ => False

/-- **A scope's hash premise**: its hash terms of one kind (not
`ecrecover`) returning one output read one input. -/
def _root_.Solidity.Fml.HashFree {Γ : Ctx} (σ : State C Γ) (φ : Fml C Γ) : Prop :=
  ∀ k, k ≠ .ecrecover → ∀ i₁ i₂ out, Fml.HashIn k i₁ out σ φ → Fml.HashIn k i₂ out σ φ → i₁ = i₂

/-- `holds`, each binder's body under its instance's premise. -/
def _root_.Solidity.Fml.holdsS : {Γ : Ctx} → State C Γ → Fml C Γ → Prop
  | _, _, .tt => True
  | _, σ, .eq a b => holds σ (.eq a b)
  | _, σ, .wellFormed s => holds σ (.wellFormed s)
  | _, σ, .not φ => ¬ Fml.holdsS σ φ
  | _, σ, .and φ ψ => Fml.holdsS σ φ ∧ Fml.holdsS σ ψ
  | _, σ, .imp φ ψ => Fml.holdsS σ φ → Fml.holdsS σ ψ
  | _, σ, .upd m U φ => U.afterT m σ (Fml.holdsS · φ)
  | _, σ, .modal m P κ φ => holds σ (.modal m P κ φ)
  | _, σ, .havoc φ => ∀ st nt sb, φ.HashFree (σ.havoc st nt sb) → Fml.holdsS (σ.havoc st nt sb) φ
  | _, σ, .all _ p φ => ∀ v : p.Denote, φ.HashFree (σ.push (t := .val p) v) →
      Fml.holdsS (σ.push (t := .val p) v) φ
  | _, σ, .bind m _ t φ => m.forallB fun v : t.TDenote C σ.H => φ.HashFree (σ.push v) →
      Fml.holdsS (σ.push v) φ
  | _, σ, .anon xs φ => ∀ b, φ.HashFree (σ.anon xs b) → Fml.holdsS (σ.anon xs b) φ
  | _, σ, .allocAll _ R φ => ∀ o : MObj σ.H R,
      φ.HashFree ((σ.alloc o).1.push (t := .mem R) (some (σ.alloc o).2)) →
        Fml.holdsS ((σ.alloc o).1.push (t := .mem R) (some (σ.alloc o).2)) φ
  | _, σ, .grow φ => ∀ g : Grown σ.H (fun _ => Unit), Heap.Keeps g.ext σ.heap g.heap →
      φ.HashFree (σ.adopt g).1 → Fml.holdsS (σ.adopt g).1 φ

/-- **A leaf holds under its own hash premise.** -/
def _root_.Solidity.Fml.holdsH {Γ : Ctx} (σ : State C Γ) (φ : Fml C Γ) : Prop :=
  φ.HashFree σ → Fml.holdsS σ φ

/-- **Validity as the theorem reads it.** -/
def _root_.Solidity.Fml.ValidH (φ : Fml C []) : Prop := ∀ σ : State C [], Fml.holdsH σ φ

/-! ### A leaf without a hash: the premise is empty -/

def _root_.Solidity.Op2.isHash {a b s : Srt} : Op2 C a b s → Bool
  | .hash _ => true
  | _ => false

def _root_.Solidity.Tm.hasHash {Γ : Ctx} : {s : Srt} → Tm C Γ s → Bool
  | _, .netOf _ a | _, .app1 _ a => a.hasHash
  | _, .app2 o x y => o.isHash || x.hasHash || y.hasHash
  | _, .app3 _ x y z => x.hasHash || y.hasHash || z.hasHash
  | _, _ => false

def _root_.Solidity.Rhs.hasHash {Γ : Ctx} {t : LTy} : Rhs C Γ t → Bool
  | .val a | .zint a => a.hasHash
  | .path q => q.hasHash
  | .mref i => i.hasHash
  | .store s => s.hasHash
  | .unset | .saveNet | .saveNetMt => false

def _root_.Solidity.UpdElem.hasHash {Γ Δ : Ctx} : UpdElem C Γ Δ → Bool
  | .local _ r => r.hasHash
  | .storage s | .memory s => s.hasHash
  | .selfBalance _ a | .setBalance a => a.hasHash
  | .net r _ a | .pay r a | .netMt r a => r.hasHash || a.hasHash

def _root_.Solidity.Upd.hasHash {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, .nil => false
  | _, .snoc U e => U.hasHash || e.hasHash
  | _, .decl U _ r => U.hasHash || r.hasHash
  | _, .pop U _ | _, .drop U _ => U.hasHash

/-- The leaf mentions a hash (a program's are not read: `Fml.HashIn` reads
none either). -/
def _root_.Solidity.Fml.hasHash : {Γ : Ctx} → Fml C Γ → Bool
  | _, .tt | _, .modal .. => false
  | _, .eq a b => a.hasHash || b.hasHash
  | _, .wellFormed s => s.hasHash
  | _, .not φ | _, .havoc φ | _, .all _ _ φ | _, .bind _ _ _ φ | _, .anon _ φ | _, .allocAll _ _ φ
  | _, .grow φ => φ.hasHash
  | _, .and φ ψ | _, .imp φ ψ => φ.hasHash || ψ.hasHash
  | _, .upd _ U φ => U.hasHash || φ.hasHash

theorem _root_.Solidity.Op2.isHash_of_HashIn {H : HTy} {k : HashKind} {inp : Option (List Nat)}
    {out : PrimTy.uint.Denote} {a b s : Srt} (o : Op2 C a b s) (x : Option (a.Den C H))
    (y : Option (b.Den C H)) (h : o.HashIn k inp out x y) : o.isHash = true := by
  cases o <;> first | rfl | exact h.elim

theorem _root_.Solidity.Tm.hasHash_of_HashIn {Γ : Ctx} (σ : State C Γ) {k : HashKind}
    {inp : Option (List Nat)} {out : PrimTy.uint.Denote} {s : Srt} (t : Tm C Γ s)
    (h : t.HashIn σ k inp out) : t.hasHash = true := by
  induction t with
  | netOf _ a ih | app1 _ a ih => exact ih h
  | app2 o x y ihx ihy =>
    simp only [Tm.hasHash, Bool.or_eq_true]
    rcases h with h | h | h
    · exact .inl (.inl (o.isHash_of_HashIn _ _ h))
    · exact .inl (.inr (ihx h))
    · exact .inr (ihy h)
  | app3 _ x y z ihx ihy ihz =>
    simp only [Tm.hasHash, Bool.or_eq_true]
    rcases h with h | h | h
    · exact .inl (.inl (ihx h))
    · exact .inl (.inr (ihy h))
    · exact .inr (ihz h)
  | _ => exact h.elim

theorem _root_.Solidity.Rhs.hasHash_of_HashIn {Γ : Ctx} (σ : State C Γ) {k : HashKind}
    {inp : Option (List Nat)} {out : PrimTy.uint.Denote} {t : LTy} (r : Rhs C Γ t)
    (h : r.HashIn σ k inp out) : r.hasHash = true := by
  cases r <;> first | exact h.elim | exact Tm.hasHash_of_HashIn σ _ h

theorem _root_.Solidity.UpdElem.hasHash_of_HashIn {Γ Δ : Ctx} (σ : State C Γ) {k : HashKind}
    {inp : Option (List Nat)} {out : PrimTy.uint.Denote} (e : UpdElem C Γ Δ)
    (h : e.HashIn σ k inp out) : e.hasHash = true := by
  cases e with
  | «local» _ r => exact Rhs.hasHash_of_HashIn σ r h
  | storage s | memory s | selfBalance _ s | setBalance s => exact Tm.hasHash_of_HashIn σ s h
  | net r _ a | pay r a | netMt r a =>
    simp only [UpdElem.hasHash, Bool.or_eq_true]
    rcases h with h | h
    · exact .inl (Tm.hasHash_of_HashIn σ r h)
    · exact .inr (Tm.hasHash_of_HashIn σ a h)

theorem _root_.Solidity.Upd.hasHash_of_HashIn {Γ : Ctx} (σ : State C Γ) {k : HashKind}
    {inp : Option (List Nat)} {out : PrimTy.uint.Denote} :
    ∀ {Δ : Ctx} (U : Upd C Γ Δ), U.HashIn σ k inp out → U.hasHash = true
  | _, .nil, h => h.elim
  | _, .snoc U e, h => by
    simp only [Upd.hasHash, Bool.or_eq_true]
    rcases h with h | h
    · exact .inl (Upd.hasHash_of_HashIn σ U h)
    · exact .inr (UpdElem.hasHash_of_HashIn σ e h)
  | _, .decl U _ r, h => by
    simp only [Upd.hasHash, Bool.or_eq_true]
    rcases h with h | h
    · exact .inl (Upd.hasHash_of_HashIn σ U h)
    · exact .inr (Rhs.hasHash_of_HashIn σ r h)
  | _, .pop U _, h | _, .drop U _, h => Upd.hasHash_of_HashIn σ U h

theorem _root_.Solidity.Fml.hasHash_of_HashIn {k : HashKind} {inp : Option (List Nat)}
    {out : PrimTy.uint.Denote} : ∀ {Γ : Ctx} (σ : State C Γ) (φ : Fml C Γ),
      Fml.HashIn k inp out σ φ → φ.hasHash = true
  | _, _, .tt, h | _, _, .modal .., h | _, _, .havoc _, h | _, _, .all .., h | _, _, .bind .., h
  | _, _, .anon .., h | _, _, .allocAll .., h | _, _, .grow _, h => h.elim
  | _, σ, .eq a b, h => by
    simp only [Fml.hasHash, Bool.or_eq_true]
    rcases h with h | h
    · exact .inl (Tm.hasHash_of_HashIn σ a h)
    · exact .inr (Tm.hasHash_of_HashIn σ b h)
  | _, σ, .wellFormed s, h => Tm.hasHash_of_HashIn σ s h
  | _, σ, .not φ, h => Fml.hasHash_of_HashIn σ φ h
  | _, σ, .and φ ψ, h | _, σ, .imp φ ψ, h => by
    simp only [Fml.hasHash, Bool.or_eq_true]
    rcases h with h | h
    · exact .inl (Fml.hasHash_of_HashIn σ φ h)
    · exact .inr (Fml.hasHash_of_HashIn σ ψ h)
  | _, σ, .upd _ U φ, h => by
    simp only [Fml.hasHash, Bool.or_eq_true]
    rcases h with h | ⟨_, σ', _, _, h⟩
    · exact .inl (Upd.hasHash_of_HashIn σ U h)
    · exact .inr (Fml.hasHash_of_HashIn σ' φ h)

theorem _root_.Solidity.Fml.hashFree_of_hasHash {Γ : Ctx} (σ : State C Γ) (φ : Fml C Γ)
    (h : φ.hasHash = false) : φ.HashFree σ :=
  fun _ _ _ _ _ h₁ _ => absurd (Fml.hasHash_of_HashIn σ φ h₁) (by rw [h]; decide)

theorem _root_.Solidity.Fml.holdsS_iff : ∀ {Γ : Ctx} (σ : State C Γ) (φ : Fml C Γ),
    φ.hasHash = false → (Fml.holdsS σ φ ↔ holds σ φ)
  | _, _, .tt, _ | _, _, .eq _ _, _ | _, _, .wellFormed _, _ | _, _, .modal .., _ => Iff.rfl
  | _, σ, .not φ, h => not_congr (Fml.holdsS_iff σ φ h)
  | _, σ, .and φ ψ, h => by
    simp only [Fml.hasHash, Bool.or_eq_false_iff] at h
    exact and_congr (Fml.holdsS_iff σ φ h.1) (Fml.holdsS_iff σ ψ h.2)
  | _, σ, .imp φ ψ, h => by
    simp only [Fml.hasHash, Bool.or_eq_false_iff] at h
    exact imp_congr (Fml.holdsS_iff σ φ h.1) (Fml.holdsS_iff σ ψ h.2)
  | _, σ, .upd m U φ, h => by
    simp only [Fml.hasHash, Bool.or_eq_false_iff] at h
    exact ⟨fun hh => Upd.afterT_imp hh fun σ' => (Fml.holdsS_iff σ' φ h.2).mp,
      fun hh => Upd.afterT_imp hh fun σ' => (Fml.holdsS_iff σ' φ h.2).mpr⟩
  | _, σ, .havoc φ, h => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
      ⟨fun hh => (Fml.holdsS_iff _ φ h).mp (hh (Fml.hashFree_of_hasHash _ φ h)),
        fun hh _ => (Fml.holdsS_iff _ φ h).mpr hh⟩
  | _, σ, .all _ _ φ, h | _, σ, .bind _ _ _ φ, h | _, σ, .anon _ φ, h | _, σ, .allocAll _ _ φ, h =>
    forall_congr' fun _ =>
      ⟨fun hh => (Fml.holdsS_iff _ φ h).mp (hh (Fml.hashFree_of_hasHash _ φ h)),
        fun hh _ => (Fml.holdsS_iff _ φ h).mpr hh⟩
  | _, σ, .grow φ, h => forall_congr' fun _ => imp_congr_right fun _ =>
      ⟨fun hh => (Fml.holdsS_iff _ φ h).mp (hh (Fml.hashFree_of_hasHash _ φ h)),
        fun hh _ => (Fml.holdsS_iff _ φ h).mpr hh⟩

/-- **Without a hash the premise is empty**: the reading is `holds`. -/
theorem _root_.Solidity.Fml.holdsH_iff {Γ : Ctx} (σ : State C Γ) (φ : Fml C Γ)
    (h : φ.hasHash = false) : Fml.holdsH σ φ ↔ holds σ φ :=
  ⟨fun hh => (Fml.holdsS_iff σ φ h).mp (hh (Fml.hashFree_of_hasHash σ φ h)),
    fun hh _ => (Fml.holdsS_iff σ φ h).mpr hh⟩

theorem _root_.Solidity.Fml.validH_iff {φ : Fml C []} (h : φ.hasHash = false) :
    Fml.ValidH φ ↔ Fml.Valid φ :=
  forall_congr' fun σ => Fml.holdsH_iff σ φ h

/-! ### The decision, read so -/

/-- **The decision the theorem is about**: `decideLeaf` on a leaf without
a hash; `unknown` on one with a hash, which no stage reads yet. -/
def decideGoal (φ : Fml C []) : LeafVerdict C :=
  if φ.hasHash then .unknown else decideLeaf φ

theorem decideGoal_eq {φ : Fml C []} {v : LeafVerdict C} (h : decideGoal φ = v) (hv : v ≠ .unknown) :
    φ.hasHash = false ∧ decideLeaf φ = v := by
  unfold decideGoal at h
  cases hh : φ.hasHash
  · rw [hh] at h
    exact ⟨rfl, h⟩
  · rw [hh] at h
    exact absurd h.symm hv

/-- **Soundness**, under the goal's premise. -/
theorem decideGoal_sound {φ : Fml C []} (h : decideGoal φ = .proved) : Fml.ValidH φ := by
  obtain ⟨hh, hd⟩ := decideGoal_eq h (fun h => nomatch h)
  exact (Fml.validH_iff hh).mpr (decideLeaf_sound hd)

/-- **Refutations are certified**: the state's instance meets the premise
and refutes the leaf. -/
theorem decideGoal_refutes {φ : Fml C []} {σ : State C []} (h : decideGoal φ = .refuted σ) :
    ¬ Fml.holdsH σ φ := by
  obtain ⟨hh, hd⟩ := decideGoal_eq h (fun h => nomatch h)
  exact fun hv => decideLeaf_refutes hd ((Fml.holdsH_iff σ φ hh).mp hv)

/-- **Completeness on the covered leaves without a hash.** -/
theorem decideGoal_complete {φ : Fml C []} (h : φ.Covered = true) (hh : φ.hasHash = false) :
    decideGoal φ ≠ .unknown := by
  unfold decideGoal
  rw [hh]
  exact decideLeaf_complete h

/-! ## The fragment the user named -/

/-- **The classes the closer may leave `unknown` with two symbolic
operands** (`true`: waived; the user's answer of 2026-10-25 waives all
four). -/
structure Waivers where
  /-- `/`, `%`, a modulus of `addmod`/`mulmod`: a symbolic divisor. -/
  division : Bool := true
  /-- `**`: a symbolic exponent. -/
  power : Bool := true
  /-- `<<`, `>>`: a symbolic shift amount. -/
  shift : Bool := true
  /-- `&`, `|`, `^`: two symbolic operands. -/
  bitwise : Bool := true

/-- The level of a position: `0` for the outermost local, stable under
binders further in. -/
def _root_.Solidity.Idx.level {Γ : Ctx} {t : LTy} (i : Idx Γ t) : Nat := Γ.length - 1 - i.toNat

/-- A literal's integer. -/
def _root_.Solidity.Op0.litValue? {s : Srt} : Op0 C s → Option Int
  | .lit (p := .bool) v => some (cond (show Bool from v) 1 0)
  | .lit (p := .uint) v => some v.val
  | .lit (p := .int) v => some v.val
  | .zlit n => some n
  | _ => none

def _root_.Solidity.Tm.litValue? {Γ : Ctx} {s : Srt} : Tm C Γ s → Option Int
  | .app0 o => o.litValue?
  | _ => none

def _root_.Solidity.Tm.isLitV {Γ : Ctx} {s : Srt} (t : Tm C Γ s) : Bool := t.litValue?.isSome

/-- Whether an operator applied to operands (literal or not, the second's
literal value) is in the fragment. -/
def _root_.Solidity.BinOp.admits (w : Waivers) (op : BinOp) (xl yl : Bool) (y? : Option Int) : Bool :=
  match op with
  | .mul | .mulW => xl || yl
  | .div | .mod => yl || !w.division
  | .pow | .powW =>
    match y? with
    | some n => decide (n ≤ 1)
    | none => !w.power
  | .shl | .shr => yl || !w.shift
  | .band | .bor | .bxor => xl || yl || !w.bitwise
  | _ => true

def _root_.Solidity.Op2.admits (w : Waivers) {a b s : Srt} (o : Op2 C a b s) (xl yl : Bool)
    (y? : Option Int) : Bool :=
  match o with
  | .binop op _ => op.admits w xl yl y?
  | .zbin op _ => op != .mul || xl || yl
  | .hash _ => false
  | _ => true

def _root_.Solidity.Op3.admits (w : Waivers) {a b c s : Srt} (o : Op3 C a b c s) (xl yl zl : Bool) :
    Bool :=
  match o with
  | .modular .mulmod => (xl || yl) && (zl || !w.division)
  | .modular .addmod => zl || !w.division
  | _ => true

def _root_.Solidity.Op2.hashKind? {a b s : Srt} : Op2 C a b s → Option HashKind
  | .hash k => some k
  | _ => none

/-- `==`, `!=`. -/
def _root_.Solidity.Op2.isEqNe {a b s : Srt} : Op2 C a b s → Bool
  | .binop .eqB _ | .binop .neB _ => true
  | _ => false

/-- A mapping's key: `m[k]`. -/
def _root_.Solidity.Op2.isMapAt {a b s : Srt} : Op2 C a b s → Bool
  | .at .map => true
  | _ => false

def _root_.Solidity.Op0.rootNameD? {s : Srt} : Op0 C s → Option Name
  | .root r _ => some r
  | _ => none

/-- A root of the storage. -/
def _root_.Solidity.Tm.rootNameD? {Γ : Ctx} {s : Srt} : Tm C Γ s → Option Name
  | .app0 o => o.rootNameD?
  | _ => none

/-- A hash term whose verdicts the goal's premise settles: of a kind other
than `ecrecover`, whose value is `opaque`. -/
def _root_.Solidity.Tm.hashable? {Γ : Ctx} {s : Srt} : Tm C Γ s → Option HashKind
  | .app2 o _ _ =>
    match o.hashKind? with
    | some .ecrecover => none
    | k => k
  | _ => none

/-- Two hash terms of one kind: their equation is their inputs' under the
goal's premise. -/
def _root_.Solidity.Tm.hashPair {Γ : Ctx} {s s' : Srt} (x : Tm C Γ s) (y : Tm C Γ s') : Bool :=
  match x.hashable?, y.hashable? with
  | some k, some k' => k == k'
  | _, _ => false

/-- **A term of the fragment**: every operator admitted.  A hash term is
admitted only where the goal's premise settles it (`hashOK`): an operand
of `==`/`!=` against a hash of its kind, or a key of a mapping at a root
(whose other keys must then be hashes too, `Fml.inTarget`).  Anywhere
else its verdicts may turn on a preimage, and the closer may leave them. -/
def _root_.Solidity.Tm.inTarget {Γ : Ctx} (w : Waivers) (hashOK : Bool) : {s : Srt} → Tm C Γ s → Bool
  | _, .netOf _ a => a.inTarget w false
  | _, .app1 _ x => x.inTarget w false
  | _, .app2 o x y =>
    let eqH := o.isEqNe && x.hashPair y
    let keyH := o.isMapAt && x.rootNameD?.isSome && y.hashable?.isSome
    x.inTarget w eqH && y.inTarget w (eqH || keyH) &&
      (if o.isHash then hashOK else o.admits w x.isLitV y.isLitV y.litValue?)
  | _, .app3 o x y z => x.inTarget w false && y.inTarget w false && z.inTarget w false &&
      o.admits w x.isLitV y.isLitV z.isLitV
  | _, _ => true

def _root_.Solidity.Rhs.inTarget {Γ : Ctx} (w : Waivers) {t : LTy} : Rhs C Γ t → Bool
  | .val a | .zint a => a.inTarget w false
  | .path q => q.inTarget w false
  | .mref i => i.inTarget w false
  | .store s => s.inTarget w false
  | .unset | .saveNet | .saveNetMt => true

def _root_.Solidity.UpdElem.inTarget {Γ Δ : Ctx} (w : Waivers) : UpdElem C Γ Δ → Bool
  | .local _ r => r.inTarget w
  | .storage s => s.inTarget w false
  | .memory m => m.inTarget w false
  | .selfBalance _ a | .setBalance a => a.inTarget w false
  | .net r _ a | .pay r a | .netMt r a => r.inTarget w false && a.inTarget w false

def _root_.Solidity.Upd.inTarget {Γ : Ctx} (w : Waivers) : {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, .nil => true
  | _, .snoc U e => U.inTarget w && e.inTarget w
  | _, .decl U _ r => U.inTarget w && r.inTarget w
  | _, .pop U _ | _, .drop U _ => U.inTarget w

/-! ### Reads and the array property fragment -/

/-- The symbols that read contents: storage, memory, a hash, the ledger. -/
def _root_.Solidity.Op2.isRead {a b s : Srt} : Op2 C a b s → Bool
  | .find | .len | .read | .mlen | .sfind | .copyMem | .iread | .findIn | .sfindIn | .hash _ => true
  | _ => false

/-- The symbols that write. -/
def _root_.Solidity.Op2.isWrite {a b s : Srt} : Op2 C a b s → Bool
  | .delAt | .pushSlot | .pop | .shrink | .extend | .copySt _ | .delAtIn | .copy _ => true
  | _ => false

def _root_.Solidity.Op1.isWrite {a s : Srt} : Op1 C a s → Bool
  | .alloc .. | .addM .. => true
  | _ => false

/-- The symbols that index: the second operand is the index. -/
def _root_.Solidity.Op2.isIndex {a b s : Srt} : Op2 C a b s → Bool
  | .at _ | .mat _ => true
  | _ => false

/-- A bound variable, by its level. -/
def _root_.Solidity.Tm.isBound {Γ : Ctx} (qs : List Nat) {s : Srt} : Tm C Γ s → Bool
  | .pvV i | .pvZ i => qs.contains i.level
  | _ => false

/-- The term mentions a bound variable. -/
def _root_.Solidity.Tm.mentions {Γ : Ctx} (qs : List Nat) : {s : Srt} → Tm C Γ s → Bool
  | _, .pvV i | _, .pvZ i => qs.contains i.level
  | _, .netOf _ a | _, .app1 _ a => a.mentions qs
  | _, .app2 _ x y => x.mentions qs || y.mentions qs
  | _, .app3 _ x y z => x.mentions qs || y.mentions qs || z.mentions qs
  | _, _ => false

/-- The term reads contents at a bound variable. -/
def _root_.Solidity.Tm.readsAt {Γ : Ctx} (qs : List Nat) : {s : Srt} → Tm C Γ s → Bool
  | _, .netOf _ a => a.mentions qs || a.readsAt qs
  | _, .app1 o x => (match o with | .net | .wt | .cleanTail => x.mentions qs | _ => false) ||
      x.readsAt qs
  | _, .app2 o x y => (o.isRead && (x.mentions qs || y.mentions qs)) || x.readsAt qs || y.readsAt qs
  | _, .app3 _ x y z => x.readsAt qs || y.readsAt qs || z.readsAt qs
  | _, _ => false

/-- The term reads contents at all. -/
def _root_.Solidity.Tm.readsAny {Γ : Ctx} : {s : Srt} → Tm C Γ s → Bool
  | _, .netOf _ _ => true
  | _, .app1 o x => (match o with | .net | .wt | .cleanTail => true | _ => false) || x.readsAny
  | _, .app2 o x y => o.isRead || x.readsAny || y.readsAny
  | _, .app3 _ x y z => x.readsAny || y.readsAny || z.readsAny
  | _, _ => false

/-- **A value term of the array property fragment**: a bound variable
occurs only as an index (`a[i]`, `m[k]`, a memory element, a ledger
entry), never under arithmetic, never in a nested index (`a[a[i]]`), and
nothing is written at a path that mentions it. -/
def _root_.Solidity.Tm.apfV {Γ : Ctx} (qs : List Nat) : {s : Srt} → Tm C Γ s → Bool
  | _, .pvV i | _, .pvZ i => !qs.contains i.level
  | _, .netOf _ a => a.isBound qs || !a.mentions qs
  | _, .app1 o x =>
    match o with
    | .net => x.isBound qs || !x.mentions qs
    | o => if o.isWrite then !x.mentions qs else x.apfV qs
  | _, .app2 o x y =>
    if o.isIndex then x.apfV qs && (y.isBound qs || !y.mentions qs)
    else if o.isWrite then !(x.mentions qs || y.mentions qs)
    else x.apfV qs && y.apfV qs
  | _, .app3 o x y z =>
    match o with
    | .atIn _ => !x.mentions qs && y.apfV qs && (z.isBound qs || !z.mentions qs)
    | .ite => x.apfV qs && y.apfV qs && z.apfV qs
    | .modular _ => x.apfV qs && y.apfV qs && z.apfV qs
    | _ => !(x.mentions qs || y.mentions qs || z.mentions qs)
  | _, _ => true

/-- An index term (Bradley, Manna and Sipma): a bound variable, or a term
mentioning none. -/
def _root_.Solidity.Tm.indexTerm {Γ : Ctx} (qs : List Nat) {s : Srt} (t : Tm C Γ s) : Bool :=
  t.isBound qs || !t.mentions qs

/-- A guard comparison: `<`, `>`, `<=`, `>=`, `==`, never `!=`. -/
def _root_.Solidity.Op2.isGuardCmp {a b s : Srt} : Op2 C a b s → Bool
  | .binop .lt _ | .binop .gt _ | .binop .le _ | .binop .ge _ | .binop .eqB _ => true
  | .zcmp .lt _ | .zcmp .gt _ | .zcmp .le _ | .zcmp .ge _ | .zcmp .eqB _ => true
  | _ => false

def _root_.Solidity.Op2.isAndOr {a b s : Srt} : Op2 C a b s → Bool
  | .binop .and _ | .binop .or _ => true
  | _ => false

/-- **An index-guard term**: `&&`/`||` of comparisons of index terms, or a
term mentioning no bound variable. -/
def _root_.Solidity.Tm.apfG {Γ : Ctx} (qs : List Nat) : {s : Srt} → Tm C Γ s → Bool
  | _, .app2 o x y =>
    if o.isAndOr then x.apfG qs && y.apfG qs
    else if o.isGuardCmp then x.indexTerm qs && y.indexTerm qs
    else !(x.mentions qs || y.mentions qs)
  | _, t => !t.mentions qs

/-- The literal `true`. -/
def _root_.Solidity.Tm.isTrueLit {Γ : Ctx} {p : PrimTy} : Tm C Γ (.val p) → Bool
  | .app0 o => match o with | .lit (p := .bool) v => v | _ => false
  | _ => false

/-- A quantifier-free formula not mentioning a bound variable. -/
def _root_.Solidity.Fml.groundQF {Γ : Ctx} (qs : List Nat) : Fml C Γ → Bool
  | .tt => true
  | .eq a b => !(a.mentions qs || b.mentions qs)
  | .wellFormed s => !s.mentions qs
  | .not φ => φ.groundQF qs
  | .and φ ψ | .imp φ ψ => φ.groundQF qs && ψ.groundQF qs
  | _ => false

/-- **An index guard**: conjunctions of guard atoms, an atom an equation of
guard terms (a Boolean one against `true`), or ground. -/
def _root_.Solidity.Fml.apfGuard {Γ : Ctx} (qs : List Nat) : Fml C Γ → Bool
  | .tt => true
  | .and φ ψ => φ.apfGuard qs && ψ.apfGuard qs
  | φ@(@Fml.eq _ _ p a b) =>
    φ.groundQF qs ||
      (match p with
        | .bool => (a.apfG qs && b.isTrueLit) || (a.isTrueLit && b.apfG qs)
        | _ => a.indexTerm qs && b.indexTerm qs)
  | φ => φ.groundQF qs

/-- A quantifier-free value formula over `Tm.apfV` terms. -/
def _root_.Solidity.Fml.apfValue {Γ : Ctx} (qs : List Nat) : Fml C Γ → Bool
  | .tt => true
  | .eq a b => a.apfV qs && b.apfV qs
  | .wellFormed s => s.apfV qs
  | .not φ => φ.apfValue qs
  | .and φ ψ | .imp φ ψ => φ.apfValue qs && ψ.apfValue qs
  | _ => false

/-- **The body of a universal block**: `guard → value`, conjunctions of
them. -/
def _root_.Solidity.Fml.apfBody {Γ : Ctx} (qs : List Nat) : Fml C Γ → Bool
  | .imp G V => (G.apfGuard qs && V.apfBody qs) || (Fml.imp G V).apfValue qs
  | .and φ ψ => φ.apfBody qs && ψ.apfBody qs
  | φ => φ.apfValue qs

/-- The formula reads contents at a bound variable; an update or a program
counts as one (conservative). -/
def _root_.Solidity.Fml.readsAt (qs : List Nat) : {Γ : Ctx} → Fml C Γ → Bool
  | _, .tt => false
  | _, .eq a b => a.readsAt qs || b.readsAt qs
  | _, .wellFormed s => s.mentions qs || s.readsAt qs
  | _, .not φ | _, .havoc φ | _, .anon _ φ | _, .grow φ | _, .all _ _ φ | _, .bind _ _ _ φ
  | _, .allocAll _ _ φ => φ.readsAt qs
  | _, .and φ ψ | _, .imp φ ψ => φ.readsAt qs || ψ.readsAt qs
  | _, .upd .. | _, .modal .. => true

/-- The formula reads contents at all. -/
def _root_.Solidity.Fml.readsAny : {Γ : Ctx} → Fml C Γ → Bool
  | _, .tt => false
  | _, .eq a b => a.readsAny || b.readsAny
  | _, .wellFormed _ => true
  | _, .not φ | _, .havoc φ | _, .anon _ φ | _, .grow φ | _, .all _ _ φ | _, .bind _ _ _ φ
  | _, .allocAll _ _ φ => φ.readsAny
  | _, .and φ ψ | _, .imp φ ψ => φ.readsAny || ψ.readsAny
  | _, .upd .. | _, .modal .. => true

/-- The quantifier-free formulas whose terms are in the fragment. -/
def _root_.Solidity.Fml.qfTarget {Γ : Ctx} (w : Waivers) : Fml C Γ → Bool
  | .tt => true
  | .eq a b => a.inTarget w (a.hashPair b) && b.inTarget w (a.hashPair b)
  | .wellFormed s => s.inTarget w false
  | .not φ => φ.qfTarget w
  | .and φ ψ | .imp φ ψ => φ.qfTarget w && ψ.qfTarget w
  | _ => false

/-- **A universal block of the array property fragment**, the levels of its
variables collected. -/
def _root_.Solidity.Fml.apfBlock (w : Waivers) : {Γ : Ctx} → List Nat → Fml C Γ → Bool
  | Γ, qs, .all _ _ φ => φ.apfBlock w (Γ.length :: qs)
  | _, qs, φ => φ.apfBody qs && φ.qfTarget w

/-- **The fragment, at a polarity** (`pol`: positive, the formula's own
`∀` a `∃` of its negation; `pres`: under a negative-position quantifier,
past which only Presburger quantifiers, reading nothing at their variable,
keep the negation in `∃*∀*`). -/
def _root_.Solidity.Fml.target (w : Waivers) : {Γ : Ctx} → Bool → Bool → Fml C Γ → Bool
  | _, _, _, .tt => true
  | _, _, _, .eq a b => a.inTarget w (a.hashPair b) && b.inTarget w (a.hashPair b)
  | _, _, _, .wellFormed s => s.inTarget w false
  | _, pol, n, .not φ => φ.target w (!pol) n
  | _, pol, n, .and φ ψ => φ.target w pol n && ψ.target w pol n
  | _, pol, n, .imp φ ψ => φ.target w (!pol) n && ψ.target w pol n
  | _, pol, n, .upd _ U φ => U.inTarget w && φ.target w pol n
  | _, _, _, .modal .. => false
  | Γ, pol, n, .all _ _ φ =>
    if !φ.readsAt [Γ.length] then φ.target w pol (n || !pol)
    else if n then false
    else if pol then φ.target w pol n
    else φ.apfBlock w [Γ.length]
  | Γ, pol, n, .bind _ _ t φ =>
    match t with
    | .val _ | .kint =>
      if !φ.readsAt [Γ.length] then φ.target w pol (n || !pol)
      else if n then false
      else if pol then φ.target w pol n
      else φ.apfBlock w [Γ.length]
    | _ => if pol && !n then φ.target w pol n else !φ.readsAny && φ.target w pol true
  | _, pol, n, .havoc φ | _, pol, n, .anon _ φ | _, pol, n, .grow φ | _, pol, n, .allocAll _ _ φ =>
    if pol && !n then φ.target w pol n else !φ.readsAny && φ.target w pol true

/-! ### Hashes as mapping keys

A mapping keyed by hashes (`mapping(string => V)`) compares its keys: two
hash keys compare as their inputs under the premise, a hash key and any
other key as a preimage question.  So a root with a hash key must have hash
keys only. -/

/-- The keys at the mappings at roots: the root and the key's hash kind,
where the premise settles it. -/
def _root_.Solidity.Tm.mapKeys {Γ : Ctx} : {s : Srt} → Tm C Γ s → List (Name × Option HashKind)
  | _, .netOf _ a | _, .app1 _ a => a.mapKeys
  | _, .app2 o x y =>
    (if o.isMapAt then (match x.rootNameD? with
      | some r => [(r, y.hashable?)]
      | none => [])
    else []) ++ x.mapKeys ++ y.mapKeys
  | _, .app3 _ x y z => x.mapKeys ++ y.mapKeys ++ z.mapKeys
  | _, _ => []

def _root_.Solidity.Rhs.mapKeys {Γ : Ctx} {t : LTy} : Rhs C Γ t → List (Name × Option HashKind)
  | .val a | .zint a => a.mapKeys
  | .path q => q.mapKeys
  | .mref i => i.mapKeys
  | .store s => s.mapKeys
  | .unset | .saveNet | .saveNetMt => []

def _root_.Solidity.UpdElem.mapKeys {Γ Δ : Ctx} : UpdElem C Γ Δ → List (Name × Option HashKind)
  | .local _ r => r.mapKeys
  | .storage s | .memory s => s.mapKeys
  | .selfBalance _ a | .setBalance a => a.mapKeys
  | .net r _ a | .pay r a | .netMt r a => r.mapKeys ++ a.mapKeys

def _root_.Solidity.Upd.mapKeys {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → List (Name × Option HashKind)
  | _, .nil => []
  | _, .snoc U e => U.mapKeys ++ e.mapKeys
  | _, .decl U _ r => U.mapKeys ++ r.mapKeys
  | _, .pop U _ | _, .drop U _ => U.mapKeys

def _root_.Solidity.Fml.mapKeys : {Γ : Ctx} → Fml C Γ → List (Name × Option HashKind)
  | _, .tt | _, .modal .. => []
  | _, .eq a b => a.mapKeys ++ b.mapKeys
  | _, .wellFormed s => s.mapKeys
  | _, .not φ | _, .havoc φ | _, .all _ _ φ | _, .bind _ _ _ φ | _, .anon _ φ | _, .allocAll _ _ φ
  | _, .grow φ => φ.mapKeys
  | _, .and φ ψ | _, .imp φ ψ => φ.mapKeys ++ ψ.mapKeys
  | _, .upd _ U φ => U.mapKeys ++ φ.mapKeys

/-- A root with a hash key has hash keys of that kind only. -/
def keysAgree (ks : List (Name × Option HashKind)) : Bool :=
  ks.all fun (r, h) => ks.all fun (r', h') => r' != r || h == h'

/-- **The fragment the user named**, on a scoped leaf: no program, every
operator admitted (`Waivers`), every quantifier over contents in the array
property fragment, every hash where the goal's premise settles it. -/
def _root_.Solidity.Fml.inTarget (w : Waivers) (φ : Fml C []) : Bool :=
  φ.target w true false && keysAgree φ.mapKeys

/-- **The open theorem**: on the fragment, `decideGoal` answers; its
verdicts are read under the goal's hash premise (`decideGoal_sound`,
`decideGoal_refutes`). -/
def DecisionTheorem (w : Waivers := {}) : Prop :=
  ∀ (C : Contract) (φ : Fml C []), φ.inTarget w = true → decideGoal φ ≠ .unknown

/-- info: 'Solidity.Decide.decideLeaf_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decideLeaf_sound

/-- info: 'Solidity.Decide.decideLeaf_refutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decideLeaf_refutes

/-- info: 'Solidity.Decide.decideLeaf_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decideLeaf_complete

/-- info: 'Solidity.Decide.decideGoal_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decideGoal_sound

/-- info: 'Solidity.Decide.decideGoal_refutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decideGoal_refutes

/-- info: 'Solidity.Decide.decideGoal_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decideGoal_complete

end Solidity.Decide
