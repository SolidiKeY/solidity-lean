import Solidity.Calculus.Logic

/-!
# The goal under its own hash premise (e3′)

A hash is the real function of its bytes (`Heap.hash`), so a leaf may turn
on a collision no one can exhibit.  The user's reading (2026-10-25, e3′,
`docs/automation.md`, M7): each goal is read under the premise that *its
own* hash terms are free of collisions, distinct inputs giving distinct
outputs.  The premise is part of the goal's reading, not an axiom and not a
global assumption.

`Fml.HashIn k inp out σ φ`: some hash term of `φ`, of kind `k`, outside
`φ`'s binders, evaluated at `σ` (or past `φ`'s updates), reads the bytes
`inp` and returns `out`.  The premise is taken at every scope: `Fml.holdsH`
is `holds` with each binder's body read under the premise of that
instance, so a premise is about finitely many hash evaluations, false only
at an actual collision among them.  `ecrecover` is no hash of the premise:
it is `0` on every invalid signature.  Without a hash the premise is empty
(`Fml.holdsH_iff`).  `Calculus/Decision.lean` decides goals so read.
-/

namespace Solidity.Decide

variable {C : Contract}


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

end Solidity.Decide
