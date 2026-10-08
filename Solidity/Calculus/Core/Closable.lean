import Solidity.Calculus.Core.Fml

/-!
# Formulas read where their erasure is

The syntactic side conditions under which a scoped formula and its erasure
(`Fml.erase`) agree, so that today's closer may decide a goal: every binder
fresh (`Upd.Fresh`, `Frames.Fresh`, `Prog.Fresh`).  `Fml.Plain` and
`Fml.FO` together are the two-way condition
(`Calculus/Core/HoldsErase.lean`'s `holds_erase_fo`); `Fml.Closable` the
one-way one a goal closed by its erasure's validity needs
(`Calculus/Core/CloseErase.lean`): updates, hidden binders and anonymising
updates in positive positions, as a leaf's context puts them, an update
under either modality, each name a hidden binder binds left alone by the
updates above it (`Fml.bindNames`).  `Proves.close` asks the Bool twin
(`Fml.closableB`), which the kernel decides at a closed leaf: it, and the
Bool functions it calls here, are written with `casesOn` (Gate G0,
condition 1).
-/

namespace Solidity.Core

variable {C : Contract}

/-! ## Fresh binders -/

/-- Every local an update declares takes a name not in scope. -/
def Upd.Fresh {Γ : Ctx} (ns : List Var) : {Δ : Ctx} → Upd C Γ Δ → Prop
  | _, .nil => True
  | _, .snoc U _ => U.Fresh ns
  | _, .decl U x _ => U.Fresh ns ∧ x ∉ U.names ns
  | _, .pop U _ => U.Fresh ns
  | _, .drop U _ => U.Fresh ns

/-- Every block the frames hold binds fresh names. -/
def Frames.Fresh : {Γ Γ₀ : Ctx} → List Var → Frames C Γ Γ₀ → Prop
  | _, _, _, .nil => True
  | _, _, ns, .seq ω κ => ω.Fresh [] ns ∧ κ.Fresh (ω.outNames ns)
  | _, _, ns, .pop _ h κ => κ.Fresh (ns.drop h.depth)
  | _, _, ns, .drop h κ => κ.Fresh (h.names ns)

/-- A formula whose binders are all fresh, and with no hidden binder nor an
anonymising update: their untyped readings range over more states than the
typed ones (the untyped `anon` over any binding, the erased hidden binder
over whatever the name held).  Its updates and modalities are boxes
(`Calculus/Core/Contracts.lean` reads its erasure's modalities). -/
def Fml.Plain : {Γ : Ctx} → List Var → Fml C Γ → Prop
  | _, _, .tt => True
  | _, _, .eq _ _ => True
  | _, _, .defined _ => True
  | _, ns, .not φ => φ.Plain ns
  | _, ns, .and φ ψ => φ.Plain ns ∧ ψ.Plain ns
  | _, ns, .imp φ ψ => φ.Plain ns ∧ ψ.Plain ns
  | _, ns, .upd m U φ => m = .box ∧ U.Fresh ns ∧ φ.Plain (U.names ns)
  | _, ns, .modal m P κ φ =>
    m = .box ∧ P.Fresh [] ns ∧ κ.Fresh (P.outNames ns) ∧ φ.Plain (κ.outNames (P.outNames ns))
  | _, ns, .havoc φ => φ.Plain ns
  | _, ns, .all x _ φ => x ∉ ns ∧ φ.Plain (x :: ns)
  | _, _, .bind .. => False
  | _, _, .anon .. => False

/-- The names the hidden binders of `φ` bind, in its positive positions
(where `Fml.Closable` allows them).  Written with `casesOn`, as the other
side conditions here (Gate G0, condition 1): `Proves.close` asks it of the
leaf, and the kernel evaluates it there. -/
def Fml.bindNames : {Γ : Ctx} → Fml C Γ → List Var
  | _, φ => Fml.casesOn (motive := fun _ _ => List Var) φ
    (tt := []) (eq := fun _ _ => []) (defined := fun _ => []) (not := fun _ => [])
    (and := fun φ ψ => Fml.bindNames φ ++ Fml.bindNames ψ)
    (imp := fun _ ψ => Fml.bindNames ψ) (upd := fun _ _ φ => Fml.bindNames φ)
    (modal := fun _ _ _ _ => []) (havoc := fun φ => Fml.bindNames φ)
    (all := fun _ _ φ => Fml.bindNames φ) (bind := fun _ x _ φ => x :: Fml.bindNames φ)
    (anon := fun _ φ => Fml.bindNames φ)
  termination_by structural _ φ => φ

/-- A first-order formula: no update, modality or binder but `∀`.  It reads
the same over the typed state as over its erasure
(`Calculus/Core/HoldsErase.lean`'s `holds_erase_fo`). -/
def Fml.FO : {Γ : Ctx} → Fml C Γ → Bool
  | _, φ => Fml.casesOn (motive := fun _ _ => Bool) φ
    (tt := true) (eq := fun _ _ => true) (defined := fun _ => true) (not := fun φ => Fml.FO φ)
    (and := fun φ ψ => Fml.FO φ && Fml.FO ψ) (imp := fun φ ψ => Fml.FO φ && Fml.FO ψ)
    (upd := fun _ _ _ => false) (modal := fun _ _ _ _ => false) (havoc := fun _ => false)
    (all := fun _ _ φ => Fml.FO φ) (bind := fun _ _ _ _ => false) (anon := fun _ _ => false)
  termination_by structural _ φ => φ

/-- A leaf whose erasure's validity gives it: no modality, first-order and
fresh where it is negated or assumed, and a hidden binder, an anonymising
update and an update under either modality in a positive position, every
name a hidden binder binds out of scope and left alone by the updates above
it.  An update's reading asks only of the typed states that erase to the
one it ends in (`holds`), so the erasure's run of it is enough under the
diamond too (`Calculus/Core/CloseErase.lean`'s `holds_of_erase_valid`). -/
def Fml.Closable : {Γ : Ctx} → List Var → Fml C Γ → Prop
  | _, _, .tt => True
  | _, _, .eq _ _ => True
  | _, _, .defined _ => True
  | _, ns, .not φ => φ.Plain ns ∧ φ.FO = true
  | _, ns, .and φ ψ => φ.Closable ns ∧ ψ.Closable ns
  | _, ns, .imp φ ψ => (φ.Plain ns ∧ φ.FO = true) ∧ ψ.Closable ns
  | _, ns, .upd _ U φ =>
    U.Fresh ns ∧ Avoids (Solidity.Upd.vars (U.erase ns)) φ.bindNames ∧
      Avoids φ.bindNames (U.names ns) ∧ φ.Closable (U.names ns)
  | _, _, .modal .. => False
  | _, ns, .havoc φ => φ.Closable ns
  | _, ns, .all x _ φ => x ∉ ns ∧ x ∉ φ.bindNames ∧ φ.Closable (x :: ns)
  | _, ns, .bind _ x _ φ => x ∉ ns ∧ x ∉ φ.bindNames ∧ φ.Closable (x :: ns)
  | _, ns, .anon _ φ => φ.Closable ns

/-! ## Decided

The Bool twins `Proves.close` asks, which the kernel evaluates (`rfl`,
`decide`) at a closed leaf: written with `casesOn`, as `Fml.maxIdx`
(`Calculus/Core/Step.lean`). -/

instance {vs ns : List Var} : Decidable (Avoids vs ns) :=
  inferInstanceAs (Decidable (∀ x ∈ vs, x ∉ ns))

/-- `Upd.Fresh`, decided. -/
def Upd.freshB {Γ : Ctx} (ns : List Var) : {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, U => Upd.casesOn (motive := fun _ _ => Bool) U true (fun U _ => Upd.freshB ns U)
      (fun U x _ => Upd.freshB ns U && decide (x ∉ U.names ns)) (fun U _ => Upd.freshB ns U)
      (fun U _ => Upd.freshB ns U)
  termination_by structural _ U => U

theorem Upd.freshB_sound {Γ : Ctx} {ns : List Var} :
    {Δ : Ctx} → (U : Upd C Γ Δ) → U.freshB ns = true → U.Fresh ns
  | _, .nil, _ => trivial
  | _, .snoc U _, h => Upd.freshB_sound U h
  | _, .decl U x _, h => by
    have h' : U.freshB ns = true ∧ decide (x ∉ U.names ns) = true := Bool.and_eq_true_iff.mp h
    exact ⟨Upd.freshB_sound U h'.1, of_decide_eq_true h'.2⟩
  | _, .pop U _, h => Upd.freshB_sound U h
  | _, .drop U _, h => Upd.freshB_sound U h

/-- A first-order formula whose `∀`s bind fresh names: `Fml.Plain` and
`Fml.FO`, decided. -/
def Fml.foFreshB : {Γ : Ctx} → List Var → Fml C Γ → Bool
  | _, ns, φ => Fml.casesOn (motive := fun _ _ => Bool) φ
    (tt := true) (eq := fun _ _ => true) (defined := fun _ => true)
    (not := fun φ => Fml.foFreshB ns φ)
    (and := fun φ ψ => Fml.foFreshB ns φ && Fml.foFreshB ns ψ)
    (imp := fun φ ψ => Fml.foFreshB ns φ && Fml.foFreshB ns ψ)
    (upd := fun _ _ _ => false) (modal := fun _ _ _ _ => false) (havoc := fun _ => false)
    (all := fun x _ φ => decide (x ∉ ns) && Fml.foFreshB (x :: ns) φ)
    (bind := fun _ _ _ _ => false) (anon := fun _ _ => false)
  termination_by structural _ _ φ => φ

theorem Fml.foFreshB_sound : {Γ : Ctx} → (φ : Fml C Γ) → {ns : List Var} →
    φ.foFreshB ns = true → φ.Plain ns ∧ φ.FO = true
  | _, .tt, _, _ | _, .eq .., _, _ | _, .defined _, _, _ => ⟨trivial, rfl⟩
  | _, .not φ, _, h => Fml.foFreshB_sound φ h
  | _, .and φ ψ, ns, h => by
    have h' : φ.foFreshB ns = true ∧ ψ.foFreshB ns = true := Bool.and_eq_true_iff.mp h
    have a := Fml.foFreshB_sound φ h'.1
    have b := Fml.foFreshB_sound ψ h'.2
    exact ⟨⟨a.1, b.1⟩, Bool.and_eq_true_iff.mpr ⟨a.2, b.2⟩⟩
  | _, .imp φ ψ, ns, h => by
    have h' : φ.foFreshB ns = true ∧ ψ.foFreshB ns = true := Bool.and_eq_true_iff.mp h
    have a := Fml.foFreshB_sound φ h'.1
    have b := Fml.foFreshB_sound ψ h'.2
    exact ⟨⟨a.1, b.1⟩, Bool.and_eq_true_iff.mpr ⟨a.2, b.2⟩⟩
  | _, .all x _ φ, ns, h => by
    have h' : decide (x ∉ ns) = true ∧ φ.foFreshB (x :: ns) = true := Bool.and_eq_true_iff.mp h
    have a := Fml.foFreshB_sound φ h'.2
    exact ⟨⟨of_decide_eq_true h'.1, a.1⟩, a.2⟩
  | _, .upd .., _, h | _, .modal .., _, h | _, .havoc _, _, h | _, .bind .., _, h
  | _, .anon .., _, h => nomatch h

/-- `Fml.Closable`, decided: what `Proves.close` asks of the leaf, its
context in front. -/
def Fml.closableB : {Γ : Ctx} → List Var → Fml C Γ → Bool
  | _, ns, φ => Fml.casesOn (motive := fun _ _ => Bool) φ
    (tt := true) (eq := fun _ _ => true) (defined := fun _ => true)
    (not := fun φ => Fml.foFreshB ns φ)
    (and := fun φ ψ => Fml.closableB ns φ && Fml.closableB ns ψ)
    (imp := fun φ ψ => Fml.foFreshB ns φ && Fml.closableB ns ψ)
    (upd := fun _ U φ => U.freshB ns &&
      decide (Avoids (Solidity.Upd.vars (U.erase ns)) φ.bindNames) &&
      decide (Avoids φ.bindNames (U.names ns)) && Fml.closableB (U.names ns) φ)
    (modal := fun _ _ _ _ => false) (havoc := fun φ => Fml.closableB ns φ)
    (all := fun x _ φ => decide (x ∉ ns) && decide (x ∉ φ.bindNames) && Fml.closableB (x :: ns) φ)
    (bind := fun _ x _ φ => decide (x ∉ ns) && decide (x ∉ φ.bindNames) &&
      Fml.closableB (x :: ns) φ)
    (anon := fun _ φ => Fml.closableB ns φ)
  termination_by structural _ _ φ => φ

theorem Fml.closableB_sound : {Γ : Ctx} → (φ : Fml C Γ) → {ns : List Var} →
    φ.closableB ns = true → φ.Closable ns
  | _, .tt, _, _ | _, .eq .., _, _ | _, .defined _, _, _ => trivial
  | _, .not φ, _, h => Fml.foFreshB_sound φ h
  | _, .and φ ψ, ns, h => by
    have h' : φ.closableB ns = true ∧ ψ.closableB ns = true := Bool.and_eq_true_iff.mp h
    exact ⟨Fml.closableB_sound φ h'.1, Fml.closableB_sound ψ h'.2⟩
  | _, .imp φ ψ, ns, h => by
    have h' : φ.foFreshB ns = true ∧ ψ.closableB ns = true := Bool.and_eq_true_iff.mp h
    exact ⟨Fml.foFreshB_sound φ h'.1, Fml.closableB_sound ψ h'.2⟩
  | _, .upd _ U φ, ns, h => by
    have h' : (U.freshB ns && decide (Avoids (Solidity.Upd.vars (U.erase ns)) φ.bindNames) &&
        decide (Avoids φ.bindNames (U.names ns)) && φ.closableB (U.names ns)) = true := h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
    obtain ⟨⟨⟨hU, h₁⟩, h₂⟩, hφ⟩ := h'
    exact ⟨Upd.freshB_sound U hU, h₁, h₂, Fml.closableB_sound φ hφ⟩
  | _, .modal .., _, h => nomatch h
  | _, .havoc φ, _, h => Fml.closableB_sound φ h
  | _, .all x _ φ, ns, h => by
    have h' : (decide (x ∉ ns) && decide (x ∉ φ.bindNames) && φ.closableB (x :: ns)) = true := h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
    obtain ⟨⟨hx, hxB⟩, hφ⟩ := h'
    exact ⟨hx, hxB, Fml.closableB_sound φ hφ⟩
  | _, .bind _ x _ φ, ns, h => by
    have h' : (decide (x ∉ ns) && decide (x ∉ φ.bindNames) && φ.closableB (x :: ns)) = true := h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
    obtain ⟨⟨hx, hxB⟩, hφ⟩ := h'
    exact ⟨hx, hxB, Fml.closableB_sound φ hφ⟩
  | _, .anon _ φ, _, h => Fml.closableB_sound φ h

end Solidity.Core
