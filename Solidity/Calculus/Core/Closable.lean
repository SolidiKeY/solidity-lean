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
(`Fml.closableB`), which the kernel decides at every closed leaf: it, and
the Bool functions it calls here, are written by the recursor with a
compiled twin (Gate G0, condition 2).
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
`decide`) at every leaf of `sol_prove`'s walk: written by the recursor, which
the kernel unfolds with no `brecOn`, each with a compiled twin by `match`
(`implemented_by`) for the walk the tactic runs (Gate G0, condition 2), as
`Calculus/Core/Close.lean`'s `Fml.posB`.  A name is looked up by
`Var.memB`, which compares a fresh variable's index (a `Nat`, which the
kernel compares in one step) before its base, and `Fml.binds` collects a
leaf's hidden binders once, from the leaf up, so each update and binder
asks only of the binders below it, most often none. -/

instance {vs ns : List Var} : Decidable (Avoids vs ns) :=
  inferInstanceAs (Decidable (∀ x ∈ vs, x ∉ ns))

/-- Equality of names, a fresh variable's index first. -/
def _root_.Solidity.Var.eqB (x y : Var) : Bool :=
  match x, y with
  | .fresh b k, .fresh b' k' => Nat.beq k k' && decide (b = b')
  | .user s, .user t => decide (s = t)
  | _, _ => false

/-- `x ∈ ns`, by `Var.eqB`. -/
def _root_.Solidity.Var.memB (x : Var) : List Var → Bool
  | [] => false
  | y :: ys => x.eqB y || Var.memB x ys

theorem _root_.Solidity.Var.eqB_eq {x y : Var} (h : x.eqB y = true) : x = y := by
  cases x <;> cases y <;>
    simp_all only [Var.eqB, Bool.and_eq_true, Nat.beq_eq, decide_eq_true_eq, reduceCtorEq]

theorem _root_.Solidity.Var.not_mem_of_memB {x : Var} :
    {ns : List Var} → x.memB ns = false → x ∉ ns
  | [], _ => List.not_mem_nil
  | y :: ys, h => by
    simp only [Var.memB, Bool.or_eq_false_iff] at h
    intro hm
    rcases List.mem_cons.1 hm with rfl | hm
    · cases hx : x.eqB x
      · cases x <;> simp only [Var.eqB, Nat.beq_refl, decide_true, Bool.and_self,
          reduceCtorEq] at hx
      · rw [hx] at h; cases h.1
    · exact Var.not_mem_of_memB h.2 hm

/-- Whether some name of `B` is in `vs`. -/
def meetsB (B vs : List Var) : Bool := B.any fun y => y.memB vs

theorem avoids_of_meetsB {B vs : List Var} (h : meetsB B vs = false) :
    Avoids vs B ∧ Avoids B vs := by
  simp only [meetsB, List.any_eq_false, Bool.not_eq_true] at h
  exact ⟨fun x hx hB => Var.not_mem_of_memB (h x hB) hx,
    fun x hB hx => Var.not_mem_of_memB (h x hB) hx⟩

/-- `Upd.freshB`'s compiled twin. -/
def Upd.freshBM {Γ : Ctx} (ns : List Var) : {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, .nil => true
  | _, .snoc U _ => U.freshBM ns
  | _, .decl U x _ => U.freshBM ns && !x.memB (U.names ns)
  | _, .pop U _ => U.freshBM ns
  | _, .drop U _ => U.freshBM ns

/-- `Upd.Fresh`, decided. -/
@[implemented_by Upd.freshBM]
def Upd.freshB {Γ : Ctx} (ns : List Var) {Δ : Ctx} (U : Upd C Γ Δ) : Bool :=
  Upd.rec (motive := fun _ _ => Bool) true (fun _ _ ih => ih)
    (fun U x _ ih => ih && !x.memB (U.names ns)) (fun _ _ ih => ih) (fun _ _ ih => ih) U

theorem Upd.freshB_sound {Γ : Ctx} {ns : List Var} {Δ : Ctx} (U : Upd C Γ Δ)
    (h : U.freshB ns = true) : U.Fresh ns := by
  induction U with
  | nil => trivial
  | snoc U _ ih => exact ih h
  | decl U x _ ih =>
    have h' : U.freshB ns = true ∧ x.memB (U.names ns) = false := by
      simpa only [Upd.freshB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] using h
    exact ⟨ih h'.1, Var.not_mem_of_memB h'.2⟩
  | pop U _ ih => exact ih h
  | drop U _ ih => exact ih h

/-- `Fml.foFreshB`'s compiled twin. -/
def Fml.foFreshBM : {Γ : Ctx} → List Var → Fml C Γ → Bool
  | _, _, .tt | _, _, .eq .. | _, _, .defined _ => true
  | _, ns, .not φ => φ.foFreshBM ns
  | _, ns, .and φ ψ | _, ns, .imp φ ψ => φ.foFreshBM ns && ψ.foFreshBM ns
  | _, ns, .all x _ φ => !x.memB ns && φ.foFreshBM (x :: ns)
  | _, _, .upd .. | _, _, .modal .. | _, _, .havoc _ | _, _, .bind .. | _, _, .anon .. => false

/-- A first-order formula whose `∀`s bind fresh names: `Fml.Plain` and
`Fml.FO`, decided. -/
@[implemented_by Fml.foFreshBM]
def Fml.foFreshB {Γ : Ctx} (ns : List Var) (φ : Fml C Γ) : Bool :=
  Fml.rec (motive := fun _ _ => List Var → Bool)
    (tt := fun _ => true) (eq := fun _ _ _ => true) (defined := fun _ _ => true)
    (not := fun _ ih ns => ih ns)
    (and := fun _ _ ihφ ihψ ns => ihφ ns && ihψ ns)
    (imp := fun _ _ iha ihφ ns => iha ns && ihφ ns)
    (upd := fun _ _ _ _ _ => false) (modal := fun _ _ _ _ _ _ => false)
    (havoc := fun _ _ _ => false)
    (all := fun x _ _ ih ns => !x.memB ns && ih (x :: ns))
    (bind := fun _ _ _ _ _ _ => false) (anon := fun _ _ _ _ => false) φ ns

theorem Fml.foFreshB_sound {Γ : Ctx} (φ : Fml C Γ) : ∀ {ns : List Var},
    φ.foFreshB ns = true → φ.Plain ns ∧ φ.FO = true := by
  induction φ with
  | tt | eq | defined => intro _ _; exact ⟨trivial, rfl⟩
  | not φ ih => intro ns h; exact ih h
  | and φ ψ ihφ ihψ =>
    intro ns h
    have h' : φ.foFreshB ns = true ∧ ψ.foFreshB ns = true := Bool.and_eq_true _ _ ▸ h
    exact ⟨⟨(ihφ h'.1).1, (ihψ h'.2).1⟩, Bool.and_eq_true_iff.mpr ⟨(ihφ h'.1).2, (ihψ h'.2).2⟩⟩
  | imp a φ iha ihφ =>
    intro ns h
    have h' : a.foFreshB ns = true ∧ φ.foFreshB ns = true := Bool.and_eq_true _ _ ▸ h
    exact ⟨⟨(iha h'.1).1, (ihφ h'.2).1⟩, Bool.and_eq_true_iff.mpr ⟨(iha h'.1).2, (ihφ h'.2).2⟩⟩
  | upd | modal | havoc | bind | anon => intro _ h; cases h
  | all x p φ ih =>
    intro ns h
    have h' : (!x.memB ns) = true ∧ φ.foFreshB (x :: ns) = true := Bool.and_eq_true _ _ ▸ h
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h'
    exact ⟨⟨Var.not_mem_of_memB h'.1, (ih h'.2).1⟩, (ih h'.2).2⟩

/-- `Fml.binds`'s compiled twin. -/
def Fml.bindsM : {Γ : Ctx} → List Var → Fml C Γ → Option (List Var)
  | _, _, .tt | _, _, .eq .. | _, _, .defined _ => some []
  | _, ns, .not φ => bif φ.foFreshB ns then some [] else none
  | _, ns, .and φ ψ => (φ.bindsM ns).bind fun B₁ => (ψ.bindsM ns).map (B₁ ++ ·)
  | _, ns, .imp a φ => bif a.foFreshB ns then φ.bindsM ns else none
  | _, ns, .upd _ U φ =>
    bif U.freshB ns then (φ.bindsM (U.names ns)).bind fun B =>
      bif meetsB B (Solidity.Upd.vars (U.erase ns)) || meetsB B (U.names ns) then none
      else some B
    else none
  | _, _, .modal .. => none
  | _, ns, .havoc φ | _, ns, .anon _ φ => φ.bindsM ns
  | _, ns, .all x _ φ =>
    bif x.memB ns then none
    else (φ.bindsM (x :: ns)).bind fun B => bif x.memB B then none else some B
  | _, ns, .bind _ x _ φ =>
    bif x.memB ns then none
    else (φ.bindsM (x :: ns)).bind fun B => bif x.memB B then none else some (x :: B)

/-- `Fml.Closable`, decided: `some` of the names the hidden binders bind
(`Fml.bindNames`) when the leaf is closable, collected from the leaf up, so
that an update or a `∀` tests only the binders below it. -/
@[implemented_by Fml.bindsM]
def Fml.binds {Γ : Ctx} (ns : List Var) (φ : Fml C Γ) : Option (List Var) :=
  Fml.rec (motive := fun _ _ => List Var → Option (List Var))
    (tt := fun _ => some []) (eq := fun _ _ _ => some []) (defined := fun _ _ => some [])
    (not := fun φ _ ns => bif φ.foFreshB ns then some [] else none)
    (and := fun _ _ ihφ ihψ ns => (ihφ ns).bind fun B₁ => (ihψ ns).map (B₁ ++ ·))
    (imp := fun a _ _ ih ns => bif a.foFreshB ns then ih ns else none)
    (upd := fun _ U _ ih ns =>
      bif U.freshB ns then (ih (U.names ns)).bind fun B =>
        bif meetsB B (Solidity.Upd.vars (U.erase ns)) || meetsB B (U.names ns) then none
        else some B
      else none)
    (modal := fun _ _ _ _ _ _ => none)
    (havoc := fun _ ih ns => ih ns)
    (all := fun x _ _ ih ns =>
      bif x.memB ns then none
      else (ih (x :: ns)).bind fun B => bif x.memB B then none else some B)
    (bind := fun _ x _ _ ih ns =>
      bif x.memB ns then none
      else (ih (x :: ns)).bind fun B => bif x.memB B then none else some (x :: B))
    (anon := fun _ _ ih ns => ih ns) φ ns

/-- `Fml.Closable`, decided: what `Proves.close` asks of the leaf, its
context in front. -/
def Fml.closableB {Γ : Ctx} (ns : List Var) (φ : Fml C Γ) : Bool := (φ.binds ns).isSome

theorem Fml.binds_sound {Γ : Ctx} (φ : Fml C Γ) : ∀ {ns B : List Var},
    φ.binds ns = some B → φ.Closable ns ∧ B = φ.bindNames := by
  induction φ with
  | tt | eq | defined => intro _ _ h; cases h; exact ⟨trivial, rfl⟩
  | not φ _ =>
    intro ns B h
    cases hp : φ.foFreshB ns
    · simp only [Fml.binds, hp, cond_false, reduceCtorEq] at h
    · simp only [Fml.binds, hp, cond_true, Option.some.injEq] at h
      exact ⟨Fml.foFreshB_sound φ hp, h.symm⟩
  | and φ ψ ihφ ihψ =>
    intro ns B h
    obtain ⟨B₁, h₁, h⟩ := Option.bind_eq_some_iff.1 (h : (φ.binds ns).bind
      (fun B₁ => (ψ.binds ns).map (B₁ ++ ·)) = some B)
    obtain ⟨B₂, h₂, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨c₁, rfl⟩ := ihφ h₁
    obtain ⟨c₂, rfl⟩ := ihψ h₂
    exact ⟨⟨c₁, c₂⟩, rfl⟩
  | imp a φ _ ih =>
    intro ns B h
    cases hp : a.foFreshB ns
    · simp only [Fml.binds, hp, cond_false, reduceCtorEq] at h
    · have h' : φ.binds ns = some B := by simpa only [Fml.binds, hp, cond_true] using h
      obtain ⟨c, rfl⟩ := ih h'
      exact ⟨⟨Fml.foFreshB_sound a hp, c⟩, rfl⟩
  | upd m U φ ih =>
    intro ns B h
    cases hU : U.freshB ns
    · simp only [Fml.binds, hU, cond_false, reduceCtorEq] at h
    · have h' : (φ.binds (U.names ns)).bind (fun B =>
          bif meetsB B (Solidity.Upd.vars (U.erase ns)) || meetsB B (U.names ns) then none
          else some B) = some B := by simpa only [Fml.binds, hU, cond_true] using h
      obtain ⟨B', h₁, h₂⟩ := Option.bind_eq_some_iff.1 h'
      cases hm : (meetsB B' (Solidity.Upd.vars (U.erase ns)) || meetsB B' (U.names ns))
      · simp only [hm, cond_false, Option.some.injEq] at h₂
        subst h₂
        obtain ⟨c, rfl⟩ := ih h₁
        simp only [Bool.or_eq_false_iff] at hm
        exact ⟨⟨Upd.freshB_sound U hU, (avoids_of_meetsB hm.1).1, (avoids_of_meetsB hm.2).2, c⟩,
          rfl⟩
      · simp only [hm, cond_true, reduceCtorEq] at h₂
  | modal => intro _ _ h; cases h
  | havoc φ ih => intro ns B h; exact ih h
  | anon xs φ ih => intro ns B h; exact ih h
  | all x p φ ih =>
    intro ns B h
    cases hx : x.memB ns
    · have h' : (φ.binds (x :: ns)).bind (fun B => bif x.memB B then none else some B) =
          some B := by simpa only [Fml.binds, hx, cond_false] using h
      obtain ⟨B', h₁, h₂⟩ := Option.bind_eq_some_iff.1 h'
      cases hB : x.memB B'
      · simp only [hB, cond_false, Option.some.injEq] at h₂
        subst h₂
        obtain ⟨c, rfl⟩ := ih h₁
        exact ⟨⟨Var.not_mem_of_memB hx, Var.not_mem_of_memB hB, c⟩, rfl⟩
      · simp only [hB, cond_true, reduceCtorEq] at h₂
    · simp only [Fml.binds, hx, cond_true, reduceCtorEq] at h
  | bind m x t φ ih =>
    intro ns B h
    cases hx : x.memB ns
    · have h' : (φ.binds (x :: ns)).bind (fun B => bif x.memB B then none else some (x :: B)) =
          some B := by simpa only [Fml.binds, hx, cond_false] using h
      obtain ⟨B', h₁, h₂⟩ := Option.bind_eq_some_iff.1 h'
      cases hB : x.memB B'
      · simp only [hB, cond_false, Option.some.injEq] at h₂
        subst h₂
        obtain ⟨c, rfl⟩ := ih h₁
        exact ⟨⟨Var.not_mem_of_memB hx, Var.not_mem_of_memB hB, c⟩, rfl⟩
      · simp only [hB, cond_true, reduceCtorEq] at h₂
    · simp only [Fml.binds, hx, cond_true, reduceCtorEq] at h

theorem Fml.closableB_sound {Γ : Ctx} (φ : Fml C Γ) {ns : List Var}
    (h : φ.closableB ns = true) : φ.Closable ns := by
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 h
  exact (Fml.binds_sound φ hB).1

end Solidity.Core
