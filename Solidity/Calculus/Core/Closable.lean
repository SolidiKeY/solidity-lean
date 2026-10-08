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
kernel compares in one step) before its base, and `Fml.bindsB` collects a
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

/-- `Var.memB`'s compiled twin. -/
def _root_.Solidity.Var.memBM (x : Var) : List Var → Bool
  | [] => false
  | y :: ys => x.eqB y || Var.memBM x ys

/-- `x ∈ ns`, by `Var.eqB`: by the recursor, which the kernel unfolds with no
`brecOn`, as it asks it at every binder of a leaf. -/
@[implemented_by Var.memBM]
def _root_.Solidity.Var.memB (x : Var) (ns : List Var) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => x.eqB y || ih) ns

theorem _root_.Solidity.Var.memB_eq_memBM (x : Var) (ns : List Var) : x.memB ns = x.memBM ns := by
  induction ns with
  | nil => rfl
  | cons y ys ih => exact congrArg (x.eqB y || ·) ih

theorem _root_.Solidity.Var.eqB_eq {x y : Var} (h : x.eqB y = true) : x = y := by
  cases x <;> cases y <;>
    simp_all only [Var.eqB, Bool.and_eq_true, Nat.beq_eq, decide_eq_true_eq, reduceCtorEq]

theorem _root_.Solidity.Var.not_mem_of_memB {x : Var} :
    {ns : List Var} → x.memB ns = false → x ∉ ns
  | [], _ => List.not_mem_nil
  | y :: ys, h => by
    change (x.eqB y || x.memB ys) = false at h
    simp only [Bool.or_eq_false_iff] at h
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

/-- `Fml.bindsB`'s compiled twin. -/
def Fml.bindsBM : {Γ : Ctx} → List Var → Fml C Γ → Option (List Var)
  | _, _, .tt | _, _, .eq .. | _, _, .defined _ => some []
  | _, ns, .not φ => bif φ.foFreshB ns then some [] else none
  | _, ns, .and φ ψ => (φ.bindsBM ns).bind fun B₁ => (ψ.bindsBM ns).map (B₁ ++ ·)
  | _, ns, .imp a φ => bif a.foFreshB ns then φ.bindsBM ns else none
  | _, ns, .upd _ U φ =>
    bif U.freshB ns then (φ.bindsBM (U.names ns)).bind fun B =>
      bif meetsB B (Solidity.Upd.vars (U.erase ns)) || meetsB B (U.names ns) then none
      else some B
    else none
  | _, _, .modal .. => none
  | _, ns, .havoc φ | _, ns, .anon _ φ => φ.bindsBM ns
  | _, ns, .all x _ φ =>
    bif x.memB ns then none
    else (φ.bindsBM (x :: ns)).bind fun B => bif x.memB B then none else some B
  | _, ns, .bind _ x _ φ =>
    bif x.memB ns then none
    else (φ.bindsBM (x :: ns)).bind fun B => bif x.memB B then none else some (x :: B)

/-- `Fml.Closable`, decided: `some` of the names the hidden binders bind
(`Fml.bindNames`) when the leaf is closable, collected from the leaf up, so
that an update or a `∀` tests only the binders below it. -/
@[implemented_by Fml.bindsBM]
def Fml.bindsB {Γ : Ctx} (ns : List Var) (φ : Fml C Γ) : Option (List Var) :=
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
def Fml.closableB {Γ : Ctx} (ns : List Var) (φ : Fml C Γ) : Bool := (φ.bindsB ns).isSome

theorem Fml.bindsB_sound {Γ : Ctx} (φ : Fml C Γ) : ∀ {ns B : List Var},
    φ.bindsB ns = some B → φ.Closable ns ∧ B = φ.bindNames := by
  induction φ with
  | tt | eq | defined => intro _ _ h; cases h; exact ⟨trivial, rfl⟩
  | not φ _ =>
    intro ns B h
    cases hp : φ.foFreshB ns
    · simp only [Fml.bindsB, hp, cond_false, reduceCtorEq] at h
    · simp only [Fml.bindsB, hp, cond_true, Option.some.injEq] at h
      exact ⟨Fml.foFreshB_sound φ hp, h.symm⟩
  | and φ ψ ihφ ihψ =>
    intro ns B h
    obtain ⟨B₁, h₁, h⟩ := Option.bind_eq_some_iff.1 (h : (φ.bindsB ns).bind
      (fun B₁ => (ψ.bindsB ns).map (B₁ ++ ·)) = some B)
    obtain ⟨B₂, h₂, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨c₁, rfl⟩ := ihφ h₁
    obtain ⟨c₂, rfl⟩ := ihψ h₂
    exact ⟨⟨c₁, c₂⟩, rfl⟩
  | imp a φ _ ih =>
    intro ns B h
    cases hp : a.foFreshB ns
    · simp only [Fml.bindsB, hp, cond_false, reduceCtorEq] at h
    · have h' : φ.bindsB ns = some B := by simpa only [Fml.bindsB, hp, cond_true] using h
      obtain ⟨c, rfl⟩ := ih h'
      exact ⟨⟨Fml.foFreshB_sound a hp, c⟩, rfl⟩
  | upd m U φ ih =>
    intro ns B h
    cases hU : U.freshB ns
    · simp only [Fml.bindsB, hU, cond_false, reduceCtorEq] at h
    · have h' : (φ.bindsB (U.names ns)).bind (fun B =>
          bif meetsB B (Solidity.Upd.vars (U.erase ns)) || meetsB B (U.names ns) then none
          else some B) = some B := by simpa only [Fml.bindsB, hU, cond_true] using h
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
    · have h' : (φ.bindsB (x :: ns)).bind (fun B => bif x.memB B then none else some B) =
          some B := by simpa only [Fml.bindsB, hx, cond_false] using h
      obtain ⟨B', h₁, h₂⟩ := Option.bind_eq_some_iff.1 h'
      cases hB : x.memB B'
      · simp only [hB, cond_false, Option.some.injEq] at h₂
        subst h₂
        obtain ⟨c, rfl⟩ := ih h₁
        exact ⟨⟨Var.not_mem_of_memB hx, Var.not_mem_of_memB hB, c⟩, rfl⟩
      · simp only [hB, cond_true, reduceCtorEq] at h₂
    · simp only [Fml.bindsB, hx, cond_true, reduceCtorEq] at h
  | bind m x t φ ih =>
    intro ns B h
    cases hx : x.memB ns
    · have h' : (φ.bindsB (x :: ns)).bind (fun B => bif x.memB B then none else some (x :: B)) =
          some B := by simpa only [Fml.bindsB, hx, cond_false] using h
      obtain ⟨B', h₁, h₂⟩ := Option.bind_eq_some_iff.1 h'
      cases hB : x.memB B'
      · simp only [hB, cond_false, Option.some.injEq] at h₂
        subst h₂
        obtain ⟨c, rfl⟩ := ih h₁
        exact ⟨⟨Var.not_mem_of_memB hx, Var.not_mem_of_memB hB, c⟩, rfl⟩
      · simp only [hB, cond_true, reduceCtorEq] at h₂
    · simp only [Fml.bindsB, hx, cond_true, reduceCtorEq] at h

theorem Fml.closableB_sound {Γ : Ctx} (φ : Fml C Γ) {ns : List Var}
    (h : φ.closableB ns = true) : φ.Closable ns := by
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 h
  exact (Fml.bindsB_sound φ hB).1

/-! ## The leaf in one pass

`sol_prove`'s walk asks two things of every leaf (`Seq.leafRes`,
`Calculus/Core/ProvesDerive.lean`): `Fml.closableB`, and its erasure
(`Fml.erase`), which it hands to today's residue.  `Fml.closeErase` computes
both in one pass, `Fml.closableB`'s binder names beside the erasure
(`Fml.closeErase_eq`), so the kernel walks the leaf's context once.  The
erasure is written by the recursors (Gate G0, conditions 1 and 2: `Fml.erase`,
`Upd.erase`, `Tm.erase` and `Idx.name` match on indexed families), each with
the original as its compiled twin, and an update's `Avoids` test reads the
variables of its terms in place (`Tm.anyE`) instead of collecting them. -/

/-- `Idx.name`, by the recursor: the head of the names after as many tails as
the position. -/
@[implemented_by Idx.name]
def Idx.nameR {Γ : Ctx} {t : LTy} (ns : List Var) (i : Idx Γ t) : Var :=
  Idx.rec (motive := fun _ _ _ => List Var → Var) (fun ns => ns.headD (.user "_"))
    (fun _ ih ns => ih ns.tail) i ns

theorem Idx.nameR_eq {Γ : Ctx} {t : LTy} (ns : List Var) (i : Idx Γ t) :
    i.nameR ns = i.name ns := by
  induction i generalizing ns with
  | here => cases ns <;> rfl
  | there i ih =>
    cases ns with
    | nil => exact (ih []).trans (by simp only [Idx.name, List.getD_nil])
    | cons n ns => exact (ih ns).trans (by simp only [Idx.name, Idx.toNat, List.getD_cons_succ])

/-- `Tm.erase`, by the recursor. -/
@[implemented_by Tm.erase]
def Tm.eraseR {Γ : Ctx} (ns : List Var) {s : Srt} (t : Tm C Γ s) : Solidity.Tm C s :=
  Tm.rec (motive := fun s _ => Solidity.Tm C s)
    (fun i => .pvV (i.nameR ns)) (fun i => .pvP (i.nameR ns)) (fun i => .pvS (i.nameR ns))
    (fun i => .pvI (i.nameR ns)) (fun i _ ih => .app1 (.netOf (i.nameR ns)) ih)
    (fun o => .app0 o) (fun o _ _ ih => .app1 o ih) (fun o _ _ ih ih' => .app2 o ih ih')
    (fun o _ _ _ ih ih' ih'' => .app3 o ih ih' ih'') t

theorem Tm.eraseR_eq {Γ : Ctx} (ns : List Var) {s : Srt} (t : Tm C Γ s) :
    t.eraseR ns = t.erase ns := by
  induction t with
  | pvV i | pvP i | pvS i | pvI i => simp only [Tm.erase, ← Idx.nameR_eq]; rfl
  | netOf i a ih => simp only [Tm.erase, ← Idx.nameR_eq, ← ih]; rfl
  | app0 o => rfl
  | app1 o _ x ih => simp only [Tm.erase, ← ih]; rfl
  | app2 o x y ihx ihy => simp only [Tm.erase, ← ihx, ← ihy]; rfl
  | app3 o x y z ihx ihy ihz => simp only [Tm.erase, ← ihx, ← ihy, ← ihz]; rfl

/-- `Rhs.erase`, its terms by `Tm.eraseR`. -/
def Rhs.eraseR {Γ : Ctx} (ns : List Var) (x : Var) {t : LTy} (r : Rhs C Γ t) :
    Solidity.UpdElem C :=
  Rhs.casesOn (motive := fun _ _ => Solidity.UpdElem C) r
    (fun t => .val x (t.eraseR ns)) (fun p => .path x (p.eraseR ns)) (.unset x)
    (fun i => .mref x (i.eraseR ns)) (fun s => .store x (s.eraseR ns)) (.saveNet x) (.saveNetMt x)

theorem Rhs.eraseR_eq {Γ : Ctx} (ns : List Var) (x : Var) {t : LTy} (r : Rhs C Γ t) :
    r.eraseR ns x = r.erase ns x := by
  cases r <;> simp only [Rhs.erase, ← Tm.eraseR_eq] <;> rfl

/-- `UpdElem.erase`, its terms by `Tm.eraseR`. -/
def UpdElem.eraseR {Γ Δ : Ctx} (ns ms : List Var) (e : UpdElem C Γ Δ) : Solidity.UpdElem C :=
  UpdElem.casesOn (motive := fun _ => Solidity.UpdElem C) e
    (fun i r => r.eraseR ns (i.nameR ms)) (fun s => .storage (s.eraseR ns))
    (fun m => .memory (m.eraseR ns)) (fun op a => .selfBalance op (a.eraseR ns))
    (fun r op a => .net (r.eraseR ns) op (a.eraseR ns))
    (fun r a => .pay (r.eraseR ns) (a.eraseR ns))
    (fun r a => .netMt (r.eraseR ns) (a.eraseR ns)) (fun a => .setBalance (a.eraseR ns))

theorem UpdElem.eraseR_eq {Γ Δ : Ctx} (ns ms : List Var) (e : UpdElem C Γ Δ) :
    e.eraseR ns ms = e.erase ns ms := by
  cases e with
  | «local» i r => exact (Rhs.eraseR_eq ns _ r).trans (by rw [Idx.nameR_eq]; rfl)
  | _ => simp only [UpdElem.erase, ← Tm.eraseR_eq] <;> rfl

/-- `Thin.names`, by the recursor. -/
@[implemented_by Thin.names]
def Thin.namesR {Γ Δ : Ctx} (h : Thin Γ Δ) : List Var → List Var :=
  Thin.rec (motive := fun _ _ _ => List Var → List Var) (fun ns => ns)
    (fun _ ih ns => List.casesOn (motive := fun _ => List Var) ns (ih []) (fun n ns => n :: ih ns))
    (fun _ ih ns => ih ns.tail) h

theorem Thin.namesR_eq {Γ Δ : Ctx} (h : Thin Γ Δ) (ns : List Var) :
    h.namesR ns = h.names ns := by
  induction h generalizing ns with
  | refl => rfl
  | keep h ih =>
    cases ns with
    | nil => exact (ih []).trans (by simp only [Thin.names])
    | cons n ns => exact (congrArg (n :: ·) (ih ns)).trans (by simp only [Thin.names])
  | drop h ih => exact (ih ns.tail).trans (by simp only [Thin.names])

/-- `Upd.erase` and `Upd.names` together, by the recursor. -/
def Upd.eraseNRM {Γ : Ctx} (ns : List Var) {Δ : Ctx} (U : Upd C Γ Δ) :
    Solidity.Upd C × List Var := (U.erase ns, U.names ns)

@[implemented_by Upd.eraseNRM]
def Upd.eraseNR {Γ : Ctx} (ns : List Var) {Δ : Ctx} (U : Upd C Γ Δ) :
    Solidity.Upd C × List Var :=
  Upd.rec (motive := fun _ _ => Solidity.Upd C × List Var) ([], ns)
    (fun _ e ih => (ih.1 ++ [e.eraseR ns ih.2], ih.2))
    (fun _ x r ih => (ih.1 ++ [r.eraseR ns x], x :: ih.2))
    (fun _ h ih => (ih.1, ih.2.drop h.depth)) (fun _ h ih => (ih.1, h.namesR ih.2)) U

theorem Upd.eraseNR_eq {Γ : Ctx} (ns : List Var) {Δ : Ctx} (U : Upd C Γ Δ) :
    U.eraseNR ns = (U.erase ns, U.names ns) := by
  induction U with
  | nil => rfl
  | snoc U e ih =>
    change ((U.eraseNR ns).1 ++ [e.eraseR ns (U.eraseNR ns).2], (U.eraseNR ns).2) = _
    rw [ih, UpdElem.eraseR_eq]; rfl
  | decl U x r ih =>
    change ((U.eraseNR ns).1 ++ [r.eraseR ns x], x :: (U.eraseNR ns).2) = _
    rw [ih, Rhs.eraseR_eq]; rfl
  | pop U h ih => change ((U.eraseNR ns).1, (U.eraseNR ns).2.drop h.depth) = _; rw [ih]; rfl
  | drop U h ih =>
    change ((U.eraseNR ns).1, h.namesR (U.eraseNR ns).2) = _; rw [ih, Thin.namesR_eq]; rfl

/-- `Fml.erase`, by the recursor (a modality's program by `Prog.erase`). -/
@[implemented_by Fml.erase]
def Fml.eraseR {Γ : Ctx} (ns : List Var) (φ : Fml C Γ) : Solidity.Fml C :=
  Fml.rec (motive := fun _ _ => List Var → Solidity.Fml C)
    (tt := fun _ => .tt) (eq := fun a b ns => .eq (a.eraseR ns) (b.eraseR ns))
    (defined := fun t ns => .defined (t.eraseR ns))
    (not := fun _ ih ns => .not (ih ns))
    (and := fun _ _ ih ih' ns => .and (ih ns) (ih' ns))
    (imp := fun _ _ ih ih' ns => .imp (ih ns) (ih' ns))
    (upd := fun m U _ ih ns => match U.eraseNR ns with
      | (U', ms) => match U' with
        | [] => ih ms
        | U' => .upd m U' (ih ms))
    (modal := fun m P κ _ ih ns =>
      .modal m (P.erase ns ++ κ.erase (P.outNames ns)) (ih (κ.outNames (P.outNames ns))))
    (havoc := fun _ ih ns => .havoc (ih ns))
    (all := fun x p _ ih ns => .all x p (ih (x :: ns)))
    (bind := fun _ x _ _ ih ns => ih (x :: ns))
    (anon := fun xs _ ih ns => .anon (xs.map fun x => x.2.nameR ns) (ih ns)) φ ns

theorem Fml.eraseR_eq {Γ : Ctx} (φ : Fml C Γ) : ∀ ns : List Var, φ.eraseR ns = φ.erase ns := by
  induction φ with
  | tt => intro _; rfl
  | eq a b => intro ns; simp only [Fml.erase, ← Tm.eraseR_eq]; rfl
  | defined t => intro ns; simp only [Fml.erase, ← Tm.eraseR_eq]; rfl
  | not φ ih => intro ns; simp only [Fml.erase, ← ih]; rfl
  | and φ ψ ih ih' | imp φ ψ ih ih' => intro ns; simp only [Fml.erase, ← ih, ← ih']; rfl
  | upd m U φ ih =>
    intro ns
    change (match U.eraseNR ns with
      | (U', ms) => match U' with
        | [] => φ.eraseR ms
        | U' => .upd m U' (φ.eraseR ms)) = _
    rw [Upd.eraseNR_eq]
    simp only [ih, Fml.erase]
    generalize U.erase ns = U'
    cases U' <;> rfl
  | modal m P κ φ ih => intro ns; simp only [Fml.erase, ← ih]; rfl
  | havoc φ ih => intro ns; simp only [Fml.erase, ← ih]; rfl
  | all x p φ ih => intro ns; simp only [Fml.erase, ← ih]; rfl
  | bind m x t φ ih => intro ns; simp only [Fml.erase, ← ih]; rfl
  | anon xs φ ih =>
    intro ns
    simp only [Fml.erase, ← ih, ← Idx.nameR_eq]; rfl

/-- `Tm.anyE`'s compiled twin. -/
def Tm.anyEM {Γ : Ctx} (ns : List Var) (p : Var → Bool) {s : Srt} (t : Tm C Γ s) : Bool :=
  (t.erase ns).vars.any p

/-- Whether `p` holds of a variable the erased term reads, read off the
scoped term. -/
@[implemented_by Tm.anyEM]
def Tm.anyE {Γ : Ctx} (ns : List Var) (p : Var → Bool) {s : Srt} (t : Tm C Γ s) : Bool :=
  Tm.rec (motive := fun _ _ => Bool)
    (fun i => p (i.nameR ns)) (fun i => p (i.nameR ns)) (fun i => p (i.nameR ns))
    (fun i => p (i.nameR ns)) (fun i _ ih => p (i.nameR ns) || ih)
    (fun _ => false) (fun _ _ _ ih => ih) (fun _ _ _ ih ih' => ih || ih')
    (fun _ _ _ _ ih ih' ih'' => ih || ih' || ih'') t

theorem Tm.anyE_eq {Γ : Ctx} (ns : List Var) (p : Var → Bool) {s : Srt} (t : Tm C Γ s) :
    t.anyE ns p = (t.erase ns).vars.any p := by
  induction t with
  | pvV i | pvP i | pvS i | pvI i =>
    simp only [Tm.erase, Solidity.Tm.vars, ← Idx.nameR_eq, List.any_cons, List.any_nil,
      Bool.or_false]; rfl
  | netOf i a ih =>
    simp only [Tm.erase, Solidity.Tm.vars, ← Idx.nameR_eq, List.any_cons, ← ih]; rfl
  | app0 o => simp only [Tm.erase, Solidity.Tm.vars, List.any_nil]; rfl
  | app1 o ho x ih =>
    have hv : (Solidity.Tm.app1 o (x.erase ns)).vars = (x.erase ns).vars := by
      cases o <;> first | (simp only [Op1.named, reduceCtorEq] at ho; done) | simp only [Solidity.Tm.vars]
    simp only [Tm.erase, hv, ← ih]; rfl
  | app2 o x y ihx ihy =>
    simp only [Tm.erase, Solidity.Tm.vars, List.any_append, ← ihx, ← ihy]; rfl
  | app3 o x y z ihx ihy ihz =>
    simp only [Tm.erase, Solidity.Tm.vars, List.any_append, ← ihx, ← ihy, ← ihz]; rfl

/-- `Tm.anyE` of the element `x := r`. -/
def Rhs.anyE {Γ : Ctx} (ns : List Var) (p : Var → Bool) (x : Var) {t : LTy} (r : Rhs C Γ t) :
    Bool :=
  Rhs.casesOn (motive := fun _ _ => Bool) r
    (fun t => p x || t.anyE ns p) (fun q => p x || q.anyE ns p) (p x)
    (fun i => p x || i.anyE ns p) (fun s => p x || s.anyE ns p) (p x) (p x)

theorem Rhs.anyE_eq {Γ : Ctx} (ns : List Var) (p : Var → Bool) (x : Var) {t : LTy}
    (r : Rhs C Γ t) : r.anyE ns p x = (r.erase ns x).vars.any p := by
  cases r <;> simp only [Rhs.erase, Solidity.UpdElem.vars, List.any_cons, List.any_nil,
    Bool.or_false, ← Tm.anyE_eq] <;> rfl

/-- `Tm.anyE` of an element. -/
def UpdElem.anyE {Γ Δ : Ctx} (ns ms : List Var) (p : Var → Bool) (e : UpdElem C Γ Δ) : Bool :=
  UpdElem.casesOn (motive := fun _ => Bool) e
    (fun i r => r.anyE ns p (i.nameR ms)) (fun s => s.anyE ns p)
    (fun m => m.anyE ns p) (fun _ a => a.anyE ns p)
    (fun r _ a => r.anyE ns p || a.anyE ns p) (fun r a => r.anyE ns p || a.anyE ns p)
    (fun r a => r.anyE ns p || a.anyE ns p) (fun a => a.anyE ns p)

theorem UpdElem.anyE_eq {Γ Δ : Ctx} (ns ms : List Var) (p : Var → Bool) (e : UpdElem C Γ Δ) :
    e.anyE ns ms p = (e.erase ns ms).vars.any p := by
  cases e with
  | «local» i r => exact (Rhs.anyE_eq ns p _ r).trans (by rw [Idx.nameR_eq]; rfl)
  | _ => simp only [UpdElem.erase, Solidity.UpdElem.vars, List.any_append, ← Tm.anyE_eq] <;> rfl

theorem _root_.Solidity.Upd.vars_append_single (U : Solidity.Upd C) (e : Solidity.UpdElem C) :
    Solidity.Upd.vars (U ++ [e]) = Solidity.Upd.vars U ++ e.vars := by
  induction U with
  | nil => simp only [List.nil_append, Solidity.Upd.vars, List.append_nil]
  | cons e' U ih => simp only [List.cons_append, Solidity.Upd.vars, ih, List.append_assoc]

theorem _root_.Solidity.Var.eqB_refl (x : Var) : x.eqB x = true := by
  cases x <;> simp only [Var.eqB, Nat.beq_refl, decide_true, Bool.and_self]

theorem _root_.Solidity.Var.memB_iff {x : Var} : {ns : List Var} → (x.memB ns = true ↔ x ∈ ns)
  | [] => by simp only [List.not_mem_nil, iff_false]; exact Bool.false_ne_true
  | y :: ys => by
    change (x.eqB y || x.memB ys) = true ↔ _
    rw [Bool.or_eq_true, Var.memB_iff, List.mem_cons]
    constructor
    · rintro (h | h)
      · exact .inl (Var.eqB_eq h)
      · exact .inr h
    · rintro (rfl | h)
      · exact .inl (Var.eqB_refl x)
      · exact .inr h

theorem meetsB_eq_any (B vs : List Var) : meetsB B vs = vs.any fun v => v.memB B := by
  apply Bool.eq_iff_iff.2
  simp only [meetsB, List.any_eq_true, Var.memB_iff]
  exact ⟨fun ⟨y, hy, hv⟩ => ⟨y, hv, hy⟩, fun ⟨v, hv, hy⟩ => ⟨v, hy, hv⟩⟩

/-- What a leaf's update gives `Fml.closeErase`: its erasure, the names of
the scope it leaves, and whether one of the names `B` is a variable of the
erasure (`meetsB B (Upd.vars …)`). -/
structure UpdE (C : Contract) where
  upd : Solidity.Upd C
  names : List Var
  hit : List Var → Bool

/-- `Upd.closeErase`'s compiled twin. -/
def Upd.closeEraseM {Γ : Ctx} (ns : List Var) {Δ : Ctx} (U : Upd C Γ Δ) : Option (UpdE C) :=
  bif U.freshB ns then
    some ⟨U.erase ns, U.names ns, fun B => (Solidity.Upd.vars (U.erase ns)).any (·.memB B)⟩
  else none

/-- `Upd.freshB`, and the update's erasure, names and variables, in one
pass (`Upd.closeErase_eq`). -/
@[implemented_by Upd.closeEraseM]
def Upd.closeErase {Γ : Ctx} (ns : List Var) {Δ : Ctx} (U : Upd C Γ Δ) : Option (UpdE C) :=
  Upd.rec (motive := fun _ _ => Option (UpdE C)) (some ⟨[], ns, fun _ => false⟩)
    (fun _ e ih => ih.map fun r => ⟨r.upd ++ [e.eraseR ns r.names], r.names,
      fun B => r.hit B || e.anyE ns r.names (·.memB B)⟩)
    (fun _ x rh ih => ih.bind fun r => bif x.memB r.names then none
      else some ⟨r.upd ++ [rh.eraseR ns x], x :: r.names,
        fun B => r.hit B || rh.anyE ns (·.memB B) x⟩)
    (fun _ h ih => ih.map fun r => ⟨r.upd, r.names.drop h.depth, r.hit⟩)
    (fun _ h ih => ih.map fun r => ⟨r.upd, h.namesR r.names, r.hit⟩) U

theorem Upd.closeErase_eq {Γ : Ctx} (ns : List Var) {Δ : Ctx} (U : Upd C Γ Δ) :
    U.closeErase ns = U.closeEraseM ns := by
  induction U with
  | nil => rfl
  | snoc U e ih =>
    change (U.closeErase ns).map (fun r => (⟨r.upd ++ [e.eraseR ns r.names], r.names,
      fun B => r.hit B || e.anyE ns r.names (·.memB B)⟩ : UpdE C)) = _
    rw [ih]
    unfold Upd.closeEraseM
    change _ = bif U.freshB ns then _ else _
    cases U.freshB ns
    · rfl
    · simp only [cond_true, Option.map_some, UpdElem.eraseR_eq, UpdElem.anyE_eq,
        Upd.erase, Upd.names, Solidity.Upd.vars_append_single, List.any_append]
  | decl U x r ih =>
    change (U.closeErase ns).bind (fun q => bif x.memB q.names then none
      else some (⟨q.upd ++ [r.eraseR ns x], x :: q.names,
        fun B => q.hit B || r.anyE ns (·.memB B) x⟩ : UpdE C)) = _
    rw [ih]
    unfold Upd.closeEraseM
    change _ = bif (U.freshB ns && !x.memB (U.names ns)) then _ else _
    cases U.freshB ns
    · rfl
    · simp only [cond_true, Option.bind_some]
      cases hm : x.memB (U.names ns)
      · simp only [cond_false, cond_true, Bool.and_self, Bool.not_false, Rhs.eraseR_eq, Rhs.anyE_eq,
          Upd.erase, Upd.names, Solidity.Upd.vars_append_single, List.any_append]
      · simp only [cond_true, Bool.not_true, Bool.and_false, cond_false]
  | pop U h ih =>
    change (U.closeErase ns).map (fun r => (⟨r.upd, r.names.drop h.depth, r.hit⟩ : UpdE C)) = _
    rw [ih]
    unfold Upd.closeEraseM
    change _ = bif U.freshB ns then _ else _
    cases U.freshB ns <;> rfl
  | drop U h ih =>
    change (U.closeErase ns).map (fun r => (⟨r.upd, h.namesR r.names, r.hit⟩ : UpdE C)) = _
    rw [ih]
    unfold Upd.closeEraseM
    change _ = bif U.freshB ns then _ else _
    cases U.freshB ns
    · rfl
    · simp only [cond_true, Option.map_some, Thin.namesR_eq]; rfl

/-- `Fml.closeErase`'s compiled twin. -/
def Fml.closeEraseM {Γ : Ctx} (ns : List Var) (φ : Fml C Γ) : Option (List Var × Solidity.Fml C) :=
  (φ.bindsB ns).map fun B => (B, φ.erase ns)

/-- **A leaf, decided and erased**: `Fml.bindsB` and `Fml.erase` in one pass
(`Fml.closeErase_eq`). -/
@[implemented_by Fml.closeEraseM]
def Fml.closeErase {Γ : Ctx} (ns : List Var) (φ : Fml C Γ) : Option (List Var × Solidity.Fml C) :=
  Fml.rec (motive := fun _ _ => List Var → Option (List Var × Solidity.Fml C))
    (tt := fun _ => some ([], .tt))
    (eq := fun a b ns => some ([], .eq (a.eraseR ns) (b.eraseR ns)))
    (defined := fun t ns => some ([], .defined (t.eraseR ns)))
    (not := fun φ _ ns => bif φ.foFreshB ns then some ([], .not (φ.eraseR ns)) else none)
    (and := fun _ _ ihφ ihψ ns => (ihφ ns).bind fun r₁ => (ihψ ns).map fun r₂ =>
      (r₁.1 ++ r₂.1, .and r₁.2 r₂.2))
    (imp := fun a _ _ ih ns =>
      bif a.foFreshB ns then (ih ns).map fun r => (r.1, .imp (a.eraseR ns) r.2) else none)
    (upd := fun m U _ ih ns => (U.closeErase ns).bind fun u => (ih u.names).bind fun r =>
      match r.1 with
      | [] => some ([], match u.upd with
        | [] => r.2
        | U' => .upd m U' r.2)
      | B => bif u.hit B || meetsB B u.names then none
        else some (B, match u.upd with
          | [] => r.2
          | U' => .upd m U' r.2))
    (modal := fun _ _ _ _ _ _ => none)
    (havoc := fun _ ih ns => (ih ns).map fun r => (r.1, .havoc r.2))
    (all := fun x p _ ih ns =>
      bif x.memB ns then none
      else (ih (x :: ns)).bind fun r => bif x.memB r.1 then none else some (r.1, .all x p r.2))
    (bind := fun _ x _ _ ih ns =>
      bif x.memB ns then none
      else (ih (x :: ns)).bind fun r => bif x.memB r.1 then none else some (x :: r.1, r.2))
    (anon := fun xs _ ih ns =>
      (ih ns).map fun r => (r.1, .anon (xs.map fun x => x.2.nameR ns) r.2)) φ ns

theorem Fml.closeErase_eq {Γ : Ctx} (φ : Fml C Γ) :
    ∀ ns : List Var, φ.closeErase ns = φ.closeEraseM ns := by
  unfold Fml.closeEraseM
  induction φ with
  | tt => intro _; rfl
  | eq a b =>
    intro ns
    change some ([], Solidity.Fml.eq (a.eraseR ns) (b.eraseR ns)) = _
    rw [Tm.eraseR_eq, Tm.eraseR_eq]; rfl
  | defined t =>
    intro ns
    change some ([], Solidity.Fml.defined (t.eraseR ns)) = _
    rw [Tm.eraseR_eq]; rfl
  | not φ _ =>
    intro ns
    change (bif φ.foFreshB ns then some ([], Solidity.Fml.not (φ.eraseR ns)) else none) =
      (bif φ.foFreshB ns then some [] else none).map _
    rw [Fml.eraseR_eq]
    cases φ.foFreshB ns <;> rfl
  | and φ ψ ihφ ihψ =>
    intro ns
    change ((φ.closeErase ns).bind fun r₁ => (ψ.closeErase ns).map fun r₂ =>
      (r₁.1 ++ r₂.1, Solidity.Fml.and r₁.2 r₂.2)) =
      ((φ.bindsB ns).bind fun B₁ => (ψ.bindsB ns).map (B₁ ++ ·)).map _
    rw [ihφ, ihψ]
    cases φ.bindsB ns <;> cases ψ.bindsB ns <;> rfl
  | imp a φ _ ih =>
    intro ns
    change (bif a.foFreshB ns then (φ.closeErase ns).map
        (fun r => (r.1, Solidity.Fml.imp (a.eraseR ns) r.2)) else none) =
      (bif a.foFreshB ns then φ.bindsB ns else none).map _
    rw [ih, Fml.eraseR_eq]
    cases a.foFreshB ns
    · rfl
    · cases φ.bindsB ns <;> rfl
  | upd m U φ ih =>
    intro ns
    change ((U.closeErase ns).bind fun u => (φ.closeErase u.names).bind fun r =>
      match r.1 with
      | [] => some ([], match u.upd with
        | [] => r.2
        | U' => .upd m U' r.2)
      | B => bif u.hit B || meetsB B u.names then none
        else some (B, match u.upd with
          | [] => r.2
          | U' => .upd m U' r.2)) =
      (bif U.freshB ns then (φ.bindsB (U.names ns)).bind (fun B =>
        bif meetsB B (Solidity.Upd.vars (U.erase ns)) || meetsB B (U.names ns) then none
        else some B) else none).map _
    rw [Upd.closeErase_eq]
    unfold Upd.closeEraseM
    cases U.freshB ns
    · rfl
    · simp only [cond_true, Option.bind_some]
      rw [ih]
      cases φ.bindsB (U.names ns) with
      | none => rfl
      | some B =>
        simp only [Option.map_some, Option.bind_some, ← meetsB_eq_any]
        cases B with
        | nil =>
          simp only [Fml.erase]
          generalize U.erase ns = U'
          cases U' <;> rfl
        | cons y ys =>
          dsimp only
          cases meetsB (y :: ys) (Solidity.Upd.vars (U.erase ns)) ||
              meetsB (y :: ys) (U.names ns)
          · simp only [cond_false, Option.map_some, Fml.erase]
            generalize U.erase ns = U'
            cases U' <;> rfl
          · rfl
  | modal => intro _; rfl
  | havoc φ ih =>
    intro ns
    change (φ.closeErase ns).map (fun r => (r.1, Solidity.Fml.havoc r.2)) = (φ.bindsB ns).map _
    rw [ih]
    cases φ.bindsB ns <;> rfl
  | all x p φ ih =>
    intro ns
    change (bif x.memB ns then none else (φ.closeErase (x :: ns)).bind fun r =>
        bif x.memB r.1 then none else some (r.1, Solidity.Fml.all x p r.2)) =
      (bif x.memB ns then none else (φ.bindsB (x :: ns)).bind fun B =>
        bif x.memB B then none else some B).map _
    rw [ih]
    cases x.memB ns
    · cases φ.bindsB (x :: ns) with
      | none => rfl
      | some B => simp only [cond_false, Option.map_some, Option.bind_some]; cases x.memB B <;> rfl
    · rfl
  | bind m x t φ ih =>
    intro ns
    change (bif x.memB ns then none else (φ.closeErase (x :: ns)).bind fun r =>
        bif x.memB r.1 then none else some (x :: r.1, r.2)) =
      (bif x.memB ns then none else (φ.bindsB (x :: ns)).bind fun B =>
        bif x.memB B then none else some (x :: B)).map _
    rw [ih]
    cases x.memB ns
    · cases φ.bindsB (x :: ns) with
      | none => rfl
      | some B => simp only [cond_false, Option.map_some, Option.bind_some]; cases x.memB B <;> rfl
    · rfl
  | anon xs φ ih =>
    intro ns
    change (φ.closeErase ns).map
        (fun r => (r.1, Solidity.Fml.anon (xs.map fun x => x.2.nameR ns) r.2)) =
      (φ.bindsB ns).map _
    rw [ih]
    simp only [Idx.nameR_eq]
    cases φ.bindsB ns <;> rfl

end Solidity.Core
