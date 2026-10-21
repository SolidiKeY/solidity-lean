import Solidity.Calculus.Step
import Solidity.Calculus.NamedTerm

/-!
# Names to positions in formulas

The elaborator reads a program's names as positions (`NCtx.find`,
`Syntax/Elab.lean`); this module does the same for the notation's updates and formulas, so that a
formula read with names (`dl!{ … }`, a specification's obligation, a
problem) becomes a scoped one, `Fml C Γ`, over a named context
`Γ : NCtx` (`docs/intrinsic.md`, M6b).

* **A term** is read by name (`NTm`, `Calculus/NamedTerm.lean`): the scoped
  term it is where it stands, its locals the newest of their names.
* **An update** assigns a local in scope and declares one that is not: the
  target's type is the reader's (`hint`, what the scope says of the name
  after the update), else the newest local of that name if its kind fits
  the element, else the element's own (`old := s` an `LTy.old`, `oldNet :=
  net` an `LTy.oldNet`, `x := t` a `uint`).  A target of that type in scope
  is assigned (`Upd.snoc`), any other is declared (`Upd.decl`), shadowing a
  local of another type: KeY's update binds a program variable, here a
  position.
* **A modality's program** is elaborated scoped from the formula's context
  (`Calculus/Notation.lean`), and its postcondition read in the context the
  program leaves: a local declared in a branch is out of scope after it.
  An atom is read by `NRead`, its names resolved where it stands.
* **The context's locals are closed over** by `Fml.closeN`: a value local by
  `∀` (`Fml.all`, its type's range), any other by a hidden binder
  (`Fml.bind`, every value), or every one by a hidden binder.

`Post C Γ` is a postcondition at the context `Γ` it stands in: no
weakening is ever needed to put it under a program.
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3 Modality IntOp)

variable {C : Contract}

/-! ## Postconditions -/

/-- Whether a modality occurs in the formula. -/
def Fml.active : {Γ : Ctx} → Fml C Γ → Bool
  | _, φ => Fml.casesOn (motive := fun _ _ => Bool) φ
    (tt := false) (eq := fun _ _ => false) (wellFormed := fun _ => false)
    (not := fun φ => Fml.active φ) (and := fun φ ψ => Fml.active φ || Fml.active ψ)
    (imp := fun φ ψ => Fml.active φ || Fml.active ψ) (upd := fun _ _ φ => Fml.active φ)
    (modal := fun _ _ _ _ => true) (havoc := fun φ => Fml.active φ)
    (all := fun _ _ φ => Fml.active φ) (bind := fun _ _ _ φ => Fml.active φ)
    (anon := fun _ φ => Fml.active φ) (allocAll := fun _ _ φ => Fml.active φ) (grow := fun φ => Fml.active φ)
  termination_by structural _ φ => φ

/-- A postcondition at the context `Γ`: a formula that binds no fresh name
(`se1`, `sp1`, …), so the rules' fresh names avoid it, and has no modality,
so the strategy never steps into it (`Chains.lean`'s `Post`, at the context
of the program's end instead of weakened to it). -/
structure Post (C : Contract) (Γ : Ctx) where
  fml : Fml C Γ
  noFresh : fml.maxIdx = 0 := by decide
  inactive : fml.active = false := by decide

attribute [coe] Post.fml

instance {Γ : Ctx} : Coe (Post C Γ) (Fml C Γ) := ⟨Post.fml⟩

/-! ## Slots

A Lean formula where a formula stands is read as a slot and put back
after (`Calculus/Notation.lean`'s `Fml.slotC`, `Calculus/Chains.lean`'s
`Fml.chainSlot`): a formula no reading writes, `∀ bool ⟪i⟫; true`, its
binder's name the slot's number.  (A root `⟪i⟫` marked it before W9.8.3,
when a root needed no proof that the contract declares it.) -/

/-- The mark of slot `i`. -/
def Fml.slotMark {Γ : Ctx} (i : Nat) : Fml C Γ := .all (.user s!"⟪{i}⟫") .bool .tt

/-- The slot a mark is, if it is one. -/
def Fml.slotMark? {Γ : Ctx} : Fml C Γ → Option Nat
  | .all (.user r) .bool .tt =>
    if r.startsWith "⟪" && r.endsWith "⟫" then ((r.drop 1).dropRight 1).toNat? else none
  | _ => none

section Resolve

variable [FreshNames]

/-! ## Updates -/

/-- The right-hand side an element gives a local of type `t`, read in `Γ`:
its term checked at `t`'s sort. -/
def Rhs.resolveN (Γ : NCtx) : (t : LTy) → NUpdElem C → Except String (Rhs C Γ.ctx t)
  | .val p, .val _ r => do pure (.val (← r.check (.val p) Γ))
  | .kint, .val _ r => do pure (.zint (← r.check .kint Γ))
  | .alias R, .path _ p => do pure (.path (← p.check (.path (.ref R)) Γ))
  | .alias _, .unset _ => pure .unset
  | .mem R, .mref _ i => do pure (.mref (← i.check (.ident R) Γ))
  | .old, .store _ s => do pure (.store (← s.check .st Γ))
  | .oldNet, .saveNet _ => pure .saveNet
  | .oldNet, .saveNetMt _ => pure .saveNetMt
  | t, _ => .error s!"an update sets a local of type {t.toStr} to a term of another kind"

/-- The type of the local `x` the element `e` sets, in the targets `Δ`: the
reader's (`hint`), the newest local of that name if it fits, or the
element's own: what its right-hand side synthesizes in `Γ` (a value's type,
an alias's or a memory local's reference type), a storage's `old`, a
ledger's `oldNet`. -/
def elemTy (hint : Var → Option LTy) (Γ Δ : NCtx) (x : Var) (e : NUpdElem C) :
    Except String LTy :=
  match hint x with
  | some t => if e.fits t then pure t else fallback
  | none => fallback
where
  fallback : Except String LTy :=
    match Δ.findAny x with
    | .ok ⟨t, _⟩ => if e.fits t then pure t else own
    | .error _ => own
  own : Except String LTy :=
    match e with
    | .val _ t => do
      match ← t.resolveV Γ with
      | ⟨.prim p, _⟩ => pure (.val p)
      | ⟨.kint, _⟩ => pure .kint
    | .path _ p => do
      match ← p.resolve Γ with
      | ⟨.path (.ref R), _⟩ => pure (.alias R)
      | ⟨σ, _⟩ => useError p.text σ "a storage alias's path"
    | .mref _ i => do
      match ← i.resolve Γ with
      | ⟨.ident R, _⟩ => pure (.mem R)
      | ⟨σ, _⟩ => useError i.text σ "a memory reference"
    | e => match e.ownTy? with
      | some t => pure t
      | none => .error s!"`{x}`: an update binds it, and nothing says its type \
          (declare it: `φ where Person storage {x}`)"

/-- A parallel update read in `Γ`, its elements appended to `U`, which
leaves `Δ`: a local in scope at the element's type is assigned, any other
declared. -/
def Upd.resolveN (hint : Var → Option LTy) (Γ : NCtx) :
    (Δ : NCtx) → Upd C Γ.ctx Δ.ctx → List (NUpdElem C) →
      Except String ((Δ' : NCtx) × Upd C Γ.ctx Δ'.ctx)
  | Δ, U, [] => pure ⟨Δ, U⟩
  | Δ, U, .storage s :: es => do
    Upd.resolveN hint Γ Δ (U.snoc (.storage (← s.check .st Γ))) es
  | Δ, U, .memory m :: es => do
    Upd.resolveN hint Γ Δ (U.snoc (.memory (← m.check .mem Γ))) es
  | Δ, U, .selfBalance op a :: es => do
    Upd.resolveN hint Γ Δ (U.snoc (.selfBalance op (← a.check (.val .uint) Γ))) es
  | Δ, U, .net r op a :: es => do
    Upd.resolveN hint Γ Δ (U.snoc (.net (← r.check (.val .uint) Γ) op (← a.check (.val .uint) Γ))) es
  | Δ, U, .pay r a :: es => do
    Upd.resolveN hint Γ Δ (U.snoc (.pay (← r.check (.val .uint) Γ) (← a.check (.val .uint) Γ))) es
  | Δ, U, .netMt r a :: es => do
    Upd.resolveN hint Γ Δ (U.snoc (.netMt (← r.check (.val .uint) Γ) (← a.check (.val .uint) Γ))) es
  | Δ, U, .setBalance a :: es => do
    Upd.resolveN hint Γ Δ (U.snoc (.setBalance (← a.check (.val .uint) Γ))) es
  | Δ, U, e :: es => do
    let some x := e.setsLocal? | .error "an update element of no kind"
    let t ← elemTy hint Γ Δ x e
    let r ← Rhs.resolveN Γ t e
    match Δ.find x t with
    | .ok ⟨i, _⟩ => Upd.resolveN hint Γ Δ (U.snoc (.local i r)) es
    | .error _ => Upd.resolveN hint Γ ((x, t) :: Δ) (U.decl x r) es

/-! ## Formulas -/

/-- **A formula whose locals are names**, read where it stands: at a named
context `Γ`, its locals as positions there.  What a front end builds before
it knows the context (a specification's clause, `Calculus/SurfaceSpec.lean`;
an atom of `dl!{ … }`, `Calculus/Notation.lean`'s `elabFmlC`): a quantifier
pushes its local, an update the locals it declares (`Upd.resolveN`). -/
def NRead (C : Contract) : Type := (Γ : NCtx) → Except String (Fml C Γ.ctx)

namespace NRead

/-- `true`. -/
def tt : NRead C := fun _ => pure .tt
/-- `false`. -/
def ff : NRead C := fun _ => pure .ff
/-- `a == b = true` on KeY's `int`: its equation, written `a = b`
(`Fml.eqK`). -/
def eqK {Γ : NCtx} (eqv : {p : PrimTy} → Tm C Γ.ctx (.val p) → Tm C Γ.ctx (.val p) → Fml C Γ.ctx)
    (a b : Tm C Γ.ctx .kint) : Fml C Γ.ctx :=
  eqv (.app2 (.zcmp .eqB rfl) a b) (.app0 (.lit (p := .bool) true))
/-- `a = b`, KeY's `=`, at the sides' type (on KeY's `int`, its
comparison `= true`). -/
def eq (a b : NTerm C) : NRead C := fun Γ => do
  match ← NTm.resolvePairV a b Γ with
  | ⟨.prim _, a', b'⟩ => pure (.eq a' b')
  | ⟨.kint, a', b'⟩ => pure (eqK (fun x y => .eq x y) a' b')
/-- `wt(s)`, KeY's `wellFormed(heap)` (`Fml.wellFormed`). -/
def wt (s : NSTerm C) : NRead C := fun Γ => do pure (.wellFormed (← s.check .st Γ))
/-- `¬φ`. -/
def not (φ : NRead C) : NRead C := fun Γ => do pure (.not (← φ Γ))
/-- `φ ∧ ψ`. -/
def and (φ ψ : NRead C) : NRead C := fun Γ => do pure (.and (← φ Γ) (← ψ Γ))
/-- `φ → ψ`. -/
def imp (φ ψ : NRead C) : NRead C := fun Γ => do pure (.imp (← φ Γ) (← ψ Γ))
/-- `∀ p x; φ`: `φ` read with `x` pushed. -/
def all (x : Var) (p : PrimTy) (φ : NRead C) : NRead C := fun Γ => do
  pure (.all x p (← φ ((x, .val p) :: Γ)))
/-- `φ₁ ∧ … ∧ φₙ`, `true` when there are none (`Fml.conj`). -/
def conj (φs : List (NRead C)) : NRead C := fun Γ => do pure (Fml.conj (← φs.mapM (· Γ)))

/-- `t = true`: a condition as a formula. -/
def bool (t : NTerm C) : NRead C := eq t (.bool true)

/-- `a ⊕ b = true`: a comparison as a formula, at the operands' type. -/
def cmp (op : BinOp) (a b : NTerm C) : NRead C := bool (.binop op a b)

end NRead

end Resolve

/-- The locals of `Γ` closed over, the outermost first bound outermost: a
value local by `∀` over its type's range (`Fml.all`) when `useAll`, any
other local, or every local when not `useAll`, by a hidden binder over
every value (`Fml.bind` read as the box reads it: universal). -/
def Fml.closeN (useAll : Bool) : (Γ : NCtx) → Fml C Γ.ctx → Fml C []
  | [], φ => φ
  | (x, .val p) :: Γ, φ =>
    Fml.closeN useAll Γ (if useAll then .all x p φ else .bind .box x (.val p) φ)
  | (x, t) :: Γ, φ => Fml.closeN useAll Γ (.bind .box x t φ)

end Solidity
