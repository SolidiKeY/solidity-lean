import Solidity.Calculus.Step

/-!
# Names to positions in formulas

`Syntax/Resolve.lean` reads a program's names as positions; this module
does the same for `Update.lean`'s terms, updates and formulas, so that a
formula read with names (`dl!{ … }`, a specification's obligation, a
problem) becomes a scoped one, `Fml C Γ`, over a named context
`Γ : NCtx` (`docs/intrinsic.md`, M6b).

* **A term's local** is the newest local of its name, which must be of the
  kind its sort says: a `pv` at the value sort a `.val`, at the path sort an
  alias, a storage term `old` (`LTy.old`), an identity a memory local, and
  the ledger `x` of `x[a]` (`netOf`) an `LTy.oldNet`.
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
  An atom is read as the closer's formula (`NFml.resolveIn`).
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
    (tt := false) (eq := fun _ _ => false) (defined := fun _ => false)
    (not := fun φ => Fml.active φ) (and := fun φ ψ => Fml.active φ || Fml.active ψ)
    (imp := fun φ ψ => Fml.active φ || Fml.active ψ) (upd := fun _ _ φ => Fml.active φ)
    (modal := fun _ _ _ _ => true) (havoc := fun φ => Fml.active φ)
    (all := fun _ _ φ => Fml.active φ) (bind := fun _ _ _ φ => Fml.active φ)
    (anon := fun _ φ => Fml.active φ)
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

/-! ## Terms -/

section Resolve

variable [FreshNames]

/-- The newest local named `x`, of whatever type. -/
def NCtx.findAny (x : Var) : (Γ : NCtx) → Except String ((t : LTy) × Idx Γ.ctx t)
  | [] => .error s!"unknown name {x}"
  | (y, u) :: Γ =>
    if y = x then .ok ⟨u, .here⟩
    else do
      let ⟨t, i⟩ ← NCtx.findAny x Γ
      pure ⟨t, .there i⟩

/-- `x` read as `what`, where it is a local of type `t`. -/
def kindError {α : Type} (x : Var) (t : LTy) (what : String) : Except String α :=
  .error s!"`{x}` is declared as {t.toStr}, read as {what}"

/-- A term of `Update.lean`, its locals read as positions in `Γ`. -/
def Tm.resolveN (Γ : NCtx) : {s : Srt} → Surface.Tm C s → Except String (Tm C Γ.ctx s)
  | _, .pvV x => do
    let ⟨t, i⟩ ← Γ.findAny x
    match t, i with
    | .val _, i => pure (.pvV i)
    | t, _ => kindError x t "a value"
  | _, .pvP x => do
    let ⟨t, i⟩ ← Γ.findAny x
    match t, i with
    | .alias _, i => pure (.pvP i)
    | t, _ => kindError x t "a storage alias"
  | _, .pvS x => do
    let ⟨t, i⟩ ← Γ.findAny x
    match t, i with
    | .old, i => pure (.pvS i)
    | t, _ => kindError x t "a storage"
  | _, .pvI x => do
    let ⟨t, i⟩ ← Γ.findAny x
    match t, i with
    | .mem _, i => pure (.pvI i)
    | t, _ => kindError x t "a memory reference"
  | _, .app0 o => pure (.app0 o)
  | _, .app1 o a => do
    let a' ← Tm.resolveN Γ a
    match o, a' with
    | .netOf x, a' => do
      let ⟨t, i⟩ ← Γ.findAny x
      match t, i with
      | .oldNet, i => pure (.netOf i a')
      | t, _ => kindError x t "a ledger"
    | o, a' => if h : o.named = false then pure (.app1 o h a') else .error "a named symbol"
  | _, .app2 o a b => do pure (.app2 o (← Tm.resolveN Γ a) (← Tm.resolveN Γ b))
  | _, .app3 o a b c => do
    pure (.app3 o (← Tm.resolveN Γ a) (← Tm.resolveN Γ b) (← Tm.resolveN Γ c))

/-! ## Updates -/

/-- The local an element sets, if it sets one. -/
def _root_.Solidity.Surface.UpdElem.setsLocal? : Surface.UpdElem C → Option Var
  | .val x _ | .path x _ | .unset x | .mref x _ | .store x _ | .saveNet x | .saveNetMt x => some x
  | _ => none

/-- Whether a local of type `t` is what the element sets. -/
def _root_.Solidity.Surface.UpdElem.fits : Surface.UpdElem C → LTy → Bool
  | .val .., .val _ | .path .., .alias _ | .unset _, .alias _ | .mref .., .mem _
  | .store .., .old | .saveNet _, .oldNet | .saveNetMt _, .oldNet => true
  | _, _ => false

/-- The type of the local an element sets, when nothing else says: a
storage's `old`, a ledger's `oldNet`, a value's `uint`. -/
def _root_.Solidity.Surface.UpdElem.ownTy? : Surface.UpdElem C → Option LTy
  | .val .. => some (.val .uint)
  | .store .. => some .old
  | .saveNet _ | .saveNetMt _ => some .oldNet
  | _ => none

/-- The right-hand side an element gives a local of type `t`, read in `Γ`. -/
def Rhs.resolveN (Γ : NCtx) : (t : LTy) → Surface.UpdElem C → Except String (Rhs C Γ.ctx t)
  | .val _, .val _ r => do pure (.val (← Tm.resolveN Γ r))
  | .alias _, .path _ p => do pure (.path (← Tm.resolveN Γ p))
  | .alias _, .unset _ => pure .unset
  | .mem _, .mref _ i => do pure (.mref (← Tm.resolveN Γ i))
  | .old, .store _ s => do pure (.store (← Tm.resolveN Γ s))
  | .oldNet, .saveNet _ => pure .saveNet
  | .oldNet, .saveNetMt _ => pure .saveNetMt
  | t, _ => .error s!"an update sets a local of type {t.toStr} to a term of another kind"

/-- The type of the local `x` the element `e` sets, in the targets `Δ`: the
reader's (`hint`), the newest local of that name if it fits, or the
element's own. -/
def elemTy (hint : Var → Option LTy) (Δ : NCtx) (x : Var) (e : Surface.UpdElem C) :
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
    match e.ownTy? with
    | some t => pure t
    | none => .error s!"`{x}`: an update binds it, and nothing says its type \
        (declare it: `φ where Person storage {x}`)"

/-- A parallel update read in `Γ`, its elements appended to `U`, which
leaves `Δ`: a local in scope at the element's type is assigned, any other
declared. -/
def Upd.resolveN (hint : Var → Option LTy) (Γ : NCtx) :
    (Δ : NCtx) → Upd C Γ.ctx Δ.ctx → List (Surface.UpdElem C) →
      Except String ((Δ' : NCtx) × Upd C Γ.ctx Δ'.ctx)
  | Δ, U, [] => pure ⟨Δ, U⟩
  | Δ, U, .storage s :: es => do
    Upd.resolveN hint Γ Δ (U.snoc (.storage (← Tm.resolveN Γ s))) es
  | Δ, U, .memory m :: es => do
    Upd.resolveN hint Γ Δ (U.snoc (.memory (← Tm.resolveN Γ m))) es
  | Δ, U, .selfBalance op a :: es => do
    Upd.resolveN hint Γ Δ (U.snoc (.selfBalance op (← Tm.resolveN Γ a))) es
  | Δ, U, .net r op a :: es => do
    Upd.resolveN hint Γ Δ (U.snoc (.net (← Tm.resolveN Γ r) op (← Tm.resolveN Γ a))) es
  | Δ, U, .pay r a :: es => do
    Upd.resolveN hint Γ Δ (U.snoc (.pay (← Tm.resolveN Γ r) (← Tm.resolveN Γ a))) es
  | Δ, U, .netMt r a :: es => do
    Upd.resolveN hint Γ Δ (U.snoc (.netMt (← Tm.resolveN Γ r) (← Tm.resolveN Γ a))) es
  | Δ, U, .setBalance a :: es => do
    Upd.resolveN hint Γ Δ (U.snoc (.setBalance (← Tm.resolveN Γ a))) es
  | Δ, U, e :: es => do
    let some x := e.setsLocal? | .error "an update element of no kind"
    let t ← elemTy hint Δ x e
    let r ← Rhs.resolveN Γ t e
    match Δ.find x t with
    | .ok ⟨i, _⟩ => Upd.resolveN hint Γ Δ (U.snoc (.local i r)) es
    | .error _ => Upd.resolveN hint Γ ((x, t) :: Δ) (U.decl x r) es

/-! ## Formulas -/

/-- A formula as written (`Update.lean`'s `Surface.Fml`), its locals read
as positions in `Γ`: a quantifier pushes its local, an update the locals it
declares, a program the ones it leaves (`Prog.resolve`).  `hint` types the
locals an update binds (`elemTy`).  Only `Calculus/Spec.lean`'s
`specObligation` reads it now, which the W8.2 `obligations` lane reads
scoped: it goes when that lane is merged. -/
def Fml.resolveN (hint : Var → Option LTy) : (Γ : NCtx) → Solidity.Surface.Fml C →
    Except String (Fml C Γ.ctx)
  | _, .tt => pure .tt
  | Γ, .eq a b => do pure (.eq (← Tm.resolveN Γ a) (← Tm.resolveN Γ b))
  | Γ, .defined t => do pure (.defined (← Tm.resolveN Γ t))
  | Γ, .not φ => do pure (.not (← Fml.resolveN hint Γ φ))
  | Γ, .and φ ψ => do pure (.and (← Fml.resolveN hint Γ φ) (← Fml.resolveN hint Γ ψ))
  | Γ, .imp φ ψ => do pure (.imp (← Fml.resolveN hint Γ φ) (← Fml.resolveN hint Γ ψ))
  | Γ, .upd m U φ => do
    let ⟨Δ, U'⟩ ← Upd.resolveN hint Γ Γ .nil U
    pure (.upd m U' (← Fml.resolveN hint Δ φ))
  | Γ, .modal m P φ => do
    let ⟨Γ', P'⟩ ← Prog.resolve Γ P (strict := false)
    pure (.modal m P' .nil (← Fml.resolveN hint Γ' φ))
  | Γ, .havoc φ => do pure (.havoc (← Fml.resolveN hint Γ φ))
  | Γ, .all x p φ => do pure (.all x p (← Fml.resolveN hint ((x, .val p) :: Γ) φ))
  | Γ, .anon xs φ => do
    let ys ← xs.mapM (Γ.findAny ·)
    pure (.anon ys (← Fml.resolveN hint Γ φ))

/-- The closer's formula (no modality), its locals read as positions in
`Γ`: a quantifier pushes its local, an update the locals it declares.  What
`dl!{ … }`'s scoped reader makes of an atom (`Calculus/Notation.lean`'s
`elabFmlC`). -/
def NFml.resolveIn (hint : Var → Option LTy) : (Γ : NCtx) → NFml C → Except String (Fml C Γ.ctx)
  | _, .tt => pure .tt
  | Γ, .eq a b => do pure (.eq (← Tm.resolveN Γ a) (← Tm.resolveN Γ b))
  | Γ, .defined t => do pure (.defined (← Tm.resolveN Γ t))
  | Γ, .not φ => do pure (.not (← NFml.resolveIn hint Γ φ))
  | Γ, .and φ ψ => do pure (.and (← NFml.resolveIn hint Γ φ) (← NFml.resolveIn hint Γ ψ))
  | Γ, .imp φ ψ => do pure (.imp (← NFml.resolveIn hint Γ φ) (← NFml.resolveIn hint Γ ψ))
  | Γ, .upd m U φ => do
    let ⟨Δ, U'⟩ ← Upd.resolveN hint Γ Γ .nil U
    pure (.upd m U' (← NFml.resolveIn hint Δ φ))
  | Γ, .havoc φ => do pure (.havoc (← NFml.resolveIn hint Γ φ))
  | Γ, .all x p φ => do pure (.all x p (← NFml.resolveIn hint ((x, .val p) :: Γ) φ))
  | Γ, .anon xs φ => do
    let ys ← xs.mapM (Γ.findAny ·)
    pure (.anon ys (← NFml.resolveIn hint Γ φ))

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
