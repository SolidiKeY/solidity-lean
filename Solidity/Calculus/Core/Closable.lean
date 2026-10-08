import Solidity.Calculus.Core.Fml

/-!
# Formulas read where their erasure is

The syntactic side conditions under which a scoped formula and its erasure
(`Fml.erase`) agree, so that today's closer may decide a goal: every binder
fresh (`Upd.Fresh`, `Frames.Fresh`, `Prog.Fresh`), updates and modalities
boxes (the diamond reads states whose `bool` locals hold `bool`s, which the
erasure does not ask, `Calculus/Core/Logic.lean`).  `Fml.Plain` is the
two-way condition (`Calculus/Core/HoldsErase.lean`'s `holds_erase`);
`Fml.Closable` the one-way one a goal closed by its erasure's validity needs
(`Calculus/Core/CloseErase.lean`): hidden binders and anonymising updates
in positive positions, as a leaf's context puts them, each name a hidden
binder binds left alone by the updates above it (`Fml.bindNames`).
-/

namespace Solidity.Core

variable {C : Contract}

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
over whatever the name held).  Its updates and modalities are boxes: the
diamond reads only from and into states whose `bool` locals hold `bool`s
(`State.BoolOK`), which the erasure does not ask. -/
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
(where `Fml.Closable` allows them). -/
def Fml.bindNames : {Γ : Ctx} → Fml C Γ → List Var
  | _, .and φ ψ => φ.bindNames ++ ψ.bindNames
  | _, .imp _ ψ => ψ.bindNames
  | _, .upd _ _ φ => φ.bindNames
  | _, .havoc φ => φ.bindNames
  | _, .all _ _ φ => φ.bindNames
  | _, .bind x _ φ => x :: φ.bindNames
  | _, .anon _ φ => φ.bindNames
  | _, _ => []

/-- A formula whose erasure's validity gives it: as `Fml.Plain`, but a
hidden binder and an anonymising update allowed in a positive position, out
of a modality, and every name a hidden binder binds out of scope and left
alone by the updates above it. -/
def Fml.Closable : {Γ : Ctx} → List Var → Fml C Γ → Prop
  | _, _, .tt => True
  | _, _, .eq _ _ => True
  | _, _, .defined _ => True
  | _, ns, .not φ => φ.Plain ns
  | _, ns, .and φ ψ => φ.Closable ns ∧ ψ.Closable ns
  | _, ns, .imp φ ψ => φ.Plain ns ∧ ψ.Closable ns
  | _, ns, .upd m U φ =>
    m = .box ∧ U.Fresh ns ∧ Avoids (Solidity.Upd.vars (U.erase ns)) φ.bindNames ∧
      Avoids φ.bindNames (U.names ns) ∧ φ.Closable (U.names ns)
  | _, ns, .modal m P κ φ => (Fml.modal m P κ φ).Plain ns
  | _, ns, .havoc φ => φ.Closable ns
  | _, ns, .all x _ φ => x ∉ ns ∧ x ∉ φ.bindNames ∧ φ.Closable (x :: ns)
  | _, ns, .bind x _ φ => x ∉ ns ∧ x ∉ φ.bindNames ∧ φ.Closable (x :: ns)
  | _, ns, .anon _ φ => φ.Closable ns

/-- A first-order formula: no update, modality or binder but `∀`.  It reads
the same over the typed state as over its erasure (`Calculus/Core/TCloseErase.lean`). -/
def Fml.FO : {Γ : Ctx} → Fml C Γ → Bool
  | _, .tt | _, .eq .. | _, .defined _ => true
  | _, .not φ => φ.FO
  | _, .and φ ψ | _, .imp φ ψ => φ.FO && ψ.FO
  | _, .all _ _ φ => φ.FO
  | _, _ => false

/-- A leaf of the strategy: no modality, and first-order where it is
assumed.  What its erasure gives over M3's states it gives over the typed
ones (`Calculus/Core/TCloseErase.lean`). -/
def Fml.Leaf : {Γ : Ctx} → Fml C Γ → Bool
  | _, .tt | _, .eq .. | _, .defined _ => true
  | _, .not φ => φ.FO
  | _, .and φ ψ => φ.Leaf && ψ.Leaf
  | _, .imp φ ψ => φ.FO && ψ.Leaf
  | _, .upd _ _ φ | _, .havoc φ | _, .all _ _ φ | _, .bind _ _ φ | _, .anon _ φ => φ.Leaf
  | _, .modal .. => false

end Solidity.Core
