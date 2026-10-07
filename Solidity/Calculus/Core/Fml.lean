import Solidity.Update
import Solidity.Syntax.Resolve

/-!
# Terms, updates and formulas, scoped

`Update.lean`'s terms, updates and formulas read in a context `Γ : Ctx`
(`docs/intrinsic.md`, M6a), over the scoped programs of `Syntax/Core.lean`.
A program variable is a position (`Tm.pvV i`, `i : Idx Γ (.val p)`), so a
formula cannot read a local that is not in scope.

**Updates** (`Upd C Γ Δ`) are parallel, as KeY's: every right-hand side is
read in `Γ`, the state the update is applied in, and every target is a local
of `Δ`, the context the update leaves.  An element either assigns (`snoc`,
`Δ` unchanged), declares (`decl`, a local pushed: what a declaration with a
simple initializer leaves, `{x := 3}`), or pops (`pop`, the locals of a scope
that ended).  A pop is Lean only and prints as nothing.

**The modality** keeps the program `P` apart from what follows it
(Gate G0, condition 6): `modal m P κ φ` is `⟨ P κ ⟩ φ`, where the frames `κ`
(`Frames`) are the rest of the program `ω` (`seq`) and the scope ends
(`pop`).  A rule rewrites the head of `P` and leaves `κ` as it is, so `ω` is
never re-typed.  A scope end is `pop .block` (a branch, a block: printed `}`,
KeY's block end) or `pop .capture` (the fresh `se`/`sp`/`ie` a rule declared:
invisible, their scope is Lean's only).

**A hidden binder** (`Fml.bind x t φ`) declares the local `x` for every value
of its type, printed as `φ` alone: `T v = e;` drops its initializer
(`localValueDeclInitDrop`) to `v = e;`, which the binder puts in scope, as
solkey's `⟨[ v = e; ]⟩`.

`Premise C Γ Γ'` is what a rule on a statement `Stmt C Γ Γ'` leaves, and
`Premise.fml` puts it in front of the rest `ω` and the frames `κ`.  A split
has two goals, KeY's: a condition cannot be stuck, so there is no third.

`Fml.erase` is the bridge to `Update.lean`'s formulas until the closer is
ported (Decision 6): positions become the names of their binders, frames
the statements they hold.
-/

namespace Solidity.Core

open Solidity (Srt Op0 Op1 Op2 Op3 IntOp Modality)

variable {C : Contract}

/-! ## Terms -/

/-- A unary symbol that names a local (`netOf x`, a ledger variable): the
scoped terms read it through `Tm.netOf` instead. -/
def _root_.Solidity.Op1.named {a s : Srt} : Op1 a s → Bool
  | .netOf _ => true
  | _ => false

/-- A term of sort `s`, read in `Γ`: a local by its position, or a symbol
applied to terms. -/
inductive Tm (C : Contract) (Γ : Ctx) : Srt → Type where
  /-- A stack local. -/
  | pvV {p : PrimTy} (i : Idx Γ (.val p)) : Tm C Γ .val
  /-- A storage alias. -/
  | pvP {R : RefTy} (i : Idx Γ (.alias R)) : Tm C Γ .path
  /-- A storage variable, KeY's `old`. -/
  | pvS (i : Idx Γ .old) : Tm C Γ .st
  /-- A memory local. -/
  | pvI {R : RefTy} (i : Idx Γ (.mem R)) : Tm C Γ .ident
  /-- `x[a]`: what the ledger bound at `x` holds for `a` (`Op1.netOf`). -/
  | netOf (i : Idx Γ .oldNet) (a : Tm C Γ .val) : Tm C Γ .val
  | app0 {s : Srt} (o : Op0 s) : Tm C Γ s
  | app1 {a s : Srt} (o : Op1 a s) (ho : o.named = false) (x : Tm C Γ a) : Tm C Γ s
  | app2 {a b s : Srt} (o : Op2 a b s) (x : Tm C Γ a) (y : Tm C Γ b) : Tm C Γ s
  | app3 {a b c s : Srt} (o : Op3 a b c s) (x : Tm C Γ a) (y : Tm C Γ b) (z : Tm C Γ c) : Tm C Γ s

/-- `Update.lean`'s term, the positions named by `ns` (innermost first). -/
def Tm.erase {Γ : Ctx} (ns : List Var) : {s : Srt} → Tm C Γ s → Solidity.Tm C s
  | _, .pvV i => .pvV (i.name ns)
  | _, .pvP i => .pvP (i.name ns)
  | _, .pvS i => .pvS (i.name ns)
  | _, .pvI i => .pvI (i.name ns)
  | _, .netOf i a => .app1 (.netOf (i.name ns)) (a.erase ns)
  | _, .app0 o => .app0 o
  | _, .app1 o _ x => .app1 o (x.erase ns)
  | _, .app2 o x y => .app2 o (x.erase ns) (y.erase ns)
  | _, .app3 o x y z => .app3 o (x.erase ns) (y.erase ns) (z.erase ns)

/-! ## Updates -/

/-- What a local of type `t` is set to, read in `Γ`. -/
inductive Rhs (C : Contract) (Γ : Ctx) : LTy → Type where
  /-- `v := t` -/
  | val {p : PrimTy} (t : Tm C Γ .val) : Rhs C Γ (.val p)
  /-- `lsv := p` -/
  | path {R : RefTy} (p : Tm C Γ .path) : Rhs C Γ (.alias R)
  /-- `lsv := unset` (Lean only, `storageLocalDeclSkip`). -/
  | unset {R : RefTy} : Rhs C Γ (.alias R)
  /-- `mv := i` -/
  | mref {R : RefTy} (i : Tm C Γ .ident) : Rhs C Γ (.mem R)
  /-- `old := s` -/
  | store (s : Tm C Γ .st) : Rhs C Γ .old
  /-- `oldNet := net` -/
  | saveNet : Rhs C Γ .oldNet
  /-- `oldNet := mtSt` -/
  | saveNetMt : Rhs C Γ .oldNet

/-- One assigning element: its right-hand sides read in `Γ`, its target a
local of `Δ`, or a part of the state. -/
inductive UpdElem (C : Contract) (Γ Δ : Ctx) where
  /-- `x := r` -/
  | local {t : LTy} (i : Idx Δ t) (r : Rhs C Γ t)
  /-- `storage := s` -/
  | storage (s : Tm C Γ .st)
  /-- `memory := m` -/
  | memory (m : Tm C Γ .mem)
  /-- `selfBalance := selfBalance ± a` -/
  | selfBalance (op : IntOp) (a : Tm C Γ .val)
  /-- `net := store(net, at(r), net(r) ± a)` -/
  | net (r : Tm C Γ .val) (op : IntOp) (a : Tm C Γ .val)
  /-- `net := if(r = this) then net else store(net, at(r), net(r) - a)` -/
  | pay (r a : Tm C Γ .val)
  /-- `net := store(mtSt, at(r), a)` -/
  | netMt (r a : Tm C Γ .val)
  /-- `selfBalance := a` -/
  | setBalance (a : Tm C Γ .val)

/-- A parallel update applied in `Γ`, leaving `Δ`: its elements in the order
they are written, the last one last. -/
inductive Upd (C : Contract) (Γ : Ctx) : Ctx → Type where
  | nil : Upd C Γ Γ
  /-- `{U ‖ e}`: `e` assigns. -/
  | snoc {Δ : Ctx} (U : Upd C Γ Δ) (e : UpdElem C Γ Δ) : Upd C Γ Δ
  /-- `{U ‖ x := r}`, `x` declared. -/
  | decl {Δ : Ctx} {t : LTy} (U : Upd C Γ Δ) (x : Var) (r : Rhs C Γ t) : Upd C Γ (t :: Δ)
  /-- The locals pushed on `Δ'` popped: a scope ended (Lean only, invisible). -/
  | pop {Δ Δ' : Ctx} (U : Upd C Γ Δ) (h : Ext Δ' Δ) : Upd C Γ Δ'

/-- The element setting the local named `x` to `r`, in `Update.lean`'s terms. -/
def Rhs.erase {Γ : Ctx} (ns : List Var) (x : Var) : {t : LTy} → Rhs C Γ t → Solidity.UpdElem C
  | _, .val t => .val x (t.erase ns)
  | _, .path p => .path x (p.erase ns)
  | _, .unset => .unset x
  | _, .mref i => .mref x (i.erase ns)
  | _, .store s => .store x (s.erase ns)
  | _, .saveNet => .saveNet x
  | _, .saveNetMt => .saveNetMt x

/-- The element, its right-hand sides named by `ns` (`Γ`'s names) and its
target by `ms` (`Δ`'s). -/
def UpdElem.erase {Γ Δ : Ctx} (ns ms : List Var) : UpdElem C Γ Δ → Solidity.UpdElem C
  | .local i r => r.erase ns (i.name ms)
  | .storage s => .storage (s.erase ns)
  | .memory m => .memory (m.erase ns)
  | .selfBalance op a => .selfBalance op (a.erase ns)
  | .net r op a => .net (r.erase ns) op (a.erase ns)
  | .pay r a => .pay (r.erase ns) (a.erase ns)
  | .netMt r a => .netMt (r.erase ns) (a.erase ns)
  | .setBalance a => .setBalance (a.erase ns)

/-- The names of the context an update leaves, from the names `ns` of the
one it is applied in. -/
def Upd.names {Γ : Ctx} (ns : List Var) : {Δ : Ctx} → Upd C Γ Δ → List Var
  | _, .nil => ns
  | _, .snoc U _ => U.names ns
  | _, .decl U x _ => x :: U.names ns
  | _, .pop U h => (U.names ns).drop h.depth

/-- `Update.lean`'s update: the elements in order, a pop none (there, a
local outlives its scope). -/
def Upd.erase {Γ : Ctx} (ns : List Var) : {Δ : Ctx} → Upd C Γ Δ → Solidity.Upd C
  | _, .nil => []
  | _, .snoc U e => U.erase ns ++ [e.erase ns (U.names ns)]
  | _, .decl U x r => U.erase ns ++ [r.erase ns x]
  | _, .pop U _ => U.erase ns

/-! ## Scopes of a program -/

/-- The locals a statement pushes: a declaration's, a call's left in its
caller. -/
def CallRet.scopeExt {Γ : Ctx} : {rs Γ' : Ctx} → CallRet Γ rs Γ' → Ext Γ Γ'
  | _, _, r => CallRet.casesOn (motive := fun _ Γ' _ => Ext Γ Γ') r .refl (fun _ _ _ => .refl)
      (fun {rs} _ => Ext.append Γ rs) (fun _ _ _ _ => .push .refl)

/-- What a statement pushes on its context (M3's `Stmt.ext` will replace
it). -/
def Stmt.scopeExt {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : Ext Γ Γ' :=
  Stmt.casesOn (motive_1 := fun Γ Γ' _ => Ext Γ Γ') s
    (assign := fun _ _ => .refl) (rebind := fun _ _ => .refl) (assignLocal := fun _ _ => .refl)
    (declLocal := fun _ _ _ => .push .refl) (declStorage := fun _ _ _ => .push .refl)
    (opAssign := fun _ _ _ _ _ => .refl) (incDec := fun _ _ _ => .refl)
    (assignIncDec := fun _ _ _ _ _ => .refl) (push := fun _ _ _ => .refl) (pop := fun _ => .refl)
    (transfer := fun _ _ => .refl) (send := fun _ _ _ => .refl)
    (declMem := fun _ _ _ _ _ => .push .refl) (rebindMem := fun _ _ => .refl)
    (assignFromMem := fun _ _ => .refl) (assignMem := fun _ _ => .refl) (delete := fun _ => .refl)
    (deleteMem := fun _ _ => .refl) (assignNew := fun _ _ _ => .refl) (ite := fun _ _ _ => .refl)
    (require := fun _ => .refl) (assert := fun _ => .refl) (revert := .refl)
    (call := fun _ _ ret _ => ret.scopeExt) (tryCall := fun _ _ _ _ _ _ _ => .refl)
    (loop := fun _ _ _ => .refl) (block := fun _ => .refl)

/-- What a block pushes on its context: what its scope end pops. -/
def Prog.scopeExt : {Γ Γ' : Ctx} → Prog C Γ Γ' → Ext Γ Γ'
  | _, _, P => Prog.casesOn (motive_2 := fun Γ Γ' _ => Ext Γ Γ') P .refl
      (fun s P => (Stmt.scopeExt s).trans (Prog.scopeExt P))
  termination_by structural _ _ P => P

/-- The names of the context a block leaves. -/
def Prog.outNames {Γ : Ctx} (ns : List Var) : {Γ' : Ctx} → Prog C Γ Γ' → List Var
  | _, .nil => ns
  | _, .cons s P => P.outNames (s.outNames ns)

/-! ## Frames: what follows the program -/

/-- How a scope ends: a block's `}`, or the fresh locals of a rule
(`se`, `sp`, `ie`), whose end is not printed. -/
inductive BlockKind where
  | block
  | capture
  deriving DecidableEq, Repr

/-- What follows the program of a modality, from `Γ` to the postcondition's
`Γ₀`: the rest of the program, and the scope ends. -/
inductive Frames (C : Contract) : Ctx → Ctx → Type where
  | nil {Γ : Ctx} : Frames C Γ Γ
  /-- The statements `ω`, then `κ`. -/
  | seq {Γ Γ₁ Γ₀ : Ctx} (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) : Frames C Γ Γ₀
  /-- A scope end: the locals pushed on `Γ` popped, then `κ`. -/
  | pop {Γ Γ' Γ₀ : Ctx} (b : BlockKind) (h : Ext Γ Γ') (κ : Frames C Γ Γ₀) : Frames C Γ' Γ₀

/-- The names of the postcondition's context. -/
def Frames.outNames (ns : List Var) : {Γ Γ₀ : Ctx} → Frames C Γ Γ₀ → List Var
  | _, _, .nil => ns
  | _, _, .seq ω κ => κ.outNames (ω.outNames ns)
  | _, _, .pop _ h κ => κ.outNames (ns.drop h.depth)

/-- The statements the frames hold, as `Update.lean`'s program goes on after
the head: a scope end is nothing there. -/
def Frames.erase (ns : List Var) : {Γ Γ₀ : Ctx} → Frames C Γ Γ₀ → List (Solidity.Stmt C)
  | _, _, .nil => []
  | _, _, .seq ω κ => ω.erase ns ++ κ.erase (ω.outNames ns)
  | _, _, .pop _ h κ => κ.erase (ns.drop h.depth)

/-! ## Formulas -/

/-- A formula about programs of `C`, read in `Γ`. -/
inductive Fml (C : Contract) : Ctx → Type where
  | tt {Γ : Ctx} : Fml C Γ
  /-- `a = b`, read in the Theory (`Tm.denote`). -/
  | eq {Γ : Ctx} (a b : Tm C Γ .val) : Fml C Γ
  /-- `t` returns. -/
  | defined {Γ : Ctx} (t : Tm C Γ .val) : Fml C Γ
  | not {Γ : Ctx} (φ : Fml C Γ) : Fml C Γ
  | and {Γ : Ctx} (φ ψ : Fml C Γ) : Fml C Γ
  | imp {Γ : Ctx} (φ ψ : Fml C Γ) : Fml C Γ
  /-- `{U} φ`, produced under the modality `m`. -/
  | upd {Γ Γ' : Ctx} (m : Modality) (U : Upd C Γ Γ') (φ : Fml C Γ') : Fml C Γ
  /-- `⟨ P κ ⟩ φ` or `[ P κ ] φ`. -/
  | modal {Γ Γ₁ Γ₀ : Ctx} (m : Modality) (P : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
      Fml C Γ
  /-- `{havoc} φ` -/
  | havoc {Γ : Ctx} (φ : Fml C Γ) : Fml C Γ
  /-- `∀ p x; φ`, KeY's `\forall`. -/
  | all {Γ : Ctx} (x : Var) (p : PrimTy) (φ : Fml C (.val p :: Γ)) : Fml C Γ
  /-- `φ` for every value of a local `x : t` declared in front of it: a
  binder that prints as nothing (`Premise.bind`). -/
  | bind {Γ : Ctx} (x : Var) (t : LTy) (φ : Fml C (t :: Γ)) : Fml C Γ
  /-- `{anon(xs)} φ` -/
  | anon {Γ : Ctx} (xs : List ((t : LTy) × Idx Γ t)) (φ : Fml C Γ) : Fml C Γ

/-- `false` is `¬true`. -/
abbrev Fml.ff {Γ : Ctx} : Fml C Γ := .not .tt

/-- `a = b` with both sides defined (`Solidity.Fml.eqD`). -/
abbrev Fml.eqD {Γ : Ctx} (a b : Tm C Γ .val) : Fml C Γ :=
  .and (.defined a) (.and (.defined b) (.eq a b))

/-- `Update.lean`'s formula, the positions named by `ns`: a frame is the
statements it holds, a pop and a hidden binder nothing, and an update of
pops only (`Frames.leave`) its formula. -/
def Fml.erase : {Γ : Ctx} → List Var → Fml C Γ → Solidity.Fml C
  | _, _, .tt => .tt
  | _, ns, .eq a b => .eq (a.erase ns) (b.erase ns)
  | _, ns, .defined t => .defined (t.erase ns)
  | _, ns, .not φ => .not (φ.erase ns)
  | _, ns, .and φ ψ => .and (φ.erase ns) (ψ.erase ns)
  | _, ns, .imp φ ψ => .imp (φ.erase ns) (ψ.erase ns)
  | _, ns, .upd m U φ =>
    match U.erase ns with
    | [] => φ.erase (U.names ns)
    | U' => .upd m U' (φ.erase (U.names ns))
  | _, ns, .modal m P κ φ =>
    .modal m (P.erase ns ++ κ.erase (P.outNames ns)) (φ.erase (κ.outNames (P.outNames ns)))
  | _, ns, .havoc φ => .havoc (φ.erase ns)
  | _, ns, .all x p φ => .all x p (φ.erase (x :: ns))
  | _, ns, .bind x _ φ => φ.erase (x :: ns)
  | _, ns, .anon xs φ => .anon (xs.map fun x => x.2.name ns) (φ.erase ns)

/-! ## Premises -/

/-- What a rule on a statement `Stmt C Γ Γ'` leaves. -/
inductive Premise (C : Contract) (Γ : Ctx) : Ctx → Type where
  /-- `{U} ⟨[ ]⟩`: the statement is the update `U`. -/
  | update {Γ' : Ctx} (U : Upd C Γ Γ') : Premise C Γ Γ'
  /-- `⟨[ P ]⟩`: the statement is the block `P`, which may declare fresh
  locals on top of the statement's own (`h`), popped after it. -/
  | unfold {Γ' Γ'' : Ctx} (P : Prog C Γ Γ'') (h : Ext Γ' Γ'') : Premise C Γ Γ'
  /-- `⟨[ P ]⟩` with the local `x : t` the statement declares bound in front
  of `P`, unprinted: `T v = e;` is `v = e;`. -/
  | bind {Γ' : Ctx} (x : Var) (t : LTy) (P : Prog C (t :: Γ) Γ') : Premise C Γ Γ'
  /-- Two goals, KeY's: `c ⟹ ⟨[ P ]⟩` and `c' ⟹ ⟨[ Q ]⟩`, each branch a
  block. -/
  | split {Γ₁ Γ₂ : Ctx} (c c' : Fml C Γ) (P : Prog C Γ Γ₁) (Q : Prog C Γ Γ₂) : Premise C Γ Γ
  /-- `c ⟹ ⟨[ ]⟩ ; c`: the goal with `c` assumed, and `c` to prove. -/
  | check (c : Fml C Γ) : Premise C Γ Γ
  /-- The goal closed (`true`) or failed (`false`). -/
  | done {Γ' : Ctx} (b : Bool) : Premise C Γ Γ'

/-- The premise as one formula, under the modality `m` the rule found, in
front of the rest `ω` of the program, the frames `κ` and the postcondition
`φ`.  The rest and the frames are passed apart (Gate G0, condition 6): an
update goes on into `⟨ ω κ ⟩ φ`. -/
def Premise.fml {Γ Γ' Γ₁ Γ₀ : Ctx} (m : Modality) (ω : Prog C Γ' Γ₁) (κ : Frames C Γ₁ Γ₀)
    (φ : Fml C Γ₀) (p : Premise C Γ Γ') : Fml C Γ :=
  Premise.casesOn (motive := fun Γ' _ => Prog C Γ' Γ₁ → Fml C Γ) p
    (fun U ω => .upd m U (.modal m ω κ φ))
    (fun P h ω => .modal m P (.pop .capture h (.seq ω κ)) φ)
    (fun x t P ω => .bind x t (.modal m P (.seq ω κ) φ))
    (fun c c' P Q ω =>
      .and (.imp c (.modal m P (.pop .block P.scopeExt (.seq ω κ)) φ))
        (.imp c' (.modal m Q (.pop .block Q.scopeExt (.seq ω κ)) φ)))
    (fun c ω => .and (.imp c (.modal m ω κ φ)) c)
    (fun b _ => if b then .tt else .ff) ω

/-- A modality whose program is done goes on into its frames: the rest of
the program, or a scope end, which pops the scope's locals (no rule fires). -/
def Frames.leave {Γ Γ₀ : Ctx} (m : Modality) (κ : Frames C Γ Γ₀) (φ : Fml C Γ₀) : Fml C Γ :=
  Frames.casesOn (motive := fun Γ Γ₀ _ => Fml C Γ₀ → Fml C Γ) κ
    (fun φ => φ)
    (fun ω κ φ => .modal m ω κ φ)
    (fun _ h κ φ => .upd m (Upd.nil.pop h) (.modal m .nil κ φ)) φ

/-! ### Equations

`Premise.fml`, `Frames.leave` and the `scopeExt`s are written with `casesOn`
(Gate G0, condition 1), so they have no equation lemmas of their own: these
are them, by `rfl`. -/

section Equations

variable {Γ Γ' Γ₁ Γ₀ : Ctx} (m : Modality) (ω : Prog C Γ' Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀)

theorem Premise.fml_update (U : Upd C Γ Γ') :
    (Premise.update U).fml m ω κ φ = .upd m U (.modal m ω κ φ) := rfl

theorem Premise.fml_unfold {Γ'' : Ctx} (P : Prog C Γ Γ'') (h : Ext Γ' Γ'') :
    (Premise.unfold P h).fml m ω κ φ = .modal m P (.pop .capture h (.seq ω κ)) φ := rfl

theorem Premise.fml_bind (x : Var) (t : LTy) (P : Prog C (t :: Γ) Γ') :
    (Premise.bind x t P).fml m ω κ φ = .bind x t (.modal m P (.seq ω κ) φ) := rfl

theorem Premise.fml_done (b : Bool) :
    (Premise.done (C := C) (Γ := Γ) (Γ' := Γ') b).fml m ω κ φ = if b then .tt else .ff := rfl

end Equations

theorem Premise.fml_split {Γ Γ₁ Γ₀ Δ₁ Δ₂ : Ctx} (m : Modality) (ω : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) (c c' : Fml C Γ) (P : Prog C Γ Δ₁) (Q : Prog C Γ Δ₂) :
    (Premise.split c c' P Q).fml m ω κ φ =
      .and (.imp c (.modal m P (.pop .block P.scopeExt (.seq ω κ)) φ))
        (.imp c' (.modal m Q (.pop .block Q.scopeExt (.seq ω κ)) φ)) := rfl

theorem Premise.fml_check {Γ Γ₁ Γ₀ : Ctx} (m : Modality) (ω : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) (c : Fml C Γ) :
    (Premise.check c).fml m ω κ φ = .and (.imp c (.modal m ω κ φ)) c := rfl

theorem Frames.leave_nil {Γ : Ctx} (m : Modality) (φ : Fml C Γ) :
    (Frames.nil : Frames C Γ Γ).leave m φ = φ := rfl

theorem Frames.leave_seq {Γ Γ₁ Γ₀ : Ctx} (m : Modality) (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀)
    (φ : Fml C Γ₀) : (Frames.seq ω κ).leave m φ = .modal m ω κ φ := rfl

theorem Frames.leave_pop {Γ Γ' Γ₀ : Ctx} (m : Modality) (b : BlockKind) (h : Ext Γ Γ')
    (κ : Frames C Γ Γ₀) (φ : Fml C Γ₀) :
    (Frames.pop b h κ).leave m φ = .upd m (Upd.nil.pop h) (.modal m .nil κ φ) := rfl

theorem Prog.scopeExt_nil {Γ : Ctx} : (Prog.nil : Prog C Γ Γ).scopeExt = .refl := rfl

theorem Prog.scopeExt_cons {Γ Γ₁ Γ₂ : Ctx} (s : Stmt C Γ Γ₁) (P : Prog C Γ₁ Γ₂) :
    (Prog.cons s P).scopeExt = s.scopeExt.trans P.scopeExt := rfl

end Solidity.Core
