import Solidity.Signature

/-!
# Terms, updates and formulas, scoped

Terms over KeY's typed signature (`Signature.lean`), updates and formulas,
read in a context `Γ : Ctx` (`docs/intrinsic.md`, M6a and W9.8.3), over the
scoped programs of `Syntax/Scoped.lean`.  A program variable is a position
(`Tm.pvV i`, `i : Idx Γ (.val p)`), so a formula cannot read a local that
is not in scope, and a term has its Solidity type in its sort
(`Tm C Γ (.val p)`, `Tm C Γ (.path T)`, …), so a symbol cannot be applied
to a term of another type: `save(s, p, v)` writes a `v` of `p`'s type.

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

**A hidden binder** (`Fml.bind m x t φ`) declares the local `x` for every value
of its type, printed as `φ` alone: `T v = e;` drops its initializer
(`localValueDeclInitDrop`) to `v = e;`, which the binder puts in scope, as
solkey's `⟨[ v = e; ]⟩`.  It carries the modality it was produced under
(decision 12); both read it universally (`Modality.forallB`), since every
type has a value, an unset memory local among them (decision 17').

`Premise C Γ Γ'` is what a rule on a statement `Stmt C Γ Γ'` leaves, and
`Premise.fml` puts it in front of the rest `ω` and the frames `κ`.  A split
has two goals, KeY's: a condition cannot be stuck, so there is no third.
-/

namespace Solidity

open Solidity (IntOp Modality)

variable {C : Contract}

/-! ## Terms -/

/-- A term at the sort `s`, read in `Γ`: a local by its position, or a
symbol applied to terms of its argument sorts. -/
inductive Tm (C : Contract) (Γ : Ctx) : Srt → Type where
  /-- A stack local. -/
  | pvV {p : PrimTy} (i : Idx Γ (.val p)) : Tm C Γ (.val p)
  /-- A storage alias. -/
  | pvP {R : RefTy} (i : Idx Γ (.alias R)) : Tm C Γ (.path (.ref R))
  /-- A storage variable, KeY's `old`. -/
  | pvS (i : Idx Γ .old) : Tm C Γ .st
  /-- A memory local. -/
  | pvI {R : RefTy} (i : Idx Γ (.mem R)) : Tm C Γ (.ident R)
  /-- `x[a]`: what the ledger bound at `x` holds for `a`, a KeY `int`. -/
  | netOf (i : Idx Γ .oldNet) (a : Tm C Γ (.val .uint)) : Tm C Γ .kint
  | app0 {s : Srt} (o : Op0 C s) : Tm C Γ s
  | app1 {a s : Srt} (o : Op1 C a s) (x : Tm C Γ a) : Tm C Γ s
  | app2 {a b s : Srt} (o : Op2 C a b s) (x : Tm C Γ a) (y : Tm C Γ b) : Tm C Γ s
  | app3 {a b c s : Srt} (o : Op3 C a b c s) (x : Tm C Γ a) (y : Tm C Γ b)
      (z : Tm C Γ c) : Tm C Γ s
  /-- A logical variable of KeY's `int` (a formula's parameter). -/
  | pvZ (i : Idx Γ .kint) : Tm C Γ .kint

/-! ## Updates -/

/-- What a local of type `t` is set to, read in `Γ`. -/
inductive Rhs (C : Contract) (Γ : Ctx) : LTy → Type where
  /-- `v := t` -/
  | val {p : PrimTy} (t : Tm C Γ (.val p)) : Rhs C Γ (.val p)
  /-- `lsv := p` -/
  | path {R : RefTy} (p : Tm C Γ (.path (.ref R))) : Rhs C Γ (.alias R)
  /-- `lsv := unset` (Lean only, `storageLocalDeclSkip`). -/
  | unset {R : RefTy} : Rhs C Γ (.alias R)
  /-- `mv := i` -/
  | mref {R : RefTy} (i : Tm C Γ (.ident R)) : Rhs C Γ (.mem R)
  /-- `old := s` -/
  | store (s : Tm C Γ .st) : Rhs C Γ .old
  /-- `oldNet := net` -/
  | saveNet : Rhs C Γ .oldNet
  /-- `oldNet := mtSt` -/
  | saveNetMt : Rhs C Γ .oldNet
  /-- `z := t`, a KeY `int`. -/
  | zint (t : Tm C Γ .kint) : Rhs C Γ .kint

/-- One assigning element: its right-hand sides read in `Γ`, its target a
local of `Δ`, or a part of the state.  An amount and an address are a
`uint`. -/
inductive UpdElem (C : Contract) (Γ Δ : Ctx) where
  /-- `x := r` -/
  | local {t : LTy} (i : Idx Δ t) (r : Rhs C Γ t)
  /-- `storage := s` -/
  | storage (s : Tm C Γ .st)
  /-- `memory := m` -/
  | memory (m : Tm C Γ .mem)
  /-- `selfBalance := selfBalance ± a` -/
  | selfBalance (op : IntOp) (a : Tm C Γ (.val .uint))
  /-- `net := store(net, at(r), net(r) ± a)` -/
  | net (r : Tm C Γ (.val .uint)) (op : IntOp) (a : Tm C Γ (.val .uint))
  /-- `net := if(r = this) then net else store(net, at(r), net(r) - a)` -/
  | pay (r a : Tm C Γ (.val .uint))
  /-- `net := store(mtSt, at(r), a)` -/
  | netMt (r a : Tm C Γ (.val .uint))
  /-- `selfBalance := a` -/
  | setBalance (a : Tm C Γ (.val .uint))

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
  /-- The locals of `Δ` that `Δ'` does not keep dropped, from anywhere in it:
  a call's frame under the return variables it exports (Lean only,
  invisible). -/
  | drop {Δ Δ' : Ctx} (U : Upd C Γ Δ) (h : Thin Δ' Δ) : Upd C Γ Δ'

/-- The names of the locals a thinning keeps, from the names `ns` of the
context it thins into. -/
def Thin.names : {Γ Δ : Ctx} → Thin Γ Δ → List Var → List Var
  | _, _, .refl, ns => ns
  | _, _, .keep h, n :: ns => n :: Thin.names h ns
  | _, _, .keep h, [] => Thin.names h []
  | _, _, .drop h, ns => Thin.names h ns.tail

/-- The names of the context an update leaves, from the names `ns` of the
one it is applied in. -/
def Upd.names {Γ : Ctx} (ns : List Var) : {Δ : Ctx} → Upd C Γ Δ → List Var
  | _, .nil => ns
  | _, .snoc U _ => U.names ns
  | _, .decl U x _ => x :: U.names ns
  | _, .pop U h => (U.names ns).drop h.depth
  | _, .drop U h => h.names (U.names ns)

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
  /-- A frame end under what it exports: the locals of `Γ'` that `Γ` does
  not keep dropped, then `κ` (a call's parameters under its return
  variables; invisible). -/
  | drop {Γ Γ' Γ₀ : Ctx} (h : Thin Γ Γ') (κ : Frames C Γ Γ₀) : Frames C Γ' Γ₀

/-- The names of the postcondition's context. -/
def Frames.outNames (ns : List Var) : {Γ Γ₀ : Ctx} → Frames C Γ Γ₀ → List Var
  | _, _, .nil => ns
  | _, _, .seq ω κ => κ.outNames (ω.outNames ns)
  | _, _, .pop _ h κ => κ.outNames (ns.drop h.depth)
  | _, _, .drop h κ => κ.outNames (h.names ns)

/-! ## Formulas -/

/-- A hidden binder's reading under `m`: `p` of every value, under both
modalities.  Decision 12 asked the diamond for a value first; since a memory
local may be unset (decision 17'), every local's type has one in every
state (`LTy.tdenote_nonempty`), so that clause is gone and `m` is only what
the rule wrote. -/
def _root_.Solidity.Modality.forallB (_m : Modality) {α : Sort _} (p : α → Prop) : Prop :=
  ∀ v, p v

theorem _root_.Solidity.Modality.forallB_all {m : Modality} {α : Sort _} {p : α → Prop}
    (h : m.forallB p) (v : α) : p v := h v

theorem _root_.Solidity.Modality.forallB_imp {m : Modality} {α : Sort _} {p q : α → Prop}
    (h : ∀ v, p v → q v) (hp : m.forallB p) : m.forallB q := fun v => h v (hp v)

theorem _root_.Solidity.Modality.forallB_and {m : Modality} {α : Sort _} {p q r : α → Prop}
    (h : ∀ v, p v → q v → r v) (hp : m.forallB p) (hq : m.forallB q) : m.forallB r :=
  fun v => h v (hp v) (hq v)

theorem _root_.Solidity.Modality.forallB_intro {m : Modality} {α : Sort _} {p : α → Prop}
    (h : ∀ v, p v) : m.forallB p := h

/-- A formula about programs of `C`, read in `Γ`. -/
inductive Fml (C : Contract) : Ctx → Type where
  | tt {Γ : Ctx} : Fml C Γ
  /-- `a = b`, two values of one type, read in the Theory (`Tm.denote`). -/
  | eq {Γ : Ctx} {p : PrimTy} (a b : Tm C Γ (.val p)) : Fml C Γ
  /-- `t` returns. -/
  | defined {Γ : Ctx} {p : PrimTy} (t : Tm C Γ (.val p)) : Fml C Γ
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
  /-- `φ` for every value of a local `x : t` declared in front of it, produced
  under `m`: a binder that prints as nothing (`Premise.bind`). -/
  | bind {Γ : Ctx} (m : Modality) (x : Var) (t : LTy) (φ : Fml C (t :: Γ)) : Fml C Γ
  /-- `{anon(xs)} φ` -/
  | anon {Γ : Ctx} (xs : List ((t : LTy) × Idx Γ t)) (φ : Fml C Γ) : Fml C Γ

/-- `false` is `¬true`. -/
abbrev Fml.ff {Γ : Ctx} : Fml C Γ := .not .tt

/-- `a = b` with both sides defined. -/
abbrev Fml.eqD {Γ : Ctx} {p : PrimTy} (a b : Tm C Γ (.val p)) : Fml C Γ :=
  .and (.defined a) (.and (.defined b) (.eq a b))

/-! ## Premises -/

/-- `φ₁ ∧ … ∧ φₙ`, `true` when there are none (`Update.lean`'s `Fml.conj`). -/
def Fml.conj {Γ : Ctx} : List (Fml C Γ) → Fml C Γ
  | [] => .tt
  | [φ] => φ
  | φ :: ψs => .and φ (Fml.conj ψs)

/-- `∀ xs. φ`: `φ` for every value of the locals the binders declare, the
first bound outermost. -/
def Binders.all {Γ : Ctx} : {ρ : Ctx} → Binders ρ → Fml C (ρ ++ Γ) → Fml C Γ
  | _, bs, φ => Binders.casesOn (motive := fun ρ _ => Fml C (ρ ++ Γ) → Fml C Γ) bs (fun φ => φ)
      (fun bs p x φ => Binders.all bs (.all x p φ)) φ
  termination_by structural _ bs => bs

/-- A block of a `try`: the locals `bs` its outcome binds, on top of `Γ`,
and its statements. -/
structure Branch (C : Contract) (Γ : Ctx) where
  {ρ Γ₁ : Ctx}
  bs : Binders ρ
  P : Prog C (ρ ++ Γ) Γ₁

/-- What a rule on a statement `Stmt C Γ Γ'` leaves. -/
inductive Premise (C : Contract) (Γ : Ctx) : Ctx → Type where
  /-- `{U} ⟨[ ]⟩`: the statement is the update `U`. -/
  | update {Γ' : Ctx} (U : Upd C Γ Γ') : Premise C Γ Γ'
  /-- `{U} {V} ⟨[ ]⟩`: `V` reads the state left by `U`, as in
  `a.push() += x`. Each update remains parallel internally. -/
  | updates {Δ Γ' : Ctx} (U : Upd C Γ Δ) (V : Upd C Δ Γ') : Premise C Γ Γ'
  /-- `⟨[ P ]⟩`: the statement is the block `P`, which may declare fresh
  locals on top of the statement's own (`h`), popped after it. -/
  | unfold {Γ' Γ'' : Ctx} (P : Prog C Γ Γ'') (h : Ext Γ' Γ'') : Premise C Γ Γ'
  /-- `⟨[ P ]⟩` with the local `x : t` the statement declares bound in front
  of `P`, unprinted: `T v = e;` is `v = e;`. -/
  | bind {Γ' : Ctx} (x : Var) (t : LTy) (P : Prog C (t :: Γ) Γ') : Premise C Γ Γ'
  /-- Two goals, KeY's: `c ⟹ ⟨[ P ]⟩` and `c' ⟹ ⟨[ Q ]⟩`, each branch's
  scope ended as `b` says: an `if`'s branches are blocks (`}`), a
  `require`'s goals are not (its `revert();` ends invisibly). -/
  | split {Γ₁ Γ₂ : Ctx} (b : BlockKind) (c c' : Fml C Γ) (P : Prog C Γ Γ₁) (Q : Prog C Γ Γ₂) :
      Premise C Γ Γ
  /-- `c ⟹ ⟨[ ]⟩ ; c`: the goal with `c` assumed, and `c` to prove. -/
  | check (c : Fml C Γ) : Premise C Γ Γ
  /-- The goal closed (`true`) or failed (`false`). -/
  | done {Γ' : Ctx} (b : Bool) : Premise C Γ Γ'
  /-- One goal per block, each in the statement's place, for every value of
  the locals it binds: `∀ xs. ⟨[ P ]⟩` (a `try`'s clauses). -/
  | branches (bs : List (Branch C Γ)) : Premise C Γ Γ
  /-- Goals labelled as KeY labels a taclet's: each formula of `fs` to prove,
  then for each update `U` of `us` the rest after it, `{U} ⟨[ ..ω ]⟩ φ`, one
  per way the statement may end (a `send`). -/
  | cases (fs : List (Fml C Γ)) (us : List (Upd C Γ Γ)) : Premise C Γ Γ
  /-- A loop's invariant rule: the invariant `I` now, and, whatever the body's
  frame holds (`{anon(xs)}`, with `{havoc}` when `hv`), from where `I`
  holds and after `U` (the condition's value, and under the diamond the
  variant's, declared on top of `Γ`), the body `P` to `post` where `c`
  holds, the rest where `c'` does.  The condition's local is popped before
  the body (`hb`), so the body reads `Δ₀`: `Γ`, or `Γ` with the variant on
  top (`hu`); every local `U` declares is popped before the rest.  With a
  break test `B` (solkey's `\getLoopBreak`) the loop starts and each
  iteration assumes `I ∧ ¬B`, and the body ends in `post` where `B` does not
  hold, in the rest where it does (`Fml.invHyp`, `Fml.invPost`). -/
  | inv {Δ₀ Δ Γ₁ : Ctx} (I : Fml C Γ) (B : Option (Fml C Γ)) (xs : List ((t : LTy) × Idx Γ t)) (hv : Bool)
      (U : Upd C Γ Δ) (c c' : Fml C Δ) (hu : Ext Γ Δ₀) (hb : Ext Δ₀ Δ) (P : Prog C Δ₀ Γ₁)
      (post : Fml C Δ₀) : Premise C Γ Γ
  /-- `⟨[ P ]⟩` whose end drops the locals of `Γ''` that `Γ'` does not keep,
  from anywhere in it: a call's frame under the return variables it leaves
  its caller. -/
  | inline {Γ' Γ'' : Ctx} (P : Prog C Γ Γ'') (h : Thin Γ' Γ'') : Premise C Γ Γ'
  /-- SolKey's outer zero-divisor branch in `sp.push() /= se`: when `c`
  holds, append then save; otherwise run `revert();` before the rest. -/
  | guardedUpdates {Δ : Ctx} (c : Fml C Γ) (U : Upd C Γ Δ) (V : Upd C Δ Γ) :
      Premise C Γ Γ

/-- `{anon(xs)} φ`, and `{anon(xs)} {havoc} φ` when the frame writes the
storage too (`hv`): solkey's `#loopAnon`. -/
def Fml.anonHavoc {Γ : Ctx} (xs : List ((t : LTy) × Idx Γ t)) (hv : Bool) (φ : Fml C Γ) :
    Fml C Γ :=
  if hv then .anon xs (.havoc φ) else .anon xs φ

/-- A modality whose program is done goes through its frames: a scope end
pops its locals (an update of pops, which prints as nothing), the rest of
the program is the next modality, and with no frame left the postcondition
is the goal.  No rule fires on the way (Gate G0, condition 6). -/
def Frames.exit (m : Modality) : {Γ Γ₀ : Ctx} → Frames C Γ Γ₀ → Fml C Γ₀ → Fml C Γ
  | _, _, κ => Frames.casesOn (motive := fun Γ Γ₀ _ => Fml C Γ₀ → Fml C Γ) κ
      (fun φ => φ)
      (fun ω κ φ => Prog.casesOn
        (motive_2 := fun Γ Γ₁ _ => (Unit → Fml C Γ₁) → Frames C Γ₁ _ → Fml C Γ) ω
        (fun rest _ => rest ()) (fun s ω _ κ => .modal m (.cons s ω) κ φ)
        (fun _ => Frames.exit m κ φ) κ)
      (fun _ h κ φ => .upd m (Upd.nil.pop h) (Frames.exit m κ φ))
      (fun h κ φ => .upd m (Upd.nil.drop h) (Frames.exit m κ φ))
  termination_by structural _ _ κ => κ

/-- `⟨ ω κ ⟩ φ`, gone on into the frames when `ω` is empty: the formula a
rule leaves in front of the rest of the program. -/
def Fml.modalK {Γ Γ₁ Γ₀ : Ctx} (m : Modality) (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀)
    (φ : Fml C Γ₀) : Fml C Γ :=
  Prog.casesOn (motive_2 := fun Γ Γ₁ _ => Frames C Γ₁ Γ₀ → Fml C Γ) ω
    (fun κ => κ.exit m φ) (fun s ω κ => .modal m (.cons s ω) κ φ) κ

/-- What a loop's iteration assumes: the invariant `I`, and `¬B` with a break
test `B` (solkey's `inv & !broke`). -/
def Fml.invHyp {Γ : Ctx} (I : Fml C Γ) : Option (Fml C Γ) → Fml C Γ
  | none => I
  | some B => .and I (.not B)

/-- What a loop's body ends in: `post`, and with a break test `B` `post`
where `B` does not hold, the rest of the program `⟨[ ω κ ]⟩ φ` where it does
(solkey's `(!broke -> inv) & (broke -> [c# #c] post)`), both read at the
body's scope `Δ₀` (`hu`). -/
def Fml.invPost {Γ Δ₀ Γ₁ Γ₀ : Ctx} (m : Modality) (hu : Ext Γ Δ₀) (ω : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) (post : Fml C Δ₀) : Option (Fml C Γ) → Fml C Δ₀
  | none => post
  | some B => .and (.imp (.not (.upd m (Upd.nil.pop hu) B)) post)
      (.imp (.upd m (Upd.nil.pop hu) B) (.upd m (Upd.nil.pop hu) (.modalK m ω κ φ)))

/-- The premise as one formula, under the modality `m` the rule found, in
front of the rest `ω` of the program, the frames `κ` and the postcondition
`φ`.  The rest and the frames are passed apart (Gate G0, condition 6): an
update goes on into `⟨ ω κ ⟩ φ`, or into the frames when `ω` is empty. -/
def Premise.fml {Γ Γ' Γ₁ Γ₀ : Ctx} (m : Modality) (ω : Prog C Γ' Γ₁) (κ : Frames C Γ₁ Γ₀)
    (φ : Fml C Γ₀) (p : Premise C Γ Γ') : Fml C Γ :=
  Premise.casesOn (motive := fun Γ' _ => Prog C Γ' Γ₁ → Fml C Γ) p
    (fun U ω => .upd m U (.modalK m ω κ φ))
    (fun U V ω => .upd m U (.upd m V (.modalK m ω κ φ)))
    (fun P h ω => .modal m P (.pop .capture h (.seq ω κ)) φ)
    (fun x t P ω => .bind m x t (.modal m P (.seq ω κ) φ))
    (fun b c c' P Q ω =>
      .and (.imp c (.modalK m P (.pop b P.ext (.seq ω κ)) φ))
        (.imp c' (.modalK m Q (.pop b Q.ext (.seq ω κ)) φ)))
    (fun c ω => .and (.imp c (.modalK m ω κ φ)) c)
    (fun b _ => if b then .tt else .ff)
    (fun bs ω => Fml.conj (bs.map fun b =>
      b.bs.all (.modalK m b.P (.pop .block ((Ext.append Γ b.ρ).trans b.P.ext) (.seq ω κ)) φ)))
    (fun fs us ω => Fml.conj (fs ++ us.map fun U => .upd m U (.modalK m ω κ φ)))
    (fun I B xs hv U c c' hu hb P post ω => .and (I.invHyp B) (Fml.anonHavoc xs hv (.imp (I.invHyp B)
      (.upd m U (.and (.imp c (.upd m (Upd.nil.pop hb)
          (.modalK m P (.pop .block P.ext .nil) (Fml.invPost m hu ω κ φ post B))))
        (.imp c' (.upd m (Upd.nil.pop (hu.trans hb)) (.modalK m ω κ φ))))))))
    (fun P h ω => .modal m P (.drop h (.seq ω κ)) φ)
    (fun c U V ω => .and (.imp c (.upd m U (.upd m V (.modalK m ω κ φ))))
      (.imp (.not c) (.modal m (.cons .revert ω) κ φ))) ω

/-! ### Equations

`Premise.fml`, `Frames.exit` and `Fml.modalK` are written with `casesOn`
(Gate G0, condition 1), so they have no equation lemmas of their own: these
are them, by `rfl`. -/

section Equations

variable {Γ Γ' Γ₁ Γ₀ : Ctx} (m : Modality) (ω : Prog C Γ' Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀)

theorem Premise.fml_update (U : Upd C Γ Γ') :
    (Premise.update U).fml m ω κ φ = .upd m U (.modalK m ω κ φ) := rfl

/-- `a.push() += x` leaves two updates; the second reads the first's result. -/
theorem Premise.fml_updates {Δ : Ctx} (U : Upd C Γ Δ) (V : Upd C Δ Γ') :
    (Premise.updates U V).fml m ω κ φ = .upd m U (.upd m V (.modalK m ω κ φ)) := rfl

theorem Premise.fml_unfold {Γ'' : Ctx} (P : Prog C Γ Γ'') (h : Ext Γ' Γ'') :
    (Premise.unfold P h).fml m ω κ φ = .modal m P (.pop .capture h (.seq ω κ)) φ := rfl

theorem Premise.fml_bind (x : Var) (t : LTy) (P : Prog C (t :: Γ) Γ') :
    (Premise.bind x t P).fml m ω κ φ = .bind m x t (.modal m P (.seq ω κ) φ) := rfl

theorem Premise.fml_done (b : Bool) :
    (Premise.done (C := C) (Γ := Γ) (Γ' := Γ') b).fml m ω κ φ = if b then .tt else .ff := rfl

end Equations

/-- `sp.push() /= se` keeps the zero-divisor test outside both updates. -/
theorem Premise.fml_guardedUpdates {Γ Δ Γ₁ Γ₀ : Ctx} (m : Modality)
    (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀)
    (c : Fml C Γ) (U : Upd C Γ Δ) (V : Upd C Δ Γ) :
    (Premise.guardedUpdates c U V).fml m ω κ φ =
      .and (.imp c (.upd m U (.upd m V (.modalK m ω κ φ))))
        (.imp (.not c) (.modal m (.cons .revert ω) κ φ)) := rfl

theorem Premise.fml_split {Γ Γ₁ Γ₀ Δ₁ Δ₂ : Ctx} (m : Modality) (ω : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) (b : BlockKind) (c c' : Fml C Γ) (P : Prog C Γ Δ₁)
    (Q : Prog C Γ Δ₂) :
    (Premise.split b c c' P Q).fml m ω κ φ =
      .and (.imp c (.modalK m P (.pop b P.ext (.seq ω κ)) φ))
        (.imp c' (.modalK m Q (.pop b Q.ext (.seq ω κ)) φ)) := rfl

theorem Premise.fml_check {Γ Γ₁ Γ₀ : Ctx} (m : Modality) (ω : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) (c : Fml C Γ) :
    (Premise.check c).fml m ω κ φ = .and (.imp c (.modalK m ω κ φ)) c := rfl

theorem Frames.exit_nil {Γ : Ctx} (m : Modality) (φ : Fml C Γ) :
    (Frames.nil : Frames C Γ Γ).exit m φ = φ := rfl

theorem Frames.exit_seq {Γ Γ₁ Γ₀ : Ctx} (m : Modality) (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀)
    (φ : Fml C Γ₀) : (Frames.seq ω κ).exit m φ = .modalK m ω κ φ := by
  cases ω <;> rfl

theorem Frames.exit_pop {Γ Γ' Γ₀ : Ctx} (m : Modality) (b : BlockKind) (h : Ext Γ Γ')
    (κ : Frames C Γ Γ₀) (φ : Fml C Γ₀) :
    (Frames.pop b h κ).exit m φ = .upd m (Upd.nil.pop h) (κ.exit m φ) := rfl

theorem Fml.modalK_nil {Γ Γ₀ : Ctx} (m : Modality) (κ : Frames C Γ Γ₀) (φ : Fml C Γ₀) :
    Fml.modalK m .nil κ φ = κ.exit m φ := rfl

theorem Fml.modalK_cons {Γ Γ₁ Γ₂ Γ₀ : Ctx} (m : Modality) (s : Stmt C Γ Γ₁) (ω : Prog C Γ₁ Γ₂)
    (κ : Frames C Γ₂ Γ₀) (φ : Fml C Γ₀) : Fml.modalK m (.cons s ω) κ φ = .modal m (.cons s ω) κ φ :=
  rfl

end Solidity
