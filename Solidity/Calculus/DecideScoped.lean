import Solidity.Calculus.Decide
import Solidity.Calculus.TermEq

/-!
# The reduction on a scoped leaf

`sol_decide` on a scoped leaf `Valid φ` (`φ : Fml C []`) pushes its updates
into the formula (`Fml.toLS`, mini-solkey's `Fml.applyUpds`): a term of
the reduction is the scoped term with its locals, `storage` and `memory`
replaced by what the updates bound them to, read in the state the leaf
starts in.  The reduction's terms are the typed signature's (`LTm`,
`Calculus/DecideLang.lean`), so a scoped term is pushed in symbol by
symbol (`Tm.toL`): the symbols read their arguments as the scoped term's
do.  Two symbols read the state they are read in, and are pushed in onto
the storage the updates left: an index checked (`at`, onto `atIn`) and
the slot past an array's end (`next`, onto `nextIn`).

The symbolic state (`SymS C Γ`) is indexed by the leaf's context: at each
position the term an update bound its local to (`BEnv`, a sort per local
type, `LTy.bs`), or nothing (a hidden binder, until an update binds it,
which the fragment never reads before: `Tm.toL` is `none` there); the
storage and the memory the updates left; and the next position (`next`).
A quantifier's local is the atom of its position (`LTm.var`), which the
`LFml.all` in front of the rest binds.

An update is applied element by element, each element read in the state
the update is applied in (`Upd.toLS`), and its terms must return: a box
update's guard is a premise of the rest, a diamond's a conjunct.

The fragment is where `Fml.toLS` returns: a ledger read or write other
than a payment's, a `select`, a ledger snapshot, `havoc` and `anon` are
outside it.  It has a polarity: under a negation or on the left of an
implication it takes first-order formulas only (`pos := false`), where the
reduction and the formula agree both ways.

What the kernel evaluates is written by the recursors (Gate G0), each with
its `match` form as the compiled twin (`…M`).
-/

namespace Solidity

namespace Decide

open Semantics

variable {C : Contract}

/-! ## The symbolic state -/

/-- The sort a local of type `t` is bound at: a value's, a reference's, an
identity's, a storage's. -/
def _root_.Solidity.LTy.bs : LTy → Srt
  | .val p => .val p
  | .alias R => .path (.ref R)
  | .mem R => .ident R
  | .old => .st
  | .oldNet => .kint
  | .kint => .kint

/-- What each position of `Γ` is bound to. -/
def BEnv (C : Contract) : Ctx → Type
  | [] => Unit
  | t :: Γ => Option (LTm C t.bs) × BEnv C Γ

namespace BEnv

/-- The binding at a position. -/
def get : {Γ : Ctx} → {t : LTy} → Idx Γ t → BEnv C Γ → Option (LTm C t.bs)
  | _, _, i => Idx.casesOn (motive := fun Γ t _ => BEnv C Γ → Option (LTm C t.bs)) i
      (fun e => e.1) (fun i e => BEnv.get i e.2)
  termination_by structural _ _ i => i

/-- The binding at a position, set. -/
def set : {Γ : Ctx} → {t : LTy} → Idx Γ t → Option (LTm C t.bs) → BEnv C Γ → BEnv C Γ
  | _, _, i => Idx.casesOn (motive := fun Γ t _ => Option (LTm C t.bs) → BEnv C Γ → BEnv C Γ) i
      (fun w e => (w, e.2)) (fun i w e => (e.1, BEnv.set i w e.2))
  termination_by structural _ _ i => i

/-- The positions a suffix pushed, popped. -/
def drop {Γ : Ctx} : {Δ : Ctx} → Ext Γ Δ → BEnv C Δ → BEnv C Γ
  | _, h => Ext.casesOn (motive := fun Δ _ => BEnv C Δ → BEnv C Γ) h (fun e => e)
      (fun h e => BEnv.drop h e.2)
  termination_by structural _ h => h

/-- `thin` by `match`, its compiled form. -/
def thinM : {Γ Δ : Ctx} → Thin Γ Δ → BEnv C Δ → BEnv C Γ
  | _, _, .refl, e => e
  | _, _, .keep h, e => (e.1, thinM h e.2)
  | _, _, .drop h, e => thinM h e.2

/-- The positions a thinning keeps. -/
@[implemented_by thinM]
def thin : {Γ Δ : Ctx} → Thin Γ Δ → BEnv C Δ → BEnv C Γ
  | _, _, h => Thin.rec (motive := fun Γ Δ _ => BEnv C Δ → BEnv C Γ) (fun e => e)
      (fun _ ih e => (e.1, ih e.2)) (fun _ ih e => ih e.2) h

end BEnv

/-- The updates so far, by position: what each local is bound to, the
storage and the memory they left, and the next position a binder takes. -/
structure SymS (C : Contract) (Γ : Ctx) where
  loc : BEnv C Γ
  stor : LTm C .st
  mem : LTm C .mem
  next : Nat

/-- No update yet, no local. -/
def SymS.init : SymS C [] := ⟨(), .app0 .storage, .app0 .memory, 0⟩

/-- A local pushed, bound to `b` (or to nothing). -/
def SymS.push {Γ : Ctx} {t : LTy} (ρ : SymS C Γ) (b : Option (LTm C t.bs)) : SymS C (t :: Γ) :=
  ⟨(b, ρ.loc), ρ.stor, ρ.mem, ρ.next + 1⟩

/-- A quantifier's local pushed: the atom of its position. -/
def SymS.pushQ {Γ : Ctx} (p : PrimTy) (ρ : SymS C Γ) : SymS C (.val p :: Γ) :=
  ρ.push (t := .val p) (some (.var ρ.next))

/-! ## Terms, by position -/

section Terms

variable {Γ : Ctx}

/-- A constant pushed in: `storage` and `memory` the updates left. -/
def _root_.Solidity.Op0.toL (ρ : SymS C Γ) {s : Srt} (o : Op0 C s) : Option (LTm C s) :=
  @Op0.casesOn C (fun s _ => Option (LTm C s)) s o
    (fun v => some (.app0 (.lit v))) (fun k => some (.app0 (.env k)))
    (fun r {_} h => some (.app0 (.root r h))) (some ρ.stor) (some ρ.mem)
    (some (.app0 .mtSt)) (fun s f {_} h => some (.app0 (.member s f h)))
    (fun n => some (.app0 (.zlit n)))

/-- A unary symbol pushed in: `next` onto the storage the updates left; a
read of the ledger outside the fragment. -/
def _root_.Solidity.Op1.toL (ρ : SymS C Γ) {a s : Srt} (o : Op1 C a s) (x : LTm C a) :
    Option (LTm C s) :=
  @Op1.casesOn C (fun a s _ => LTm C a → Option (LTm C s)) a s o
    (fun op {_} h x => some (.app1 (.unop op h) x))
    (fun _ => none)
    (fun {_} x => some (.app1 .delValue x))
    (fun {_} {_} {_} h x => some (.app1 (.field h) x))
    (fun {_} x => some (.app2 .nextIn ρ.stor x))
    (fun {_} x => some (.app1 .sval x))
    (fun {_} h x => some (.app1 (.newArr h) x))
    (fun R h x => some (.app1 (.alloc R h) x))
    (fun {_} {_} {_} h x => some (.app1 (.mfield h) x))
    (fun R h x => some (.app1 (.addM R h) x))
    (fun {_} x => some (.app1 .mval x))
    (fun {_} x => some (.app1 .ref x))
    (fun x => some (.app1 .wt x))
    (fun {_} r h x => some (.app1 (.select r h) x))
    (fun {_} {_} {_} h x => some (.app1 (.selectIn h) x))
    (fun {_} {_} {_} {_} h x => some (.app1 (.fieldIn h) x))
    (fun x => some (.app1 .toInt x)) x

/-- A binary symbol pushed in: a checked index onto the storage the
updates left (`atIn`). -/
def _root_.Solidity.Op2.toL (ρ : SymS C Γ) {a b s : Srt} (o : Op2 C a b s) (x : LTm C a)
    (y : LTm C b) : Option (LTm C s) :=
  @Op2.casesOn C (fun a b s _ => LTm C a → LTm C b → Option (LTm C s)) a b s o
    (fun op {_} h x y => some (.app2 (.binop op h) x y))
    (fun {_} x y => some (.app2 .find x y))
    (fun {_} x y => some (.app2 .len x y))
    (fun {_} x y => some (.app2 .read x y))
    (fun {_} x y => some (.app2 .mlen x y))
    (fun {_} {_} {_} it x y => some (.app3 (.atIn it) ρ.stor x y))
    (fun {_} x y => some (.app2 .nextIn x y))
    (fun {_} x y => some (.app2 .delAt x y))
    (fun {_} x y => some (.app2 .pushSlot x y))
    (fun {_} x y => some (.app2 .pop x y))
    (fun {_} x y => some (.app2 .shrink x y))
    (fun {_} x y => some (.app2 .extend x y))
    (fun {_} x y => some (.app2 .sfind x y))
    (fun {_} x y => some (.app2 .copyMem x y))
    (fun {_} x y => some (.app2 .iread x y))
    (fun {_} h x y => some (.app2 (.copy h) x y))
    (fun {_} {_} a x y => some (.app2 (.mat a) x y))
    (fun {_} h x y => some (.app2 (.copySt h) x y))
    (fun {_} {_} x y => some (.app2 .findIn x y))
    (fun {_} {_} x y => some (.app2 .delAtIn x y))
    (fun {_} {_} x y => some (.app2 .sfindIn x y))
    (fun op h x y => some (.app2 (.zbin op h) x y))
    (fun op h x y => some (.app2 (.zcmp op h) x y)) x y

/-- A ternary symbol pushed in. -/
def _root_.Solidity.Op3.toL {a b c s : Srt} (o : Op3 C a b c s) (x : LTm C a) (y : LTm C b)
    (z : LTm C c) : Option (LTm C s) :=
  some (.app3 o x y z)

/-- `Tm.toL`'s compiled twin. -/
def _root_.Solidity.Tm.toLM (ρ : SymS C Γ) : {s : Srt} → Tm C Γ s → Option (LTm C s)
  | _, .pvV i => ρ.loc.get i
  | _, .pvP i => ρ.loc.get i
  | _, .pvS i => ρ.loc.get i
  | _, .pvI i => ρ.loc.get i
  | _, .netOf _ _ => none
  | _, .app0 o => o.toL ρ
  | _, .app1 o x => (x.toLM ρ).bind (o.toL ρ)
  | _, .app2 o x y => (x.toLM ρ).bind fun x' => (y.toLM ρ).bind (o.toL ρ x')
  | _, .app3 o x y z =>
    (x.toLM ρ).bind fun x' => (y.toLM ρ).bind fun y' => (z.toLM ρ).bind (o.toL x' y')
  | _, .pvZ i => ρ.loc.get i

/-- **A term with the updates pushed in**, its locals read by position;
`none` outside the fragment.  By the recursor. -/
@[implemented_by Tm.toLM]
def _root_.Solidity.Tm.toL (ρ : SymS C Γ) {s : Srt} (t : Tm C Γ s) : Option (LTm C s) :=
  @Tm.rec C Γ (fun s _ => Option (LTm C s))
    (fun {_} i => ρ.loc.get i) (fun {_} i => ρ.loc.get i) (fun i => ρ.loc.get i)
    (fun {_} i => ρ.loc.get i) (fun _ _ _ => none) (fun o => o.toL ρ)
    (fun o _ ix => ix.bind (o.toL ρ))
    (fun o _ _ ix iy => ix.bind fun x' => iy.bind (o.toL ρ x'))
    (fun o _ _ _ ix iy iz => ix.bind fun x' => iy.bind fun y' => iz.bind (o.toL x' y'))
    (fun i => ρ.loc.get i) s t

end Terms

/-! ## Updates, by position

An update's elements are read in the state it is applied in (`ρ₀`) and
applied in order: an element binds its local, writes the storage, or sets
the memory; a declaration pushes a position, a pop or a frame's drop pops
or drops positions.  What the update must return is the conjunction of
its elements' terms (`seqL`). -/

section Upd

variable {Γ : Ctx}

/-- What a right-hand side binds its local to: the term pushed in, an unset
alias to nothing that returns (`err`, which reads as no reference). -/
def _root_.Solidity.Rhs.toL (ρ : SymS C Γ) {t : LTy} (r : Rhs C Γ t) :
    Option (LTm C t.bs × LTm C (.val .bool)) :=
  @Rhs.casesOn C Γ (fun t _ => Option (LTm C t.bs × LTm C (.val .bool))) t r
    (fun {_} x => (x.toL ρ).map fun x' => (x', seqL x' .tt))
    (fun {_} p => (p.toL ρ).map fun p' => (p', seqL p' .tt))
    (fun {_} => some (.err, .tt))
    (fun {_} i => (i.toL ρ).map fun i' => (i', seqL i' .tt))
    (fun s => (s.toL ρ).map fun s' => (s', seqL s' .tt))
    none none
    (fun x => (x.toL ρ).map fun x' => (x', seqL x' .tt))

/-- One element applied to the state `ρ`, read in `ρ₀`; its guard. -/
def _root_.Solidity.UpdElem.toLS {Δ : Ctx} (ρ₀ : SymS C Γ) (e : UpdElem C Γ Δ) (ρ : SymS C Δ) :
    Option (SymS C Δ × LTm C (.val .bool)) :=
  @UpdElem.casesOn C Γ Δ (fun _ => Option (SymS C Δ × LTm C (.val .bool))) e
    (fun {_} i r => (r.toL ρ₀).map fun b => (⟨ρ.loc.set i (some b.1), ρ.stor, ρ.mem, ρ.next⟩, b.2))
    (fun s => (s.toL ρ₀).map fun s' => (⟨ρ.loc, s', ρ.mem, ρ.next⟩, seqL s' .tt))
    (fun m => (m.toL ρ₀).map fun m' => (⟨ρ.loc, ρ.stor, m', ρ.next⟩, seqL m' .tt))
    (fun _ _ => none)
    (fun r _ a => (r.toL ρ₀).bind fun r' => (a.toL ρ₀).map fun a' => (ρ, seqL r' (seqL a' .tt)))
    (fun r a => (r.toL ρ₀).bind fun r' => (a.toL ρ₀).map fun a' => (ρ, seqL r' (seqL a' .tt)))
    (fun _ _ => none) (fun _ => none)

/-- `Upd.toLS`'s compiled twin. -/
def _root_.Solidity.Upd.toLSM (ρ₀ : SymS C Γ) : {Δ : Ctx} → Upd C Γ Δ →
    Option (SymS C Δ × LTm C (.val .bool))
  | _, .nil => some (ρ₀, .tt)
  | _, .snoc U e => (U.toLSM ρ₀).bind fun p => (e.toLS ρ₀ p.1).map fun q => (q.1, seqL p.2 q.2)
  | _, .decl U _ r => (U.toLSM ρ₀).bind fun p => (r.toL ρ₀).map fun b =>
    (p.1.push (some b.1), seqL p.2 b.2)
  | _, .pop U h => (U.toLSM ρ₀).map fun p => (⟨p.1.loc.drop h, p.1.stor, p.1.mem, p.1.next⟩, p.2)
  | _, .drop U h => (U.toLSM ρ₀).map fun p => (⟨p.1.loc.thin h, p.1.stor, p.1.mem, p.1.next⟩, p.2)

/-- **An update pushed in**: the state it leaves and what must return for
it to land; `none` outside the fragment.  By the recursor. -/
@[implemented_by Upd.toLSM]
def _root_.Solidity.Upd.toLS (ρ₀ : SymS C Γ) {Δ : Ctx} (U : Upd C Γ Δ) :
    Option (SymS C Δ × LTm C (.val .bool)) :=
  @Upd.rec C Γ (fun Δ _ => Option (SymS C Δ × LTm C (.val .bool))) (some (ρ₀, .tt))
    (fun {_} _ e ih => ih.bind fun p => (e.toLS ρ₀ p.1).map fun q => (q.1, seqL p.2 q.2))
    (fun {_} {_} _ _ r ih => ih.bind fun p => (r.toL ρ₀).map fun b =>
      (p.1.push (some b.1), seqL p.2 b.2))
    (fun {_} {_} _ h ih => ih.map fun p => (⟨p.1.loc.drop h, p.1.stor, p.1.mem, p.1.next⟩, p.2))
    (fun {_} {_} _ h ih => ih.map fun p => (⟨p.1.loc.thin h, p.1.stor, p.1.mem, p.1.next⟩, p.2))
    Δ U

end Upd

/-! ## Formulas, by position -/

section Fml

/-- The update's guard as a premise (box) or a conjunct (diamond). -/
def guardM : Modality → LTm C (.val .bool) → LFml C → LFml C
  | .box, g, φ => .imp (.eq g g) φ
  | .diamond, g, φ => .and (.eq g g) φ

/-- A term that returns in every state: a literal, a value of the
transaction, a value local. -/
def _root_.Solidity.Tm.retsS {Γ : Ctx} {s : Srt} (t : Tm C Γ s) : Bool :=
  @Tm.casesOn C Γ (fun _ _ => Bool) s t (fun _ => true) (fun _ => false) (fun _ => false)
    (fun _ => false) (fun _ _ => false)
    (fun o => @Op0.casesOn C (fun _ _ => Bool) _ o (fun _ => true) (fun _ => true)
      (fun _ _ _ => false) false false false (fun _ _ _ _ => false) (fun _ => false))
    (fun _ _ => false) (fun _ _ _ => false) (fun _ _ _ _ => false) (fun _ => false)

/-- `eqD a b`: `a` and `b` defined and equal, read as one equation. -/
def _root_.Solidity.Fml.eqDView? {Γ : Ctx} (φ ψ : Fml C Γ) :
    Option ((p : PrimTy) × Tm C Γ (.val p) × Tm C Γ (.val p)) :=
  match φ, ψ with
  | .defined (p := p) a, .and (.defined (p := q) b) (.eq (p := r) a' b') =>
    if h : p = r ∧ q = r then
      if a.beqR a' && b.beqR b' then some ⟨r, h.1 ▸ a, h.2 ▸ b⟩ else none
    else none
  | _, _ => none

/-- `Fml.toLS`'s compiled twin. -/
def _root_.Solidity.Fml.toLSM : {Γ : Ctx} → Bool → SymS C Γ → Fml C Γ → Option (LFml C)
  | _, _, _, .tt => some .tt
  | _, pos, ρ, .eq a b =>
    if pos || (a.retsS && b.retsS) then
      (a.toL ρ).bind fun a' => (b.toL ρ).map fun b' => .eq a' b'
    else none
  | _, _, ρ, .defined t => (t.toL ρ).map fun t' => .eq t' t'
  | _, pos, ρ, .not φ => (φ.toLSM (!pos) ρ).map .not
  | _, pos, ρ, .and φ ψ =>
    match Fml.eqDView? φ ψ with
    | some ⟨_, a, b⟩ => (a.toL ρ).bind fun a' => (b.toL ρ).map fun b' => .eq a' b'
    | none => (φ.toLSM pos ρ).bind fun φ' => (ψ.toLSM pos ρ).map fun ψ' => .and φ' ψ'
  | _, pos, ρ, .imp φ ψ => (φ.toLSM (!pos) ρ).bind fun φ' => (ψ.toLSM pos ρ).map fun ψ' => .imp φ' ψ'
  | _, pos, ρ, .upd m U φ =>
    if pos then (U.toLS ρ).bind fun p => (φ.toLSM pos p.1).map fun φ' => guardM m p.2 φ'
    else none
  | _, pos, _, .modal .. => if pos then some .ff else none
  | _, _, _, .havoc _ => none
  | _, pos, ρ, .all _ p φ => (φ.toLSM pos (ρ.pushQ p)).map fun φ' => .all ρ.next p φ'
  | _, pos, ρ, .bind _ _ _ φ => if pos then φ.toLSM pos (ρ.push none) else none
  | _, _, _, .anon .. => none

/-- **A scoped formula with its updates pushed in**, at the polarity `pos`
(`false` under a negation or on the left of an implication, where only a
first-order formula is taken), its binders' locals the reduction's atoms by
position; `none` outside the fragment.  By the recursor. -/
@[implemented_by Fml.toLSM]
def _root_.Solidity.Fml.toLS {Γ : Ctx} (pos : Bool) (ρ : SymS C Γ) (φ : Fml C Γ) :
    Option (LFml C) :=
  @Fml.rec C (fun Γ _ => Bool → SymS C Γ → Option (LFml C))
    (fun _ _ => some .tt)
    (fun a b pos ρ =>
      if pos || (a.retsS && b.retsS) then
        (a.toL ρ).bind fun a' => (b.toL ρ).map fun b' => .eq a' b'
      else none)
    (fun t _ ρ => (t.toL ρ).map fun t' => .eq t' t')
    (fun _ ih pos ρ => (ih (!pos) ρ).map .not)
    (fun φ ψ ihφ ihψ pos ρ =>
      match Fml.eqDView? φ ψ with
      | some ⟨_, a, b⟩ => (a.toL ρ).bind fun a' => (b.toL ρ).map fun b' => .eq a' b'
      | none => (ihφ pos ρ).bind fun φ' => (ihψ pos ρ).map fun ψ' => .and φ' ψ')
    (fun _ _ ihφ ihψ pos ρ => (ihφ (!pos) ρ).bind fun φ' => (ihψ pos ρ).map fun ψ' => .imp φ' ψ')
    (fun m U _ ih pos ρ =>
      if pos then (U.toLS ρ).bind fun p => (ih pos p.1).map fun φ' => guardM m p.2 φ'
      else none)
    (fun _ _ _ _ _ pos _ => if pos then some .ff else none)
    (fun _ _ _ _ => none)
    (fun _ p _ ih pos ρ => (ih pos (ρ.pushQ p)).map fun φ' => .all ρ.next p φ')
    (fun _ _ _ _ ih pos ρ => if pos then ih pos (ρ.push none) else none)
    (fun _ _ _ _ _ => none) _ φ pos ρ

/-- **What `sol_decide` proves of a scoped leaf**: its updates pushed in by
position, the reads of writes eliminated (`LFml.elim`); `none` outside the
fragment. -/
def _root_.Solidity.Fml.reduceS (φ : Fml C []) : Option (LFml C) :=
  (φ.toLS true SymS.init).map LFml.elim

end Fml

end Decide

end Solidity
