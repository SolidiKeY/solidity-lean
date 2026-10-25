import Solidity.Calculus.Decide
import Solidity.Calculus.ReadBounds
import Solidity.Calculus.TermEq
import Solidity.Calculus.TermAgree
import Solidity.Calculus.MemRead

/-!
# The reduction on a scoped leaf

`sol_decide` on a scoped leaf `Fml.Valid φ` (`φ : Fml C []`) pushes its updates
into the formula (`Fml.toLS`, mini-solkey's `Fml.applyUpds`): a term of
the reduction is the scoped term with its locals, `storage` and `memory`
replaced by what the updates bound them to, read in the state the leaf
starts in.  The reduction's terms are the typed signature's (`LTm`,
`Calculus/DecideLang.lean`), so a scoped term is pushed in symbol by
symbol (`Tm.toL`): the symbols read their arguments as the scoped term's
do.  Two symbols read the state they are read in, and are pushed in onto
the storage the updates left: an index checked (`at`, onto `atIn`) and
the slot past an array's end (`next`, onto `nextIn`).  Where the check, or
the length, reads as a literal there (`foldAt`, `foldNext`), the index is
the plain `q[i]`: solkey closes `inBounds` at the statement too, and a path
that kept the storage would be copied by every later write that reads it.

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

The fragment is where `Fml.toLS` returns: a ledger write (`net`, `pay`,
`netMt`: the reduction keeps no ledger), a balance moved by `selfBalance :=
selfBalance ± a`, a snapshot of an empty ledger, a `select`, `havoc` and
`anon` are outside it.  So the ledger is the start state's throughout: a
ledger read is `net(a)` of the start state (`LTm.app1 .net`), and so is a
read `x[a]` of a snapshot `x := net` (`Tm.netOf`, `Rhs.saveNet`).  A
deployment's `selfBalance := a` sets the balance the state reads
(`SymS.bal`, `SymS.envL`).  It has a polarity: under a negation or on the left of an
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

theorem thin_eq_thinM {Γ Δ : Ctx} (h : Thin Γ Δ) (e : BEnv C Δ) :
    BEnv.thin h e = BEnv.thinM h e := by
  induction h with
  | refl => rfl
  | keep h ih | drop h ih => simp only [BEnv.thinM, ← ih]; rfl

end BEnv

/-- The updates so far, by position: what each local is bound to, the
storage, the memory and the contract's balance they left, the next
position a binder takes, and whether the ledger is still the start
state's (no ledger write so far: a ledger read is then `net(a)` of the
start state). -/
structure SymS (C : Contract) (Γ : Ctx) where
  loc : BEnv C Γ
  stor : LTm C .st
  mem : LTm C .mem
  bal : LTm C (.val .uint)
  next : Nat
  netOk : Bool

/-- No update yet, no local. -/
def SymS.init : SymS C [] :=
  ⟨(), .app0 .storage, .app0 .memory, .app0 (.env .selfBalance), 0, true⟩

/-- An environment value read in `ρ`: the balance the updates left, the
transaction's values as they are. -/
def SymS.envL {Γ : Ctx} (ρ : SymS C Γ) : EnvKey → LTm C (.val .uint)
  | .selfBalance => ρ.bal
  | k => .app0 (.env k)

/-- A local pushed, bound to `b` (or to nothing). -/
def SymS.push {Γ : Ctx} {t : LTy} (ρ : SymS C Γ) (b : Option (LTm C t.bs)) : SymS C (t :: Γ) :=
  ⟨(b, ρ.loc), ρ.stor, ρ.mem, ρ.bal, ρ.next + 1, ρ.netOk⟩

/-- A quantifier's local pushed: the atom of its position. -/
def SymS.pushQ {Γ : Ctx} (p : PrimTy) (ρ : SymS C Γ) : SymS C (.val p :: Γ) :=
  ρ.push (t := .val p) (some (.var ρ.next))

/-- A hidden binder's local pushed: a value binds the atom of its position,
as a quantifier does (it reads as one, `Fml.toLS`); any other local is
unknown until an update binds it. -/
def SymS.pushB {Γ : Ctx} (t : LTy) (ρ : SymS C Γ) : SymS C (t :: Γ) :=
  match t with
  | .val p => ρ.pushQ p
  | _ => ρ.push none

/-! ## Terms, by position -/

section Terms

variable {Γ : Ctx}

/-- A constant pushed in: `storage` and `memory` the updates left. -/
def _root_.Solidity.Op0.toL (ρ : SymS C Γ) {s : Srt} (o : Op0 C s) : Option (LTm C s) :=
  @Op0.casesOn C (fun s _ => Option (LTm C s)) s o
    (fun v => some (.app0 (.lit v))) (fun k => some (ρ.envL k))
    (fun r {_} h => some (.app0 (.root r h))) (some ρ.stor) (some ρ.mem)
    (some (.app0 .mtSt)) (fun s f {_} h => some (.app0 (.member s f h)))
    (fun n => some (.app0 (.zlit n)))

/-- Keep symbolic reads in their original form so later antecedents can normalize them.
Over a history not known, only through at most `exposeBound` exposing
updates: past them the elimination grows sevenfold with each. -/
def LTm.literalRead {p : PrimTy} (t : LTm C (.val p)) : LTm C (.val p) :=
  if t.boundsOk && (t.known?.isSome || decide (t.exposeDepth ≤ exposeBound)) then
    let r := t.elim
    if r.litV?.isSome then r else t
  else t

/-- Apply the existing memory taclets before a later write duplicates a demanded
read. The input has an explicit node bound; the retained result cannot be larger. -/
def foldMem2 {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) : LTm C s :=
  let original := LTm.app2 o x y
  match original.fits normalizationSize with
  | some remaining =>
    let reduced := o.memRes x y
    if (reduced.fits (normalizationSize - remaining)).isSome then reduced else original
  | none => original

/-- Resolve demanded storage and memory observations before later writes
duplicate them. The stores themselves remain lazy terms. -/
def foldRead2 {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) : LTm C s :=
  match o with
  | .find => (LTm.app2 .find x y).literalRead
  | .len => (LTm.app2 .len x y).literalRead
  | .read => foldMem2 .read x y
  | .mlen => foldMem2 .mlen x y
  | .iread => foldMem2 .iread x y
  | .copy h => foldMem2 (.copy h) x y
  | o => fold2 o x y

/-- A storage worth reading at a formation: within `concreteSize` nodes,
its history concrete (`LTm.known?`).  Elsewhere a read may grow with the
history, and the checked index stays lazy. -/
def LTm.foldable (S : LTm C .st) : Bool :=
  (S.fits concreteSize).isSome && S.known?.isSome

/-- `q[i]` checked in the storage `S` (`atIn`), unchecked where the check
reads as `true`: solkey's `inBounds` branch closed at the statement, the
index a plain `at(i)`.  The path then no longer carries the storage it was
checked in, which each later write would otherwise copy. -/
def foldAt {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) (S : LTm C .st)
    (q : LTm C (.path (.ref R))) (i : LTm C (.val k)) : LTm C (.path V) :=
  if S.foldable then
    match (LTm.seq (.app3 (.atIn it) S q i) LTm.tt).literalRead.litV? with
    | some true => .index it q i
    | _ => .app3 (.atIn it) S q i
  else .app3 (.atIn it) S q i

/-- `q[q.length]` in the storage `S` (`nextIn`), at a literal index where
the length reads as one (`foldAt`'s reason). -/
def foldNext {E : Ty} (S : LTm C .st) (q : LTm C (.path (.ref (.array E)))) :
    LTm C (.path E) :=
  if S.foldable then
    match (LTm.app2 .len S q).literalRead.litV? with
    | some n => .index (.arr .dyn) q (.lit n)
    | none => .app2 .nextIn S q
  else .app2 .nextIn S q

/-- A unary symbol pushed in: an operator folded on a literal, `next`
onto the storage the updates left; a read of the ledger as the start
state's (the fragment writes no ledger, `UpdElem.toLS`). -/
def _root_.Solidity.Op1.toL (ρ : SymS C Γ) {a s : Srt} (o : Op1 C a s) (x : LTm C a) :
    Option (LTm C s) :=
  @Op1.casesOn C (fun a s _ => LTm C a → Option (LTm C s)) a s o
    (fun op {_} h x => some (fold1 (.unop op h) x))
    (fun x => if ρ.netOk then some (.app1 .net x) else none)
    (fun {_} x => some (.app1 .delValue x))
    (fun {_} {_} {_} h x => some (.app1 (.field h) x))
    (fun {_} x => some (foldNext ρ.stor x))
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
    (fun x => some (.app1 .toInt x))
    (fun {_} {_} {_} shape x => some (.app1 (.fixedCopy shape) x))
    (fun x => some (.app1 .cleanTail x)) x

/-- A binary symbol pushed in: an operator folded on literals, a checked
index onto the storage the updates left (`atIn`). -/
def _root_.Solidity.Op2.toL (ρ : SymS C Γ) {a b s : Srt} (o : Op2 C a b s) (x : LTm C a)
    (y : LTm C b) : Option (LTm C s) :=
  @Op2.casesOn C (fun a b s _ => LTm C a → LTm C b → Option (LTm C s)) a b s o
    (fun op {_} h x y => some (fold2 (.binop op h) x y))
    (fun {_} x y => some (foldRead2 .find x y))
    (fun {_} x y => some (foldRead2 .len x y))
    (fun {_} x y => some (foldRead2 .read x y))
    (fun {_} x y => some (foldRead2 .mlen x y))
    (fun {_} {_} {_} it x y => some (foldAt it ρ.stor x y))
    (fun {_} x y => some (.app2 .nextIn x y))
    (fun {_} x y => some (.app2 .delAt x y))
    (fun {_} x y => some (.app2 .pushSlot x y))
    (fun {_} x y => some (.app2 .pop x y))
    (fun {_} x y => some (.app2 .shrink x y))
    (fun {_} x y => some (.app2 .extend x y))
    (fun {_} x y => some (.app2 .sfind x y))
    (fun {_} x y => some (.app2 .copyMem x y))
    (fun {_} x y => some (foldRead2 .iread x y))
    (fun {_} h x y => some (foldRead2 (.copy h) x y))
    (fun {_} {_} a x y => some (.app2 (.mat a) x y))
    (fun {_} h x y => some (.app2 (.copySt h) x y))
    (fun {_} {_} x y => some (.app2 .findIn x y))
    (fun {_} {_} x y => some (.app2 .delAtIn x y))
    (fun {_} {_} x y => some (.app2 .sfindIn x y))
    (fun op h x y => some (.app2 (.zbin op h) x y))
    (fun op h x y => some (.app2 (.zcmp op h) x y))
    (fun {_} k x y => some (.app2 (.hash k) x y))
    (fun L x y => some (.app2 (.anon L) x y)) x y

/-- A ternary symbol, an index checked in a storage it names (`atIn`)
folded as `foldAt`. -/
def foldRead3 {a b c s : Srt} (o : Op3 C a b c s) (x : LTm C a) (y : LTm C b) (z : LTm C c) :
    LTm C s :=
  match o with
  | .atIn it => foldAt it x y z
  | o => .app3 o x y z

/-- A ternary symbol pushed in. -/
def _root_.Solidity.Op3.toL {a b c s : Srt} (o : Op3 C a b c s) (x : LTm C a) (y : LTm C b)
    (z : LTm C c) : Option (LTm C s) :=
  some (foldRead3 o x y z)

/-- `Tm.toL`'s compiled twin. -/
def _root_.Solidity.Tm.toLM (ρ : SymS C Γ) : {s : Srt} → Tm C Γ s → Option (LTm C s)
  | _, .pvV i => ρ.loc.get i
  | _, .pvP i => ρ.loc.get i
  | _, .pvS i => ρ.loc.get i
  | _, .pvI i => ρ.loc.get i
  | _, .netOf i a => (ρ.loc.get i).bind fun _ => (a.toLM ρ).map (LTm.app1 .net)
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
    (fun {_} i => ρ.loc.get i) (fun i _ ia => (ρ.loc.get i).bind fun _ => ia.map (LTm.app1 .net))
    (fun o => o.toL ρ)
    (fun o _ ix => ix.bind (o.toL ρ))
    (fun o _ _ ix iy => ix.bind fun x' => iy.bind (o.toL ρ x'))
    (fun o _ _ _ ix iy iz => ix.bind fun x' => iy.bind fun y' => iz.bind (o.toL x' y'))
    (fun i => ρ.loc.get i) s t

theorem _root_.Solidity.Tm.toL_eq_toLM (ρ : SymS C Γ) {s : Srt} (t : Tm C Γ s) :
    t.toL ρ = t.toLM ρ := by
  induction t with
  | pvV | pvP | pvS | pvI | app0 | pvZ => rfl
  | netOf i a ih => simp only [Tm.toLM, ← ih]; rfl
  | app1 o x ih => simp only [Tm.toLM, ← ih]; rfl
  | app2 o x y ihx ihy => simp only [Tm.toLM, ← ihx, ← ihy]; rfl
  | app3 o x y z ihx ihy ihz => simp only [Tm.toLM, ← ihx, ← ihy, ← ihz]; rfl

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
    -- A snapshot taken before any ledger write is of the start state's ledger.
    (if ρ.netOk then some (.app0 (.zlit 0), .tt) else none) none
    (fun x => (x.toL ρ).map fun x' => (x', seqL x' .tt))

/-- One element applied to the state `ρ`, read in `ρ₀`; its guard. -/
def _root_.Solidity.UpdElem.toLS {Δ : Ctx} (ρ₀ : SymS C Γ) (e : UpdElem C Γ Δ) (ρ : SymS C Δ) :
    Option (SymS C Δ × LTm C (.val .bool)) :=
  @UpdElem.casesOn C Γ Δ (fun _ => Option (SymS C Δ × LTm C (.val .bool))) e
    (fun {_} i r => (r.toL ρ₀).map fun b =>
      (⟨ρ.loc.set i (some b.1), ρ.stor, ρ.mem, ρ.bal, ρ.next, ρ.netOk⟩, b.2))
    (fun s => (s.toL ρ₀).map fun s' => (⟨ρ.loc, s', ρ.mem, ρ.bal, ρ.next, ρ.netOk⟩, seqL s' .tt))
    (fun m => (m.toL ρ₀).map fun m' => (⟨ρ.loc, ρ.stor, m', ρ.bal, ρ.next, ρ.netOk⟩, seqMemL m' .tt))
    (fun _ _ => none)
    -- A ledger write is kept only as no longer the start state's ledger:
    -- a ledger read past it is outside the fragment (`Op1.toL`).
    (fun r _ a => (r.toL ρ₀).bind fun r' => (a.toL ρ₀).map fun a' =>
      (⟨ρ.loc, ρ.stor, ρ.mem, ρ.bal, ρ.next, false⟩, seqL r' (seqL a' .tt)))
    -- Payments change the balance, which the old no-op encoding omitted.
    -- Leave them to semantic closing until this fragment represents that change.
    (fun _ _ => none)
    (fun r a => (r.toL ρ₀).bind fun r' => (a.toL ρ₀).map fun a' =>
      (⟨ρ.loc, ρ.stor, ρ.mem, ρ.bal, ρ.next, false⟩, seqL r' (seqL a' .tt)))
    (fun a => (a.toL ρ₀).map fun a' => (⟨ρ.loc, ρ.stor, ρ.mem, a', ρ.next, ρ.netOk⟩, seqL a' .tt))

/-- `Upd.toLS`'s compiled twin. -/
def _root_.Solidity.Upd.toLSM (ρ₀ : SymS C Γ) : {Δ : Ctx} → Upd C Γ Δ →
    Option (SymS C Δ × LTm C (.val .bool))
  | _, .nil => some (ρ₀, .tt)
  | _, .snoc U e => (U.toLSM ρ₀).bind fun p => (e.toLS ρ₀ p.1).map fun q => (q.1, seqL p.2 q.2)
  | _, .decl U _ r => (U.toLSM ρ₀).bind fun p => (r.toL ρ₀).map fun b =>
    (p.1.push (some b.1), seqL p.2 b.2)
  | _, .pop U h => (U.toLSM ρ₀).map fun p => (⟨p.1.loc.drop h, p.1.stor, p.1.mem, p.1.bal, p.1.next, p.1.netOk⟩, p.2)
  | _, .drop U h => (U.toLSM ρ₀).map fun p => (⟨p.1.loc.thin h, p.1.stor, p.1.mem, p.1.bal, p.1.next, p.1.netOk⟩, p.2)

/-- **An update pushed in**: the state it leaves and what must return for
it to land; `none` outside the fragment.  By the recursor. -/
@[implemented_by Upd.toLSM]
def _root_.Solidity.Upd.toLS (ρ₀ : SymS C Γ) {Δ : Ctx} (U : Upd C Γ Δ) :
    Option (SymS C Δ × LTm C (.val .bool)) :=
  @Upd.rec C Γ (fun Δ _ => Option (SymS C Δ × LTm C (.val .bool))) (some (ρ₀, .tt))
    (fun {_} _ e ih => ih.bind fun p => (e.toLS ρ₀ p.1).map fun q => (q.1, seqL p.2 q.2))
    (fun {_} {_} _ _ r ih => ih.bind fun p => (r.toL ρ₀).map fun b =>
      (p.1.push (some b.1), seqL p.2 b.2))
    (fun {_} {_} _ h ih => ih.map fun p => (⟨p.1.loc.drop h, p.1.stor, p.1.mem, p.1.bal, p.1.next, p.1.netOk⟩, p.2))
    (fun {_} {_} _ h ih => ih.map fun p => (⟨p.1.loc.thin h, p.1.stor, p.1.mem, p.1.bal, p.1.next, p.1.netOk⟩, p.2))
    Δ U

theorem _root_.Solidity.Upd.toLS_eq_toLSM (ρ₀ : SymS C Γ) {Δ : Ctx} (U : Upd C Γ Δ) :
    U.toLS ρ₀ = U.toLSM ρ₀ := by
  induction U with
  | nil => rfl
  | snoc U e ih | decl U _ r ih | pop U h ih | drop U h ih => simp only [Upd.toLSM, ← ih]; rfl

/-- The array at `q` of `st` is full (`Storage.full`): `2^256 - 1` live
elements. -/
def fullL (st : LTm C .st) {E : Ty} (q : LTm C (.path (.ref (.array E)))) : LTm C (.val .bool) :=
  .app2 (.binop .eqB rfl) (.app2 .len st q) (.lit (uintOfNat (2 ^ 256 - 1)))

/-- `Tm.exhL` at a binary symbol: `pushSlot`, `extend`. -/
def _root_.Solidity.Op2.exhL (ρ : SymS C Γ) {a b s : Srt} (o : Op2 C a b s) (x : Tm C Γ a)
    (y : Tm C Γ b) : Option (LTm C (.val .bool)) :=
  match o, x, y with
  | .pushSlot, st, q | .extend, st, q =>
    (st.toL ρ).bind fun st' => (q.toL ρ).map fun q' => fullL st' q'
  | _, _, _ => none

/-- `Tm.exhL` at a ternary symbol: `push`, its value returning. -/
def _root_.Solidity.Op3.exhL (ρ : SymS C Γ) {a b c s : Srt} (o : Op3 C a b c s) (x : Tm C Γ a)
    (y : Tm C Γ b) (z : Tm C Γ c) : Option (LTm C (.val .bool)) :=
  match o, x, y, z with
  | .push, st, q, v =>
    (st.toL ρ).bind fun st' => (q.toL ρ).bind fun q' => (v.toL ρ).map fun v' =>
      .kite (fullL st' q') .tt (seqL v' .tt) (.lit (p := .bool) false)
  | _, _, _, _ => none

/-- **A push out of gas, read**: a word that is `true` where the storage
term is a push at a full array, its arguments returning (`Tm.exhB`). -/
def _root_.Solidity.Tm.exhL (ρ : SymS C Γ) {s : Srt} (t : Tm C Γ s) : Option (LTm C (.val .bool)) :=
  match t with
  | .app2 o x y => o.exhL ρ x y
  | .app3 o x y z => o.exhL ρ x y z
  | _ => none

/-- A push paired with a local binding: exhaustion is accepted only where
the parallel binding's right-hand side returns in the original state. -/
def pushLocalExhL (ρ : SymS C Γ) {t : LTy} (s : Tm C Γ .st) (r : Rhs C Γ t) :
    Option (LTm C (.val .bool)) := do
  let X ← s.exhL ρ
  let b ← r.toL ρ
  some (seqL b.2 X)

/-- **An update out of gas, read** (`Upd.exh`): a single push, or a push
paired with a returning local binding, at a full array. -/
def _root_.Solidity.Upd.exhL (ρ₀ : SymS C Γ) {Δ : Ctx} (U : Upd C Γ Δ) : Option (LTm C (.val .bool)) :=
  match U with
  | .snoc .nil (.storage s) => s.exhL ρ₀
  | .snoc (.snoc .nil (.storage s)) (.local _ r) => pushLocalExhL ρ₀ s r
  | _ => none

end Upd

/-! ## Formulas, by position -/

section Fml

/-- The update's guard as a premise (box) or a conjunct (diamond); under
the diamond, where the update is a push that may be out of gas (`X`, the
array full: `Upd.exh`, which both modalities accept), the guard is asked
only where it is not, and what follows only where the update lands. -/
def guardM : Modality → Option (LTm C (.val .bool)) → LTm C (.val .bool) → LFml C → LFml C
  | .box, _, g, φ => .imp (.eq g g) φ
  | .diamond, none, g, φ => .and (.eq g g) φ
  | .diamond, some X, g, φ => .and (.imp (.not (.eq X .tt)) (.eq g g)) (.imp (.eq g g) φ)

/-- A term that returns in every state: a literal, a value of the
transaction, a value local. -/
def _root_.Solidity.Tm.retsS {Γ : Ctx} {s : Srt} (t : Tm C Γ s) : Bool :=
  @Tm.casesOn C Γ (fun _ _ => Bool) s t (fun _ => true) (fun _ => false) (fun _ => false)
    (fun _ => false) (fun _ _ => false)
    (fun o => @Op0.casesOn C (fun _ _ => Bool) _ o (fun _ => true) (fun _ => true)
      (fun _ _ _ => false) false false false (fun _ _ _ _ => false) (fun _ => false))
    (fun _ _ => false) (fun _ _ _ => false) (fun _ _ _ _ => false) (fun _ => false)

/-- `a` and `b` return one value or both halt: the equation of two
`Option`s, in the reduction's language. -/
def _root_.Solidity.LFml.optEq {p : PrimTy} (a b : LTm C (.val p)) : LFml C :=
  .and (.imp (.eq a a) (.imp (.eq b b) (.eq a b))) (.and (.imp (.eq a a) (.eq b b))
    (.imp (.eq b b) (.eq a a)))

/-- A Theory equation `a = b` read by the interpreter.  Exactly, at either
polarity, where the Theory reads both sides as the interpreter does
(`Tm.agreeB`): their equation where one of them returns (`Tm.totB`), the
equation of their typed readings, a halt included, otherwise.  Otherwise as its equation where it is a
goal (`pos`), which implies it; as a hypothesis, that the sides are equal
where they both return, which it implies (`Tm.denote_eval`). -/
def _root_.Solidity.Fml.eqAt {Γ : Ctx} {p : PrimTy} (pos : Bool) (a b : Tm C Γ (.val p))
    (a' b' : LTm C (.val p)) : LFml C :=
  if a.agreeB && b.agreeB then
    if a.totB || b.totB then .eq a' b' else LFml.optEq a' b'
  else if pos then .eq a' b'
  else .imp (.eq a' a') (.imp (.eq b' b') (.eq a' b'))

/-- `Fml.toLS`'s compiled twin. -/
def _root_.Solidity.Fml.toLSM : {Γ : Ctx} → Bool → SymS C Γ → Fml C Γ → Option (LFml C)
  | _, _, _, .tt => some .tt
  | _, pos, ρ, .eq a b => (a.toL ρ).bind fun a' => (b.toL ρ).map fun b' => Fml.eqAt pos a b a' b'
  | _, _, ρ, .wellFormed s => ((Tm.app1 .wt s).toL ρ).map fun t' => .eq t' t'
  | _, pos, ρ, .not φ => (φ.toLSM (!pos) ρ).map .not
  | _, pos, ρ, .and φ ψ =>
    (φ.toLSM pos ρ).bind fun φ' => (ψ.toLSM pos ρ).map fun ψ' => .and φ' ψ'
  | _, pos, ρ, .imp φ ψ => (φ.toLSM (!pos) ρ).bind fun φ' => (ψ.toLSM pos ρ).map fun ψ' => .imp φ' ψ'
  | _, pos, ρ, .upd m U φ =>
    if pos then (U.toLS ρ).bind fun p => (φ.toLSM pos p.1).map fun φ' => guardM m (U.exhL ρ) p.2 φ'
    else some .tt
  | _, pos, _, .modal .. => if pos then some .ff else some .tt
  | _, pos, _, .havoc _ => if pos then none else some .tt
  | _, pos, ρ, .all _ p φ => (φ.toLSM pos (ρ.pushQ p)).map fun φ' => .all ρ.next p φ'
  | _, pos, ρ, .bind _ _ t φ =>
    if pos then (φ.toLSM pos (ρ.pushB t)).map (LFml.allB t ρ.next) else none
  | _, pos, _, .anon .. => if pos then none else some .tt
  | _, pos, _, .allocAll .. => if pos then some .ff else some .tt
  | _, pos, _, .grow .. => if pos then none else some .tt

/-- **A scoped formula with its updates pushed in**, at the polarity `pos`
(`false` under a negation or on the left of an implication, where only a
first-order formula is taken), its binders' locals the reduction's atoms by
position; `none` outside the fragment.  By the recursor. -/
@[implemented_by Fml.toLSM]
def _root_.Solidity.Fml.toLS {Γ : Ctx} (pos : Bool) (ρ : SymS C Γ) (φ : Fml C Γ) :
    Option (LFml C) :=
  @Fml.rec C (fun Γ _ => Bool → SymS C Γ → Option (LFml C))
    (fun _ _ => some .tt)
    (fun a b pos ρ => (a.toL ρ).bind fun a' => (b.toL ρ).map fun b' => Fml.eqAt pos a b a' b')
    (fun s _ ρ => ((Tm.app1 .wt s).toL ρ).map fun t' => .eq t' t')
    (fun _ ih pos ρ => (ih (!pos) ρ).map .not)
    (fun _ _ ihφ ihψ pos ρ => (ihφ pos ρ).bind fun φ' => (ihψ pos ρ).map fun ψ' => .and φ' ψ')
    (fun _ _ ihφ ihψ pos ρ => (ihφ (!pos) ρ).bind fun φ' => (ihψ pos ρ).map fun ψ' => .imp φ' ψ')
    (fun m U _ ih pos ρ =>
      if pos then (U.toLS ρ).bind fun p => (ih pos p.1).map fun φ' => guardM m (U.exhL ρ) p.2 φ'
      else some .tt)
    (fun _ _ _ _ _ pos _ => if pos then some .ff else some .tt)
    (fun _ _ pos _ => if pos then none else some .tt)
    (fun _ p _ ih pos ρ => (ih pos (ρ.pushQ p)).map fun φ' => .all ρ.next p φ')
    (fun _ _ t _ ih pos ρ => if pos then (ih pos (ρ.pushB t)).map (LFml.allB t ρ.next) else none)
    (fun _ _ _ pos _ => if pos then none else some .tt)
    (fun _ _ _ _ pos _ => if pos then some .ff else some .tt)
    (fun _ _ pos _ => if pos then none else some .tt) _ φ pos ρ

theorem _root_.Solidity.Fml.toLS_eq_toLSM {Γ : Ctx} (pos : Bool) (ρ : SymS C Γ) (φ : Fml C Γ) :
    φ.toLS pos ρ = φ.toLSM pos ρ := by
  induction φ generalizing pos with
  | tt | eq | wellFormed | modal | havoc | anon | allocAll | grow => rfl
  | not φ ih | all x p φ ih | bind m x t φ ih | upd m U φ ih =>
    simp only [Fml.toLSM, ← ih]; rfl
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ => simp only [Fml.toLSM, ← ihφ, ← ihψ]; rfl

/-- **What `sol_decide` proves of a scoped leaf**: its updates pushed in by
position, the reads of writes eliminated (`LFml.elim`); `none` outside the
fragment. -/
def _root_.Solidity.Fml.reduceS (φ : Fml C []) : Option (LFml C) :=
  (φ.toLS true SymS.init).map LFml.elim

end Fml

end Decide

end Solidity
