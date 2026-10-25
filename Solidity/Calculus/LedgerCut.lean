import Solidity.Calculus.QuotientCut

/-!
# Ledger reads cut to reads at fresh constants (M7, plan step 3)

A leaf reads the ledger of the state it starts in (`net(a)`, `LTm.app1
.net`; `Calculus/DecideScoped.lean`), a KeY `int` per address, unbounded.
`LFml.ledgerCut` replaces the `j`-th read `net(aⱼ)` by `aⱼ` then the read
at the constant `j` (`seq aⱼ (net(j))`), and puts the functional
consistency of the reads in the antecedent: `aᵢ == aⱼ → net(i) == net(j)`.
The reads at constants are then atoms of the arithmetic (two natural codes
each, `Calculus/LedgerArithmetic.lean`).

The cut is exact in a universal reading (`LFml.ledgerCut_valid_iff`), and a
state refuting the cut leaf gives one refuting the leaf, its ledger the
reads pulled back to their addresses (`LFml.ledgerCut_refutes`).  It needs
every address to read no ledger itself (`LFml.netOK`), and the reads fewer
than `2^256`, so that their constants are distinct addresses.
-/

namespace Solidity.Decide

open Semantics

variable {C : Contract}

/-- `net`. -/
def _root_.Solidity.Op1.isNetB {a s : Srt} : Op1 C a s → Bool
  | .net => true
  | _ => false

/-! ## Terms that read no ledger -/

/-- A term that reads no ledger. -/
def LTm.netFree : {s : Srt} → LTm C s → Bool
  | _, .var _ | _, .app0 _ | _, .err => true
  | _, .app1 o a => !o.isNetB && a.netFree
  | _, .app2 _ a b | _, .index _ a b | _, .seq a b | _, .orElse a b => a.netFree && b.netFree
  | _, .app3 _ a b c => a.netFree && b.netFree && c.netFree
  | _, .obsW a | _, .obsL a | _, .obsH a => a.netFree
  | _, .kite a b t e => a.netFree && b.netFree && t.netFree && e.netFree

/-- The state `g` with the ledger `l`. -/
abbrev State.withLedger (g : State C []) (l : Ledger) : State C [] := { g with net := l }

theorem Op1.eval_withLedger (g : State C []) (l : Ledger) {a s : Srt} (o : Op1 C a s)
    (h : o.isNetB = false) (x : Option (a.Den C g.H)) :
    o.eval (State.withLedger g l) x = o.eval g x := by
  cases o <;> first | rfl | (simp only [Op1.isNetB, Bool.true_eq_false] at h)

theorem LTm.eval_withLedger (g : State C []) (l : Ledger) (ν : AEnv) {s : Srt} (t : LTm C s)
    (h : t.netFree = true) : t.eval (State.withLedger g l) ν = t.eval g ν := by
  induction t with
  | var k => rfl
  | app0 o => cases o <;> rfl
  | err => rfl
  | app1 o a ih =>
    simp only [LTm.netFree, Bool.and_eq_true, Bool.not_eq_true'] at h
    rw [LTm.eval_app1, LTm.eval_app1, ih h.2]
    exact Op1.eval_withLedger g l o h.1 _
  | app2 o a b iha ihb =>
    simp only [LTm.netFree, Bool.and_eq_true] at h
    rw [LTm.eval_app2, LTm.eval_app2, iha h.1, ihb h.2]
    cases o <;> rfl
  | app3 o a b c iha ihb ihc =>
    simp only [LTm.netFree, Bool.and_eq_true] at h
    rw [LTm.eval_app3, LTm.eval_app3, iha h.1.1, ihb h.1.2, ihc h.2]
    cases o <;> rfl
  | index it a b iha ihb =>
    simp only [LTm.netFree, Bool.and_eq_true] at h
    rw [LTm.eval_index, LTm.eval_index, iha h.1, ihb h.2]
  | obsW a ih => simp only [LTm.netFree] at h; rw [LTm.eval_obsW, LTm.eval_obsW, ih h]
  | obsL a ih => simp only [LTm.netFree] at h; rw [LTm.eval_obsL, LTm.eval_obsL, ih h]
  | obsH a ih => simp only [LTm.netFree] at h; rw [LTm.eval_obsH, LTm.eval_obsH, ih h]
  | seq a b iha ihb =>
    simp only [LTm.netFree, Bool.and_eq_true] at h
    rw [LTm.eval_seq, LTm.eval_seq, iha h.1, ihb h.2]
  | orElse a b iha ihb =>
    simp only [LTm.netFree, Bool.and_eq_true] at h
    rw [LTm.eval_orElse, LTm.eval_orElse, iha h.1, ihb h.2]
  | kite a b t e iha ihb iht ihe =>
    simp only [LTm.netFree, Bool.and_eq_true] at h
    rw [LTm.eval_kite, LTm.eval_kite, iha h.1.1.1, ihb h.1.1.2, iht h.1.2, ihe h.2]

/-! ## The cut of a term -/

/-- The constant the `j`-th read is moved to. -/
abbrev netConst (j : Nat) : PrimTy.uint.Denote := uintOfNat j

/-- The read at the constant `j`. -/
abbrev LTm.netAt (j : Nat) : LTm C .kint := .app1 .net (.app0 (.lit (netConst j)))

/-- A unary node over its operand's cut, the next constant `n`: a ledger
read becomes its address then the read at `n`. -/
def cutNet1 {a s : Srt} (o : Op1 C a s) (x : LTm C a) (n : Nat) : LTm C s × Nat :=
  match a, s, o, x with
  | _, _, .net, x => (.seq x (LTm.netAt n), n + 1)
  | _, _, o, x => (.app1 o x, n)

/-- The address of a unary node that reads the ledger. -/
def read1 {a s : Srt} (o : Op1 C a s) (x : LTm C a) : List (LTm C (.val .uint)) :=
  match a, s, o, x with
  | _, _, .net, x => [x]
  | _, _, _, _ => []

/-- **The cut of a term**, its constants from `n`: the term and the next
constant. -/
def LTm.netCut : {s : Srt} → LTm C s → Nat → LTm C s × Nat
  | _, .var k, n => (.var k, n)
  | _, .app0 o, n => (.app0 o, n)
  | _, .err, n => (.err, n)
  | _, .app1 o a, n => let A := a.netCut n; cutNet1 o A.1 A.2
  | _, .app2 o a b, n => let A := a.netCut n; let B := b.netCut A.2; (.app2 o A.1 B.1, B.2)
  | _, .app3 o a b c, n =>
    let A := a.netCut n; let B := b.netCut A.2; let D := c.netCut B.2
    (.app3 o A.1 B.1 D.1, D.2)
  | _, .index it a b, n => let A := a.netCut n; let B := b.netCut A.2; (.index it A.1 B.1, B.2)
  | _, .obsW a, n => let A := a.netCut n; (.obsW A.1, A.2)
  | _, .obsL a, n => let A := a.netCut n; (.obsL A.1, A.2)
  | _, .obsH a, n => let A := a.netCut n; (.obsH A.1, A.2)
  | _, .seq a b, n => let A := a.netCut n; let B := b.netCut A.2; (.seq A.1 B.1, B.2)
  | _, .orElse a b, n => let A := a.netCut n; let B := b.netCut A.2; (.orElse A.1 B.1, B.2)
  | _, .kite a b t e, n =>
    let A := a.netCut n; let B := b.netCut A.2; let T := t.netCut B.2; let E := e.netCut T.2
    (.kite A.1 B.1 T.1 E.1, E.2)

/-- The addresses of a term's ledger reads, in the order of their constants. -/
def LTm.netReads : {s : Srt} → LTm C s → List (LTm C (.val .uint))
  | _, .var _ | _, .app0 _ | _, .err => []
  | _, .app1 o a => a.netReads ++ read1 o a
  | _, .app2 _ a b | _, .index _ a b | _, .seq a b | _, .orElse a b => a.netReads ++ b.netReads
  | _, .app3 _ a b c => a.netReads ++ b.netReads ++ c.netReads
  | _, .obsW a | _, .obsL a | _, .obsH a => a.netReads
  | _, .kite a b t e => a.netReads ++ b.netReads ++ t.netReads ++ e.netReads

/-- Every ledger read's address reads no ledger. -/
def LTm.netOK : {s : Srt} → LTm C s → Bool
  | _, .var _ | _, .app0 _ | _, .err => true
  | _, .app1 o a => a.netOK && (!o.isNetB || a.netFree)
  | _, .app2 _ a b | _, .index _ a b | _, .seq a b | _, .orElse a b => a.netOK && b.netOK
  | _, .app3 _ a b c => a.netOK && b.netOK && c.netOK
  | _, .obsW a | _, .obsL a | _, .obsH a => a.netOK
  | _, .kite a b t e => a.netOK && b.netOK && t.netOK && e.netOK

theorem cutNet1_snd {a s : Srt} (o : Op1 C a s) (x : LTm C a) (n : Nat) :
    (cutNet1 o x n).2 = n + (read1 o x).length := by
  cases o <;> rfl

theorem LTm.netCut_snd {s : Srt} (t : LTm C s) (n : Nat) :
    (t.netCut n).2 = n + t.netReads.length := by
  induction t generalizing n with
  | var | app0 | err => rfl
  | app1 o a ih =>
    show (cutNet1 o (a.netCut n).1 (a.netCut n).2).2 = _
    rw [cutNet1_snd, ih]
    simp only [LTm.netReads, List.length_append]
    cases o <;> rfl
  | app2 o a b iha ihb | index it a b iha ihb | seq a b iha ihb | orElse a b iha ihb =>
    show (b.netCut (a.netCut n).2).2 = _
    rw [ihb, iha]; simp only [LTm.netReads, List.length_append]; omega
  | app3 o a b c iha ihb ihc =>
    show (c.netCut (b.netCut (a.netCut n).2).2).2 = _
    rw [ihc, ihb, iha]; simp only [LTm.netReads, List.length_append]; omega
  | obsW a ih | obsL a ih | obsH a ih => exact ih n
  | kite a b t e iha ihb iht ihe =>
    show (e.netCut (t.netCut (b.netCut (a.netCut n).2).2).2).2 = _
    rw [ihe, iht, ihb, iha]; simp only [LTm.netReads, List.length_append]; omega

theorem LTm.netReads_of_netFree {s : Srt} (t : LTm C s) (h : t.netFree = true) :
    t.netReads = [] := by
  induction t with
  | var | app0 | err => rfl
  | app1 o a ih =>
    simp only [LTm.netFree, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [LTm.netReads, ih h.2, List.nil_append]
    cases o <;> first | rfl | (exfalso; simp_all only [Op1.isNetB, Bool.true_eq_false, false_and])
  | app2 o a b iha ihb | index it a b iha ihb | seq a b iha ihb | orElse a b iha ihb =>
    simp only [LTm.netFree, Bool.and_eq_true] at h
    simp only [LTm.netReads, iha h.1, ihb h.2, List.append_nil]
  | app3 o a b c iha ihb ihc =>
    simp only [LTm.netFree, Bool.and_eq_true] at h
    simp only [LTm.netReads, iha h.1.1, ihb h.1.2, ihc h.2, List.append_nil]
  | obsW a ih | obsL a ih | obsH a ih => exact ih h
  | kite a b t e iha ihb iht ihe =>
    simp only [LTm.netFree, Bool.and_eq_true] at h
    simp only [LTm.netReads, iha h.1.1.1, ihb h.1.1.2, iht h.1.2, ihe h.2, List.append_nil]

/-! ## The cut reads what the term reads -/

/-- **The reads `rs`, cut to the constants from `n`, read in `g` what they
read in the ledger `l`.** -/
def NetAgree (g : State C []) (ν : AEnv) (l : Ledger) (rs : List (LTm C (.val .uint)))
    (n : Nat) : Prop :=
  ∀ (j : Nat) (a : LTm C (.val .uint)), rs[j]? = some a → ∀ v, (a.eval g ν : Option _) = some v →
    ledgerAt l v = ledgerAt g.net (netConst (n + j))

theorem NetAgree.left {g : State C []} {ν : AEnv} {l : Ledger} {rs qs : List (LTm C (.val .uint))}
    {n : Nat} (h : NetAgree g ν l (rs ++ qs) n) : NetAgree g ν l rs n :=
  fun j a ha v hv => h j a (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 ha).1]; exact ha) v hv

theorem NetAgree.right {g : State C []} {ν : AEnv} {l : Ledger} {rs qs : List (LTm C (.val .uint))}
    {n : Nat} (h : NetAgree g ν l (rs ++ qs) n) : NetAgree g ν l qs (n + rs.length) := by
  intro j a ha v hv
  have := h (rs.length + j) a (by rw [List.getElem?_append_right (by omega)]; simpa using ha) v hv
  rw [this, Nat.add_assoc]

theorem eval_netAt (g : State C []) (ν : AEnv) (j : Nat) :
    ((LTm.netAt (C := C) j).eval g ν : Option Int) = some (ledgerAt g.net (netConst j)) := rfl

theorem eval_netAt_cmp (g : State C []) (ν : AEnv) (i j : Nat) :
    ((LTm.app2 (.zcmp .eqB rfl) (LTm.netAt (C := C) i) (LTm.netAt j)).eval g ν : Option Bool) =
      some (BinOp.cmpZ .eqB (ledgerAt g.net (netConst i)) (ledgerAt g.net (netConst j))) := rfl

theorem cutNet1_eval (g : State C []) (ν : AEnv) (l : Ledger) {a s : Srt} (o : Op1 C a s)
    (x x' : LTm C a) (n : Nat) (hok : !o.isNetB || x.netFree)
    (hx : x'.eval g ν = x.eval (State.withLedger g l) ν)
    (hxx : o.isNetB = true → x' = x)
    (hA : NetAgree g ν l (read1 o x) n) :
    (cutNet1 o x' n).1.eval g ν = (LTm.app1 o x).eval (State.withLedger g l) ν := by
  cases o with
  | net =>
    have hf : x.netFree = true := by simpa only [Op1.isNetB, Bool.not_true, Bool.false_or] using hok
    have hx' : x' = x := hxx rfl
    subst hx'
    show (LTm.seq x' (LTm.netAt n)).eval g ν = Option.map _ (x'.eval (State.withLedger g l) ν)
    rw [LTm.eval_seq, LTm.eval_withLedger g l ν x' hf]
    cases hv : (x'.eval g ν : Option PrimTy.uint.Denote) with
    | none => rfl
    | some v =>
      show some (ledgerAt g.net (netConst n)) = some ((lookupBy v l).getD 0)
      have := hA 0 x' rfl v hv
      rw [Nat.add_zero] at this
      exact congrArg some this.symm
  | _ =>
    show (LTm.app1 _ x').eval g ν = (LTm.app1 _ x).eval (State.withLedger g l) ν
    rw [LTm.eval_app1, LTm.eval_app1, hx]
    exact (Op1.eval_withLedger g l _ rfl _).symm

theorem LTm.netCut_of_netFree {s : Srt} (t : LTm C s) (h : t.netFree = true) (n : Nat) :
    t.netCut n = (t, n) := by
  induction t generalizing n with
  | var | app0 | err => rfl
  | app1 o a ih =>
    simp only [LTm.netFree, Bool.and_eq_true, Bool.not_eq_true'] at h
    show cutNet1 o (a.netCut n).1 (a.netCut n).2 = _
    rw [ih h.2]
    cases o <;> first | rfl | (exfalso; simp_all only [Op1.isNetB, Bool.true_eq_false, false_and])
  | app2 o a b iha ihb | index it a b iha ihb | seq a b iha ihb | orElse a b iha ihb =>
    simp only [LTm.netFree, Bool.and_eq_true] at h
    simp only [LTm.netCut, iha h.1, ihb h.2]
  | app3 o a b c iha ihb ihc =>
    simp only [LTm.netFree, Bool.and_eq_true] at h
    simp only [LTm.netCut, iha h.1.1, ihb h.1.2, ihc h.2]
  | obsW a ih | obsL a ih | obsH a ih =>
    simp only [LTm.netFree] at h
    simp only [LTm.netCut, ih h]
  | kite a b t e iha ihb iht ihe =>
    simp only [LTm.netFree, Bool.and_eq_true] at h
    simp only [LTm.netCut, iha h.1.1.1, ihb h.1.1.2, iht h.1.2, ihe h.2]

/-- **A cut term reads in `g` what the term reads with the ledger `l`.** -/
theorem LTm.netCut_eval (g : State C []) (ν : AEnv) (l : Ledger) {s : Srt} (t : LTm C s)
    (hok : t.netOK = true) (n : Nat) (hA : NetAgree g ν l t.netReads n) :
    (t.netCut n).1.eval g ν = t.eval (State.withLedger g l) ν := by
  induction t generalizing n with
  | var k => rfl
  | app0 o => show (LTm.app0 o).eval g ν = _; rw [LTm.eval_app0, LTm.eval_app0]; cases o <;> rfl
  | err => rfl
  | app1 o a ih =>
    simp only [LTm.netOK, Bool.and_eq_true] at hok
    show (cutNet1 o (a.netCut n).1 (a.netCut n).2).1.eval g ν = _
    simp only [LTm.netReads] at hA
    have iha := ih hok.1 n hA.left
    rw [LTm.netCut_snd] at *
    refine cutNet1_eval g ν l o a (a.netCut n).1 _ hok.2 iha (fun hn => ?_) hA.right
    have hf : a.netFree = true := by
      cases o <;> simp_all only [Op1.isNetB, Bool.not_true, Bool.false_or, reduceCtorEq]
    rw [LTm.netCut_of_netFree a hf]
  | app2 o a b iha ihb =>
    simp only [LTm.netOK, Bool.and_eq_true] at hok
    simp only [LTm.netReads] at hA
    show (LTm.app2 o (a.netCut n).1 (b.netCut (a.netCut n).2).1).eval g ν = _
    rw [LTm.eval_app2, LTm.eval_app2, iha hok.1 n hA.left,
      ihb hok.2 _ (by rw [LTm.netCut_snd]; exact hA.right)]
    cases o <;> rfl
  | app3 o a b c iha ihb ihc =>
    simp only [LTm.netOK, Bool.and_eq_true] at hok
    simp only [LTm.netReads] at hA
    show (LTm.app3 o (a.netCut n).1 (b.netCut (a.netCut n).2).1
      (c.netCut (b.netCut (a.netCut n).2).2).1).eval g ν = _
    rw [LTm.eval_app3, LTm.eval_app3, iha hok.1.1 n hA.left.left,
      ihb hok.1.2 _ (by rw [LTm.netCut_snd]; exact hA.left.right),
      ihc hok.2 _ (by
        rw [LTm.netCut_snd, LTm.netCut_snd]
        simpa only [List.length_append, Nat.add_assoc] using hA.right)]
    cases o <;> rfl
  | index it a b iha ihb =>
    simp only [LTm.netOK, Bool.and_eq_true] at hok
    simp only [LTm.netReads] at hA
    show (LTm.index it (a.netCut n).1 (b.netCut (a.netCut n).2).1).eval g ν = _
    rw [LTm.eval_index, LTm.eval_index, iha hok.1 n hA.left,
      ihb hok.2 _ (by rw [LTm.netCut_snd]; exact hA.right)]
  | obsW a ih =>
    simp only [LTm.netOK] at hok
    show (LTm.obsW (a.netCut n).1).eval g ν = _
    rw [LTm.eval_obsW, LTm.eval_obsW, ih hok n hA]
  | obsL a ih =>
    simp only [LTm.netOK] at hok
    show (LTm.obsL (a.netCut n).1).eval g ν = _
    rw [LTm.eval_obsL, LTm.eval_obsL, ih hok n hA]
  | obsH a ih =>
    simp only [LTm.netOK] at hok
    show (LTm.obsH (a.netCut n).1).eval g ν = _
    rw [LTm.eval_obsH, LTm.eval_obsH, ih hok n hA]
  | seq a b iha ihb =>
    simp only [LTm.netOK, Bool.and_eq_true] at hok
    simp only [LTm.netReads] at hA
    show (LTm.seq (a.netCut n).1 (b.netCut (a.netCut n).2).1).eval g ν = _
    rw [LTm.eval_seq, LTm.eval_seq, iha hok.1 n hA.left,
      ihb hok.2 _ (by rw [LTm.netCut_snd]; exact hA.right)]
  | orElse a b iha ihb =>
    simp only [LTm.netOK, Bool.and_eq_true] at hok
    simp only [LTm.netReads] at hA
    show (LTm.orElse (a.netCut n).1 (b.netCut (a.netCut n).2).1).eval g ν = _
    rw [LTm.eval_orElse, LTm.eval_orElse, iha hok.1 n hA.left,
      ihb hok.2 _ (by rw [LTm.netCut_snd]; exact hA.right)]
  | kite a b t e iha ihb iht ihe =>
    simp only [LTm.netOK, Bool.and_eq_true] at hok
    simp only [LTm.netReads] at hA
    show (LTm.kite (a.netCut n).1 (b.netCut (a.netCut n).2).1
      (t.netCut (b.netCut (a.netCut n).2).2).1
      (e.netCut (t.netCut (b.netCut (a.netCut n).2).2).2).1).eval g ν = _
    rw [LTm.eval_kite, LTm.eval_kite, iha hok.1.1.1 n hA.left.left.left,
      ihb hok.1.1.2 _ (by rw [LTm.netCut_snd]; exact hA.left.left.right),
      iht hok.1.2 _ (by
        rw [LTm.netCut_snd, LTm.netCut_snd]
        simpa only [List.length_append, Nat.add_assoc] using hA.left.right),
      ihe hok.2 _ (by
        rw [LTm.netCut_snd, LTm.netCut_snd, LTm.netCut_snd]
        simpa only [List.length_append, Nat.add_assoc] using hA.right)]

theorem LTm.netFree_of_reads {s : Srt} (t : LTm C s) (hok : t.netOK = true)
    (h : t.netReads = []) : t.netFree = true := by
  induction t with
  | var | app0 | err => rfl
  | app1 o a ih =>
    simp only [LTm.netOK, Bool.and_eq_true] at hok
    simp only [LTm.netReads, List.append_eq_nil_iff] at h
    simp only [LTm.netFree, ih hok.1 h.1, Bool.and_true, Bool.not_eq_true']
    cases o <;> first | rfl | (exfalso; simp_all only [read1, reduceCtorEq, and_false])
  | app2 o a b iha ihb | index it a b iha ihb | seq a b iha ihb | orElse a b iha ihb =>
    simp only [LTm.netOK, Bool.and_eq_true] at hok
    simp only [LTm.netReads, List.append_eq_nil_iff] at h
    simp only [LTm.netFree, iha hok.1 h.1, ihb hok.2 h.2, Bool.and_self]
  | app3 o a b c iha ihb ihc =>
    simp only [LTm.netOK, Bool.and_eq_true] at hok
    simp only [LTm.netReads, List.append_eq_nil_iff] at h
    simp only [LTm.netFree, iha hok.1.1 h.1.1, ihb hok.1.2 h.1.2, ihc hok.2 h.2, Bool.and_self]
  | obsW a ih | obsL a ih | obsH a ih => exact ih hok h
  | kite a b t e iha ihb iht ihe =>
    simp only [LTm.netOK, Bool.and_eq_true] at hok
    simp only [LTm.netReads, List.append_eq_nil_iff] at h
    simp only [LTm.netFree, iha hok.1.1.1 h.1.1.1, ihb hok.1.1.2 h.1.1.2, iht hok.1.2 h.1.2,
      ihe hok.2 h.2, Bool.and_self]

/-! ## The cut of a formula -/

/-- A formula that reads no ledger. -/
def LFml.netFree : LFml C → Bool
  | .tt => true
  | .eq a b => a.netFree && b.netFree
  | .not φ | .all _ _ φ => φ.netFree
  | .and φ ψ | .imp φ ψ => φ.netFree && ψ.netFree

/-- Every ledger read's address reads no ledger, and none is under a binder. -/
def LFml.netOK : LFml C → Bool
  | .tt => true
  | .eq a b => a.netOK && b.netOK
  | .not φ => φ.netOK
  | .and φ ψ | .imp φ ψ => φ.netOK && ψ.netOK
  | .all _ _ φ => φ.netFree

/-- The addresses of a formula's ledger reads, outside binders. -/
def LFml.netReads : LFml C → List (LTm C (.val .uint))
  | .tt | .all .. => []
  | .eq a b => a.netReads ++ b.netReads
  | .not φ => φ.netReads
  | .and φ ψ | .imp φ ψ => φ.netReads ++ ψ.netReads

/-- **The cut of a formula**, its constants from `n`; a binder is kept whole. -/
def LFml.netCut : LFml C → Nat → LFml C × Nat
  | .tt, n => (.tt, n)
  | .eq a b, n => let A := a.netCut n; let B := b.netCut A.2; (.eq A.1 B.1, B.2)
  | .not φ, n => let F := φ.netCut n; (.not F.1, F.2)
  | .and φ ψ, n => let F := φ.netCut n; let G := ψ.netCut F.2; (.and F.1 G.1, G.2)
  | .imp φ ψ, n => let F := φ.netCut n; let G := ψ.netCut F.2; (.imp F.1 G.1, G.2)
  | .all k p φ, n => (.all k p φ, n)

theorem LFml.netCut_snd (φ : LFml C) (n : Nat) : (φ.netCut n).2 = n + φ.netReads.length := by
  induction φ generalizing n with
  | tt | all => rfl
  | eq a b =>
    show (b.netCut (a.netCut n).2).2 = _
    rw [LTm.netCut_snd, LTm.netCut_snd]; simp only [LFml.netReads, List.length_append]; omega
  | not φ ih => exact ih n
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ =>
    show (ψ.netCut (φ.netCut n).2).2 = _
    rw [ihψ, ihφ]; simp only [LFml.netReads, List.length_append]; omega


theorem LFml.holds_withLedger (g : State C []) (l : Ledger) :
    ∀ (φ : LFml C) (ν : AEnv), φ.netFree = true →
      (φ.holds (State.withLedger g l) ν ↔ φ.holds g ν)
  | .tt, _, _ => Iff.rfl
  | .eq a b, ν, h => by
    simp only [LFml.netFree, Bool.and_eq_true] at h
    rw [LFml.holds_eq_iff, LFml.holds_eq_iff, LTm.eval_withLedger g l ν a h.1,
      LTm.eval_withLedger g l ν b h.2]
  | .not φ, ν, h => not_congr (LFml.holds_withLedger g l φ ν h)
  | .and φ ψ, ν, h => by
    simp only [LFml.netFree, Bool.and_eq_true] at h
    exact and_congr (LFml.holds_withLedger g l φ ν h.1) (LFml.holds_withLedger g l ψ ν h.2)
  | .imp φ ψ, ν, h => by
    simp only [LFml.netFree, Bool.and_eq_true] at h
    exact imp_congr (LFml.holds_withLedger g l φ ν h.1) (LFml.holds_withLedger g l ψ ν h.2)
  | .all k p φ, ν, h => forall_congr' fun v => LFml.holds_withLedger g l φ _ h

/-- **A cut formula holds in `g` where the formula holds with the ledger `l`.** -/
theorem LFml.netCut_holds (g : State C []) (l : Ledger) :
    ∀ (φ : LFml C) (ν : AEnv), φ.netOK = true → ∀ n, NetAgree g ν l φ.netReads n →
      ((φ.netCut n).1.holds g ν ↔ φ.holds (State.withLedger g l) ν)
  | .tt, _, _, _, _ => Iff.rfl
  | .eq a b, ν, hok, n, hA => by
    simp only [LFml.netOK, Bool.and_eq_true] at hok
    simp only [LFml.netReads] at hA
    show (LFml.eq (a.netCut n).1 (b.netCut (a.netCut n).2).1).holds g ν ↔ _
    rw [LFml.holds_eq_iff, LFml.holds_eq_iff, LTm.netCut_eval g ν l a hok.1 n hA.left,
      LTm.netCut_eval g ν l b hok.2 (a.netCut n).2 (by rw [LTm.netCut_snd]; exact hA.right)]
  | .not φ, ν, hok, n, hA => not_congr (LFml.netCut_holds g l φ ν hok n hA)
  | .and φ ψ, ν, hok, n, hA => by
    simp only [LFml.netOK, Bool.and_eq_true] at hok
    simp only [LFml.netReads] at hA
    exact and_congr (LFml.netCut_holds g l φ ν hok.1 n hA.left)
      (LFml.netCut_holds g l ψ ν hok.2 _ (by rw [LFml.netCut_snd]; exact hA.right))
  | .imp φ ψ, ν, hok, n, hA => by
    simp only [LFml.netOK, Bool.and_eq_true] at hok
    simp only [LFml.netReads] at hA
    exact imp_congr (LFml.netCut_holds g l φ ν hok.1 n hA.left)
      (LFml.netCut_holds g l ψ ν hok.2 _ (by rw [LFml.netCut_snd]; exact hA.right))
  | .all k p φ, ν, hok, _, _ => (LFml.holds_withLedger g l (.all k p φ) ν hok).symm

theorem LFml.netFree_of_reads (φ : LFml C) (hok : φ.netOK = true) (h : φ.netReads = []) :
    φ.netFree = true := by
  induction φ with
  | tt => rfl
  | all k p φ _ => exact hok
  | eq a b =>
    simp only [LFml.netOK, Bool.and_eq_true] at hok
    simp only [LFml.netReads, List.append_eq_nil_iff] at h
    simp only [LFml.netFree, LTm.netFree_of_reads a hok.1 h.1, LTm.netFree_of_reads b hok.2 h.2,
      Bool.and_self]
  | not φ ih => exact ih hok h
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ =>
    simp only [LFml.netOK, Bool.and_eq_true] at hok
    simp only [LFml.netReads, List.append_eq_nil_iff] at h
    simp only [LFml.netFree, ihφ hok.1 h.1, ihψ hok.2 h.2, Bool.and_self]

theorem LFml.netReads_free (φ : LFml C) (hok : φ.netOK = true) :
    ∀ a ∈ φ.netReads, a.netFree = true := by
  have key : ∀ {s : Srt} (t : LTm C s), t.netOK = true → ∀ a ∈ t.netReads, a.netFree = true := by
    intro s t ht
    induction t with
    | var | app0 | err => intro a ha; cases ha
    | app1 o x ih =>
      simp only [LTm.netOK, Bool.and_eq_true] at ht
      intro a ha
      simp only [LTm.netReads, List.mem_append] at ha
      rcases ha with ha | ha
      · exact ih ht.1 a ha
      · cases o <;> simp only [read1, List.not_mem_nil, List.mem_singleton] at ha
        subst ha
        simpa only [Op1.isNetB, Bool.not_true, Bool.false_or] using ht.2
    | app2 o x y ihx ihy | index it x y ihx ihy | seq x y ihx ihy | orElse x y ihx ihy =>
      simp only [LTm.netOK, Bool.and_eq_true] at ht
      intro a ha
      simp only [LTm.netReads, List.mem_append] at ha
      exact ha.elim (ihx ht.1 a) (ihy ht.2 a)
    | app3 o x y z ihx ihy ihz =>
      simp only [LTm.netOK, Bool.and_eq_true] at ht
      intro a ha
      simp only [LTm.netReads, List.mem_append] at ha
      rcases ha with (ha | ha) | ha
      · exact ihx ht.1.1 a ha
      · exact ihy ht.1.2 a ha
      · exact ihz ht.2 a ha
    | obsW x ih | obsL x ih | obsH x ih => exact ih ht
    | kite x y t e ihx ihy iht ihe =>
      simp only [LTm.netOK, Bool.and_eq_true] at ht
      intro a ha
      simp only [LTm.netReads, List.mem_append] at ha
      rcases ha with ((ha | ha) | ha) | ha
      · exact ihx ht.1.1.1 a ha
      · exact ihy ht.1.1.2 a ha
      · exact iht ht.1.2 a ha
      · exact ihe ht.2 a ha
  induction φ with
  | tt | all => intro a ha; cases ha
  | eq x y =>
    simp only [LFml.netOK, Bool.and_eq_true] at hok
    intro a ha
    simp only [LFml.netReads, List.mem_append] at ha
    exact ha.elim (key x hok.1 a) (key y hok.2 a)
  | not φ ih => exact ih hok
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ =>
    simp only [LFml.netOK, Bool.and_eq_true] at hok
    intro a ha
    simp only [LFml.netReads, List.mem_append] at ha
    exact ha.elim (ihφ hok.1 a) (ihψ hok.2 a)

/-! ## Functional consistency -/

/-- `aᵢ == aⱼ → net(i) == net(j)`. -/
def netPair (a b : LTm C (.val .uint)) (i j : Nat) : LFml C :=
  .imp (.eq a b) (.eq (.app2 (.zcmp .eqB rfl) (LTm.netAt i) (LTm.netAt j)) LTm.tt)

/-- The pairs `i < j` of the reads `rs`. -/
def netPairs (rs : List (LTm C (.val .uint))) : List (LFml C) :=
  (List.range rs.length).flatMap fun j =>
    (List.range j).map fun i => netPair (rs.getD i .err) (rs.getD j .err) i j

/-- **The reads at equal addresses read equal entries**, at the constants. -/
def netCons (rs : List (LTm C (.val .uint))) : LFml C := LFml.conj (netPairs rs)

/-- What `netCons` says. -/
def NetCons (g : State C []) (ν : AEnv) (rs : List (LTm C (.val .uint))) : Prop :=
  ∀ (i j : Nat) (a b : LTm C (.val .uint)) (v : PrimTy.uint.Denote), i < j → rs[i]? = some a →
    rs[j]? = some b → (a.eval g ν : Option _) = some v → (b.eval g ν : Option _) = some v →
    ledgerAt g.net (netConst i) = ledgerAt g.net (netConst j)

theorem netPair_holds (g : State C []) (ν : AEnv) (a b : LTm C (.val .uint)) (i j : Nat) :
    (netPair a b i j).holds g ν ↔ ∀ v, (a.eval g ν : Option _) = some v →
      (b.eval g ν : Option _) = some v → ledgerAt g.net (netConst i) = ledgerAt g.net (netConst j) := by
  show ((LFml.eq a b).holds g ν → (LFml.eq _ _).holds g ν) ↔ _
  rw [LFml.holds_eq_iff, LFml.holds_eq_iff, eval_netAt_cmp]
  constructor
  · intro h v ha hb
    obtain ⟨w, hw, hw'⟩ := h ⟨v, ha, hb⟩
    cases hw'
    simpa only [Option.some.injEq, BinOp.cmpZ, decide_eq_true_eq] using hw
  · intro h hab
    obtain ⟨v, ha, hb⟩ := hab
    refine ⟨true, ?_, rfl⟩
    simp only [Option.some.injEq, BinOp.cmpZ, decide_eq_true_eq]
    exact h v ha hb

theorem netCons_holds (g : State C []) (ν : AEnv) (rs : List (LTm C (.val .uint))) :
    (netCons rs).holds g ν ↔ NetCons g ν rs := by
  rw [netCons, LFml.holds_conj]
  constructor
  · intro h i j a b v hij ha hb hva hvb
    have hj : j < rs.length := (List.getElem?_eq_some_iff.1 hb).1
    have hm : netPair (rs.getD i .err) (rs.getD j .err) i j ∈ netPairs rs :=
      List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, List.mem_map.2 ⟨i, List.mem_range.2 hij, rfl⟩⟩
    have := (netPair_holds g ν _ _ i j).1 (h _ hm) v
    rw [List.getD_eq_getElem?_getD, ha, List.getD_eq_getElem?_getD, hb] at this
    exact this hva hvb
  · intro h d hd
    obtain ⟨j, hj, hd⟩ := List.mem_flatMap.1 hd
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hd
    have hj' := List.mem_range.1 hj
    have hi' := List.mem_range.1 hi
    rw [netPair_holds]
    intro v hva hvb
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at hva
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'] at hvb
    exact h i j _ _ v hi' (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem hj') hva hvb

/-! ## The ledgers of the two readings -/

/-- **The reads pulled back to their addresses** (`vs` their values): the
ledger of the leaf, its entry at each read's address the entry at its
constant in `l`. -/
def pullL (l : Ledger) : List (Option PrimTy.uint.Denote) → Nat → Ledger
  | [], _ => []
  | some v :: vs, j => (v, ledgerAt l (netConst j)) :: pullL l vs (j + 1)
  | none :: vs, j => pullL l vs (j + 1)

/-- **The reads pushed forward to their constants**: the ledger of the cut
leaf, its entry at each constant the entry in `l` at the read's address. -/
def pushL (l : Ledger) : List (Option PrimTy.uint.Denote) → Nat → Ledger
  | [], _ => []
  | v :: vs, j => (netConst j, (v.map (ledgerAt l)).getD 0) :: pushL l vs (j + 1)

/-- The values of the reads' addresses. -/
noncomputable def readVals (g : State C []) (ν : AEnv) (rs : List (LTm C (.val .uint))) :
    List (Option PrimTy.uint.Denote) :=
  rs.map fun a => (a.eval g ν : Option PrimTy.uint.Denote)

theorem netConst_inj {i j : Nat} (hi : i < 2 ^ 256) (hj : j < 2 ^ 256)
    (h : (netConst i : PrimTy.uint.Denote) = netConst j) : i = j := by
  have h' := congrArg Subtype.val h
  rw [uintOfNat_val hi, uintOfNat_val hj] at h'
  exact_mod_cast h'

theorem pushL_at (l : Ledger) :
    ∀ (vs : List (Option PrimTy.uint.Denote)) (n j : Nat) (v : Option PrimTy.uint.Denote),
      vs[j]? = some v → n + vs.length ≤ 2 ^ 256 →
      ledgerAt (pushL l vs n) (netConst (n + j)) = (v.map (ledgerAt l)).getD 0
  | [], _, _, _, hv, _ => by cases hv
  | w :: vs, n, j, v, hv, hl => by
    simp only [List.length_cons] at hl
    cases j with
    | zero =>
      cases hv
      simp only [pushL, ledgerAt, lookupBy, Nat.add_zero, if_true, Option.getD_some]
    | succ j =>
      have hj : j < vs.length := (List.getElem?_eq_some_iff.1 (by simpa using hv)).1
      have hne : (netConst (n + (j + 1)) : PrimTy.uint.Denote) ≠ netConst n := by
        intro he
        have := netConst_inj (by omega) (by omega) he
        omega
      have ih := pushL_at l vs (n + 1) j v (by simpa using hv) (by omega)
      simp only [pushL, ledgerAt, lookupBy, hne, if_false]
      rw [show n + (j + 1) = n + 1 + j by omega]
      exact ih

theorem pushL_agree (h : State C []) (ν : AEnv) (rs : List (LTm C (.val .uint)))
    (hf : ∀ a ∈ rs, a.netFree = true) (hl : rs.length ≤ 2 ^ 256) :
    NetAgree (State.withLedger h (pushL h.net (readVals h ν rs) 0)) ν h.net rs 0 := by
  intro j a ha v hv
  rw [LTm.eval_withLedger h _ ν a (hf a (List.mem_of_getElem? ha))] at hv
  show _ = ledgerAt (pushL h.net (readVals h ν rs) 0) (netConst (0 + j))
  rw [pushL_at h.net _ 0 j (a.eval h ν) (by simp only [readVals, List.getElem?_map, ha,
    Option.map_some]) (by simp only [readVals, List.length_map]; omega), hv]
  rfl

theorem pushL_cons (h : State C []) (ν : AEnv) (rs : List (LTm C (.val .uint)))
    (hf : ∀ a ∈ rs, a.netFree = true) (hl : rs.length ≤ 2 ^ 256) :
    NetCons (State.withLedger h (pushL h.net (readVals h ν rs) 0)) ν rs := by
  intro i j a b v _ ha hb hva hvb
  have hA := pushL_agree h ν rs hf hl
  have h1 := hA i a ha v hva
  have h2 := hA j b hb v hvb
  simp only [Nat.zero_add] at h1 h2
  rw [← h1, ← h2]

theorem pullL_at (g : State C []) (ν : AEnv) :
    ∀ (rs : List (LTm C (.val .uint))) (n : Nat),
      (∀ (i j : Nat) (a b : LTm C (.val .uint)) (v : PrimTy.uint.Denote), i < j → rs[i]? = some a →
        rs[j]? = some b → (a.eval g ν : Option _) = some v → (b.eval g ν : Option _) = some v →
        ledgerAt g.net (netConst (n + i)) = ledgerAt g.net (netConst (n + j))) →
      ∀ (j : Nat) (a : LTm C (.val .uint)), rs[j]? = some a → ∀ v,
        (a.eval g ν : Option _) = some v →
        ledgerAt (pullL g.net (readVals g ν rs) n) v = ledgerAt g.net (netConst (n + j))
  | [], _, _, _, _, ha, _, _ => by cases ha
  | b :: rs, n, hc, j, a, ha, v, hv => by
    have hc' : ∀ (i j : Nat) (a b : LTm C (.val .uint)) (v : PrimTy.uint.Denote), i < j →
        rs[i]? = some a → rs[j]? = some b → (a.eval g ν : Option _) = some v →
        (b.eval g ν : Option _) = some v →
        ledgerAt g.net (netConst (n + 1 + i)) = ledgerAt g.net (netConst (n + 1 + j)) := by
      intro i j a' b' v' hij ha' hb' hva hvb
      have := hc (i + 1) (j + 1) a' b' v' (by omega) (by simpa using ha') (by simpa using hb') hva hvb
      rw [show n + 1 + i = n + (i + 1) by omega, show n + 1 + j = n + (j + 1) by omega]
      exact this
    have hrv : readVals g ν (b :: rs) = (b.eval g ν : Option PrimTy.uint.Denote) :: readVals g ν rs := rfl
    rw [hrv]
    cases hb : (b.eval g ν : Option PrimTy.uint.Denote) with
    | none =>
      simp only [pullL]
      cases j with
      | zero => cases ha; rw [hb] at hv; cases hv
      | succ j =>
        rw [pullL_at g ν rs (n + 1) hc' j a (by simpa using ha) v hv]
        rw [show n + 1 + j = n + (j + 1) by omega]
    | some w =>
      simp only [pullL]
      by_cases hvw : v = w
      · subst hvw
        simp only [ledgerAt, lookupBy, if_true, Option.getD_some]
        cases j with
        | zero => rfl
        | succ j =>
          have := hc 0 (j + 1) b a v (by omega) rfl (by simpa using ha) hb hv
          simpa only [Nat.add_zero, ledgerAt] using this
      · have hl : ledgerAt ((w, ledgerAt g.net (netConst n)) :: pullL g.net (readVals g ν rs) (n + 1)) v =
            ledgerAt (pullL g.net (readVals g ν rs) (n + 1)) v := by
          simp only [ledgerAt, lookupBy, hvw, if_false]
        rw [hl]
        cases j with
        | zero => cases ha; rw [hb] at hv; exact absurd (Option.some.inj hv).symm hvw
        | succ j =>
          rw [pullL_at g ν rs (n + 1) hc' j a (by simpa using ha) v hv]
          rw [show n + 1 + j = n + (j + 1) by omega]

theorem pullL_agree (g : State C []) (ν : AEnv) (rs : List (LTm C (.val .uint)))
    (hc : NetCons g ν rs) : NetAgree g ν (pullL g.net (readVals g ν rs) 0) rs 0 :=
  fun j a ha v hv => pullL_at g ν rs 0 (fun i j a b v hij ha hb hva hvb => by
    simpa only [Nat.zero_add] using hc i j a b v hij ha hb hva hvb) j a ha v hv

/-! ## The cut leaf -/

/-- **The ledger cut of a leaf**: its reads at their constants, their
consistency in the antecedent; the leaf itself where it reads no ledger. -/
def LFml.ledgerCut (φ : LFml C) : LFml C :=
  if φ.netReads.isEmpty then φ else .imp (netCons φ.netReads) (φ.netCut 0).1

/-- The state refuting the leaf, from one refuting the cut leaf: its ledger
the reads pulled back, `vs` the values of their addresses. -/
def LFml.ledgerPull (g : State C []) (vs : List (Option PrimTy.uint.Denote)) : State C [] :=
  State.withLedger g (pullL g.net vs 0)

/-- **A state refuting the cut leaf gives one refuting the leaf**, the
values `vs` those of the reads' addresses. -/
theorem LFml.ledgerCut_refutes (φ : LFml C) (hok : φ.netOK = true) (g : State C []) (ν : AEnv)
    (vs : List (Option PrimTy.uint.Denote)) (hvs : vs = readVals g ν φ.netReads)
    (h : ¬ φ.ledgerCut.holds g ν) : ¬ φ.holds (LFml.ledgerPull g vs) ν := by
  subst hvs
  unfold LFml.ledgerCut at h
  unfold LFml.ledgerPull
  intro hφ
  by_cases he : φ.netReads.isEmpty = true
  · rw [if_pos he] at h
    have hr : φ.netReads = [] := List.isEmpty_iff.1 he
    exact h ((LFml.holds_withLedger g _ φ ν (LFml.netFree_of_reads φ hok hr)).1 hφ)
  · rw [if_neg he] at h
    simp only [LFml.holds, not_imp] at h
    obtain ⟨hc, hb⟩ := h
    exact hb ((LFml.netCut_holds g _ φ ν hok 0
      (pullL_agree g ν _ ((netCons_holds g ν _).1 hc))).2 hφ)

/-- **The ledger cut is exact in a universal reading.** -/
theorem LFml.ledgerCut_valid_iff (φ : LFml C) (hok : φ.netOK = true)
    (hn : φ.netReads.length ≤ 2 ^ 256) : φ.Valid ↔ φ.ledgerCut.Valid := by
  constructor
  · intro hv g ν
    exact Classical.byContradiction fun h =>
      LFml.ledgerCut_refutes φ hok g ν _ rfl h (hv _ ν)
  · intro hv h ν
    have hc := hv (State.withLedger h (pushL h.net (readVals h ν φ.netReads) 0)) ν
    unfold LFml.ledgerCut at hc
    by_cases he : φ.netReads.isEmpty = true
    · rw [if_pos he] at hc
      have hr : φ.netReads = [] := List.isEmpty_iff.1 he
      exact (LFml.holds_withLedger h _ φ ν (LFml.netFree_of_reads φ hok hr)).1 hc
    · rw [if_neg he] at hc
      have hf := LFml.netReads_free φ hok
      have hb := hc ((netCons_holds _ ν _).2 (pushL_cons h ν φ.netReads hf hn))
      have := (LFml.netCut_holds _ h.net φ ν hok 0 (pushL_agree h ν φ.netReads hf hn)).1 hb
      exact this

end Solidity.Decide
