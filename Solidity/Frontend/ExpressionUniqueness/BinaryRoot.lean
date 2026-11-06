import Solidity.Frontend.ExpressionUniqueness.ExpressionBinaryFree

/-!
# Certified binary root markers follow their associativity

Left-associative roots select the last marker of their exact rank; exponentiation
selects the first. Scanner conditions are derived from existing recursive prec.
These results retain arbitrary subtree sizes and operator values. Complete
operand spans, prefix-minus state and global tree uniqueness remain open.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def LastBinaryIs (rank : Nat) (marker : Tok) (items : List (List Tok)) : Prop :=
  ∃ n, lastTop (binaryMarker rank) items.flatten = some (n, marker)

def FirstBinaryIs (rank : Nat) (marker : Tok) (items : List (List Tok)) : Prop :=
  ∃ n, firstTop (binaryMarker rank) [] items.flatten = some (n, marker)

theorem derives_lastBinary (e : Syn .expr) (ts : List Tok) (rank : Nat) (marker : Tok)
    (hy : Produces e.yield (LastBinaryIs rank marker)) (hd : e.Derives ts) :
    ∃ n, lastTop (binaryMarker rank) ts = some (n, marker) := by
  obtain ⟨L, ht⟩ := hd
  have h : LastBinaryIs rank marker [ts] := hy L [ts] [] ((expr_toks_iff e L ts).mp ht)
  simpa only [LastBinaryIs, List.flatten_cons, List.flatten_nil, List.append_nil] using h

theorem derives_firstBinary (e : Syn .expr) (ts : List Tok) (rank : Nat) (marker : Tok)
    (hy : Produces e.yield (FirstBinaryIs rank marker)) (hd : e.Derives ts) :
    ∃ n, firstTop (binaryMarker rank) [] ts = some (n, marker) := by
  obtain ⟨L, ht⟩ := hd
  have h : FirstBinaryIs rank marker [ts] := hy L [ts] [] ((expr_toks_iff e L ts).mp ht)
  simpa only [FirstBinaryIs, List.flatten_cons, List.flatten_nil, List.append_nil] using h

theorem mul_yield_lastBinary (op : MulOp) (a b : Syn .expr)
    (hp : (Syn.mulDivMod op a b).prec = true) : Produces (Syn.mulDivMod op a b).yield (LastBinaryIs 11 (.punct op.punct)) := by
  have hprecb : b.prec = true := by
    apply all_prec_implies_prec b
    have hall : (Syn.mulDivMod op a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have hlevelb : 11 < b.level := by
    have hr : (Syn.mulDivMod op a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 11 < 12) hr.2
  have ht : binaryMarker 11 (.punct op.punct) = true := by cases op <;> rfl
  apply produces_bind_all a.yield _ (LastBinaryIs 11 (.punct op.punct))
  intro xs
  apply produces_bind b.yield _ (BinaryFreeItems 11) (LastBinaryIs 11 (.punct op.punct))
    (high_expr_yield_binaryFree 11 (by decide) (by decide) b hprecb hlevelb)
  intro ys hy
  apply produces_pure
  refine ⟨xs.flatten.length, ?_⟩
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] using
    lastTop_marker (binaryMarker 11) (binaryMarker_atomic 11) xs.flatten ys.flatten (.punct op.punct)
      (binaryFreeItems_flatten hy) ht

theorem mul_derives_lastBinary (op : MulOp) (a b : Syn .expr) (ts : List Tok)
    (hp : (Syn.mulDivMod op a b).prec = true) (hd : (Syn.mulDivMod op a b).Derives ts) :
    ∃ n, lastTop (binaryMarker 11) ts = some (n, .punct op.punct) :=
  derives_lastBinary _ ts 11 (.punct op.punct) (mul_yield_lastBinary op a b hp) hd

theorem shift_yield_lastBinary (op : ShiftOp) (a b : Syn .expr)
    (hp : (Syn.shift op a b).prec = true) : Produces (Syn.shift op a b).yield (LastBinaryIs 9 (.punct op.punct)) := by
  have hprecb : b.prec = true := by
    apply all_prec_implies_prec b
    have hall : (Syn.shift op a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have hlevelb : 9 < b.level := by
    have hr : (Syn.shift op a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 9 < 10) hr.2
  have ht : binaryMarker 9 (.punct op.punct) = true := by cases op <;> rfl
  apply produces_bind_all a.yield _ (LastBinaryIs 9 (.punct op.punct))
  intro xs
  apply produces_bind b.yield _ (BinaryFreeItems 9) (LastBinaryIs 9 (.punct op.punct))
    (high_expr_yield_binaryFree 9 (by decide) (by decide) b hprecb hlevelb)
  intro ys hy
  apply produces_pure
  refine ⟨xs.flatten.length, ?_⟩
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] using
    lastTop_marker (binaryMarker 9) (binaryMarker_atomic 9) xs.flatten ys.flatten (.punct op.punct)
      (binaryFreeItems_flatten hy) ht

theorem shift_derives_lastBinary (op : ShiftOp) (a b : Syn .expr) (ts : List Tok)
    (hp : (Syn.shift op a b).prec = true) (hd : (Syn.shift op a b).Derives ts) :
    ∃ n, lastTop (binaryMarker 9) ts = some (n, .punct op.punct) :=
  derives_lastBinary _ ts 9 (.punct op.punct) (shift_yield_lastBinary op a b hp) hd

theorem order_yield_lastBinary (op : OrderOp) (a b : Syn .expr)
    (hp : (Syn.order op a b).prec = true) : Produces (Syn.order op a b).yield (LastBinaryIs 5 (.punct op.punct)) := by
  have hprecb : b.prec = true := by
    apply all_prec_implies_prec b
    have hall : (Syn.order op a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have hlevelb : 5 < b.level := by
    have hr : (Syn.order op a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 5 < 6) hr.2
  have ht : binaryMarker 5 (.punct op.punct) = true := by cases op <;> rfl
  apply produces_bind_all a.yield _ (LastBinaryIs 5 (.punct op.punct))
  intro xs
  apply produces_bind b.yield _ (BinaryFreeItems 5) (LastBinaryIs 5 (.punct op.punct))
    (high_expr_yield_binaryFree 5 (by decide) (by decide) b hprecb hlevelb)
  intro ys hy
  apply produces_pure
  refine ⟨xs.flatten.length, ?_⟩
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] using
    lastTop_marker (binaryMarker 5) (binaryMarker_atomic 5) xs.flatten ys.flatten (.punct op.punct)
      (binaryFreeItems_flatten hy) ht

theorem order_derives_lastBinary (op : OrderOp) (a b : Syn .expr) (ts : List Tok)
    (hp : (Syn.order op a b).prec = true) (hd : (Syn.order op a b).Derives ts) :
    ∃ n, lastTop (binaryMarker 5) ts = some (n, .punct op.punct) :=
  derives_lastBinary _ ts 5 (.punct op.punct) (order_yield_lastBinary op a b hp) hd

theorem equality_yield_lastBinary (op : EqOp) (a b : Syn .expr)
    (hp : (Syn.equality op a b).prec = true) : Produces (Syn.equality op a b).yield (LastBinaryIs 4 (.punct op.punct)) := by
  have hprecb : b.prec = true := by
    apply all_prec_implies_prec b
    have hall : (Syn.equality op a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have hlevelb : 4 < b.level := by
    have hr : (Syn.equality op a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 4 < 5) hr.2
  have ht : binaryMarker 4 (.punct op.punct) = true := by cases op <;> rfl
  apply produces_bind_all a.yield _ (LastBinaryIs 4 (.punct op.punct))
  intro xs
  apply produces_bind b.yield _ (BinaryFreeItems 4) (LastBinaryIs 4 (.punct op.punct))
    (high_expr_yield_binaryFree 4 (by decide) (by decide) b hprecb hlevelb)
  intro ys hy
  apply produces_pure
  refine ⟨xs.flatten.length, ?_⟩
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] using
    lastTop_marker (binaryMarker 4) (binaryMarker_atomic 4) xs.flatten ys.flatten (.punct op.punct)
      (binaryFreeItems_flatten hy) ht

theorem equality_derives_lastBinary (op : EqOp) (a b : Syn .expr) (ts : List Tok)
    (hp : (Syn.equality op a b).prec = true) (hd : (Syn.equality op a b).Derives ts) :
    ∃ n, lastTop (binaryMarker 4) ts = some (n, .punct op.punct) :=
  derives_lastBinary _ ts 4 (.punct op.punct) (equality_yield_lastBinary op a b hp) hd

theorem bitAnd_yield_lastBinary (a b : Syn .expr)
    (hp : (Syn.bitAnd a b).prec = true) : Produces (Syn.bitAnd a b).yield (LastBinaryIs 8 (.punct .bitAnd)) := by
  have hprecb : b.prec = true := by
    apply all_prec_implies_prec b
    have hall : (Syn.bitAnd a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have hlevelb : 8 < b.level := by
    have hr : (Syn.bitAnd a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 8 < 9) hr.2
  have ht : binaryMarker 8 (.punct .bitAnd) = true := rfl
  apply produces_bind_all a.yield _ (LastBinaryIs 8 (.punct .bitAnd))
  intro xs
  apply produces_bind b.yield _ (BinaryFreeItems 8) (LastBinaryIs 8 (.punct .bitAnd))
    (high_expr_yield_binaryFree 8 (by decide) (by decide) b hprecb hlevelb)
  intro ys hy
  apply produces_pure
  refine ⟨xs.flatten.length, ?_⟩
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] using
    lastTop_marker (binaryMarker 8) (binaryMarker_atomic 8) xs.flatten ys.flatten (.punct .bitAnd)
      (binaryFreeItems_flatten hy) ht

theorem bitAnd_derives_lastBinary (a b : Syn .expr) (ts : List Tok)
    (hp : (Syn.bitAnd a b).prec = true) (hd : (Syn.bitAnd a b).Derives ts) :
    ∃ n, lastTop (binaryMarker 8) ts = some (n, .punct .bitAnd) :=
  derives_lastBinary _ ts 8 (.punct .bitAnd) (bitAnd_yield_lastBinary a b hp) hd

theorem bitXor_yield_lastBinary (a b : Syn .expr)
    (hp : (Syn.bitXor a b).prec = true) : Produces (Syn.bitXor a b).yield (LastBinaryIs 7 (.punct .bitXor)) := by
  have hprecb : b.prec = true := by
    apply all_prec_implies_prec b
    have hall : (Syn.bitXor a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have hlevelb : 7 < b.level := by
    have hr : (Syn.bitXor a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 7 < 8) hr.2
  have ht : binaryMarker 7 (.punct .bitXor) = true := rfl
  apply produces_bind_all a.yield _ (LastBinaryIs 7 (.punct .bitXor))
  intro xs
  apply produces_bind b.yield _ (BinaryFreeItems 7) (LastBinaryIs 7 (.punct .bitXor))
    (high_expr_yield_binaryFree 7 (by decide) (by decide) b hprecb hlevelb)
  intro ys hy
  apply produces_pure
  refine ⟨xs.flatten.length, ?_⟩
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] using
    lastTop_marker (binaryMarker 7) (binaryMarker_atomic 7) xs.flatten ys.flatten (.punct .bitXor)
      (binaryFreeItems_flatten hy) ht

theorem bitXor_derives_lastBinary (a b : Syn .expr) (ts : List Tok)
    (hp : (Syn.bitXor a b).prec = true) (hd : (Syn.bitXor a b).Derives ts) :
    ∃ n, lastTop (binaryMarker 7) ts = some (n, .punct .bitXor) :=
  derives_lastBinary _ ts 7 (.punct .bitXor) (bitXor_yield_lastBinary a b hp) hd

theorem bitOr_yield_lastBinary (a b : Syn .expr)
    (hp : (Syn.bitOr a b).prec = true) : Produces (Syn.bitOr a b).yield (LastBinaryIs 6 (.punct .bitOr)) := by
  have hprecb : b.prec = true := by
    apply all_prec_implies_prec b
    have hall : (Syn.bitOr a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have hlevelb : 6 < b.level := by
    have hr : (Syn.bitOr a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 6 < 7) hr.2
  have ht : binaryMarker 6 (.punct .bitOr) = true := rfl
  apply produces_bind_all a.yield _ (LastBinaryIs 6 (.punct .bitOr))
  intro xs
  apply produces_bind b.yield _ (BinaryFreeItems 6) (LastBinaryIs 6 (.punct .bitOr))
    (high_expr_yield_binaryFree 6 (by decide) (by decide) b hprecb hlevelb)
  intro ys hy
  apply produces_pure
  refine ⟨xs.flatten.length, ?_⟩
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] using
    lastTop_marker (binaryMarker 6) (binaryMarker_atomic 6) xs.flatten ys.flatten (.punct .bitOr)
      (binaryFreeItems_flatten hy) ht

theorem bitOr_derives_lastBinary (a b : Syn .expr) (ts : List Tok)
    (hp : (Syn.bitOr a b).prec = true) (hd : (Syn.bitOr a b).Derives ts) :
    ∃ n, lastTop (binaryMarker 6) ts = some (n, .punct .bitOr) :=
  derives_lastBinary _ ts 6 (.punct .bitOr) (bitOr_yield_lastBinary a b hp) hd

theorem and_yield_lastBinary (a b : Syn .expr)
    (hp : (Syn.and a b).prec = true) : Produces (Syn.and a b).yield (LastBinaryIs 3 (.punct .and)) := by
  have hprecb : b.prec = true := by
    apply all_prec_implies_prec b
    have hall : (Syn.and a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have hlevelb : 3 < b.level := by
    have hr : (Syn.and a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 3 < 4) hr.2
  have ht : binaryMarker 3 (.punct .and) = true := rfl
  apply produces_bind_all a.yield _ (LastBinaryIs 3 (.punct .and))
  intro xs
  apply produces_bind b.yield _ (BinaryFreeItems 3) (LastBinaryIs 3 (.punct .and))
    (high_expr_yield_binaryFree 3 (by decide) (by decide) b hprecb hlevelb)
  intro ys hy
  apply produces_pure
  refine ⟨xs.flatten.length, ?_⟩
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] using
    lastTop_marker (binaryMarker 3) (binaryMarker_atomic 3) xs.flatten ys.flatten (.punct .and)
      (binaryFreeItems_flatten hy) ht

theorem and_derives_lastBinary (a b : Syn .expr) (ts : List Tok)
    (hp : (Syn.and a b).prec = true) (hd : (Syn.and a b).Derives ts) :
    ∃ n, lastTop (binaryMarker 3) ts = some (n, .punct .and) :=
  derives_lastBinary _ ts 3 (.punct .and) (and_yield_lastBinary a b hp) hd

theorem or_yield_lastBinary (a b : Syn .expr)
    (hp : (Syn.or a b).prec = true) : Produces (Syn.or a b).yield (LastBinaryIs 2 (.punct .or)) := by
  have hprecb : b.prec = true := by
    apply all_prec_implies_prec b
    have hall : (Syn.or a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have hlevelb : 2 < b.level := by
    have hr : (Syn.or a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 2 < 3) hr.2
  have ht : binaryMarker 2 (.punct .or) = true := rfl
  apply produces_bind_all a.yield _ (LastBinaryIs 2 (.punct .or))
  intro xs
  apply produces_bind b.yield _ (BinaryFreeItems 2) (LastBinaryIs 2 (.punct .or))
    (high_expr_yield_binaryFree 2 (by decide) (by decide) b hprecb hlevelb)
  intro ys hy
  apply produces_pure
  refine ⟨xs.flatten.length, ?_⟩
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] using
    lastTop_marker (binaryMarker 2) (binaryMarker_atomic 2) xs.flatten ys.flatten (.punct .or)
      (binaryFreeItems_flatten hy) ht

theorem or_derives_lastBinary (a b : Syn .expr) (ts : List Tok)
    (hp : (Syn.or a b).prec = true) (hd : (Syn.or a b).Derives ts) :
    ∃ n, lastTop (binaryMarker 2) ts = some (n, .punct .or) :=
  derives_lastBinary _ ts 2 (.punct .or) (or_yield_lastBinary a b hp) hd

theorem exp_yield_firstBinary (a b : Syn .expr) (hp : (Syn.exp a b).prec = true) :
    Produces (Syn.exp a b).yield (FirstBinaryIs 12 (.punct .exp)) := by
  have hpreca : a.prec = true := by
    apply all_prec_implies_prec a
    have hall : (Syn.exp a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.1.2
  have hlevela : 12 < a.level := by
    have hr : (Syn.exp a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 12 < 13) hr.1
  apply produces_bind a.yield _ (BinaryFreeItems 12) (FirstBinaryIs 12 (.punct .exp))
    (high_expr_yield_binaryFree 12 (by decide) (by decide) a hpreca hlevela)
  intro xs hx
  apply produces_bind_all b.yield _ (FirstBinaryIs 12 (.punct .exp))
  intro ys
  apply produces_pure
  refine ⟨xs.flatten.length, ?_⟩
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] using
    firstTop_marker (binaryMarker 12) xs.flatten ys.flatten (.punct .exp)
      (binaryFreeItems_flatten hx) rfl

theorem exp_derives_firstBinary (a b : Syn .expr) (ts : List Tok)
    (hp : (Syn.exp a b).prec = true) (hd : (Syn.exp a b).Derives ts) :
    ∃ n, firstTop (binaryMarker 12) [] ts = some (n, .punct .exp) :=
  derives_firstBinary _ ts 12 (.punct .exp) (exp_yield_firstBinary a b hp) hd

theorem lastTop_none_of_binaryFree (rank : Nat) (ts : List Tok) (hf : BinaryFree rank ts) :
    lastTop (binaryMarker rank) ts = none := by
  unfold lastTop
  rw [firstTop_none_of_skip (binaryMarker rank) (mirrorWord ts)
    (skip_reverse (binaryMarker rank) (binaryMarker_atomic rank) ts [] [] hf)]
  rfl

end Solidity.Frontend.ExpressionUniqueness
