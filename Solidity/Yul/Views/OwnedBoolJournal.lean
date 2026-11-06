import Solidity.Yul.Views.OwnedBoolEncoding

namespace Solidity.Yul.Views

/-- Physical identity of an owned byte, not a Source path or unowned residual.
Same numeric slot in two banks/accounts is a different representation cell. -/
structure OwnedByteKey where
  transient : Bool
  account : Roadmap.Address
  slot : Roadmap.Word
  offset : Fin 32
  deriving DecidableEq

/-- Only physical true-byte choices are added. Logical storage remains the
actual Source storage; all 8 owned bits are represented, not residual padding. -/
structure BoolEncodingJournal where
  cells : OwnedByteKey → BoolTrueByte
  journal : List (OwnedByteKey × BoolTrueByte)

def boolEncodingInitial : BoolEncodingJournal := ⟨fun _ => canonicalTrueByte,[]⟩

def boolEncodingSave (cells : OwnedByteKey → BoolTrueByte) (key : OwnedByteKey) (value : BoolTrueByte) : OwnedByteKey → BoolTrueByte :=
  fun q => if q=key then value else cells q

theorem boolEncodingSave_get (cells) (key) (value) : boolEncodingSave cells key value key=value := if_pos rfl

theorem boolEncodingSave_other (cells) (key q) (value) (different : q≠key) :
    boolEncodingSave cells key value q=cells q := if_neg different

theorem boolEncodingSave_restore (cells) (key) (value) :
    boolEncodingSave (boolEncodingSave cells key value) key (cells key)=cells := by
  funext q
  by_cases same : q=key
  · subst q; exact boolEncodingSave_get _ _ _
  · simp only [boolEncodingSave_other _ _ _ _ same]

def boolEncodingWrite (s : BoolEncodingJournal) (w : OwnedByteKey × BoolTrueByte) : BoolEncodingJournal :=
  ⟨boolEncodingSave s.cells w.1 w.2,(w.1,s.cells w.1)::s.journal⟩

def boolEncodingRun (s : BoolEncodingJournal) : List (OwnedByteKey × BoolTrueByte) → BoolEncodingJournal
  | [] => s
  | w::ws => boolEncodingRun (boolEncodingWrite s w) ws

def boolEncodingUndo (s : BoolEncodingJournal) : BoolEncodingJournal :=
  match s.journal with
  | [] => s
  | (key,old)::rest => ⟨boolEncodingSave s.cells key old,rest⟩

def boolEncodingUndoN : Nat → BoolEncodingJournal → BoolEncodingJournal
  | 0,s => s
  | n+1,s => boolEncodingUndoN n (boolEncodingUndo s)

def boolEncodingRollback (mark : Nat) (s : BoolEncodingJournal) : BoolEncodingJournal :=
  boolEncodingUndoN (s.journal.length-mark) s

theorem boolEncodingUndo_write (s) (w) : boolEncodingUndo (boolEncodingWrite s w)=s := by
  cases s
  simp only [boolEncodingWrite,boolEncodingUndo,boolEncodingSave_restore]

theorem boolEncodingUndoN_succ (n) (s) : boolEncodingUndoN (n+1) s=boolEncodingUndo (boolEncodingUndoN n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact ih (boolEncodingUndo s)

theorem boolEncodingUndoN_run (s) (ws) : boolEncodingUndoN ws.length (boolEncodingRun s ws)=s := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih => rw [boolEncodingRun,List.length_cons,boolEncodingUndoN_succ,ih,boolEncodingUndo_write]

theorem boolEncodingRun_length (s) (ws) : (boolEncodingRun s ws).journal.length=s.journal.length+ws.length := by
  induction ws generalizing s with
  | nil => exact (Nat.add_zero _).symm
  | cons w ws ih => rw [boolEncodingRun,ih]; simp only [boolEncodingWrite,List.length_cons]; omega

theorem boolEncodingRollback_run (s) (ws) : boolEncodingRollback s.journal.length (boolEncodingRun s ws)=s := by
  rw [boolEncodingRollback,boolEncodingRun_length,Nat.add_sub_cancel_left,boolEncodingUndoN_run]

theorem boolEncodingRun_append (s : BoolEncodingJournal) (xs ys) :
    boolEncodingRun s (xs++ys)=boolEncodingRun (boolEncodingRun s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons w xs ih => exact ih (boolEncodingWrite s w)

def boolEncodingEndTx (s : BoolEncodingJournal) : BoolEncodingJournal :=
  ⟨fun key => if key.transient then canonicalTrueByte else s.cells key,[]⟩

theorem boolEncodingEndTx_persistent (s) (key) (bank : key.transient=false) :
    (boolEncodingEndTx s).cells key=s.cells key := by simp only [boolEncodingEndTx,bank,Bool.false_eq_true,if_false]

theorem boolEncodingEndTx_transient (s) (key) (bank : key.transient=true) :
    (boolEncodingEndTx s).cells key=canonicalTrueByte := by simp only [boolEncodingEndTx,bank,if_true]

end Solidity.Yul.Views
