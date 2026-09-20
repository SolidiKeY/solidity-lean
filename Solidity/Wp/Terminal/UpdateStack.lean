import Solidity.Wp.Terminal.Vocab

/-!
# Terminal-rule updates: stack targets

Reads into a stack variable (`storageRootReadSelect`,
`storageFieldReadFind`, `storageIndexRead{ArrayFind{Box,Diamond},MappingFind}`,
`memoryFieldReadHeap`, `memoryIndexReadHeap{Box,Diamond}`,
`localValueAssign`), the operator rules (`binopAssignment op`,
`unopAssignment op`) and the inc/dec assignments (`localAssignIncrement op`,
`storage{Root,Field,Index}IncrementAssignment op`,
`memory{Field,IndexArray}IncrementAssignment op`).
-/

namespace Solidity
namespace Wp

open Semantics Rules

/-! ## Shape facts from the guards -/

/-- A stack-kind assignable place is a stack variable, or a stack-kind
field/index place (on which the interpreter is stuck). -/
theorem stack_place_shape (lhs : PlaceExpr) (h : isStack lhs) :
    (∃ t fld, lhs.expr = WrappedExpr.var Kind.stack t fld) ∨
    (∃ t base f, lhs.expr = WrappedExpr.field Kind.stack t base f) ∨
    (∃ t base ix, lhs.expr = WrappedExpr.index Kind.stack t base ix) := by
  obtain ⟨e, hass⟩ := lhs
  cases e with
  | var k t fld =>
      have hk : k = Kind.stack := by
        simpa [isStack, Typed.WrappedExpr.isStack, Typed.WrappedExpr.kind] using h
      exact Or.inl ⟨t, fld, by rw [hk]⟩
  | field k t base f =>
      have hk : k = Kind.stack := by
        simpa [isStack, Typed.WrappedExpr.isStack, Typed.WrappedExpr.kind] using h
      exact Or.inr (Or.inl ⟨t, base, f, by rw [hk]⟩)
  | index k t base ix =>
      have hk : k = Kind.stack := by
        simpa [isStack, Typed.WrappedExpr.isStack, Typed.WrappedExpr.kind] using h
      exact Or.inr (Or.inr ⟨t, base, ix, by rw [hk]⟩)
  | pushPlace target =>
      exact absurd h (by simp [isStack, Typed.WrappedExpr.isStack,
        Typed.WrappedExpr.kind])
  | _ => exact absurd hass (by simp [Typed.WrappedExpr.assignable])

/-- A stack *variable* target (`isStackVar`). -/
theorem stackVar_shape (lhs : PlaceExpr) (h : isStackVar lhs) :
    ∃ t fld, lhs.expr = WrappedExpr.var Kind.stack t fld := by
  rcases stack_place_shape lhs h.1 with hv | ⟨t, base, f, he⟩ | ⟨t, base, ix, he⟩
  · exact hv
  · exact absurd (show (lhs.expr).simple = true from h.2)
      (by rw [he]; simp [Typed.WrappedExpr.simple])
  · exact absurd (show (lhs.expr).simple = true from h.2)
      (by rw [he]; simp [Typed.WrappedExpr.simple])

/-! ## The interpreter on a stack target -/

/-- `execAssign` on a stack-kind target: a variable binds the right-hand
side's value, any other stack place is stuck before the right-hand side
runs.  Stated with an arbitrary value computation `rv` so the operator
and inc/dec rules reuse it. -/
theorem execAssign_stack (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr)
    (hk : isStack lhs) (rv : State -> Res (State × Value))
    (hrv : evalValue s rhs = rv s) :
    execAssign s lhs rhs = assignStack lhs rv s := by
  rcases stack_place_shape lhs hk with ⟨t, fld, he⟩ | ⟨t, base, f, he⟩ |
    ⟨t, base, ix, he⟩
  · obtain ⟨e, hass⟩ := lhs
    simp only at he
    subst he
    unfold execAssign assignStack
    simp only [hrv, bind, Except.bind]
  · obtain ⟨e, hass⟩ := lhs
    simp only at he
    subst he
    unfold execAssign assignStack
    rfl
  · obtain ⟨e, hass⟩ := lhs
    simp only at he
    subst he
    unfold execAssign assignStack
    rfl

theorem execStmt_assign_stackRead (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr) (hk : isStack lhs) (hr : terminalRhsB rhs = true) :
    execStmt s (Stmt.assign lhs rhs) = assignStackRead lhs rhs s := by
  show execAssign s lhs rhs = _
  exact execAssign_stack s lhs rhs hk _ (evalValue_readVal s rhs hr)

/-! ## Reads into a stack variable -/

theorem storageRootReadSelect_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageRootReadSelect).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .storageRootReadSelect (Stmt.assign lhs rhs) s := by
  have hc : isStack lhs ∧ isStorage rhs ∧ isSimple rhs := hcond
  show execStmt s (Stmt.assign lhs rhs) = assignStackRead lhs rhs s
  exact execStmt_assign_stackRead s lhs rhs hc.1 (terminalRhsB_of_simple hc.2.2)

theorem localValueAssign_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .localValueAssign).cond (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .localValueAssign (Stmt.assign lhs rhs) s := by
  have hc : isStackVar lhs ∧ isStack rhs ∧ isSimple rhs := hcond
  show execStmt s (Stmt.assign lhs rhs) = assignStackRead lhs rhs s
  exact execStmt_assign_stackRead s lhs rhs hc.1.1
    (terminalRhsB_of_simple hc.2.2)

theorem terminalRhsB_storageField {t : Ty} {path : WrappedExpr} {f : Field}
    (hp : isSimple path) :
    terminalRhsB (WrappedExpr.field Kind.storage t path f) = true := by
  have hp' : path.simple = true := hp
  simp [terminalRhsB, simplePathB, hp']

theorem terminalRhsB_storageIndex {t : Ty} {path ix : WrappedExpr}
    (hp : isSimple path) (hi : isSimple ix) :
    terminalRhsB (WrappedExpr.index Kind.storage t path ix) = true := by
  have hp' : path.simple = true := hp
  have hi' : ix.simple = true := hi
  simp [terminalRhsB, simplePathB, hp', hi']

theorem terminalRhsB_memoryField {t : Ty} {path : WrappedExpr} {f : Field}
    (hp : isSimple path) :
    terminalRhsB (WrappedExpr.field Kind.memory t path f) = true := by
  have hp' : path.simple = true := hp
  simp [terminalRhsB, simplePathB, hp']

theorem terminalRhsB_memoryIndex {t : Ty} {path ix : WrappedExpr}
    (hp : isSimple path) (hi : isSimple ix) :
    terminalRhsB (WrappedExpr.index Kind.memory t path ix) = true := by
  have hp' : path.simple = true := hp
  have hi' : ix.simple = true := hi
  simp [terminalRhsB, simplePathB, hp', hi']

theorem storageFieldReadFind_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageFieldReadFind).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .storageFieldReadFind (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = assignStackRead lhs rhs s
  match rhs, hcond with
  | WrappedExpr.field Kind.storage t path f, hc =>
      have hc' : isStack lhs ∧ isSimple path := hc
      exact execStmt_assign_stackRead s lhs _ hc'.1
        (terminalRhsB_storageField hc'.2)

theorem storageIndexReadArrayFindBox_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageIndexReadArrayFindBox).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .storageIndexReadArrayFindBox (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = assignStackRead lhs rhs s
  match rhs, hcond with
  | WrappedExpr.index Kind.storage t path ix, hc =>
      have hc' : isStack lhs ∧ isSimple path ∧ isSimple ix ∧ isArray path := hc
      exact execStmt_assign_stackRead s lhs _ hc'.1
        (terminalRhsB_storageIndex hc'.2.1 hc'.2.2.1)

theorem storageIndexReadArrayFindDiamond_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageIndexReadArrayFindDiamond).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .storageIndexReadArrayFindDiamond (Stmt.assign lhs rhs) s :=
  storageIndexReadArrayFindBox_update s lhs rhs hcond

theorem storageIndexReadMappingFind_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageIndexReadMappingFind).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .storageIndexReadMappingFind (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = assignStackRead lhs rhs s
  match rhs, hcond with
  | WrappedExpr.index Kind.storage t path ix, hc =>
      have hc' : isStack lhs ∧ isSimple path ∧ isSimple ix ∧ isMapping path := hc
      exact execStmt_assign_stackRead s lhs _ hc'.1
        (terminalRhsB_storageIndex hc'.2.1 hc'.2.2.1)

theorem memoryFieldReadHeap_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .memoryFieldReadHeap).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .memoryFieldReadHeap (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = assignStackRead lhs rhs s
  match rhs, hcond with
  | WrappedExpr.field Kind.memory t path f, hc =>
      have hc' : isStack lhs ∧ isSimple path := hc
      exact execStmt_assign_stackRead s lhs _ hc'.1
        (terminalRhsB_memoryField hc'.2)

theorem memoryIndexReadHeapBox_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .memoryIndexReadHeapBox).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .memoryIndexReadHeapBox (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = assignStackRead lhs rhs s
  match rhs, hcond with
  | WrappedExpr.index Kind.memory t path ix, hc =>
      have hc' : isStack lhs ∧ isSimple path ∧ isSimple ix := hc
      exact execStmt_assign_stackRead s lhs _ hc'.1
        (terminalRhsB_memoryIndex hc'.2.1 hc'.2.2)

theorem memoryIndexReadHeapDiamond_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .memoryIndexReadHeapDiamond).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .memoryIndexReadHeapDiamond (Stmt.assign lhs rhs) s :=
  memoryIndexReadHeapBox_update s lhs rhs hcond

/-! ## Operators -/

theorem binopAssignment_update (op : BinOp) (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect (.binopAssignment op)).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate (.binopAssignment op) (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = binopAssignUpd op lhs rhs s
  match rhs, hcond with
  | WrappedExpr.binop op' l r, hc =>
      have hc' : op' = op ∧ isStackVar lhs ∧ isSimple l ∧ isSimple r := hc
      obtain ⟨rfl, hlhs, hl, hr⟩ := hc'
      show execAssign s lhs (WrappedExpr.binop op' l r) =
        assignStack lhs (fun s => (binopVal op' l r s).map fun v => (s, v)) s
      exact execAssign_stack s lhs _ hlhs.1 _
        (evalValue_binop s op' l r (terminalRhsB_of_simple hl)
          (terminalRhsB_of_simple hr))

theorem unopAssignment_update (op : UnOp) (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect (.unopAssignment op)).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate (.unopAssignment op) (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = unopAssignUpd op lhs rhs s
  match rhs, hcond with
  | WrappedExpr.unop op' a, hc =>
      have hc' : op' = op ∧ isStackVar lhs ∧ isSimple a := hc
      obtain ⟨rfl, hlhs, ha⟩ := hc'
      show execAssign s lhs (WrappedExpr.unop op' a) =
        assignStack lhs (fun s => (unopVal op' a s).map fun v => (s, v)) s
      exact execAssign_stack s lhs _ hlhs.1 _
        (evalValue_unop s op' a (terminalRhsB_of_simple ha))

/-! ## Inc/dec assignments `x = ++t` -/

theorem incDecTargetB_of_stackSimple {t : WrappedExpr} (hk : isStack t)
    (hs : isSimple t) : incDecTargetB t = true := by
  cases t <;> simp_all [incDecTargetB, isStack, Typed.WrappedExpr.isStack,
    Typed.WrappedExpr.kind, isSimple, Typed.WrappedExpr.simple]

theorem incDecTargetB_of_global {t : WrappedExpr} (hg : isGlobal t) :
    incDecTargetB t = true := by
  cases t with
  | var k ty fld => cases k <;> simp_all [incDecTargetB, isGlobal, Typed.WrappedExpr.isGlobal]
  | _ => simp_all [incDecTargetB, isGlobal, Typed.WrappedExpr.isGlobal]

theorem localAssignIncrement_update (op : IncDec) (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect (.localAssignIncrement op)).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate (.localAssignIncrement op) (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = incDecAssignUpd op lhs rhs s
  match rhs, hcond with
  | WrappedExpr.incDec op' t, hc =>
      have hc' : op' = op ∧ isStackVar lhs ∧ isStack t ∧ isSimple t := hc
      obtain ⟨rfl, hlhs, hk, hs⟩ := hc'
      show execAssign s lhs _ = assignStack lhs _ s
      exact execAssign_stack s lhs _ hlhs.1 _
        (evalValue_incDec s op' t (incDecTargetB_of_stackSimple hk hs))

theorem storageRootIncrementAssignment_update (op : IncDec) (s : State)
    (lhs : PlaceExpr) (rhs : WrappedExpr)
    (hcond : (ruleEffect (.storageRootIncrementAssignment op)).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate (.storageRootIncrementAssignment op) (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = incDecAssignUpd op lhs rhs s
  match rhs, hcond with
  | WrappedExpr.incDec op' t, hc =>
      have hc' : op' = op ∧ isStackVar lhs ∧ isGlobal t := hc
      obtain ⟨rfl, hlhs, hg⟩ := hc'
      show execAssign s lhs _ = assignStack lhs _ s
      exact execAssign_stack s lhs _ hlhs.1 _
        (evalValue_incDec s op' t (incDecTargetB_of_global hg))

theorem storageFieldIncrementAssignment_update (op : IncDec) (s : State)
    (lhs : PlaceExpr) (rhs : WrappedExpr)
    (hcond : (ruleEffect (.storageFieldIncrementAssignment op)).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate (.storageFieldIncrementAssignment op) (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = incDecAssignUpd op lhs rhs s
  match rhs, hcond with
  | WrappedExpr.incDec op' (WrappedExpr.field Kind.storage ty path f), hc =>
      have hc' : op' = op ∧ isStackVar lhs ∧ isSimple path := hc
      obtain ⟨rfl, hlhs, hp⟩ := hc'
      show execAssign s lhs _ = assignStack lhs _ s
      exact execAssign_stack s lhs _ hlhs.1 _
        (evalValue_incDec s op' _ (by
          have hp' : path.simple = true := hp
          simp [incDecTargetB, hp']))

theorem storageIndexIncrementAssignment_update (op : IncDec) (s : State)
    (lhs : PlaceExpr) (rhs : WrappedExpr)
    (hcond : (ruleEffect (.storageIndexIncrementAssignment op)).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate (.storageIndexIncrementAssignment op) (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = incDecAssignUpd op lhs rhs s
  match rhs, hcond with
  | WrappedExpr.incDec op' (WrappedExpr.index Kind.storage ty path ix), hc =>
      have hc' : op' = op ∧ isStackVar lhs ∧ isSimple path ∧ isSimple ix := hc
      obtain ⟨rfl, hlhs, hp, hi⟩ := hc'
      show execAssign s lhs _ = assignStack lhs _ s
      exact execAssign_stack s lhs _ hlhs.1 _
        (evalValue_incDec s op' _ (by
          have hp' : path.simple = true := hp
          have hi' : ix.simple = true := hi
          simp [incDecTargetB, hp', hi']))

/-! ### The memory twins

`v = mv.f++;` / `v = mv[i]++;`: the stack bind is the same, and only the
inc/dec target changes kind.  `evalValue_incDec` already covers the memory
slots (`incDecTargetB`), so these are the storage proofs verbatim with
`Kind.memory`. -/

theorem memoryFieldIncrementAssignment_update (op : IncDec) (s : State)
    (lhs : PlaceExpr) (rhs : WrappedExpr)
    (hcond : (ruleEffect (.memoryFieldIncrementAssignment op)).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate (.memoryFieldIncrementAssignment op) (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = incDecAssignUpd op lhs rhs s
  match rhs, hcond with
  | WrappedExpr.incDec op' (WrappedExpr.field Kind.memory ty path f), hc =>
      have hc' : op' = op ∧ isStackVar lhs ∧ isSimple path := hc
      obtain ⟨rfl, hlhs, hp⟩ := hc'
      show execAssign s lhs _ = assignStack lhs _ s
      exact execAssign_stack s lhs _ hlhs.1 _
        (evalValue_incDec s op' _ (by
          have hp' : path.simple = true := hp
          simp [incDecTargetB, hp']))

theorem memoryIndexArrayIncrementAssignment_update (op : IncDec) (s : State)
    (lhs : PlaceExpr) (rhs : WrappedExpr)
    (hcond : (ruleEffect (.memoryIndexArrayIncrementAssignment op)).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate (.memoryIndexArrayIncrementAssignment op) (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = incDecAssignUpd op lhs rhs s
  match rhs, hcond with
  | WrappedExpr.incDec op' (WrappedExpr.index Kind.memory ty path ix), hc =>
      have hc' : op' = op ∧ isStackVar lhs ∧ isSimple path ∧ isSimple ix := hc
      obtain ⟨rfl, hlhs, hp, hi⟩ := hc'
      show execAssign s lhs _ = assignStack lhs _ s
      exact execAssign_stack s lhs _ hlhs.1 _
        (evalValue_incDec s op' _ (by
          have hp' : path.simple = true := hp
          have hi' : ix.simple = true := hi
          simp [incDecTargetB, hp', hi']))

end Wp
end Solidity
