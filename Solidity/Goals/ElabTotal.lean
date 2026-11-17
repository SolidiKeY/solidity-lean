import Solidity.Tools.Goal
import Solidity.Syntax.Elab.Stmt

/-!
# The elaborator kernel, total (et0-elab-total-goal)

The goal-first statement for the elaborator's `mutual` knot
(`Syntax/Elab/Stmt.lean`), as `loweringKernelTotal` is for the lowering kernel:
stated here, proved by et3-elab-knot-total.  Written against the public names
only, so it reads the same over the `partial` knot of today and over its
totalization.  Outputs are not part of it: the totalization keeps them.

Clauses: `ElabKernelFix`/`ElabKernelNames` (equations), `ElabKernelInduction`
(successful runs), `ElabKernelHelpers` (the reached `partial` helpers).
-/

namespace Solidity.Goals

open Solidity Semantics

section Elab

variable [FreshNames] (C : Contract)

/-- `x`, from `sc` and `st`, succeeds with `b` and state `st'` (any memo). -/
def ElabRan {β : Type} (x : ElabM β) (sc : ElabScope) (st : ECtx × Nat) (b : β)
    (st' : ECtx × Nat) : Prop :=
  ∃ m m', ((x.run sc).run st).run m = .ok ((b, st'), m')

/-- Every successful run of `f` meets `Q`. -/
def ElabSat {α β : Type} (Q : α → ElabScope → ECtx × Nat → β → ECtx × Nat → Prop)
    (f : α → ElabM β) : Prop :=
  ∀ a sc st b st', ElabRan (f a) sc st b st' → Q a sc st b st'

/-- The block's `elabStmtsP`, over the record `rc`. -/
def elabStmtsStep (rc : ElabRec C) : List RawStmt → ElabM (SProg C)
  | [] => pure []
  | s :: ss => do
    let P ← rc.elabStmtP s
    let Q ← rc.elabStmtsP ss
    pure (P ++ Q)

/-- The record `rc` satisfies the knot's defining equations. -/
def ElabKernelFix (rc : ElabRec C) : Prop :=
  rc.elabStmtsP [] = pure [] ∧
  (∀ s ss, rc.elabStmtsP (s :: ss) = do
    let P ← rc.elabStmtP s
    let Q ← rc.elabStmtsP ss
    pure (P ++ Q)) ∧
  rc.elabStmtP = elabStmtPWith C rc ∧
  rc.elabStmt1 = elabStmt1With C rc ∧
  rc.hoistStmt = hoistStmtWith C rc ∧
  rc.hoist = hoistWith C rc

/-- Each field of `elabRec C ()` is the block's function of that name, and
`elabCallRet` is its arm over the record. -/
def ElabKernelNames : Prop :=
  let rc := elabRec C ()
  rc.hoist = hoist C ∧ rc.hoistBinop = hoistBinop C ∧ rc.hoistTop = hoistTop C ∧
  rc.hoistAssign = hoistAssign C ∧ rc.hoistArgs = hoistArgs C ∧
  rc.abiMemBytes = abiMemBytes C ∧ rc.abiDecodeBytes = abiDecodeBytes C ∧
  rc.abiEncode = abiEncode C ∧ rc.hoistCallArgs = hoistCallArgs C ∧
  rc.fnDispatch = fnDispatch C ∧ rc.fnMemoryDispatch = fnMemoryDispatch C ∧
  rc.callValue = callValue C ∧ rc.elabCall = elabCall C ∧
  rc.elabMemCall = elabMemCall C ∧ rc.elabStorageCall = elabStorageCall C ∧
  rc.elabCallReceiver = elabCallReceiver C ∧
  rc.elabCallReceiverPush = elabCallReceiverPush C ∧
  (∀ g Γ args ρ, rc.trySelfBody g (Γ := Γ) args ρ = trySelfBody C g (Γ := Γ) args ρ) ∧
  rc.elabValueCall = elabValueCall C ∧ rc.elabCtor = elabCtor C ∧
  rc.hoistStmt = hoistStmt C ∧ rc.elabStmtP = elabStmtP C ∧
  rc.elabStmt1 = elabStmt1 C ∧ rc.loopExpr = loopExpr C ∧ rc.loopQ = loopQ C ∧
  rc.elabStmtsP = elabStmtsP C ∧ rc.elabBranch = elabBranch C ∧
  rc.elabScope = elabScope C ∧ rc.elabTuple = elabTuple C ∧
  (∀ f args res resW targets ctor resNew selfFrame,
    elabCallRet C f args res resW targets ctor resNew selfFrame =
      elabCallRetWith C rc f args res resW targets ctor resNew selfFrame)

/-- **Induction over successful runs**: predicates on the runs of `hoist`,
`hoistStmt`, `elabStmtP`, `elabStmt1` and `elabStmtsP` that their arms meet
over every record whose fields meet them hold of `rc`'s fields. -/
def ElabKernelInduction (rc : ElabRec C) : Prop :=
  ∀ (QH : RawExpr → ElabScope → ECtx × Nat → SProg C × RawExpr → ECtx × Nat → Prop)
    (QS : RawStmt → ElabScope → ECtx × Nat → SProg C × RawStmt → ECtx × Nat → Prop)
    (QP Q1 : RawStmt → ElabScope → ECtx × Nat → SProg C → ECtx × Nat → Prop)
    (QL : List RawStmt → ElabScope → ECtx × Nat → SProg C → ECtx × Nat → Prop),
    (∀ r : ElabRec C, ElabSat QH r.hoist → ElabSat QS r.hoistStmt →
        ElabSat QP r.elabStmtP → ElabSat Q1 r.elabStmt1 → ElabSat QL r.elabStmtsP →
      ElabSat QH (hoistWith C r) ∧ ElabSat QS (hoistStmtWith C r) ∧
        ElabSat QP (elabStmtPWith C r) ∧ ElabSat Q1 (elabStmt1With C r) ∧
        ElabSat QL (elabStmtsStep C r)) →
    ElabSat QH rc.hoist ∧ ElabSat QS rc.hoistStmt ∧ ElabSat QP rc.elabStmtP ∧
      ElabSat Q1 rc.elabStmt1 ∧ ElabSat QL rc.elabStmtsP

end Elab

/-- **The helpers' defining equations**.  `RawExpr.mapM` rewrites a node, then
the children of the result: for a growing callback (`pure (.unop .neg ·)`) the
unfolding never ends, only throwing functions satisfy it, and no well-founded
totalization computes one.  So it is stated in `Except String` (as `orderNamed`
and `uncheck` run it) for callbacks whose results are no larger (`sizeOf`). -/
def ElabKernelHelpers : Prop :=
  (∀ (f : RawExpr → Except String RawExpr),
    (∀ e e', f e = .ok e' → sizeOf e' ≤ sizeOf e) →
    ∀ e, RawExpr.mapM f e = do
      match ← f e with
      | .field a g => return .field (← a.mapM f) g
      | .index a b => return .index (← a.mapM f) (← b.mapM f)
      | .binop op a b => return .binop op (← a.mapM f) (← b.mapM f)
      | .unop op a => return .unop op (← a.mapM f)
      | .ternary c a b => return .ternary (← c.mapM f) (← a.mapM f) (← b.mapM f)
      | .incDec op a => return .incDec op (← a.mapM f)
      | .newArr T n => return .newArr T (← n.mapM f)
      | .call g as => return .call g (← as.mapM (·.mapM f))
      | .modular op a b k => return .modular op (← a.mapM f) (← b.mapM f) (← k.mapM f)
      | .named g ns as => return .named g ns (← as.mapM (·.mapM f))
      | .tuple as => return .tuple (← as.mapM (·.mapM f))
      | .assign l r => return .assign (← l.mapM f) (← r.mapM f)
      | .opAssign op l r => return .opAssign op (← l.mapM f) (← r.mapM f)
      | e => pure e) ∧
  (∀ r ss, lowerReturns r ss = match ss with
    | [] => pure []
    | .ret none :: _ => pure []
    | .ret (some e) :: _ => lowerReturn r e
    | .block b :: ss => do
      if b.any RawStmt.hasReturn && !ss.isEmpty then
        for x in b.flatMap RawStmt.declaredAll do
          if ss.any (·.mentions x) then
            throw s!"`return` in a block declaring {x}, which the statements after it name"
        lowerReturns r (b ++ ss)
      else
        pure (.block (← lowerReturns r b) :: (← lowerReturns r ss))
    | .ite c t e :: ss => do
      if (t.any RawStmt.hasReturn || e.any RawStmt.hasReturn) && !ss.isEmpty then
        for x in (t ++ e).flatMap RawStmt.declaredAll do
          if ss.any (·.mentions x) then
            throw s!"`return` in a branch declaring {x}, which the statements after it name"
        pure [.ite c (← lowerReturns r (t ++ ss)) (← lowerReturns r (e ++ ss))]
      else
        pure (.ite c (← lowerReturns r t) (← lowerReturns r e) :: (← lowerReturns r ss))
    | .tryCall e g as rets ok err code pnc other :: ss => do
      let bs := [ok, err, pnc, other]
      if bs.any (·.any RawStmt.hasReturn) && !ss.isEmpty then
        for x in (bs.flatten.flatMap RawStmt.declaredAll ++ rets.map (·.2) ++ code.toList) do
          if ss.any (·.mentions x) then
            throw s!"`return` in a clause declaring {x}, which the statements after it name"
        pure [.tryCall e g as rets (← lowerReturns r (ok ++ ss)) (← lowerReturns r (err ++ ss))
          code (← lowerReturns r (pnc ++ ss)) (← lowerReturns r (other ++ ss))]
      else
        pure (.tryCall e g as rets (← lowerReturns r ok) (← lowerReturns r err) code
          (← lowerReturns r pnc) (← lowerReturns r other) :: (← lowerReturns r ss))
    | .unchecked b :: ss => do
      if b.any RawStmt.hasReturn && !ss.isEmpty then
        throw "`return` inside `unchecked { … }` with statements after the block"
      pure (.unchecked (← lowerReturns r b) :: (← lowerReturns r ss))
    | .checked o b :: ss => do
      if b.any RawStmt.hasReturn && !ss.isEmpty then
        throw "`return` inside `checked { … }` with statements after the block"
      pure (.checked o (← lowerReturns r b) :: (← lowerReturns r ss))
    | s :: ss => do pure (s :: (← lowerReturns r ss))) ∧
  ∀ [FreshNames] (ρ : List (String × String)) (ss : List RawStmt),
    renameStmts ρ ss = match ss with
    | [] => pure []
    | s :: ss => do
      let r := RawExpr.rename ρ
      let ra (a : RawLoopSpec) : RawLoopSpec :=
        { Id.run (a.mapM (pure ∘ r)) with qinv := a.qinv.map (RawInv.rename ρ) }
      let fresh (base x : String) : ElabM (String × List (String × String)) := do
        let y := toString (← freshCapture base)
        pure (y, (x, y) :: ρ)
      match s with
      | .decl T x i =>
        let (y, ρ') ← fresh "se" x
        pure (.decl T y (i.map r) :: (← renameStmts ρ' ss))
      | .declStorage T x i =>
        let (y, ρ') ← fresh "sp" x
        pure (.declStorage T y (i.map r) :: (← renameStmts ρ' ss))
      | .declMemory T x i =>
        let (y, ρ') ← fresh "mv" x
        pure (.declMemory T y (i.map r) :: (← renameStmts ρ' ss))
      | .declStoragePush T x b =>
        let (y, ρ') ← fresh "sp" x
        pure (.declStoragePush T y (r b) :: (← renameStmts ρ' ss))
      | .declPush T x b =>
        let (y, ρ') ← fresh "se" x
        pure (.declPush T y (r b) :: (← renameStmts ρ' ss))
      | .send (some T) (.name x) e a g =>
        let (y, ρ') ← fresh "se" x
        pure (.send (some T) (.name y) (r e) (r a) g :: (← renameStmts ρ' ss))
      | .ite c t e =>
        pure (.ite (r c) (← renameStmts ρ t) (← renameStmts ρ e) :: (← renameStmts ρ ss))
      | .unchecked b => pure (.unchecked (← renameStmts ρ b) :: (← renameStmts ρ ss))
      | .checked o b => pure (.checked o (← renameStmts ρ b) :: (← renameStmts ρ ss))
      | .block b => pure (.block (← renameStmts ρ b) :: (← renameStmts ρ ss))
      | .tupleDecl vs e =>
        let mut ρ' := ρ
        let mut vs' := []
        for v in vs do
          match v with
          | some (T, x) =>
            let y := toString (← freshCapture "se")
            ρ' := (x, y) :: ρ'
            vs' := vs' ++ [some (T, y)]
          | none => vs' := vs' ++ [none]
        pure (.tupleDecl vs' (r e) :: (← renameStmts ρ' ss))
      | .tryCall e g as rets ok err code pnc other =>
        let mut ρok := ρ
        let mut rets' := []
        for (T, x) in rets do
          let y := toString (← freshCapture "se")
          ρok := (x, y) :: ρok
          rets' := rets' ++ [(T, y)]
        let (code', ρp) ← match code with
          | some x => fresh "se" x >>= fun (y, ρ') => pure (some y, ρ')
          | none => pure (none, ρ)
        pure (.tryCall (r e) g (as.map r) rets' (← renameStmts ρok ok) (← renameStmts ρ err)
          code' (← renameStmts ρp pnc) (← renameStmts ρ other) :: (← renameStmts ρ ss))
      | .whileLoop a c b =>
        pure (.whileLoop (ra a) (r c) (← renameStmts ρ b) :: (← renameStmts ρ ss))
      | .doWhile a b c =>
        pure (.doWhile (ra a) (← renameStmts ρ b) (r c) :: (← renameStmts ρ ss))
      | .loop a c b =>
        pure (.loop (ra a) (r c) (← renameStmts ρ b) :: (← renameStmts ρ ss))
      | .forLoop a [] c u b =>
        pure (.forLoop (ra a) [] (c.map r) (← renameStmts ρ u) (← renameStmts ρ b) ::
          (← renameStmts ρ ss))
      | .forLoop a i c u b =>
        let out ← renameStmts ρ (i ++ [.forLoop a [] c u b])
        match out.getLast? with
        | some (.forLoop a' [] c' u' b') =>
          pure (.forLoop a' out.dropLast c' u' b' :: (← renameStmts ρ ss))
        | _ => throw "a `for` loop's initialisation, renamed"
      | s => pure ((Id.run (s.mapExprsM (pure ∘ r))) :: (← renameStmts ρ ss))

/-- **The elaborator kernel, total** (et3-elab-knot-total): at every spelling
of fresh names and every contract, the knot of `Syntax/Elab/Stmt.lean`
satisfies its defining equations, its successful runs admit induction over
its arms, and the helpers it reaches keep their defining equations. -/
@[goal Solidity.elabKernel_total "et3-elab-knot-total"]
def elabKernelTotal : Prop :=
  (∀ [FreshNames] (C : Contract),
    ElabKernelFix C (elabRec C ()) ∧ ElabKernelNames C ∧
      ElabKernelInduction C (elabRec C ())) ∧
  ElabKernelHelpers

end Solidity.Goals
