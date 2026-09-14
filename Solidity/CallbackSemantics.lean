import Solidity.Semantics

/-!
# Callback-aware transfer semantics (KeY `transferWithCallback`)

KeY's `transferSemantics:withCallback` rule splits a proof at
`a.transfer(v);` into two branches: (a) prove the contract invariant
`CInv(storage, net)` in the post-debit state, and (b) resume after the
callback in a *havocked* state assumed to satisfy `CInv` (solkey
`docs/net.md`; storage, net, and the contract's own funds
(`selfBalance`) are havocked — the sound reading).

A havoc branch is nondeterministic, so it cannot live in the total
deterministic interpreter. This module adds a thin *relational* layer
over `execStmt`: `ExecC` runs a block exactly like the interpreter
except at `transfer`, where it forks into the invariant-exit obligation
(`.invViolated` outcome — the judgment must rule it out) and the
resume-under-havoc continuation. `holdsC_transfer_split` is the Lean
image of the KeY branch split; `holds_of_holdsC` records that the
callback reading soundly over-approximates the executable one.

`HoldsC` is deliberately a `Prop`, not decidable: the havoc branch
quantifies over all invariant states, exactly as in KeY, where branch
(b) is a genuine proof obligation.
-/

namespace Solidity
namespace CallbackSemantics

open Semantics

/-- `CInv(Struct, Struct)` (solkey `netHeader.key`): an abstract
predicate over the contract storage and the payment ledger. Invariants
cannot see locals, mirroring solkey. -/
abbrev CInvPred := List (Name × SVal) -> List (Int × Int) -> Prop

/-- The callback havoc: the callee may change storage, the ledger, and
the contract's own funds (re-entrant code can move money in or out)
arbitrarily; heap, locals and the allocation counter belong to the
caller's frame and survive. -/
def State.havoc (s : State) (st : List (Name × SVal))
    (nt : List (Int × Int)) (bal : Int) : State :=
  { s with storage := st, net := nt, selfBalance := bal }

@[simp] theorem State.havoc_self (s : State) :
    State.havoc s s.storage s.net s.selfBalance = s := rfl

/-- Outcomes of a callback-aware run: a normal interpreter outcome, or
a violated invariant at a transfer's exit point. -/
inductive COut where
  | halted (r : Res State)
  | invViolated

/-- `stmt` is a payment statement (the only nondeterministic point). -/
def IsTransfer : Stmt -> Prop
  | Stmt.transfer _ _ => True
  | _ => False

/-- Callback-aware big-step execution, parameterized by the contract
invariant. Every non-transfer statement is lifted from the
deterministic interpreter (`execStmt`), so this relation cannot drift
from the executable semantics; `transfer` books the debit via
`execStmt` as well and then forks. -/
inductive ExecC (inv : CInvPred) : State -> Block -> COut -> Prop where
  | nil (s : State) : ExecC inv s [] (.halted (.ok s))
  | det_ok {s s' : State} {stmt : Stmt} {rest : Block} {o : COut}
      (hnt : ¬ IsTransfer stmt) (hex : execStmt s stmt = .ok s')
      (hrest : ExecC inv s' rest o) : ExecC inv s (stmt :: rest) o
  | det_err {s : State} {stmt : Stmt} {rest : Block} {e : Halt}
      (hnt : ¬ IsTransfer stmt) (hex : execStmt s stmt = .error e) :
      ExecC inv s (stmt :: rest) (.halted (.error e))
  | transfer_eval_err {s : State} {r a : WrappedExpr} {rest : Block}
      {e : Halt} (hex : execStmt s (Stmt.transfer r a) = .error e) :
      ExecC inv s (Stmt.transfer r a :: rest) (.halted (.error e))
  /-- KeY branch "invariant on exit", as a failure outcome the judgment
  must exclude. -/
  | transfer_violated {s s₁ : State} {r a : WrappedExpr} {rest : Block}
      (hex : execStmt s (Stmt.transfer r a) = .ok s₁)
      (hinv : ¬ inv s₁.storage s₁.net) :
      ExecC inv s (Stmt.transfer r a :: rest) .invViolated
  /-- KeY branch "resume after callback": continue in any havocked
  state satisfying the invariant. -/
  | transfer_resume {s s₁ : State} {r a : WrappedExpr} {rest : Block}
      {st : List (Name × SVal)} {nt : List (Int × Int)} {bal : Int}
      {o : COut}
      (hex : execStmt s (Stmt.transfer r a) = .ok s₁)
      (hinv : inv st nt)
      (hrest : ExecC inv (State.havoc s₁ st nt bal) rest o) :
      ExecC inv s (Stmt.transfer r a :: rest) o

/-- What an outcome must satisfy for the judgment to hold: the mirror
of `SolidityJudgment.check` on `COut`, with `.invViolated` always
fatal. -/
def COut.checkOut (m : SolidityModality) (post : WrappedExpr) :
    COut -> Prop
  | .invViolated => False
  | .halted (.ok s) =>
      match evalValue s post with
      | .ok (_, Value.bool b) => b = true
      | _ => False
  | .halted (.error .revert) => m = SolidityModality.box
  | .halted (.error .stuck) => False

end CallbackSemantics

/-- Validity under the callback-aware semantics: every `ExecC` run —
including all havocked resumptions — validates the judgment, and no run
exits a transfer with the invariant violated. -/
def SolidityJudgment.HoldsC (inv : CallbackSemantics.CInvPred)
    (j : SolidityJudgment)
    (s0 : Semantics.State := Semantics.State.exampleStore) : Prop :=
  ∀ o, CallbackSemantics.ExecC inv s0 j.block.stmts o ->
    CallbackSemantics.COut.checkOut j.block.modality j.post o

namespace CallbackSemantics

open Semantics

/-- The Lean image of the KeY `transferWithCallback` branch split: given
that the debit itself succeeds, the judgment holds iff (a) the invariant
holds on exit and (b) the continuation holds in every invariant-
satisfying havocked state. -/
theorem holdsC_transfer_split
    {inv : CInvPred} {m : SolidityModality} {r a : WrappedExpr}
    {rest : Block} {post : WrappedExpr} {s s₁ : State}
    (hex : execStmt s (Stmt.transfer r a) = .ok s₁) :
    (SolidityJudgment.mk ⟨m, Stmt.transfer r a :: rest⟩ post).HoldsC inv s ↔
      (inv s₁.storage s₁.net ∧
        ∀ st nt bal, inv st nt ->
          (SolidityJudgment.mk ⟨m, rest⟩ post).HoldsC inv
            (State.havoc s₁ st nt bal)) := by
  constructor
  · intro H
    by_cases hinv : inv s₁.storage s₁.net
    · refine ⟨hinv, fun st nt bal hst o hrun => ?_⟩
      exact H o (ExecC.transfer_resume hex hst hrun)
    · exact absurd (H .invViolated (ExecC.transfer_violated hex hinv))
        (by simp [COut.checkOut])
  · rintro ⟨hinv, hrest⟩ o hrun
    cases hrun with
    | det_ok hnt _ _ => exact absurd trivial hnt
    | det_err hnt _ => exact absurd trivial hnt
    | transfer_eval_err hex' => rw [hex] at hex'; exact nomatch hex'
    | transfer_violated hex' hinv' =>
        rw [hex] at hex'
        cases hex'
        exact absurd hinv hinv'
    | transfer_resume hex' hst hrun' =>
        rw [hex] at hex'
        cases hex'
        exact hrest _ _ _ hst o hrun'

/-- The empty block: validity is the postcondition check in the current
state. -/
theorem holdsC_nil {inv : CInvPred} {m : SolidityModality}
    {post : WrappedExpr} {s : State} :
    (SolidityJudgment.mk ⟨m, []⟩ post).HoldsC inv s ↔
      COut.checkOut m post (.halted (.ok s)) := by
  constructor
  · intro H
    exact H _ (ExecC.nil s)
  · intro h o hrun
    cases hrun
    exact h

/-- Peeling a successfully executing non-transfer statement. -/
theorem holdsC_cons_det {inv : CInvPred} {m : SolidityModality}
    {stmt : Stmt} {rest : Block} {post : WrappedExpr} {s s' : State}
    (hnt : ¬ IsTransfer stmt) (hex : execStmt s stmt = .ok s') :
    (SolidityJudgment.mk ⟨m, stmt :: rest⟩ post).HoldsC inv s ↔
      (SolidityJudgment.mk ⟨m, rest⟩ post).HoldsC inv s' := by
  constructor
  · intro H o hrun
    exact H o (ExecC.det_ok hnt hex hrun)
  · intro H o hrun
    cases hrun with
    | det_ok hnt' hex' hrun' =>
        rw [hex] at hex'
        cases hex'
        exact H o hrun'
    | det_err hnt' hex' => rw [hex] at hex'; exact nomatch hex'
    | transfer_eval_err hex' => exact absurd trivial hnt
    | transfer_violated hex' hinv' => exact absurd trivial hnt
    | transfer_resume hex' hst hrun' => exact absurd trivial hnt

/-- The deterministic interpreter run is one of the `ExecC` runs (via
identity havocs), so callback validity implies plain validity:
`transferWithCallback` soundly over-approximates the executable
semantics. -/
theorem holds_of_holdsC {inv : CInvPred} {j : SolidityJudgment}
    {s0 : State} (H : j.HoldsC inv s0) : j.Holds s0 := by
  obtain ⟨⟨m, stmts⟩, post⟩ := j
  rw [SolidityJudgment.Holds, SolidityJudgment.check]
  suffices h : ∀ (blk : Block) (s : State),
      ((SolidityJudgment.mk ⟨m, blk⟩ post).HoldsC inv s) ->
        (match execBlock s blk with
          | .ok t =>
              match evalValue t post with
              | .ok (_, Value.bool b) => b
              | _ => false
          | .error .revert => decide (m = SolidityModality.box)
          | .error .stuck => false) = true by
    exact h stmts s0 H
  intro blk
  induction blk with
  | nil =>
      intro s H
      have := H (.halted (.ok s)) (ExecC.nil s)
      simp only [COut.checkOut] at this
      rw [execBlock]
      revert this
      cases hev : evalValue s post with
      | error e => exact fun h => h.elim
      | ok x =>
          obtain ⟨t, v⟩ := x
          cases v with
          | int i => exact fun h => h.elim
          | bool b =>
              exact fun h => by
                show (match evalValue s post with
                  | Except.ok (_, Value.bool b) => b
                  | _ => false) = true
                rw [hev]
                exact h
  | cons stmt rest ih =>
      intro s H
      rw [execBlock]
      match hstmt : stmt with
      | Stmt.transfer r a =>
          cases hex : execStmt s (Stmt.transfer r a) with
          | error e =>
              have := H (.halted (.error e)) (ExecC.transfer_eval_err hex)
              simp only [COut.checkOut] at this
              cases e
              · exact decide_eq_true this
              · exact this.elim
          | ok s₁ =>
              have hsplit := (holdsC_transfer_split hex).mp H
              have hcont :=
                hsplit.2 s₁.storage s₁.net s₁.selfBalance hsplit.1
              rw [State.havoc_self] at hcont
              simpa using ih s₁ hcont
      | Stmt.expr e => exact det_case s rest ih H (by exact fun h => h)
      | Stmt.assign lhs rhs => exact det_case s rest ih H (fun h => h)
      | Stmt.storageDecl ty n i => exact det_case s rest ih H (fun h => h)
      | Stmt.storagePlaceAlias ty n i =>
          exact det_case s rest ih H (fun h => h)
      | Stmt.memoryDecl ty n i => exact det_case s rest ih H (fun h => h)
      | Stmt.stackDecl ty n i => exact det_case s rest ih H (fun h => h)
      | Stmt.delete t => exact det_case s rest ih H (fun h => h)
      | Stmt.push t v => exact det_case s rest ih H (fun h => h)
      | Stmt.pushAssign t v => exact det_case s rest ih H (fun h => h)
      | Stmt.pushFieldAssign t f v =>
          exact det_case s rest ih H (fun h => h)
      | Stmt.pop t => exact det_case s rest ih H (fun h => h)
      | Stmt.revert msg => exact det_case s rest ih H (fun h => h)
      | Stmt.compoundAssign op lhs rhs =>
          exact det_case s rest ih H (fun h => h)
      | Stmt.ite c thn els => exact det_case s rest ih H (fun h => h)
      | Stmt.assertStmt c => exact det_case s rest ih H (fun h => h)
      | Stmt.requireStmt c => exact det_case s rest ih H (fun h => h)
      | Stmt.callStmt res fn args => exact det_case s rest ih H (fun h => h)
where
  det_case {m : SolidityModality} {post : WrappedExpr} {stmt : Stmt}
      (s : State) (rest : Block)
      (ih : ∀ s, (SolidityJudgment.mk ⟨m, rest⟩ post).HoldsC inv s ->
        (match execBlock s rest with
          | .ok t =>
              match evalValue t post with
              | .ok (_, Value.bool b) => b
              | _ => false
          | .error .revert => decide (m = SolidityModality.box)
          | .error .stuck => false) = true)
      (H : (SolidityJudgment.mk ⟨m, stmt :: rest⟩ post).HoldsC inv s)
      (hnt : ¬ IsTransfer stmt) :
      (match (execStmt s stmt >>= fun t => execBlock t rest) with
        | .ok t =>
            match evalValue t post with
            | .ok (_, Value.bool b) => b
            | _ => false
        | .error .revert => decide (m = SolidityModality.box)
        | .error .stuck => false) = true := by
    cases hex : execStmt s stmt with
    | error e =>
        have := H (.halted (.error e)) (ExecC.det_err hnt hex)
        simp only [COut.checkOut] at this
        cases e
        · exact decide_eq_true this
        · exact this.elim
    | ok s' =>
        have hcont : (SolidityJudgment.mk ⟨m, rest⟩ post).HoldsC inv s' :=
          fun o hrun => H o (ExecC.det_ok hnt hex hrun)
        simpa using ih s' hcont

end CallbackSemantics
end Solidity
