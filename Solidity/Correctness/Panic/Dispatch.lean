import Solidity.Syntax.Elab.Stmt
import Solidity.Semantics.Dispatch

/-!
# What the dispatch and self-call producers emit (plan w3d-panic-dispatch)

For an arbitrary `rc : PanicProducerRec C` (the `partial` hooks `elabStmtsP`, `elabScope`,
`elabCallRet`, `extDispatch` are its fields and nothing is assumed of them), every successful run of a
producer of `Syntax/Elab/Stmt.lean`:

* `fnDispatchWith`, at an internal function type: the program ends in a `DispatchArm.chain` whose
  fallback is `Panic(0x51)` data when `selfFrame || retainFailureData`, the bare revert otherwise
  (`fnDispatchWith_fallback`); the fallback runs when no arm's guard holds (`dispatch_fallback_run`);
* `fnTupleDispatchWith`, `fnMemoryDispatchWith`: the run ends by handing `rc.elabStmtsP` a raw dispatch
  whose last `else` is `rawFallback` (`fnTupleDispatchWith_fallback`, `fnMemoryDispatchWith_fallback`);
* `trySelfBodyWith`: the body is `Stmt.selfCall?` of the statement `rc.elabCallRet` returned for the
  callee, instrumented (`withPanics`) exactly when the callee is not a compiler getter
  (`trySelfBodyWith_instrumented`);
* `receiveSelfBodyWith`: the body is `Stmt.selfCall?` of the statement `rc.elabCallRet` returned for
  `receive`, with no `withPanics` (`receiveSelfBodyWith_plain`).

`Post` and `Hands` are the two run predicates, `Returns` records where a value came from; their rules are applied by head symbol (`post_step`,
`hands_step`), so no proof restates a producer's body.
-/

namespace Solidity.Correctness.Panic

open Solidity Semantics

/-- A bind in `ElabM`, run. -/
theorem bind_run {α β : Type} (x : ElabM α) (f : α → ElabM β) (sc : ElabScope) (st : ECtx × Nat)
    (m : CallMemo) : (x >>= f) sc st m =
      (match x sc st m with | .ok ((a, s), m₁) => f a sc s m₁ | .error e => .error e) := by
  show (x sc st m >>= _) = _
  cases x sc st m <;> rfl

/-- `a` is the value of some successful run of `x` in scope `sc`. -/
def Returns {α : Type} (x : ElabM α) (sc : ElabScope) (a : α) : Prop :=
  ∃ st m st' m', x sc st m = .ok ((a, st'), m')

/-- A value returned under `withReader` is returned in the changed scope. -/
theorem Returns.reader {α : Type} {g : ElabScope → ElabScope} {x : ElabM α} {sc : ElabScope} {a : α}
    (h : Returns (withReader g x) sc a) : Returns x (g sc) a := h

/-- A guarded call that returned `some b` did so through a successful run of the call. -/
theorem Returns.of_tryCatch_some {α β : Type} {x : ElabM α} {g : α → β} {sc : ElabScope} {b : β}
    (h : Returns (tryCatch (x >>= fun a => pure (some (g a))) fun _ => pure none) sc (some b)) :
    ∃ a, Returns x sc a ∧ g a = b := by
  obtain ⟨st, m, st', m', h⟩ := h
  have e : (tryCatch (x >>= fun a => pure (some (g a))) fun _ => (pure none : ElabM (Option β)))
      sc st m = (match x sc st m with
        | .ok ((a, s), m₁) => .ok ((some (g a), s), m₁)
        | .error _ => .ok ((none, st), m)) := by
    show (tryCatch ((x >>= fun a => pure (some (g a))) sc st m) _) = _
    rw [bind_run]
    cases x sc st m <;> rfl
  rw [e] at h
  split at h
  · next a s m₁ hx => cases h; exact ⟨a, ⟨st, m, _, _, hx⟩, rfl⟩
  · cases h

/-- Every successful run of `x` in scope `sc` returns a value satisfying `Q`. -/
def Post {α : Type} (x : ElabM α) (sc : ElabScope) (Q : α → Prop) : Prop :=
  ∀ st m a st' m', x sc st m = .ok ((a, st'), m') → Q a

namespace Post
variable {α β : Type} {sc : ElabScope}

theorem bind {x : ElabM α} {f : α → ElabM β} {Q₁ : α → Prop} {Q : β → Prop}
    (hx : Post x sc Q₁) (hf : ∀ a, Q₁ a → Post (f a) sc Q) : Post (x >>= f) sc Q := by
  intro st m b st' m' h
  rw [bind_run] at h
  split at h
  · next a s m₁ hx' => exact hf a (hx _ _ _ _ _ hx') _ _ _ _ _ h
  · cases h

/-- The continuation may use that its argument was returned by `x`. -/
theorem bind_ret {x : ElabM α} {f : α → ElabM β} {Q : β → Prop}
    (hf : ∀ a, Returns x sc a → Post (f a) sc Q) : Post (x >>= f) sc Q :=
  bind (Q₁ := Returns x sc) (fun st m _ st' m' h => ⟨st, m, st', m', h⟩) hf

theorem bind_true {x : ElabM α} {f : α → ElabM β} {Q : β → Prop}
    (hf : ∀ a, Post (f a) sc Q) : Post (x >>= f) sc Q := bind_ret fun a _ => hf a

theorem ret {a : α} {Q : α → Prop} (h : Q a) : Post (Pure.pure a) sc Q := by
  intro st m b st' m' e; cases e; exact h

theorem fail {e : String} {Q : α → Prop} : Post (throw e : ElabM α) sc Q := by
  intro st m b st' m' h; cases h

theorem throw_bind {e : String} {f : α → ElabM β} {Q : β → Prop} :
    Post ((throw e : ElabM α) >>= f) sc Q := bind (Q₁ := fun _ => False) fail fun _ h => h.elim

theorem read_bind {f : ElabScope → ElabM β} {Q : β → Prop} (h : Post (f sc) sc Q) :
    Post ((read : ElabM ElabScope) >>= f) sc Q :=
  bind (Q₁ := (· = sc)) (by intro st m a st' m' e; cases e; rfl) fun _ e => e ▸ h

theorem cond {c : Prop} [Decidable c] {x y : ElabM α} {Q : α → Prop}
    (hx : Post x sc Q) (hy : Post y sc Q) : Post (if c then x else y) sc Q := by
  split <;> assumption

theorem reader {g : ElabScope → ElabScope} {x : ElabM α} {Q : α → Prop}
    (h : Post x (g sc) Q) : Post (withReader g x) sc Q := fun st m => h st m

theorem zeta {γ : Type} {v : γ} {f : γ → ElabM α} {Q : α → Prop} (h : Post (f v) sc Q) :
    Post (have x := v; f x) sc Q := h

/-- A scoped block followed by a state reset returns the block's value. -/
theorem frame {g : ElabScope → ElabScope} {x : ElabM α} {k : ECtx × Nat → ECtx × Nat}
    {Q : α → Prop} (h : Post x (g sc) Q) :
    Post (withReader g x >>= fun a => modify k >>= fun _ => Pure.pure a) sc Q :=
  bind (reader h) fun _ q => bind_true fun _ => ret q

end Post

/-- One syntax-directed step on a `Post` goal. -/
macro "post_step" : tactic => `(tactic| with_reducible first
  | exact Post.fail
  | exact Post.throw_bind
  | refine Post.frame ?_
  | refine Post.read_bind ?_
  | refine Post.cond ?_ ?_
  | refine Post.bind_ret fun _ _ => ?_
  | split)

/-- Every successful run of `x` in scope `sc` is the run, from some state, of a computation in `K`:
what `x` finally hands over. -/
def Hands {α : Type} (x : ElabM α) (sc : ElabScope) (K : ElabM α → Prop) : Prop :=
  ∀ st m r, x sc st m = .ok r → ∃ y st₁ m₁, K y ∧ y sc st₁ m₁ = .ok r

namespace Hands
variable {α β : Type} {sc : ElabScope}

theorem self {y : ElabM α} {K : ElabM α → Prop} (h : K y) : Hands y sc K :=
  fun st m _ e => ⟨y, st, m, h, e⟩

theorem bind_true {x : ElabM α} {f : α → ElabM β} {K : ElabM β → Prop}
    (hf : ∀ a, Hands (f a) sc K) : Hands (x >>= f) sc K := by
  intro st m r h
  rw [bind_run] at h
  split at h
  · exact hf _ _ _ _ h
  · cases h

theorem fail {e : String} {K : ElabM α → Prop} : Hands (throw e : ElabM α) sc K := by
  intro st m r h; cases h

theorem throw_bind {e : String} {f : α → ElabM β} {K : ElabM β → Prop} :
    Hands ((throw e : ElabM α) >>= f) sc K := by
  intro st m r h; cases h

theorem read_bind {f : ElabScope → ElabM β} {K : ElabM β → Prop} (h : Hands (f sc) sc K) :
    Hands ((read : ElabM ElabScope) >>= f) sc K := fun st m r e => h st m r e

theorem cond {c : Prop} [Decidable c] {x y : ElabM α} {K : ElabM α → Prop}
    (hx : Hands x sc K) (hy : Hands y sc K) : Hands (if c then x else y) sc K := by
  split <;> assumption

/-- A call of `f` in tail position is what is handed over. -/
theorem call {γ : Type} {K : ElabM α → Prop} (f : γ → ElabM α) (l : γ) (h : K (f l)) :
    Hands (f l) sc K := self h

theorem call_bind {γ : Type} {K : ElabM β → Prop} (f : γ → ElabM α) (l : γ) (k : α → ElabM β)
    (h : K (f l >>= k)) : Hands (f l >>= k) sc K := self h

end Hands

/-- One syntax-directed step on a `Hands` goal. -/
macro "hands_step" : tactic => `(tactic| with_reducible first
  | exact Hands.fail
  | exact Hands.throw_bind
  | refine Hands.read_bind ?_
  | refine Hands.cond ?_ ?_
  | refine Hands.bind_true fun _ => ?_
  | split)

/-- The raw fallback of a dispatch through an internal function value. -/
def rawFallback (sc : ElabScope) : RawStmt :=
  if sc.selfFrame || sc.retainFailureData then
    .revertRaw (.bytesLit ((encodePanic 0x51).map UInt8.toNat)) else .revert

variable {C : Contract}

/-- With every guard false a dispatch chain runs its fallback: the data arm emits exactly
`Panic(0x51)`, the other is V1's bare revert. No premise restricts the tag. -/
theorem dispatch_fallback_run {Γ : Ctx} (arms : List (DispatchArm C Γ)) (σ : State C Γ)
    (unmatched : ∀ arm ∈ arms, arm.cond.evalT σ = .ok false) :
    (DispatchArm.chain arms (.revertData [.bytes (encodePanic 0x51)])).runR σ =
      .error (THalt.ofData (encodePanic 0x51)) ∧
    (DispatchArm.chain arms .revert).runR σ = .error .revert := by
  have run (fail : Stmt C Γ Γ) : (DispatchArm.chain arms fail).runR σ = fail.runR σ := by
    rw [Stmt.runR_eq, Stmt.runR_eq]
    exact DispatchArm.chain_none arms fail σ unmatched
  refine ⟨(run _).trans ?_, (run _).trans rfl⟩
  simp [Stmt.runR, TRun.revertData, RevPart.evalT, bind, Except.bind, pure, Except.pure]

variable [FreshNames]

/-- `fnTupleDispatchWith` ends by handing `rc.elabStmtsP` a dispatch whose last `else` is the fallback. -/
theorem fnTupleDispatchWith_fallback (rc : PanicProducerRec C) (ts : List (Option RawExpr))
    (h ty : String) (args : List RawExpr) (sc : ElabScope) :
    Hands (fnTupleDispatchWith C rc ts h ty args) sc fun y =>
      ∃ (pre : List RawStmt) (cands : List (String × Nat)) (tag : RawExpr) (as : List RawExpr),
        y = rc.elabStmtsP (pre ++ [cands.foldr (fun (g, t) rest =>
          RawStmt.ite (.binop .eqB tag (.num t)) [.tupleAssign ts (.call g as)] [rest])
          (rawFallback sc)]) := by
  unfold fnTupleDispatchWith
  dsimp only
  repeat' first
    | (with_reducible refine Hands.call rc.elabStmtsP _ ?_); exact ⟨_, _, _, _, rfl⟩
    | hands_step

/-- `fnMemoryDispatchWith` likewise, before binding the selected call's alias. -/
theorem fnMemoryDispatchWith_fallback (rc : PanicProducerRec C) (h : RawExpr) (ty : String)
    (args : List RawExpr) (sc : ElabScope) :
    Hands (fnMemoryDispatchWith C rc h ty args) sc fun y =>
      ∃ (P : SProg C) (dst : String) (cands : List (String × Nat)) (tag : RawExpr)
          (as : List RawExpr),
        y = (do
          let Q ← rc.elabStmtsP [cands.foldr (fun (g, t) rest =>
            RawStmt.ite (.binop .eqB tag (.num t)) [.assign (.name dst) (.call g as)] [rest])
            (rawFallback sc)]
          pure (P ++ Q, .name dst)) := by
  unfold fnMemoryDispatchWith
  dsimp only
  repeat' first
    | (with_reducible refine Hands.call_bind rc.elabStmtsP _ _ ?_); exact ⟨_, _, _, _, _, rfl⟩
    | hands_step

/-- At an internal function type, every program `fnDispatchWith` returns ends in a dispatch chain
whose fallback is `Panic(0x51)` data exactly when `selfFrame || retainFailureData`. -/
theorem fnDispatchWith_fallback (rc : PanicProducerRec C) (h ty : String) (args : List RawExpr)
    (res : Option (Var × PrimTy)) (resW : Nat) (resNew : Bool) (sc : ElabScope)
    (ps rs : List String) (internal : fnParts? ty = some (ps, rs, false)) :
    Post (fnDispatchWith C rc h ty args res resW resNew) sc fun P =>
      ∃ (P₀ : SProg C) (Γ : NCtx) (arms : List (DispatchArm C Γ.ctx)),
        P = P₀ ++ [.of Γ (DispatchArm.chain arms
          (if sc.selfFrame || sc.retainFailureData then
            .revertData [.bytes (encodePanic 0x51)] else .revert))] := by
  unfold fnDispatchWith
  split
  · rename_i ps' rs' ext' heq
    cases internal.symm.trans heq
    simp (config := {zeta := false}) only [Bool.false_eq_true, ↓reduceIte]
    dsimp only
    repeat' post_step
    all_goals exact Post.ret ⟨_, _, _, rfl⟩
  · exact Post.fail

omit [FreshNames] in
/-- `receiveSelfBodyWith` returns `Stmt.selfCall?` of the very statement `rc.elabCallRet` returned
for the inlined `receive`: no `withPanics` is added. -/
theorem receiveSelfBodyWith_plain (rc : PanicProducerRec C) {Γ : NCtx} (v : RawExpr)
    (sc : ElabScope) :
    Post (receiveSelfBodyWith C rc (Γ := Γ) v) sc fun body =>
      body = none ∨ ∃ (sc' : ElabScope) (st : SStmt C)
          (rest : Option (NCtx × RefTy × Var × Bool) × List (Var × LocalTy))
          (h : st.Γ.ctx = Γ.ctx),
        Returns (rc.elabCallRet "receive" [v] none (targets := true) (selfFrame := true)) sc'
          ([st], rest) ∧
        body = Stmt.selfCall? C [] (h ▸ st.s) := by
  unfold receiveSelfBodyWith
  dsimp only
  repeat' first
    | exact Post.ret (Or.inl rfl)
    | (obtain ⟨⟨_, rest⟩, called, rfl⟩ := Returns.of_tryCatch_some ‹Returns (tryCatch _ _) _ _›
       exact Post.ret (Or.inr ⟨_, _, rest, ‹_›, called.reader, rfl⟩))
    | post_step

/-- `trySelfBodyWith` returns `Stmt.selfCall?` of the very statement `rc.elabCallRet` returned for
the callee `g`, instrumented (`withPanics`) exactly when `g`'s declaration is not a compiler getter. -/
theorem trySelfBodyWith_instrumented (rc : PanicProducerRec C) (g : String) {Γ : NCtx}
    (args : List (ExtArg C Γ.ctx)) (ρ : Ctx) (sc : ElabScope) :
    Post (trySelfBodyWith C rc g args ρ) sc fun body =>
      body = none ∨ ∃ (name : Name) (d : FunDecl) (st : SStmt C)
          (rest : Option (NCtx × RefTy × Var × Bool) × List (Var × LocalTy))
          (h : st.Γ.ctx = Γ.ctx),
        sc.funs.find? (·.1 == g) = some (name, d) ∧
        Returns (rc.elabCallRet g (args.map fun a => Simple.toRaw C Γ.names a.2) none
          (targets := !ρ.isEmpty || d.rets.isEmpty) (selfFrame := true)) sc ([st], rest) ∧
        body = (Stmt.selfCall? C ρ (h ▸ st.s)).map fun ⟨ps, Γf, sargs, sbody⟩ =>
          ⟨ps, Γf, sargs, if (d.sourceDecl.any fun source => match source.callable with
            | .getter _ => true
            | _ => false) then sbody else sbody.withPanics⟩ := by
  unfold trySelfBodyWith
  dsimp only
  repeat' first
    | exact Post.ret (Or.inl rfl)
    | (obtain ⟨⟨_, rest⟩, called, rfl⟩ := Returns.of_tryCatch_some ‹Returns (tryCatch _ _) _ _›
       exact Post.ret (Or.inr ⟨_, _, _, rest, ‹_›, ‹_›, called, rfl⟩))
    | post_step

end Solidity.Correctness.Panic
