import Solidity.Semantics.ContractWorld

/-!
# Source-wrapper certificates for executed world operations

Certificates erase only a returned value, never a world or a failure. The
paid empty caller frame remains outside the creation catch. Reachability
requires both a funded reachable input and the explicit admission premise.
These are world API laws, not new statements or dynamic-logic rules.
-/

namespace Solidity.ContractWorld
variable {K : Type} [DecidableEq K] {contracts : K → Contract}

/-- Forget a source return value while retaining the exact world or halt. -/
def forgetResult {α : Type} : TRes (World contracts × α) → TRes (World contracts)
  | .ok (next, _) => .ok next
  | .error e => .error e

/-- An empty caller frame, before the source wrapper's world effect. -/
def World.paidRun {α : Type} (w : World contracts) {k : K} (self : Handle k)
    (ctx : Context) (payable : Bool)
    (next : World contracts → TRes (World contracts × α)) : TRes (World contracts × α) := do
  let st ← TRes.ofOpt (w.storage? self)
  let entry ← w.enter self.address ctx st payable
  let paid ← w.finish self.address entry
  next paid

/-- An empty typed call executes exactly the source wrapper's paid entry. -/
theorem World.call_empty (w : World contracts) {k : K} (self : Handle k)
    (ctx : Context) (payable : Bool) :
    w.call self (Entry.unit .nil payable) ctx =
      if w.isLibrary k then .error .revert else
        w.paidRun self ctx payable (fun next => .ok (next, ())) := by
  unfold World.call World.callFrame Entry.unit
  simp only [emptyBody, Bool.not_true, Bool.and_false, Bool.or_false]
  split
  · rfl
  · unfold World.paidRun
    cases hs : w.storage? self with
    | none => rfl
    | some st =>
      simp only [TRes.ofOpt, bind, Except.bind]
      cases he : w.enter self.address ctx st payable with
      | error e => rfl
      | ok entry =>
        have empty : (Prog.nil : Prog (contracts k) [] []).run entry =
            .ok ⟨entry, List.prefix_refl _⟩ := rfl
        simp only [empty]
        cases hf : w.finish self.address entry <;> rfl

/-- A paid caller prefix composes with the same actual operation as its tail. -/
theorem World.paidRun_certificate {α : Type} (w : World contracts) {k : K}
    (self : Handle k) (ctx : Context) (payable : Bool)
    (tail : World contracts → TRes (World contracts × α)) (op : Operation contracts)
    (ordinary : w.isLibrary k = false)
    (certified : ∀ next, forgetResult (tail next) = op.run next) :
    forgetResult (w.paidRun self ctx payable tail) =
      (Operation.seq (.call k self (Entry.unit .nil payable) ctx) op).run w := by
  simp only [Operation.run, World.call_empty, ordinary, Bool.false_eq_true, ↓reduceIte]
  unfold World.paidRun
  cases hs : w.storage? self with
  | none => rfl
  | some st =>
    simp only [TRes.ofOpt, bind, Except.bind]
    cases he : w.enter self.address ctx st payable with
    | error e => rfl
    | ok entry =>
      dsimp only
      cases hf : w.finish self.address entry with
      | error e => rfl
      | ok next => exact certified next

/-- The factory's static guard remains outside its paid caller and creation
frames. This equality includes failures, not just successful worlds. -/
theorem World.guardedPaidRun_certificate {α : Type} (w : World contracts) {k : K}
    (self : Handle k) (ctx : Context) (payable : Bool)
    (tail : World contracts → TRes (World contracts × α)) (op : Operation contracts)
    (certified : ∀ next, forgetResult (tail next) = op.run next) :
    forgetResult (if w.isLibrary k || ctx.isStatic then .error .revert else
      w.paidRun self ctx payable tail) =
      (Operation.seq (.guard (!ctx.isStatic))
        (.seq (.call k self (Entry.unit .nil payable) ctx) op)).run w := by
  cases hr : w.isLibrary k <;> cases hs : ctx.isStatic
  · simpa only [hr, hs, Bool.false_or, Bool.not_false, Bool.false_eq_true,
      ↓reduceIte, Operation.run, bind, Except.bind] using
      World.paidRun_certificate w self ctx payable tail op hr certified
  · simp only [Bool.false_or, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, Operation.run, bind, Except.bind, forgetResult]
  · simp only [Bool.true_or, Bool.not_false, ↓reduceIte,
      Operation.run, World.call_empty, hr, bind, Except.bind, forgetResult]
  · simp only [Bool.true_or, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, Operation.run, bind, Except.bind, forgetResult]

/-- A linked call's world-only result is its existing operation. -/
theorem Operation.libraryCall_certificate (w : World contracts) (k : K)
    (self : Handle k) (library : Library contracts k Unit) (ctx : Context) :
    forgetResult (w.libraryCall self library ctx) =
      (.libraryCall k self library ctx : Operation contracts).run w := by
  simp only [Operation.run]
  cases w.libraryCall self library ctx <;> rfl

/-- Direct creation's result erasure is its existing operation. -/
theorem Operation.create_certificate (w : World contracts) (k : K) (target : Address)
    (ctor : Prog (contracts k) [] []) (ctx : Context) :
    forgetResult (w.create k target ctor ctx) = (.create k target ctor ctx : Operation contracts).run w := by
  simp only [Operation.run]
  cases w.create k target ctor ctx <;> rfl

/-- Constant success/catch returns do not alter the executed creation world.
The equality retains every failure, including argument failure and exhaustion. -/
theorem Operation.tryCreate_certificate {α β : Type} (w : World contracts)
    (args : TRes α) (k : K) (target : α → Address)
    (ctor : α → Prog (contracts k) [] []) (context : α → Context) (ok err : β) :
    forgetResult (w.tryCreate args k target ctor context
      (fun next _ => .ok (next, ok)) (fun before _ => .ok (before, err))) =
      (.tryCreate args k target ctor context : Operation contracts).run w := by
  cases args with
  | error e => rfl
  | ok a =>
    simp only [World.tryCreate, Operation.run, bind, Except.bind]
    split
    · rfl
    · cases w.create k (target a) (ctor a) (context a) with
      | ok result => rfl
      | error e =>
        cases hc : catchable e <;>
          simp only [hc, Bool.false_eq_true, ↓reduceIte, forgetResult, pure, Except.pure]

/-- Argument failure remains outside the operation's creation catch. -/
theorem Operation.tryCreate_argument_failure {α : Type} (w : World contracts) (e : THalt)
    (k : K) (target : α → Address) (ctor : α → Prog (contracts k) [] [])
    (context : α → Context) :
    (.tryCreate (.error e) k target ctor context : Operation contracts).run w = .error e := rfl

/-- Exhaustion/divergence of the constructor supplies neither a catch nor a
successful operation. In particular it cannot witness a committed transition. -/
theorem Operation.tryCreate_uncaught {α : Type} (w : World contracts) (a : α)
    (k : K) (target : α → Address) (ctor : α → Prog (contracts k) [] [])
    (context : α → Context) (e : THalt) (mutable : (context a).isStatic = false)
    (failed : w.create k (target a) (ctor a) (context a) = .error e)
    (uncaught : catchable e = false) :
    (.tryCreate (.ok a) k target ctor context : Operation contracts).run w = .error e := by
  simp only [Operation.run, World.tryCreate, bind, Except.bind, mutable,
    Bool.false_eq_true, ↓reduceIte, failed, uncaught]

/-- A caught creation failure retains exactly its input world. For a factory
this input is the world after the outer caller's payment, not before it. -/
theorem Operation.tryCreate_caught {α : Type} (w : World contracts) (a : α)
    (k : K) (target : α → Address) (ctor : α → Prog (contracts k) [] [])
    (context : α → Context) (e : THalt) (mutable : (context a).isStatic = false)
    (failed : w.create k (target a) (ctor a) (context a) = .error e)
    (caught : catchable e = true) :
    (.tryCreate (.ok a) k target ctor context : Operation contracts).run w = .ok w := by
  simp only [Operation.run, World.tryCreate, bind, Except.bind, mutable,
    Bool.false_eq_true, ↓reduceIte, failed, caught, ↓reduceIte, pure, Except.pure]

/-- An exact execution certificate yields funded reachability only from a
reachable input, under the world's explicit admission relation. -/
theorem Reachable.of_certificate {α : Type} {funding : Address → Word} {roles : K → Role}
    {allowed : World contracts → Operation contracts → Prop} {w next : World contracts}
    {op : Operation contracts} {run : TRes (World contracts × α)} {result : α}
    (before : Reachable funding roles allowed w) (admitted : allowed w op)
    (certificate : forgetResult run = op.run w) (success : run = .ok (next, result)) :
    Reachable funding roles allowed next := by
  apply before.step (Step.commit admitted ?_)
  rw [← certificate, success]
  rfl

#print axioms World.paidRun_certificate
#print axioms Operation.tryCreate_certificate
#print axioms Operation.tryCreate_uncaught
#print axioms Reachable.of_certificate
end Solidity.ContractWorld
