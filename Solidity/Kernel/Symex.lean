import Solidity.Kernel.Logic

/-!
# The symbolic executor

`Kont.vc n H k` runs the calculus: at each modality it takes the rule
`Stmt.step` picks, and what is left are the goals no rule decides — a
postcondition under the hypotheses the run collected, a branch the
hypotheses rule out, a diamond condition's definedness.  `Kont.vc_sound`
turns a proof of them into a derivation of `Proves`, so a program is proved
by stating the goals it leaves and discharging them.

`n` is fuel, one unit per rule application; the termination measure
(`Taclet.smaller`) says a program's size is enough for its own statements.
-/

namespace Solidity
namespace Kernel

open Semantics

variable {C : Contract}

/-- The goals `H ⊢ k` leaves once every statement is run, with `n` rule
applications to spend (`False` when they run out).  `ψ` under `H` is a goal;
a `revert` under a box closes as far as `H` allows, and under a diamond only
where `H` is false. -/
def Kont.vc : Nat → {Γ₀ Γ : Ctx} → Hyps C Γ₀ Γ → Kont C Γ → Prop
  | 0, _, _, _, _ => False
  | _ + 1, _, _, H, .post ψ => ∀ σ, H.holds ψ.holds σ
  | n + 1, _, _, H, .up h k => Kont.vc n (H.shrink h) k
  | n + 1, _, _, H, .modal m P k =>
    match P with
    | .nil => Kont.vc n H k
    | .cons s ω =>
      match (s.step m).1 with
      | .update U => Kont.vc n (H.upd m U) (.modal m ω k)
      | .unfold _ P h => Kont.vc n H (.modal m P (.up h (.modal m ω k)))
      | .split c P Q =>
        Kont.vc n (H.cond c true) (.modal m (P.append ω) k) ∧
        Kont.vc n (H.cond c false) (.modal m (Q.append ω) k) ∧
        (m = .diamond → ∀ σ, H.holds (Post.defined c).holds σ)
      | .done b => ∀ σ, H.holds (fun _ => b = true) σ

/-- **The executor is sound**: the goals it leaves prove the continuation.
`⟨ uint x = 1; ⟩ x == 1` follows from `{x := 1} x == 1`. -/
theorem Kont.vc_sound : (n : Nat) → {Γ₀ Γ : Ctx} → (H : Hyps C Γ₀ Γ) → (k : Kont C Γ) →
    k.vc n H → Proves H k
  | 0, _, _, _, _, h => h.elim
  | _ + 1, _, _, _, .post _, h => .close h
  | n + 1, _, _, _, .up _ k, h => .up (Kont.vc_sound n _ k h)
  | n + 1, _, _, H, .modal m P k, h => by
    cases P with
    | nil => exact .empty (Kont.vc_sound n H k h)
    | cons s ω =>
      simp only [Kont.vc] at h
      have d := (s.step m).2
      revert h d
      generalize (s.step m).1 = pr
      intro h d
      cases pr with
      | update U => exact .update d (Kont.vc_sound n _ _ h)
      | unfold ns P h' => exact .unfold d (Kont.vc_sound n _ _ h)
      | split c P Q =>
        exact .split d (Kont.vc_sound n _ _ h.1) (Kont.vc_sound n _ _ h.2.1)
          (fun hm => .close (h.2.2 hm))
      | done b =>
        cases b with
        | true => exact .done d (.close fun σ => Hyps.mono (fun _ _ => trivial) _ σ (h σ))
        | false => exact .absurd fun σ => Hyps.mono (fun _ h => Bool.false_ne_true h) _ σ (h σ)

/-- **A proved program runs correctly**: if the executor's goals for
`⟨ P ⟩ ψ` hold from the precondition `φ`, then from every state satisfying
`φ`, `P` ends normally in a state satisfying `ψ`; for `[ P ] ψ`, it may also
fail.  Stated over the untyped interpreter, `execBlock`: from a state whose
storage is `alice.age = 0`, `alice.age = 10; assert(alice.age == 10);`
does not revert. -/
theorem Prog.correct {Γ Γ' : Ctx} (m : Modality) (P : Prog C Γ Γ') (ψ : Post C Γ') (n : Nat)
    (φ : State → Prop) (h : (Kont.modal m P (.post ψ)).vc n (.assume φ)) (σ : State) (hσ : φ σ) :
    after m (execBlock σ P.erase) ψ.holds := by
  rw [Prog.run_eq]; exact (Kont.vc_sound n _ _ h).sound σ hσ

/-! ## Termination

The fuel is not a limit: `Kont.weight` is enough, and any more gives the
same goals.  A statement weighs `5 ^ size`; `Taclet.smaller` makes every
rule lower the weight of the goal. -/

/-- A block's weight: `Σ 5 ^ size`. -/
def Prog.weight {Γ Γ' : Ctx} : Prog C Γ Γ' → Nat
  | .nil => 0
  | .cons s P => 5 ^ s.size + P.weight

/-- A goal's weight: its blocks, and one for each modality, `up` and
postcondition. -/
def Kont.weight {Γ : Ctx} : Kont C Γ → Nat
  | .post _ => 1
  | .modal _ P k => 5 * P.weight + k.weight + 1
  | .up _ k => k.weight + 1

theorem Kont.one_le_weight {Γ : Ctx} (k : Kont C Γ) : 1 ≤ k.weight := by
  cases k <;> simp only [Kont.weight] <;> omega

theorem Stmt.one_le_size {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : 1 ≤ s.size := by
  cases s <;> simp only [Stmt.size] <;> (try split) <;> omega

theorem Prog.weight_append {Γ Γ₁ Γ₂ : Ctx} :
    (P : Prog C Γ Γ₁) → (Q : Prog C Γ₁ Γ₂) → (P.append Q).weight = P.weight + Q.weight
  | .nil, Q => by simp [Prog.append, Prog.weight]
  | .cons s P, Q => by simp only [Prog.append, Prog.weight, Prog.weight_append P Q]; omega

theorem five_pow_add {a b : Nat} (ha : 1 ≤ a) (hb : 1 ≤ b) : 5 ^ a + 5 ^ b ≤ 5 ^ (a + b) := by
  rw [Nat.pow_add]
  have h₁ : 5 ^ a * 5 ≤ 5 ^ a * 5 ^ b :=
    Nat.mul_le_mul_left _ (by simpa using Nat.pow_le_pow_right (by omega) hb)
  have h₂ : 5 * 5 ^ b ≤ 5 ^ a * 5 ^ b :=
    Nat.mul_le_mul_right _ (by simpa using Nat.pow_le_pow_right (by omega) ha)
  omega

/-- A block weighs at most `5 ^` its size: `x = 1; y = 2;` weighs
`5² + 5² ≤ 5⁴`. -/
theorem Prog.weight_le {Γ Γ' : Ctx} : (P : Prog C Γ Γ') → P.weight ≤ 5 ^ P.size
  | .nil => by simp [Prog.weight]
  | .cons s P => by
    simp only [Prog.weight, Prog.size]
    cases P with
    | nil => simp [Prog.weight, Prog.size]
    | cons s' P' =>
      have := Prog.weight_le (.cons s' P')
      have h1 := s.one_le_size
      have h2 : 1 ≤ (Prog.cons s' P').size := by
        simp only [Prog.size]; have := s'.one_le_size; omega
      have := five_pow_add h1 h2
      omega

/-- At most four statements, each smaller than `m`, weigh at most
`4 · 5 ^ (m - 1)`. -/
theorem Prog.weight_of_sizes {Γ Γ' : Ctx} (m : Nat) :
    (P : Prog C Γ Γ') → (∀ n ∈ P.sizes, n < m) → 5 * P.weight ≤ P.sizes.length * 5 ^ m
  | .nil, _ => by simp [Prog.weight]
  | .cons s P, h => by
    simp only [Prog.weight, Prog.sizes, List.length, List.mem_cons, forall_eq_or_imp] at h ⊢
    have ih := Prog.weight_of_sizes m P h.2
    have : 5 ^ s.size * 5 ≤ 5 ^ m := by
      rw [← Nat.pow_succ]; exact Nat.pow_le_pow_right (by omega) h.1
    rw [Nat.add_mul, Nat.one_mul]; omega

/-- **The executor normalizes**: once the fuel reaches the goal's weight,
more changes nothing.  `⟨ uint x = 1; ⟩ true` has the same goals at fuel
30 as at fuel 3000. -/
theorem Kont.vc_fuel : (n n' : Nat) → {Γ₀ Γ : Ctx} → (H : Hyps C Γ₀ Γ) → (k : Kont C Γ) →
    k.weight ≤ n → k.weight ≤ n' → (k.vc n H ↔ k.vc n' H)
  | 0, _, _, _, _, k, h, _ => absurd h (by have := k.one_le_weight; omega)
  | _ + 1, 0, _, _, _, k, _, h => absurd h (by have := k.one_le_weight; omega)
  | _ + 1, _ + 1, _, _, _, .post _, _, _ => Iff.rfl
  | n + 1, n' + 1, _, _, _, .up _ k, h, h' => by
    simp only [Kont.weight] at h h'
    exact Kont.vc_fuel n n' _ k (by omega) (by omega)
  | n + 1, n' + 1, _, _, H, .modal m P k, h, h' => by
    cases P with
    | nil =>
      simp only [Kont.weight, Prog.weight] at h h'
      exact Kont.vc_fuel n n' H k (by omega) (by omega)
    | cons s ω =>
      simp only [Kont.vc]
      have hs := Taclet.smaller (s.step m).2
      have h1 := s.one_le_size
      have h5 : 5 ≤ 5 ^ s.size := by simpa using Nat.pow_le_pow_right (by omega) h1
      simp only [Kont.weight, Prog.weight] at h h'
      revert hs
      generalize (s.step m).1 = pr
      intro hs
      cases pr with
      | update U =>
        exact Kont.vc_fuel n n' _ _ (by simp only [Kont.weight]; omega) (by simp only [Kont.weight]; omega)
      | unfold ns P hsub =>
        obtain ⟨hlen, hlt⟩ := hs
        have hw := Prog.weight_of_sizes s.size P hlt
        have : P.sizes.length * 5 ^ s.size ≤ 4 * 5 ^ s.size := Nat.mul_le_mul_right _ hlen
        exact Kont.vc_fuel n n' _ _ (by simp only [Kont.weight]; omega) (by simp only [Kont.weight]; omega)
      | split c P Q =>
        obtain ⟨hP, hQ⟩ := hs
        have hP' : P.weight < 5 ^ s.size :=
          Nat.lt_of_le_of_lt P.weight_le (Nat.pow_lt_pow_right (by omega) hP)
        have hQ' : Q.weight < 5 ^ s.size :=
          Nat.lt_of_le_of_lt Q.weight_le (Nat.pow_lt_pow_right (by omega) hQ)
        dsimp only
        rw [Kont.vc_fuel n n' _ (.modal m (P.append ω) k)
            (by simp only [Kont.weight, Prog.weight_append]; omega)
            (by simp only [Kont.weight, Prog.weight_append]; omega),
          Kont.vc_fuel n n' _ (.modal m (Q.append ω) k)
            (by simp only [Kont.weight, Prog.weight_append]; omega)
            (by simp only [Kont.weight, Prog.weight_append]; omega)]
      | done b => exact Iff.rfl

/-- The goals of `H ⊢ k`, with the fuel its weight gives. -/
def Kont.goals {Γ₀ Γ : Ctx} (H : Hyps C Γ₀ Γ) (k : Kont C Γ) : Prop := k.vc k.weight H

/-- The goals at any fuel past the weight are `Kont.goals`. -/
theorem Kont.vc_goals {Γ₀ Γ : Ctx} {H : Hyps C Γ₀ Γ} {k : Kont C Γ} {n : Nat}
    (h : k.weight ≤ n) : k.vc n H ↔ k.goals H :=
  Kont.vc_fuel n k.weight H k h (Nat.le_refl _)

/-- The goals prove the continuation: `⟨ uint x = 1; ⟩ true` follows from
`{x := 0} {x := 1} true`. -/
theorem Kont.goals_sound {Γ₀ Γ : Ctx} {H : Hyps C Γ₀ Γ} {k : Kont C Γ} (h : k.goals H) :
    Proves H k :=
  Kont.vc_sound _ H k h

/-! ## Tactics -/

open Lean Meta Simp in
/-- A scratch name at a closed context is a string: `freshName C [se] "se"`
is `"se1"`.  Evaluated, then checked by the kernel by reduction. -/
dsimproc reduceFreshName (freshName _ _ _) := fun e => do
  unless e.isAppOfArity ``freshName 3 do return .continue
  if e.hasFVar || e.hasMVar then return .continue
  let s ← unsafe evalExpr String (mkConst ``String) e
  return .done (toExpr s)

/-- `symex`: run the executor on a goal `k.vc n H`, stepping through every
statement and splitting every branch, until what is left are the goals
`∀ σ, H.holds ψ σ` (or `False`, when the fuel runs out). -/
macro "symex" : tactic => `(tactic| repeat' (first
  | (rw [Kont.vc]; try simp only [Stmt.step, localStep, assignStep, rebindStep, deleteStep,
      binopRightStep, shortCircuitStep, copyStep, opStep, incStep, assignIncStep, ternaryStep, pushStep, popStep, transferStep, rebindMemStep, declMemStep, assignMemStep, assignFromMemStep,
      MHole.unfoldStep, MHole.fill, MHole.extend, MPath.isSimple, MPath.isBindable, MPath.new,
      MPath.weaken, MLoc.weaken, VHole.fill, VHole.weaken,
      Src.isSimple, Src.decl, Src.fresh,
      Hole.unfoldStep, Prog.append, Val.weaken,
      OpLoc.weaken,
      Simple.weaken, Loc.weaken, SPath.weaken, Src.weaken, Val.isSimple, SPath.isSimple,
      SPath.isBindable, dite_true, dite_false, Bool.false_eq_true, and_self, and_true, true_and,
      and_false, false_and, reduceFreshName])
  | constructor))

/-- `symex_close [lemmas]`: discharge a goal `symex` leaves by evaluating the
hypotheses' updates and conditions, the precondition's facts among them;
`lemmas` unfold what the precondition names (a contract's initial
storage). -/
syntax "symex_close" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| symex_close) => `(tactic| symex_close [])
  | `(tactic| symex_close [$args,*]) =>
    `(tactic| (simp only [Hyps.holds]; intros; simp_all [Upd.apply, after, Val.eval, Simple.eval,
      PrimTy.defaultSimple, Post.holds, Post.defined, getEnv_setEnv_ne, bind, Except.bind, pure,
      Except.pure, applyBinOp, applyUnOp, unopCheck, checkArith, BinOp.retTy, Value.asInt,
      Value.asBool, Value.toSVal, BinOp.isArith, uintBound, intBound, reduceFreshName, Src.value,
      Loc.target, Loc.resolve, SPath.resolve, Simple.new, envPath, State.saveStorage, OpLoc.store,
      opStore, opLocal, pickBranch, pushAt, popAt, Src.pushVal, pushSlot, transferAt, State.setNet, State.getNet,
      MPath.mval, MLoc.read, MLoc.write, MSrc.mval, MRhs.bind, memWriteField, memWriteIndex,
      MVal.asRef, MVal.asValue, Value.toMVal, allocDefault, copyStToM, copyStFields, copyStElems,
      State.getObj, State.setObj, State.alloc, opMem, bumpMem, readLoc, writeLoc, copyMem, copyMToSt, copyMFields, copyMElems, OpLoc.bump, bumpStore, bumpLocal, IncDec.isPre, IncDec.isIncrement,
      State.findStorage, State.setEnv, State.getEnv, SVal.save, SVal.find, SVal.asValue,
      SVal.defaultOf, defaultForRef, defaultForTy, defaultForFields, structDef, Functor.map,
      Except.map, lookupBy, setBy, SemanticsProperties.lookupBy_setBy_self,
      SemanticsProperties.lookupBy_setBy_ne, $args,*]))

/-! ## Examples

A specification is a diamond ending in `assert`s: `⟨ P; assert(c); ⟩ true`
says `P` does not fail and ends where `c` holds. -/

section Examples

local instance instSymexContract : InContract := ⟨StandardExample⟩

def exAdd := ksol{ uint x = 1; x = x + 2; assert(x == 3); }
def exIf := ksol{ uint x = 1; if (x == 1) { x = 2; } else { x = 3; }; assert(x == 2); }
def exStore := ksol{ alice.age = 10; assert(alice.age == 10); }
def exBad := ksol{ uint x = 1; x = x + 2; assert(x == 4); }

example : (Kont.modal .diamond exAdd (.post .tt)).vc 30 .nil := by
  unfold exAdd; symex <;> symex_close

/-- The same goals, at the fuel the weight bounds (`19502`; 30 is enough, and any fuel past the weight gives the same goals). -/
example : (Kont.modal .diamond exAdd (.post .tt)).goals .nil := by
  rw [← Kont.vc_goals (n := 20000) (by decide)]
  unfold exAdd; symex <;> symex_close

/-- Both branches run; the `else` one is ruled out by its condition. -/
example : (Kont.modal .diamond exIf (.post .tt)).vc 60 .nil := by
  unfold exIf; symex <;> symex_close

/-- From the initial storage, and no locals, `alice.age = 10;` makes
`alice.age == 10` hold. -/
theorem exStore_vc : (Kont.modal .diamond exStore (.post .tt)).vc 60
    (.assume fun σ => σ.storage = StandardExample.initStorage ∧ σ.env = []) := by
  unfold exStore; symex <;> symex_close [initStorage_standardExample, State.exampleStore]

def exOp := ksol{ uint x = 1; x += 2; x *= x; assert(x == 9); }
def exOpStore := ksol{ total += 5; alice.age -= 0; assert(total == 5); }

/-- Compound assignments on a local. -/
example : (Kont.modal .diamond exOp (.post .tt)).vc 30 .nil := by
  unfold exOp; symex <;> symex_close

/-- And in storage, from the initial one. -/
example : (Kont.modal .diamond exOpStore (.post .tt)).vc 60
    (.assume fun σ => σ.storage = StandardExample.initStorage ∧ σ.env = []) := by
  unfold exOpStore; symex <;> symex_close [initStorage_standardExample, State.exampleStore]

def exInc := ksol{ uint x = 1; uint y; x++; y = ++x; assert(y == 3); total++; y = total++; assert(y == 1); }

/-- `++` on a local and in storage, both forms. -/
example : (Kont.modal .diamond exInc (.post .tt)).vc 60
    (.assume fun σ => σ.storage = StandardExample.initStorage ∧ σ.env = []) := by
  unfold exInc; symex <;> symex_close [initStorage_standardExample, State.exampleStore]

def exTern := ksol{ uint x = 3; x = (x > 2) ? x + 1 : 0; total = (x == 4) ? 7 : x; assert(total == 7); }

set_option maxHeartbeats 1000000 in
/-- A conditional lowers to a branch; the branch not taken is ruled out. -/
example : (Kont.modal .diamond exTern (.post .tt)).vc 80
    (.assume fun σ => σ.storage = StandardExample.initStorage ∧ σ.env = []) := by
  unfold exTern; symex <;> symex_close [initStorage_standardExample, State.exampleStore]

def exPush := ksol{ values.push(5); values.push(); uint x = values[0]; assert(x == 5); values.pop(); values.pop(); }

set_option maxHeartbeats 1000000 in
/-- Two pushes and two pops on an empty array, reading the first element. -/
example : (Kont.modal .diamond exPush (.post .tt)).vc 80
    (.assume fun σ => σ.storage = StandardExample.initStorage ∧ σ.env = []) := by
  unfold exPush; symex <;> symex_close [initStorage_standardExample, State.exampleStore]

def exPay := ksol{ uint a = 3; a.transfer(4); a.transfer(a + 3); }

/-- With 10 in funds, paying 4 and then 6 does not revert. -/
example : (Kont.modal .diamond exPay (.post .tt)).vc 40 (.assume fun σ => σ.selfBalance = 10) := by
  unfold exPay; symex <;> symex_close

def exMem := ksol{ Person memory m; m.age = 5; Person memory n = m; uint x = n.age; assert(x == 5); }

set_option maxHeartbeats 1000000 in
/-- A fresh memory object, written and read back through an alias. -/
example : (Kont.modal .diamond exMem (.post .tt)).vc 80
    (.assume fun σ => σ.heap = [] ∧ σ.nextId = 0 ∧ σ.env = []) := by
  unfold exMem; symex <;> symex_close

def exCopy := ksol{ alice.age = 7; Person memory m = alice; alice.age = 8; uint x = m.age; assert(x == 7); }

set_option maxHeartbeats 2000000 in
/-- A copy into memory is a snapshot: a later write to storage does not reach it. -/
example : (Kont.modal .diamond exCopy (.post .tt)).vc 80
    (.assume fun σ => σ.storage = StandardExample.initStorage ∧ σ.heap = [] ∧ σ.nextId = 0 ∧ σ.env = []) := by
  unfold exCopy; symex <;> symex_close [initStorage_standardExample, State.exampleStore]

def exBack := ksol{ Person memory m; m.age = 9; alice = m; m.age = 1; uint x = alice.age; assert(x == 9); }

set_option maxHeartbeats 2000000 in
/-- A copy into storage is a snapshot too. -/
example : (Kont.modal .diamond exBack (.post .tt)).vc 80
    (.assume fun σ => σ.storage = StandardExample.initStorage ∧ σ.heap = [] ∧ σ.nextId = 0 ∧ σ.env = []) := by
  unfold exBack; symex <;> symex_close [initStorage_standardExample, State.exampleStore]

def exMemOp := ksol{ Person memory m; m.age += 3; m.age++; bool b = true; m.age = b ? m.age * 2 : 0; uint x = m.age; assert(x == 8); }

set_option maxHeartbeats 2000000 in
/-- Arithmetic on a memory member, and a conditional into it. -/
example : (Kont.modal .diamond exMemOp (.post .tt)).vc 120
    (.assume fun σ => σ.heap = [] ∧ σ.nextId = 0 ∧ σ.env = []) := by
  unfold exMemOp; symex <;> symex_close

/-- A false specification leaves a goal no evaluation closes. -/
example : True := by
  fail_if_success
    have : (Kont.modal .diamond exBad (.post .tt)).vc 30 .nil := by
      unfold exBad; symex <;> symex_close
  trivial

/-- **The interpreter agrees**: from `StandardExample`'s initial storage,
`alice.age = 10; bool se = alice.age == 10; assert(se);` runs without
reverting. -/
theorem exStore_runs (σ : State) (hs : σ.storage = StandardExample.initStorage) (he : σ.env = []) :
    ∃ τ, execBlock σ exStore.erase = .ok τ := by
  have := Prog.correct .diamond exStore .tt 60 _ exStore_vc σ ⟨hs, he⟩
  revert this; cases execBlock σ exStore.erase <;> simp [after]

end Examples

end Kernel
end Solidity
