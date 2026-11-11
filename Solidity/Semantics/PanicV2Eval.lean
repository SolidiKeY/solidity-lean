import Solidity.Semantics.PanicV2

/-!
# Expression and path evaluation through the exact V2 result interface

This structural evaluator uses the same typed state and the same operand
order/short circuit as V1. Each path/value constructor has an unconditional
projection theorem. Site classifiers are refined by family; unclassified
failed options remain unknown rather than receiving guessed panic codes.
-/

namespace Solidity.PanicV2.Eval

variable {C : Contract} {Γ : Ctx}

mutual

def path (σ : State C Γ) : {T : Ty} → SPath C Γ T → Result (SRef C T)
  | _, .alias i => ofOpt (TEnv.get i σ.env)
  | _, .loc l => loc σ l

def loc (σ : State C Γ) : {T : Ty} → Loc C Γ T → Result (SRef C T)
  | _, .root r h => .ok (SRef.ofRoot r h)
  | _, .field b _ h => do
    let r ← path σ b
    pure (r.field h)
  | _, .index it b i => do
    let r ← path σ b
    let k ← value σ i
    let _ ← ofOpt (σ.storage.checkIndex r it k)
    pure (r.index it k)

def mpath (σ : State C Γ) : {T : Ty} → MPath C Γ T → Result (MVal σ.H T)
  | _, .var i _ => ofOpt (TEnv.get i σ.env)
  | _, .loc l => do ofOpt (σ.heap.readAddr (← mloc σ l))

def mloc (σ : State C Γ) : {T : Ty} → MLoc C Γ T → Result (MAddr σ.H T)
  | _, .field b _ h => do
    let r ← mpath σ b
    pure (.field r h)
  | _, .index a b i => do
    let r ← mpath σ b
    let k ← value σ i
    pure (.index r a k)

def value (σ : State C Γ) : {p : PrimTy} → Val C Γ p → Result p.Denote
  | _, .simple s => .ok (s.evalT σ)
  | _, .read l => do
    let r ← loc σ l
    let v ← ofOpt (σ.storage.find r)
    pure v.view
  | _, .binop op h hq a b => do
    let x ← value σ a
    match op.shortT x with
    | some y => pure (hq ▸ y)
    | none => do
      let y ← value σ b
      hq ▸ ofOpt (op.evalT h x y)
  | _, .unop op h hq a => do
    let x ← value σ a
    hq ▸ ofOpt (op.evalT h x)
  | _, .ternary c a b => do
    let test ← value σ c
    if boolT test then value σ a else value σ b
  | _, .readMem l => do ofOpt (σ.heap.readAddr (← mloc σ l))
  | _, .len b hp => do
    let r ← path σ b
    let n ← ofOpt (σ.storage.len r)
    pure (hp ▸ n)
  | _, .mlen b hp => do
    let r ← mpath σ b
    pure (hp ▸ σ.heap.lenU r)
  | _, .modular op a b k => do
    let x ← value σ a
    let y ← value σ b
    let m ← value σ k
    ofOpt (op.evalT x y m)
  | _, .hash k b hp => do
    let r ← mpath σ b
    pure (hp ▸ σ.heap.hash k r)

end

mutual

theorem path_erase (σ : State C Γ) : {T : Ty} → (b : SPath C Γ T) →
    erase (path σ b) = b.resolveT σ
  | _, .alias i => by
      simp only [path, SPath.resolveT, erase_ofOpt, TRes.ofOpt]
      cases TEnv.get i σ.env <;> rfl
  | _, .loc l => loc_erase σ l

theorem loc_erase (σ : State C Γ) : {T : Ty} → (l : Loc C Γ T) →
    erase (loc σ l) = l.resolveT σ
  | _, .root .. => rfl
  | _, .field b _ _ => erase_bind_congr (path_erase σ b) fun _ => rfl
  | _, .index _ b i => erase_bind_congr (path_erase σ b) fun _ =>
      erase_bind_congr (value_erase σ i) fun _ =>
        erase_bind_congr (erase_ofOpt _) fun _ => rfl

theorem mpath_erase (σ : State C Γ) : {T : Ty} → (b : MPath C Γ T) →
    erase (mpath σ b) = b.mvalT σ
  | _, .var i _ => by
      simp only [mpath, MPath.mvalT, erase_ofOpt, TRes.ofOpt]
      cases TEnv.get i σ.env <;> rfl
  | _, .loc l => erase_bind_congr (mloc_erase σ l) fun _ => erase_ofOpt _

theorem mloc_erase (σ : State C Γ) : {T : Ty} → (l : MLoc C Γ T) →
    erase (mloc σ l) = l.addrT σ
  | _, .field b _ _ => erase_bind_congr (mpath_erase σ b) fun _ => rfl
  | _, .index _ b i => erase_bind_congr (mpath_erase σ b) fun _ =>
      erase_bind_congr (value_erase σ i) fun _ => rfl

theorem value_erase (σ : State C Γ) : {p : PrimTy} → (v : Val C Γ p) →
    erase (value σ v) = v.evalT σ
  | _, .simple _ => rfl
  | _, .read l => erase_bind_congr (loc_erase σ l) fun _ =>
      erase_bind_congr (erase_ofOpt _) fun _ => rfl
  | _, .binop op _ hq a b => by
    subst hq
    refine erase_bind_congr (value_erase σ a) fun x => ?_
    cases op.shortT x with
    | some _ => rfl
    | none => exact erase_bind_congr (value_erase σ b) fun _ => erase_ofOpt _
  | _, .unop _ _ hq a => by
    subst hq
    exact erase_bind_congr (value_erase σ a) fun _ => erase_ofOpt _
  | _, .ternary c a b => erase_bind_congr (value_erase σ c) fun test => by
      cases test with
      | false => exact value_erase σ b
      | true => exact value_erase σ a
  | _, .readMem l => erase_bind_congr (mloc_erase σ l) fun _ => erase_ofOpt _
  | _, .len b _ => erase_bind_congr (path_erase σ b) fun _ =>
      erase_bind_congr (erase_ofOpt _) fun _ => rfl
  | _, .mlen b _ => erase_bind_congr (mpath_erase σ b) fun _ => rfl
  | _, .modular _ a b k => erase_bind_congr (value_erase σ a) fun _ =>
      erase_bind_congr (value_erase σ b) fun _ =>
        erase_bind_congr (value_erase σ k) fun _ => erase_ofOpt _
  | _, .hash _ b _ => erase_bind_congr (mpath_erase σ b) fun _ => rfl

end

/-- Exact successful values can be recovered from the projection without
assuming any invariant on the state. -/
theorem value_of_ok (σ : State C Γ) {p : PrimTy} (v : Val C Γ p) (a : p.Denote)
    (h : v.evalT σ = .ok a) : value σ v = .ok a := by
  have he := value_erase σ v
  rw [h] at he
  cases hv : value σ v with
  | ok b => rw [hv] at he; cases he; rfl
  | error halt => rw [hv] at he; cases he

/-- info: 'Solidity.PanicV2.Eval.path_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms path_erase
/-- info: 'Solidity.PanicV2.Eval.loc_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms loc_erase
/-- info: 'Solidity.PanicV2.Eval.mpath_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mpath_erase
/-- info: 'Solidity.PanicV2.Eval.mloc_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mloc_erase
/-- info: 'Solidity.PanicV2.Eval.value_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms value_erase
/-- info: 'Solidity.PanicV2.Eval.value_of_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms value_of_ok

end Solidity.PanicV2.Eval
