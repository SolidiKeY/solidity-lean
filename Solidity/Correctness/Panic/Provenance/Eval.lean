import Solidity.Semantics.Panic.Run.Control

/-!
# Panic code provenance: the evaluator leaves

A halt is *coded* when an intrinsic halt's solc code is the code of the site its
retained origin certifies; every other halt is coded trivially. Each evaluator
of `Semantics/Panic/Eval.lean` that returns an `EvalResult` can only fail with a
coded halt, since intrinsic halts are built by `evalProducer` alone there.
-/

namespace Solidity.Correctness.Panic

open Solidity.Semantics.Panic

/-- An intrinsic halt's code is the code of its retained failed site. -/
def Coded : Halt Raised → Prop
  | .intrinsic code origin => code = siteCode origin.site
  | .externalRevert _ | .revert | .revertWith _ | .exhausted | .diverge => True

/-- Every failure of the result is coded. -/
def ErrCoded {α : Type} (r : EvalResult α) : Prop :=
  ∀ halt, r = .error halt → Coded halt

namespace ErrCoded

theorem ok {α : Type} (a : α) : ErrCoded (.ok a : EvalResult α) :=
  fun _ h => nomatch h

theorem pure {α : Type} (a : α) : ErrCoded (Pure.pure a : EvalResult α) :=
  ok a

/-- A non-intrinsic failure is coded. -/
theorem error {α : Type} (halt : Halt Raised)
    (h : ∀ code origin, halt ≠ .intrinsic code origin) :
    ErrCoded (.error halt : EvalResult α) := by
  intro _ e
  cases e
  cases halt with
  | intrinsic code origin => exact absurd rfl (h code origin)
  | _ => trivial

theorem revert {α : Type} : ErrCoded (.error .revert : EvalResult α) :=
  error _ fun _ _ e => nomatch e

theorem bind {α β : Type} {r : EvalResult α} {f : α → EvalResult β}
    (hr : ErrCoded r) (hf : ∀ a, ErrCoded (f a)) : ErrCoded (r >>= f) := by
  intro halt e
  cases r with
  | ok a => exact hf a halt e
  | error h' => cases e; exact hr _ rfl

theorem map {α β : Type} {r : EvalResult α} (f : α → β)
    (hr : ErrCoded r) : ErrCoded (r.map f) := by
  intro halt e
  cases r with
  | ok a => cases e
  | error h' => cases e; exact hr _ rfl

theorem ofOpt {α : Type} (o : Option α) : ErrCoded (Solidity.Semantics.Panic.ofOpt o) := by
  cases o
  · exact revert
  · exact ok _

/-- A cast along a type equality keeps the result's failures. -/
theorem cast {α β : Type} (e : α = β) {r : EvalResult α} (hr : ErrCoded r) :
    ErrCoded (e ▸ r : EvalResult β) := by
  subst e
  exact hr

theorem evalProducer {α : Type} (p : Solidity.Panic.Producer α) :
    ErrCoded (Solidity.Semantics.Panic.evalProducer p) := by
  intro halt e
  cases halt with
  | intrinsic code origin => exact Run.producer_actual_code p code origin e
  | _ => trivial

end ErrCoded

theorem binary_coded (op : BinOp) {p : PrimTy} (h : op.accepts p = true) (x y : p.Denote) :
    ErrCoded (binary op h x y) := by
  cases op <;> first | exact ErrCoded.evalProducer _ | exact ErrCoded.ofOpt _

theorem unary_coded (op : UnOp) {p : PrimTy} (h : op.accepts p = true) (x : p.Denote) :
    ErrCoded (unary op h x) := by
  unfold unary
  split <;> first | exact ErrCoded.evalProducer _ | exact ErrCoded.ofOpt _

theorem modular_coded (op : ModOp) (x y k : PrimTy.uint.Denote) :
    ErrCoded (modular op x y k) :=
  ErrCoded.evalProducer _

variable {C : Contract} {Γ : Ctx}

theorem storageIndex_coded {R : RefTy} {k : PrimTy} {V : Ty} (st : Storage C)
    (r : SRef C (.ref R)) (it : IndexTy R k V) (i : k.Denote) :
    ErrCoded (storageIndex st r it i) := by
  cases it <;> first | exact ErrCoded.evalProducer _ | exact ErrCoded.ofOpt _

theorem memoryRead_coded {H : HTy} (hp : Heap H) {T : Ty} (addr : MAddr H T) :
    ErrCoded (memoryRead hp addr) := by
  cases addr
  · exact ErrCoded.ok _
  · exact ErrCoded.evalProducer _

open ErrCoded in
mutual

theorem path_coded (σ : State C Γ) : {T : Ty} → (b : SPath C Γ T) → ErrCoded (path σ b)
  | _, .alias _ => ofOpt _
  | _, .loc l => loc_coded σ l

theorem loc_coded (σ : State C Γ) : {T : Ty} → (l : Loc C Γ T) → ErrCoded (loc σ l)
  | _, .root .. => ok _
  | _, .field b _ _ => bind (path_coded σ b) fun _ => ok _
  | _, .index _ b i => bind (path_coded σ b) fun _ =>
      bind (value_coded σ i) fun _ =>
        bind (storageIndex_coded _ _ _ _) fun _ => ok _

theorem mpath_coded (σ : State C Γ) : {T : Ty} → (b : MPath C Γ T) → ErrCoded (mpath σ b)
  | _, .var .. => ofOpt _
  | _, .loc l => bind (mloc_coded σ l) fun _ => memoryRead_coded _ _

theorem mloc_coded (σ : State C Γ) : {T : Ty} → (l : MLoc C Γ T) → ErrCoded (mloc σ l)
  | _, .field b _ _ => bind (mpath_coded σ b) fun _ => ok _
  | _, .index _ b i => bind (mpath_coded σ b) fun _ =>
      bind (value_coded σ i) fun _ => ok _

theorem value_coded (σ : State C Γ) : {p : PrimTy} → (v : Val C Γ p) → ErrCoded (value σ v)
  | _, .simple _ => ok _
  | _, .read l => bind (loc_coded σ l) fun _ => bind (ofOpt _) fun _ => ok _
  | _, .binop op _ hq a b => by
    subst hq
    refine bind (value_coded σ a) fun x => ?_
    cases op.shortT x with
    | some _ => exact ok _
    | none => exact bind (value_coded σ b) fun _ => binary_coded _ _ _ _
  | _, .unop _ _ hq a => by
    subst hq
    exact bind (value_coded σ a) fun _ => unary_coded _ _ _
  | _, .ternary c a b => bind (value_coded σ c) fun test => by
      cases test with
      | false => exact value_coded σ b
      | true => exact value_coded σ a
  | _, .readMem l => bind (mloc_coded σ l) fun _ => memoryRead_coded _ _
  | _, .len b _ => bind (path_coded σ b) fun _ => bind (ofOpt _) fun _ => ok _
  | _, .mlen b _ => bind (mpath_coded σ b) fun _ => ok _
  | _, .modular _ a b k => bind (value_coded σ a) fun _ =>
      bind (value_coded σ b) fun _ =>
        bind (value_coded σ k) fun _ => modular_coded _ _ _ _
  | _, .hash _ b _ => bind (mpath_coded σ b) fun _ => ok _

end

open ErrCoded in
theorem source_coded (σ : State C Γ) {T : Ty} : (src : Src C Γ T) →
    ErrCoded (source σ src)
  | .val v => bind (value_coded σ v) fun _ => ok _
  | .copy p _ => bind (path_coded σ p) fun _ => ofOpt _
  | .fixedCopy p _ _ => bind (path_coded σ p) fun _ => bind (ofOpt _) fun _ => ok _
  | .copyMem p => bind (mpath_coded σ p) fun _ => ok _
  | .fixedCopyMem p _ => bind (mpath_coded σ p) fun _ => ok _

theorem msource_coded (σ : State C Γ) {T : Ty} (src : MSrc C Γ T) :
    ErrCoded (msource σ src) := by
  cases src with
  | val v => exact value_coded σ v
  | ref p => exact mpath_coded σ p

/-- A leaf's failure carries the code of its retained site. -/
theorem ErrCoded.intrinsic {α : Type} {r : EvalResult α} (hr : ErrCoded r)
    {code : Code} {origin : Raised} (e : r = .error (.intrinsic code origin)) :
    code = siteCode origin.site :=
  hr _ e

end Solidity.Correctness.Panic
