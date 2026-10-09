import Solidity.Calculus.Blocks

/-!
# The strategy on scoped formulas

master's `Stmt.step` (`Calculus/Completeness.lean` at `ad728b16`) and
`symex` on the scoped formulas of `Calculus/Fml.lean` (`docs/intrinsic.md`, M6a): the rule of a
statement is one function of its constructors (`Stmt.step`), and the strategy
fires the rule of the first statement of a formula until none is left.  The
fresh names are numbered as master's `Symex.lean` numbered them, one above
every index in the formula (`Fml.fresh`); `Examples/Tactics/Symex.lean` pins
the results, which agreed with master's strategy until W4 `calc-del`.

The kernel evaluates these functions when a goal is closed by them, so they
follow Gate G0's conditions:

* **no `match` on a family indexed by contexts** (condition 1): `Stmt.step`
  is one `Stmt.casesOn` over the statement, and `Prog`, `Frames` and `Fml`
  are taken apart by `casesOn` with a motive over their indices; a `match`
  is left on the expression families, whose context is a parameter, and a
  rule's schema variables are shifted under its fresh local by `Val.up` and
  its kin, which match only on those.  Five exceptions remain, each once
  per rule fired: `ifElseUnfold` weakens the branches with `Prog.wk up`, a
  call its body with `Prog.wk (Thin.atop …)`, `whileInvariantDiamond` the
  body with `Prog.wk up`; `Prog.wk` matches on `Prog`, `Stmt`, `Thin` and
  `Idx`, so the kernel runs it.  A call with returns builds its thinning
  with `Thin.ofExt`, a `match` on `Ext`; and every invariant rule computes
  the body's frame (`Prog.frame`), whose positions go through `Idx.toNat`
  (a `match` on `Idx`) and back through `Ctx.idx?` (deciding `LTy`
  equality, then a cast);
* **the stepper is `Fml.rec`** (condition 2): `Fml.stepR`, the definition the
  kernel unfolds, recurses by the recursor; `Fml.stepAt` is its compiled
  twin (`implemented_by`), by `casesOn` and structural recursion, and
  `Fml.stepR_eq` says they agree.

Every statement has a rule: `Stmt.step` dispatches to the arms of
`Calculus/Arms.lean` (expressions, storage, memory, payments, `if`,
`require`, `assert`) and `Calculus/Blocks.lean` (calls, `try`,
loops), each arm the rule of a constructor of `Taclet`/`LeanTaclet`
(`Calculus/Rules.lean`; `Taclet.toStep`, `Calculus/Taclet.lean`); the
strategy stops only at a modality-free goal.

A rule that declares fresh locals (`T se = nse; v = se ⊕ e;`) leaves them in
a scope of their own, which ends after the statement (`Premise.unfold`, a
`pop .capture` frame); a declaration with an initializer binds its local in
front of the rest (`Premise.bind`); a branch is a block, its locals popped at
its end.  A modality whose program is done goes through its frames
(`Frames.exit`): a scope end is a popping update, the rest of the program
the next modality.
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3 Modality)

variable {C : Contract}


/-- **The rule for a statement** under the modality `m`, its fresh locals
named at index `k`: one `casesOn` over the statement (Gate G0, condition 1),
each arm the rule `Taclet.toStep` names (`Calculus/Arms.lean`,
`Calculus/Blocks.lean`).  Every statement
has one, so the step is total (decision 76). -/
def Stmt.step (k : Nat) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : Premise C Γ Γ' :=
  Stmt.casesOn (motive_1 := fun Γ Γ' _ => Premise C Γ Γ') s
    (assign := fun l r => assignStep k l r)
    (rebind := fun i r => rebindStep k i r)
    (assignLocal := fun i v => localStep k i v)
    -- valueDeclSkip, localValueDeclInitDrop
    (declLocal := fun p x init => match init with
      | none => .update (Upd.nil.decl x (.val (.app0 (.lit p.default))))
      | some e => .bind x (.val p) (.cons (.assignLocal .here e.up) .nil))
    -- storageLocalDeclSkip, storageLocalDeclInitDrop
    (declStorage := fun R x init => match init with
      | none => .update (Upd.nil.decl (t := .alias R) x .unset)
      | some r => .bind x (.alias R) (.cons (.rebind .here r.up) .nil))
    (opAssign := fun op hop hp l r => opStep k op hop hp l r)
    (incDec := fun op hp l => incStep k op hp l)
    (assignIncDec := fun i op _ l _ => assignIncStep i op l)
    (push := fun b v hd => pushStep k b v hd) (pop := fun b => popStep k b)
    (transfer := fun r a => transferStep k m r a) (send := fun pv r a => sendStep k m pv r a)
    -- memoryReferenceDeclFreshAlloc, memoryLocalDeclInitDrop
    (declMem := fun R x init _ _ => match init with
      | none => .update ((Upd.nil.decl x (.mref (.app1 (.alloc R) rfl .memory))).snoc
          (.memory (.app1 (.addM R) rfl .memory)))
      | some r => .bind x (.mem R) (.cons (.rebindMem .here r.up) .nil))
    (rebindMem := fun i r => rebindMemStep k i r)
    (assignFromMem := fun l p => assignFromMemStep k l p)
    (assignMem := fun l r => assignMemStep k l r)
    (delete := fun l => deleteStep k l)
    (deleteMem := fun p hd => deleteMemStep k p hd)
    (assignNew := fun l n h => assignNewStep k l n h)
    (ite := fun c thn els => iteStep k c thn els)
    (require := fun c => requireStep k c)
    (assert := fun c => assertStep k c)
    -- revertBox, revertDiamond
    (revert := match m with
      | .box => .done true
      | .diamond => .done false)
    (call := fun f args ret body => callStep k f args ret body)
    (tryCall := fun _ rets ok err code pnc other => tryStep m rets ok err code pnc other)
    (loop := fun a c body => loopStep k m a c body)
    -- a block is its statements, its locals popped after it
    (block := fun body => .unfold body body.ext)

/-! ## Fresh names: one above every index in the formula -/

section Fresh

/-- The largest index of a name the binders give. -/
def Binders.maxIdx {ρ : Ctx} (bs : Binders ρ) : Nat := bs.names.foldl (fun n x => max n x.idx) 0

mutual

/-- The largest index of a name a statement binds. -/
def Stmt.maxIdx : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Nat
  | _, _, s => Stmt.casesOn (motive_1 := fun _ _ _ => Nat) s
    (assign := fun _ _ => 0) (rebind := fun _ _ => 0) (assignLocal := fun _ _ => 0)
    (declLocal := fun _ x _ => x.idx) (declStorage := fun _ x _ => x.idx)
    (opAssign := fun _ _ _ _ _ => 0) (incDec := fun _ _ _ => 0)
    (assignIncDec := fun _ _ _ _ _ => 0) (push := fun _ _ _ => 0) (pop := fun _ => 0)
    (transfer := fun _ _ => 0) (send := fun _ _ _ => 0)
    (declMem := fun _ x _ _ _ => x.idx) (rebindMem := fun _ _ => 0)
    (assignFromMem := fun _ _ => 0) (assignMem := fun _ _ => 0) (delete := fun _ => 0)
    (deleteMem := fun _ _ => 0) (assignNew := fun _ _ _ => 0)
    (ite := fun _ thn els => max (Prog.maxIdx thn) (Prog.maxIdx els))
    (require := fun _ => 0) (assert := fun _ => 0) (revert := 0)
    (call := fun _ args ret body =>
      max ((args.names ++ ret.names).foldl (fun n x => max n x.idx) 0) (Prog.maxIdx body))
    (tryCall := fun _ rets ok err code pnc other =>
      max (max (max rets.maxIdx ((code.names).foldl (fun n x => max n x.idx) 0))
        (max (Prog.maxIdx ok) (Prog.maxIdx err))) (max (Prog.maxIdx pnc) (Prog.maxIdx other)))
    (loop := fun _ _ body => Prog.maxIdx body) (block := fun body => Prog.maxIdx body)
  termination_by structural _ _ s => s

/-- The largest index of a name a block binds. -/
def Prog.maxIdx : {Γ Γ' : Ctx} → Prog C Γ Γ' → Nat
  | _, _, P => Prog.casesOn (motive_2 := fun _ _ _ => Nat) P 0
      (fun s P => max (Stmt.maxIdx s) (Prog.maxIdx P))
  termination_by structural _ _ P => P

end

/-- The largest index of a name an update declares. -/
def Upd.maxIdx {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → Nat
  | _, U => Upd.casesOn (motive := fun _ _ => Nat) U 0 (fun U _ => Upd.maxIdx U)
      (fun U x _ => max (Upd.maxIdx U) x.idx) (fun U _ => Upd.maxIdx U) (fun U _ => Upd.maxIdx U)
  termination_by structural _ U => U

/-- The largest index of a name the frames bind. -/
def Frames.maxIdx : {Γ Γ₀ : Ctx} → Frames C Γ Γ₀ → Nat
  | _, _, κ => Frames.casesOn (motive := fun _ _ _ => Nat) κ 0
      (fun ω κ => max ω.maxIdx (Frames.maxIdx κ)) (fun _ _ κ => Frames.maxIdx κ)
      (fun _ κ => Frames.maxIdx κ)
  termination_by structural _ _ κ => κ

/-- The largest index of a name the formula binds (`Calculus/Hyp.lean`'s `maxIdx`
of its erasure's names). -/
def Fml.maxIdx : {Γ : Ctx} → Fml C Γ → Nat
  | _, φ => Fml.casesOn (motive := fun _ _ => Nat) φ
    (tt := 0) (eq := fun _ _ => 0) (defined := fun _ => 0) (not := fun φ => Fml.maxIdx φ)
    (and := fun φ ψ => max (Fml.maxIdx φ) (Fml.maxIdx ψ))
    (imp := fun φ ψ => max (Fml.maxIdx φ) (Fml.maxIdx ψ))
    (upd := fun _ U φ => max U.maxIdx (Fml.maxIdx φ))
    (modal := fun _ P κ φ => max (max P.maxIdx κ.maxIdx) (Fml.maxIdx φ))
    (havoc := fun φ => Fml.maxIdx φ) (all := fun x _ φ => max x.idx (Fml.maxIdx φ))
    (bind := fun _ x _ φ => max x.idx (Fml.maxIdx φ)) (anon := fun _ φ => Fml.maxIdx φ)
  termination_by structural _ φ => φ

/-- The index of the next fresh names. -/
def Fml.fresh {Γ : Ctx} (φ : Fml C Γ) : Nat := φ.maxIdx + 1

end Fresh

/-! ## The strategy -/

/-- The modality `⟨ P κ ⟩ φ` one step on: the first statement's rule, its
premise in front of the rest, or the frames when `P` is done. -/
def Fml.modalStep (k : Nat) (m : Modality) {Γ Γ₁ Γ₀ : Ctx} (P : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) : Option (Fml C Γ) :=
  Prog.casesOn (motive_2 := fun Γ Γ₁ _ => Frames C Γ₁ Γ₀ → Option (Fml C Γ)) P
    (fun κ => some (κ.exit m φ))
    (fun s ω κ => some ((s.step k m).fml m ω κ φ)) κ

/-- Fire the rule of the first statement with a rule, looking through
updates, a precondition, binders and the goals of a branch, fresh names at
`k` (`Symex.lean`'s `Fml.stepAt`).  Compiled code; the kernel unfolds
`Fml.stepR`. -/
def Fml.stepAt (k : Nat) : {Γ : Ctx} → Fml C Γ → Option (Fml C Γ)
  | _, φ => Fml.casesOn (motive := fun Γ _ => Option (Fml C Γ)) φ
    (tt := none) (eq := fun _ _ => none) (defined := fun _ => none) (not := fun _ => none)
    (and := fun φ ψ => match Fml.stepAt k φ with
      | some φ' => some (.and φ' ψ)
      | none => (Fml.stepAt k ψ).map (.and φ))
    (imp := fun a φ => (Fml.stepAt k φ).map (.imp a))
    (upd := fun m U φ => (Fml.stepAt k φ).map (.upd m U))
    (modal := fun m P κ φ => Fml.modalStep k m P κ φ)
    (havoc := fun φ => (Fml.stepAt k φ).map .havoc)
    (all := fun x p φ => (Fml.stepAt k φ).map (.all x p))
    (bind := fun m x t φ => (Fml.stepAt k φ).map (.bind m x t))
    (anon := fun xs φ => (Fml.stepAt k φ).map (.anon xs))
  termination_by structural _ φ => φ

/-- `Fml.stepAt` by the recursor, which the kernel unfolds with no
`brecOn` (Gate G0, condition 2); the compiled code is `Fml.stepAt`. -/
@[implemented_by Fml.stepAt]
def Fml.stepR (k : Nat) {Γ : Ctx} (φ : Fml C Γ) : Option (Fml C Γ) :=
  Fml.rec (motive := fun Γ _ => Option (Fml C Γ))
    (tt := none) (eq := fun _ _ => none) (defined := fun _ => none) (not := fun _ _ => none)
    (and := fun φ ψ ihφ ihψ => match ihφ with
      | some φ' => some (.and φ' ψ)
      | none => ihψ.map (.and φ))
    (imp := fun a _ _ ih => ih.map (.imp a))
    (upd := fun m U _ ih => ih.map (.upd m U))
    (modal := fun m P κ φ _ => Fml.modalStep k m P κ φ)
    (havoc := fun _ ih => ih.map .havoc)
    (all := fun x p _ ih => ih.map (.all x p))
    (bind := fun m x t _ ih => ih.map (.bind m x t))
    (anon := fun xs _ ih => ih.map (.anon xs)) φ

/-- The recursor's stepper is the compiled one. -/
theorem Fml.stepR_eq (k : Nat) {Γ : Ctx} (φ : Fml C Γ) : Fml.stepR k φ = Fml.stepAt k φ := by
  induction φ with
  | tt | eq | defined | not | modal => rfl
  | and φ ψ ihφ ihψ =>
    show (match Fml.stepR k φ with
      | some φ' => some (Fml.and φ' ψ)
      | none => (Fml.stepR k ψ).map (Fml.and φ)) = _
    rw [ihφ, ihψ]; rfl
  | imp a φ _ ih => show (Fml.stepR k φ).map (Fml.imp a) = _; rw [ih]; rfl
  | upd m U φ ih => show (Fml.stepR k φ).map (Fml.upd m U) = _; rw [ih]; rfl
  | havoc φ ih => show (Fml.stepR k φ).map Fml.havoc = _; rw [ih]; rfl
  | all x p φ ih => show (Fml.stepR k φ).map (Fml.all x p) = _; rw [ih]; rfl
  | bind m x t φ ih => show (Fml.stepR k φ).map (Fml.bind m x t) = _; rw [ih]; rfl
  | anon xs φ ih => show (Fml.stepR k φ).map (Fml.anon xs) = _; rw [ih]; rfl

/-- One step, its fresh names above every index in the formula. -/
def Fml.step {Γ : Ctx} (φ : Fml C Γ) : Option (Fml C Γ) := φ.stepR φ.fresh

/-- Run the strategy for at most `n` steps. -/
def symex {Γ : Ctx} : Nat → Fml C Γ → Fml C Γ
  | 0, φ => φ
  | n + 1, φ => match φ.step with
    | some ψ => symex n ψ
    | none => φ

end Solidity
