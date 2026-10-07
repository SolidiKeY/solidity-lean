import Solidity.Calculus.Core.Lower

/-!
# The strategy on scoped formulas

`Completeness.lean`'s `Stmt.step` and `Symex.lean`'s `symex` on the scoped
formulas of `Calculus/Core/Fml.lean` (`docs/intrinsic.md`, M6a): the rule of a
statement is one function of its constructors (`Stmt.step`), and the strategy
fires the rule of the first statement of a formula until none is left.  The
fresh names are numbered as `Symex.lean` numbers them, one above every index
in the formula (`Fml.fresh`), so the erasure of what `symex` leaves is what
today's `symex` leaves of the erasure (`Examples/Tactics/CoreSymex.lean` pins it).

The kernel evaluates these functions when a goal is closed by them, so they
follow Gate G0's conditions:

* **no `match` on a family indexed by contexts** (condition 1): `Stmt.step`
  is one `Stmt.casesOn` over the statement, and `Prog`, `Frames` and `Fml`
  are taken apart by `casesOn` with a motive over their indices; a `match`
  is left only on the expression families, whose context is a parameter;
* **the stepper is `Fml.rec`** (condition 2): `Fml.stepR`, the definition the
  kernel unfolds, recurses by the recursor; `Fml.stepAt` is its compiled
  twin (`implemented_by`), by `casesOn` and structural recursion, and
  `Fml.stepR_eq` says they agree.

What `Stmt.step` covers is the part of the rule table ported so far: the
assignments, reads and writes of locals, state variables and members, the
operators, the declarations of values and aliases, `if`, `require`,
`assert` and `revert`.  Any other statement has no rule yet (`none`), and the
strategy stops in front of it.

A rule that declares fresh locals (`T se = nse; v = se ⊕ e;`) leaves them in
a scope of their own, which ends after the statement (`Premise.unfold`, a
`pop .capture` frame); a declaration with an initializer binds its local in
front of the rest (`Premise.bind`); a branch is a block, its locals popped at
its end.  A modality whose program is done goes through its frames
(`Frames.exit`): a scope end is a popping update, the rest of the program
the next modality.
-/

namespace Solidity.Core

open Solidity (Srt Op0 Op1 Op2 Op3 Modality)

variable {C : Contract}

/-! ## The premises the rules build -/

/-- `se = true`, the condition of a branch's goal (`Fml.eq`, as the rules
write it). -/
def Fml.isBool {Γ : Ctx} (t : Tm C Γ .val) (b : Bool) : Fml C Γ :=
  .eq t (.app0 (.lit (.bool b)))

/-- `{v := v'}`: a local set to a value's term. -/
def Premise.setLocal {Γ : Ctx} {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p) :
    Premise C Γ Γ :=
  .update (Upd.nil.snoc (.local i (.val v.lower)))

/-- `{storage := save(storage, l, src)}`. -/
def Premise.save {Γ : Ctx} {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) : Premise C Γ Γ :=
  .update (Upd.nil.snoc (.storage (.app3 .save (.app0 .storage) l.lower r.lower)))

/-- `T se = nse; s`: a value captured into the fresh local `x`, `s` read with
it on top, the local popped after `s`. -/
def Premise.capture {Γ : Ctx} (p : PrimTy) (x : Var) (e : Val C Γ p)
    (s : Stmt C (.val p :: Γ) (.val p :: Γ)) : Premise C Γ Γ :=
  .unfold (.cons (.declLocal p x (some e)) (.cons s .nil)) (.push .refl)

/-- A part read in `Γ`, read with one local more on top. -/
abbrev up {Γ : Ctx} {t : LTy} : Thin Γ (t :: Γ) := .drop .refl

/-- The fresh names of a rule fired at index `k`. -/
abbrev fse (k : Nat) : Var := .fresh "se" k
abbrev fsp (k : Nat) : Var := .fresh "sp" k

/-! ## The rules of the statements -/

section Rules

variable (k : Nat)

/-- A local assigned (`localStep`): a simple value, a state variable, a
member of a simple path, an operator over simple operands is an update;
anything else captures the part that is not simple. -/
def localStep {Γ : Ctx} {p : PrimTy} (i : Idx Γ (.val p)) : Val C Γ p → Option (Premise C Γ Γ)
  -- localValueAssign
  | .simple s => some (.setLocal i (.simple s))
  -- storageRootReadSelect
  | .read (.root r h) => some (.setLocal i (.read (.root r h)))
  | .read (@Loc.field _ _ s _ b f h) =>
    -- storageFieldReadFind
    if b.isSimple then some (.setLocal i (.read (.field b f h)))
    -- storageFieldRead_unfold_rightFst
    else some (.unfold
      (.cons (.declStorage (.struct s) (fsp k) (some (.path b)))
        (.cons (.assignLocal i.there (.read (.field (.alias .here) f h))) .nil))
      (.push .refl))
  -- binopAssignment
  | .binop op ha hq (.simple a) (.simple b) => some (.setLocal i (.binop op ha hq (.simple a) (.simple b)))
  | @Val.binop _ _ p' _ op ha hq (.simple a) b =>
    -- binopUnfoldRight; `&&`/`||` not ported
    if op.shortCircuits then none
    else some (.capture p' (fse k) b
      (.assignLocal i.there (.binop op ha hq (.simple (a.wk up)) (.simple (.local .here)))))
  -- binopUnfoldLeft
  | @Val.binop _ _ p' _ op ha hq a b =>
    some (.capture p' (fse k) a
      (.assignLocal i.there (.binop op ha hq (.simple (.local .here)) (b.wk up))))
  -- unopAssignment
  | .unop op ha hq (.simple a) => some (.setLocal i (.unop op ha hq (.simple a)))
  -- unopCapture
  | @Val.unop _ _ p' _ op ha hq a =>
    some (.capture p' (fse k) a (.assignLocal i.there (.unop op ha hq (.simple (.local .here)))))
  | _ => none

/-- A storage write (`assignStep`): a simple source written to a state
variable or a member of a simple path is an update; a source that is not
simple is captured, a member of a path that is not simple unfolds its
receiver; a conditional, an entry and a copy have no rule yet. -/
def assignStep {Γ : Ctx} : {T : Ty} → Loc C Γ T → Src C Γ T → Option (Premise C Γ Γ)
  -- storageRootWriteStore
  | _, .root r h, .val (.simple s) => some (.save (.root r h) (.val (.simple s)))
  | _, .root _ _, .val (.ternary ..) => none
  -- storageRootWriteValueRhsCapture
  | _, .root r h, .val e =>
    some (.capture _ (fse k) e (.assign (.root r h) (.val (.simple (.local .here)))))
  | _, .field _ _ _, .val (.ternary ..) => none
  | _, @Loc.field _ _ s _ b f h, .val e =>
    if b.isSimple then
      match e with
      -- storageFieldWriteSave
      | .simple se => some (.save (.field b f h) (.val (.simple se)))
      -- fieldWriteValueRhsCapture
      | e => some (.capture _ (fse k) e
          (.assign (.field (b.wk up) f h) (.val (.simple (.local .here)))))
    -- storageFieldWrite_unfold_leftFst
    else some (.unfold
      (.cons (.declLocal _ (fse k) (some e))
        (.cons (.declStorage (.struct s) (fsp k) (some (.path (b.wk up))))
          (.cons (.assign (.field (.alias .here) f h) (.val (.simple (.local (.there .here))))) .nil)))
      (.push (.push .refl)))
  | _, _, _ => none

/-- An alias bound to an alias or a state variable (`storageLocalRootRebind`). -/
def rebindStep {Γ : Ctx} {R : RefTy} (i : Idx Γ (.alias R)) : ARhs C Γ R → Option (Premise C Γ Γ)
  | .path (.alias j) => some (.update (Upd.nil.snoc (.local i (.path (SPath.alias j).lower))))
  | .path (.loc (.root r h)) =>
    some (.update (Upd.nil.snoc (.local i (.path (Loc.root (Γ := Γ) r h).lower))))
  | _ => none

/-- `if (c) …`: split on a simple condition (`ifElseSplit`), capture any
other (`ifElseUnfold`), the branches read with the capture on top. -/
def iteStep {Γ Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (thn : Prog C Γ Γ₁) (els : Prog C Γ Γ₂) :
    Option (Premise C Γ Γ) :=
  match c with
  | .simple s => some (.split (Fml.isBool s.lower true) (Fml.isBool s.lower false) thn els)
  | c => some (.capture .bool (fse k) c
      (.ite (.simple (.local .here)) (thn.wk up).2.2 (els.wk up).2.2))

/-- `require(c);`: two goals on a simple condition (`requireSimple`), the
condition captured otherwise (`requireConditionCapture`). -/
def requireStep {Γ : Ctx} : Val C Γ .bool → Option (Premise C Γ Γ)
  | .simple s => some (.split (Fml.isBool s.lower true) (Fml.isBool s.lower false) .nil
      (.cons .revert .nil))
  | c => some (.capture .bool (fse k) c (.require (.simple (.local .here))))

/-- `assert(c);`: the check of a simple condition (`assertSimple`), the
condition captured otherwise (`assertConditionCapture`). -/
def assertStep {Γ : Ctx} : Val C Γ .bool → Option (Premise C Γ Γ)
  | .simple s => some (.check (Fml.isBool s.lower true))
  | c => some (.capture .bool (fse k) c (.assert (.simple (.local .here))))

end Rules

/-- **The rule for a statement** under the modality `m`, its fresh locals
named at index `k`, if the statement's rule is ported: one `casesOn` over the
statement (Gate G0, condition 1), each arm the rule `Completeness.lean`'s
`Stmt.step` fires. -/
def Stmt.step (k : Nat) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : Option (Premise C Γ Γ') :=
  Stmt.casesOn (motive_1 := fun Γ Γ' _ => Option (Premise C Γ Γ')) s
    (assign := fun l r => assignStep k l r)
    (rebind := fun i r => rebindStep i r)
    (assignLocal := fun i v => localStep k i v)
    -- valueDeclSkip, localValueDeclInitDrop
    (declLocal := fun p x init => match init with
      | none => some (.update (Upd.nil.decl x (.val (.app0 (.lit p.default)))))
      | some e => some (.bind x (.val p) (.cons (.assignLocal .here (e.wk up)) .nil)))
    -- storageLocalDeclSkip, storageLocalDeclInitDrop
    (declStorage := fun R x init => match init with
      | none => some (.update (Upd.nil.decl (t := .alias R) x .unset))
      | some r => some (.bind x (.alias R) (.cons (.rebind .here (r.wk up)) .nil)))
    (opAssign := fun _ _ _ _ _ => none) (incDec := fun _ _ _ => none)
    (assignIncDec := fun _ _ _ _ _ => none) (push := fun _ _ _ => none) (pop := fun _ => none)
    (transfer := fun _ _ => none) (send := fun _ _ _ => none)
    (declMem := fun _ _ _ _ _ => none) (rebindMem := fun _ _ => none)
    (assignFromMem := fun _ _ => none) (assignMem := fun _ _ => none) (delete := fun _ => none)
    (deleteMem := fun _ _ => none) (assignNew := fun _ _ _ => none)
    (ite := fun c thn els => iteStep k c thn els)
    (require := fun c => requireStep k c)
    (assert := fun c => assertStep k c)
    -- revertBox, revertDiamond
    (revert := match m with
      | .box => some (.done true)
      | .diamond => some (.done false))
    (call := fun _ _ _ _ => none) (tryCall := fun _ _ _ _ _ _ _ => none)
    (loop := fun _ _ _ => none) (block := fun _ => none)

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
      (fun U x _ => max (Upd.maxIdx U) x.idx) (fun U _ => Upd.maxIdx U)
  termination_by structural _ U => U

/-- The largest index of a name the frames bind. -/
def Frames.maxIdx : {Γ Γ₀ : Ctx} → Frames C Γ Γ₀ → Nat
  | _, _, κ => Frames.casesOn (motive := fun _ _ _ => Nat) κ 0
      (fun ω κ => max ω.maxIdx (Frames.maxIdx κ)) (fun _ _ κ => Frames.maxIdx κ)
  termination_by structural _ _ κ => κ

/-- The largest index of a name the formula binds (`Logic.lean`'s `maxIdx`
of its erasure's names). -/
def Fml.maxIdx : {Γ : Ctx} → Fml C Γ → Nat
  | _, φ => Fml.casesOn (motive := fun _ _ => Nat) φ
    (tt := 0) (eq := fun _ _ => 0) (defined := fun _ => 0) (not := fun φ => Fml.maxIdx φ)
    (and := fun φ ψ => max (Fml.maxIdx φ) (Fml.maxIdx ψ))
    (imp := fun φ ψ => max (Fml.maxIdx φ) (Fml.maxIdx ψ))
    (upd := fun _ U φ => max U.maxIdx (Fml.maxIdx φ))
    (modal := fun _ P κ φ => max (max P.maxIdx κ.maxIdx) (Fml.maxIdx φ))
    (havoc := fun φ => Fml.maxIdx φ) (all := fun x _ φ => max x.idx (Fml.maxIdx φ))
    (bind := fun x _ φ => max x.idx (Fml.maxIdx φ)) (anon := fun _ φ => Fml.maxIdx φ)
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
    (fun s ω κ => (s.step k m).map fun p => p.fml m ω κ φ) κ

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
    (bind := fun x t φ => (Fml.stepAt k φ).map (.bind x t))
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
    (bind := fun x t _ ih => ih.map (.bind x t))
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
  | bind x t φ ih => show (Fml.stepR k φ).map (Fml.bind x t) = _; rw [ih]; rfl
  | anon xs φ ih => show (Fml.stepR k φ).map (Fml.anon xs) = _; rw [ih]; rfl

/-- One step, its fresh names above every index in the formula. -/
def Fml.step {Γ : Ctx} (φ : Fml C Γ) : Option (Fml C Γ) := φ.stepR φ.fresh

/-- Run the strategy for at most `n` steps. -/
def symex {Γ : Ctx} : Nat → Fml C Γ → Fml C Γ
  | 0, φ => φ
  | n + 1, φ => match φ.step with
    | some ψ => symex n ψ
    | none => φ

end Solidity.Core
