import Solidity.Scratch.ITree.Tree
import Solidity.Calculus.CallerModelRun

/-!
# Scratch (itree-inspection, Experiment A): payments as a tree

The `transfer`/`send` fragment of `ExecS` and `ExecSM` as one tree semantics
(`Stmt.tree`, `Prog.tree`) and the handler `Handle` at two allowances:
`anyA` (`ExecS J`) and `M.Allows J` (`ExecSM M J`).  Validation theorems:
the tree reading equals both relations on straight-line programs whose other
statements do not fork.  Not for merge.
-/

namespace Solidity.Scratch.ITree

open Solidity

variable {C : Contract} {Γ : Ctx}

/-! ## The tree semantics -/

/-- A transfer: control leaves after the payment is booked. -/
def transferTree (r a : Val C Γ .uint) (σ : State C Γ) : Tree C (COut C σ.H Γ) :=
  match TRun.transfer r a σ with
  | .error e => .ret (.halt e)
  | .ok o₁ => .vis ⟨o₁.st, .transfer⟩ fun (x : Resume C) =>
      .ret (.ok ⟨o₁.st.havoc x.1 x.2.1 x.2.2, o₁.ext⟩)

/-- A send: a refusal returns `false` at once; otherwise control leaves
after the payment, and the callee reverts (`false`, nothing booked) or
resumes (`true`). -/
def sendTree (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) (full : Bool) (σ : State C Γ) :
    Tree C (COut C σ.H Γ) :=
  match TRun.send pv r a σ with
  | .error e => .ret (.halt e)
  | .ok o =>
    match TRun.transfer r a σ with
    | .error _ => .ret (.ok o)
    | .ok o₁ => .vis ⟨o₁.st, .send full⟩ fun (y : Option (Resume C)) =>
      match y with
      | none => .ret (.ok ⟨σ.setLocal pv (false : Bool), List.prefix_refl _⟩)
      | some x => .ret (.ok ⟨(o₁.st.havoc x.1 x.2.1 x.2.2).setLocal pv (true : Bool), o₁.ext⟩)

/-- A statement's tree: payments emit events, every other statement is its
deterministic run (faithful where it does not fork). -/
def Stmt.tree : {Γ Γ' : Ctx} → Stmt C Γ Γ' → (σ : State C Γ) → Tree C (COut C σ.H Γ')
  | _, _, .transfer r a, σ => transferTree r a σ
  | _, _, .send pv r a full, σ => sendTree pv r a full σ
  | _, _, s, σ => .ret (.ofRes (s.run σ))

/-- After a statement, the rest; a halt or a broken invariant stops. -/
def COut.thenTree {H : HTy} {Γ₁ Γ₂ : Ctx}
    (cont : (σ : State C Γ₁) → Tree C (COut C σ.H Γ₂)) : COut C H Γ₁ → Tree C (COut C H Γ₂)
  | .ok o₁ => (cont o₁.st).map (COut.map (Out.cat o₁))
  | .halt e => .ret (.halt e)
  | .violated => .ret .violated

def Prog.tree : {Γ Γ' : Ctx} → Prog C Γ Γ' → (σ : State C Γ) → Tree C (COut C σ.H Γ')
  | _, _, .nil, σ => .ret (.ok ⟨σ, List.prefix_refl _⟩)
  | _, _, .cons s P, σ => (Stmt.tree s σ).bind (COut.thenTree (Prog.tree P))

/-- A payment. -/
def Stmt.isPay {Γ Γ' : Ctx} : Stmt C Γ Γ' → Bool
  | .transfer .. | .send .. => true
  | _ => false

/-- The fragment: payments, and statements that do not fork. -/
def Stmt.Frag {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : Prop := Stmt.isPay s = true ∨ s.forks = false

def Prog.Frag : {Γ Γ' : Ctx} → Prog C Γ Γ' → Prop
  | _, _, .nil => True
  | _, _, .cons s P => Stmt.Frag s ∧ Prog.Frag P


/-! ## Validation: the tree reading is `ExecSM` (transfer) -/

section Transfer

variable {M : CallerModel C} {J : StateInv C} {r a : Val C Γ .uint} {σ : State C Γ}

theorem run_transfer : Stmt.run σ (.transfer r a) = TRun.transfer r a σ := rfl

theorem transfer_iffM {o : COut C σ.H Γ} :
    ExecSM M J σ (.transfer r a) o ↔ Handle (M.Allows J) J .violated (transferTree r a σ) o := by
  constructor
  · intro h
    cases h with
    | det hf =>
      rw [run_transfer]; unfold transferTree
      cases ht : TRun.transfer r a σ with
      | error e => exact .ret
      | ok o₁ => exact .det hf .ret
    | transferHalt _ he => unfold transferTree; rw [he]; exact .ret
    | transferViolated hp ho hJ => unfold transferTree; rw [ho]; exact .violated hp hJ
    | transferResume hp ho hJ hJ' hA => unfold transferTree; rw [ho]; exact .resume hp hJ hJ' hA .ret
  · intro h
    unfold transferTree at h
    cases hp : J.pay with
    | false =>
      have hd := ExecSM.det (M := M) (J := J) (σ := σ) (s := .transfer r a) hp
      rw [run_transfer] at hd
      split at h <;> rename_i ht <;> rw [ht] at hd
      · cases h; exact hd
      · cases h with
        | det _ h' => cases h'; exact hd
        | violated hc _ | resume hc _ _ _ _ => simp [Kind.callsBack, hp] at hc
    | true =>
      split at h <;> rename_i ht
      · cases h; exact .transferHalt hp ht
      · cases h with
        | det hc _ => simp [Kind.callsBack, hp] at hc
        | violated _ hJ => exact .transferViolated hp ht hJ
        | resume _ hJ hJ' hA h' => cases h'; exact .transferResume hp ht hJ hJ' hA

end Transfer

/-! ## Validation: the tree reading is `ExecSM` (send) -/

section Send

variable {M : CallerModel C} {J : StateInv C} {pv : Idx Γ (.val .bool)} {r a : Val C Γ .uint}
  {full : Bool} {σ : State C Γ}

theorem send_of_transfer {o₁ : Out C σ.H Γ} (ht : TRun.transfer r a σ = .ok o₁) :
    TRun.send pv r a σ = .ok ⟨o₁.st.setLocal pv (true : Bool), o₁.ext⟩ := by
  unfold TRun.transfer at ht
  cases hr : r.evalT σ with
  | error e => simp [hr, bind, Except.bind] at ht
  | ok addr =>
    cases ha : a.evalT σ with
    | error e => simp [hr, ha, bind, Except.bind] at ht
    | ok amt =>
      cases hp : σ.canPay addr amt with
      | false => simp [hr, ha, hp, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at ht
      | true =>
        simp only [hr, ha, hp, bind, Except.bind, if_true, pure, Except.pure, Except.ok.injEq] at ht
        subst ht
        simp only [TRun.send, hr, ha, bind, Except.bind, pure, Except.pure]
        unfold sendT; rw [hp]; rfl

theorem send_of_transfer_error {e : THalt} {o : Out C σ.H Γ} (ht : TRun.transfer r a σ = .error e)
    (hs : TRun.send pv r a σ = .ok o) : o = ⟨σ.setLocal pv (false : Bool), List.prefix_refl _⟩ := by
  rcases TRun.send_cases pv r a σ with ⟨e', he⟩ | ⟨o₁, ht', _⟩ | hs'
  · rw [hs] at he; cases he
  · rw [ht] at ht'; cases ht'
  · rw [hs] at hs'; cases hs'; rfl

theorem run_send : Stmt.run σ (.send pv r a full) = TRun.send pv r a σ := rfl

theorem send_iffM {o : COut C σ.H Γ} :
    ExecSM M J σ (.send pv r a full) o ↔
      Handle (M.Allows J) J .violated (sendTree pv r a full σ) o := by
  constructor
  · intro h
    cases h with
    | det hf =>
      rw [run_send]; unfold sendTree
      cases hs : TRun.send pv r a σ with
      | error e => exact .ret
      | ok o =>
        cases ht : TRun.transfer r a σ with
        | error _ => exact .ret
        | ok o₁ =>
          rw [send_of_transfer ht] at hs; cases hs
          exact .det hf .ret
    | sendHalt _ he => unfold sendTree; rw [he]; exact .ret
    | sendFailed hp ht =>
      unfold sendTree; rw [send_of_transfer ht, ht]; exact .failed hp .ret
    | sendRefused hp hs =>
      unfold sendTree; rw [hs]
      cases ht : TRun.transfer r a σ with
      | error _ => exact .ret
      | ok o₁ => exact .failed hp .ret
    | sendViolated hp ht hJ =>
      unfold sendTree; rw [send_of_transfer ht, ht]; exact .violated hp hJ
    | sendResume hp ht hJ hJ' hA =>
      unfold sendTree; rw [send_of_transfer ht, ht]; exact .resume hp hJ hJ' hA .ret
  · intro h
    unfold sendTree at h
    cases hp : (J.pay || full) with
    | false =>
      have hd := ExecSM.det (M := M) (J := J) (σ := σ) (s := .send pv r a full) hp
      rw [run_send] at hd
      split at h <;> rename_i hs <;> rw [hs] at hd
      · cases h; exact hd
      · split at h <;> rename_i ht
        · cases h; exact hd
        · rw [send_of_transfer ht] at hs; cases hs
          cases h with
          | det _ h' => cases h'; exact hd
          | violated hc _ | resume hc _ _ _ _ => simp [Kind.callsBack, hp] at hc
          | failed hc _ => simp [hp] at hc
    | true =>
      split at h <;> rename_i hs
      · cases h; exact .sendHalt hp hs
      · split at h <;> rename_i ht
        · cases h; have he := send_of_transfer_error ht hs; subst he; exact .sendRefused hp hs
        · cases h with
          | det hc _ => simp [Kind.callsBack, hp] at hc
          | violated _ hJ => exact .sendViolated hp ht hJ
          | resume _ hJ hJ' hA h' => cases h'; exact .sendResume hp ht hJ hJ' hA
          | failed _ h' => cases h'; exact .sendFailed hp ht

end Send

/-! ## Validation: statements and programs of the fragment -/

section Prog

variable {M : CallerModel C} {J : StateInv C}

theorem tree_of_forks {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} (hf : s.forks = false) (σ : State C Γ) :
    Stmt.tree s σ = .ret (.ofRes (s.run σ)) := by
  cases s <;> first | rfl | cases hf

theorem stmt_iffM {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} (hs : Stmt.Frag s) {σ : State C Γ}
    {o : COut C σ.H Γ'} :
    ExecSM M J σ s o ↔ Handle (M.Allows J) J .violated (Stmt.tree s σ) o := by
  rcases hs with hp | hf
  · cases s <;> first | exact transfer_iffM | exact send_iffM | cases hp
  · rw [tree_of_forks hf]
    constructor
    · intro h; rw [h.toExecS.eq_run_of_forksIn (Stmt.forksIn_of_forks hf)]; exact .ret
    · intro h; cases h; exact .det (Stmt.forksIn_of_forks hf)

/-- **The tree reading of a fragment program is `ExecPM`.** -/
theorem prog_iffM : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → Prog.Frag P → {σ : State C Γ} →
    {o : COut C σ.H Γ'} → (ExecPM M J σ P o ↔ Handle (M.Allows J) J .violated (Prog.tree P σ) o)
  | _, _, .nil, _, σ, o => by
    constructor
    · intro h; cases h; exact .ret
    · intro h; cases h; exact .nil
  | _, _, .cons s P, hsP, σ, o => by
    obtain ⟨hs, hP⟩ : Stmt.Frag s ∧ Prog.Frag P := hsP
    rw [Prog.tree, Handle.bind_iff (f := COut.thenTree (Prog.tree P)) (viol := COut.violated) rfl]
    constructor
    · intro h
      cases h with
      | @cons _ _ _ _ _ _ o₁ _ h₁ h₂ =>
        exact ⟨_, (stmt_iffM hs).mp h₁, (Handle.map_iff (viol := COut.violated)
          (g := COut.map (Out.cat o₁)) rfl).mpr ⟨_, (prog_iffM P hP).mp h₂, rfl⟩⟩
      | halt h₁ => exact ⟨_, (stmt_iffM hs).mp h₁, .ret⟩
      | violated h₁ => exact ⟨_, (stmt_iffM hs).mp h₁, .ret⟩
    · rintro ⟨r, hr, hr'⟩
      cases r with
      | ok o₁ =>
        obtain ⟨o', h', rfl⟩ := (Handle.map_iff (viol := COut.violated)
          (g := COut.map (Out.cat o₁)) rfl).mp hr'
        exact .cons ((stmt_iffM hs).mpr hr) ((prog_iffM P hP).mpr h')
      | halt e => cases hr'; exact .halt ((stmt_iffM hs).mpr hr)
      | violated => cases hr'; exact .violated ((stmt_iffM hs).mpr hr)

/-- `ExecP` (today's callback reading) on the fragment, through the existing
bridge `ExecP.ofExecPM`/`ExecPM.toExecP`: in a tree semantics this is the
definition (`Handle anyA`). -/
theorem prog_iff {Γ Γ' : Ctx} (P : Prog C Γ Γ') (hP : Prog.Frag P) {σ : State C Γ}
    {o : COut C σ.H Γ'} : ExecP J σ P o ↔ Handle anyA J .violated (Prog.tree P σ) o :=
  ⟨fun h => (prog_iffM (M := .any) P hP).mp h.ofExecPM,
   fun h => ((prog_iffM (M := .any) P hP).mpr h).toExecP⟩

end Prog

/-! ## Re-proved results on the fragment -/

section Reproved

variable {J : StateInv C}

/-- `any` is the havoc handler, by definition (`validM_any`'s run-level
content, `ExecSM.toExecS`/`ExecS.ofExecSM`). -/
theorem allows_any {Γ : Ctx} (σ : State C Γ) st nt sb :
    CallerModel.any.Allows J σ st nt sb = anyA σ st nt sb := rfl

/-- **`ExecPM .any` is `ExecP`**, on the fragment, by the handler alone. -/
theorem execPM_any_iff {Γ Γ' : Ctx} (P : Prog C Γ Γ') (hP : Prog.Frag P) {σ : State C Γ}
    {o : COut C σ.H Γ'} : ExecPM .any J σ P o ↔ ExecP J σ P o := by
  rw [prog_iffM P hP, prog_iff P hP]; rfl

/-- **Weakening of the attacker** (`ExecPM.mono`), on the fragment, from
`Handle.mono`. -/
theorem execPM_mono {M M' : CallerModel C}
    (hA : ∀ {Γ : Ctx} (σ : State C Γ) st nt sb, M.Allows J σ st nt sb → M'.Allows J σ st nt sb)
    {Γ Γ' : Ctx} (P : Prog C Γ Γ') (hP : Prog.Frag P) {σ : State C Γ} {o : COut C σ.H Γ'}
    (h : ExecPM M J σ P o) : ExecPM M' J σ P o :=
  (prog_iffM P hP).mpr (((prog_iffM P hP).mp h).mono hA)

/-- **The deterministic run is one under every model** (`Prog.execM_run`):
with no callback (`J.pay = false`, no value call) the handler answers
`Ev.same`, and a fragment program's tree reads as `Prog.run`. -/
theorem handle_det {A : Allow C} {R : Type} {viol : R} {e : Ev C} {k : e.Ans → Tree C R}
    {o : R} (hc : e.kind.callsBack J.pay = false) (h : Handle A J viol (k e.same) o) :
    Handle A J viol (.vis e k) o := .det hc h

/-- The tree's deterministic reading is the typed run, on the fragment. -/
theorem stmt_runDet {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} (hs : Stmt.Frag s) (σ : State C Γ) :
    (Stmt.tree s σ).runDet = .ofRes (s.run σ) := by
  rcases hs with hp | hf
  · cases s <;> try cases hp
    case inl.transfer.refl r a =>
      show (transferTree r a σ).runDet = .ofRes (TRun.transfer r a σ)
      unfold transferTree; cases TRun.transfer r a σ <;> rfl
    case inl.send.refl full pv r a =>
      show (sendTree pv r a full σ).runDet = .ofRes (TRun.send pv r a σ)
      unfold sendTree
      cases hs : TRun.send pv r a σ with
      | error e => rfl
      | ok o =>
        cases ht : TRun.transfer r a σ with
        | error _ => rfl
        | ok o₁ => rw [send_of_transfer ht] at hs; cases hs; rfl
  · rw [tree_of_forks hf]; rfl

theorem prog_runDet : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → Prog.Frag P → (σ : State C Γ) →
    (Prog.tree P σ).runDet = .ofRes (P.run σ)
  | _, _, .nil, _, _ => rfl
  | _, _, .cons s P, hsP, σ => by
    obtain ⟨hs, hP⟩ : Stmt.Frag s ∧ Prog.Frag P := hsP
    rw [Prog.tree, Tree.runDet_bind, stmt_runDet hs]
    cases h : s.run σ with
    | error e =>
      show COut.halt e = COut.ofRes (TRun.seq s.runR P.runR σ)
      simp only [TRun.seq, Stmt.run] at h ⊢; rw [h]; rfl
    | ok o₁ =>
      rw [Prog.run_cons_ok h]
      show (Tree.map _ (Prog.tree P o₁.st)).runDet = _
      rw [Tree.map, Tree.runDet_bind, prog_runDet P hP o₁.st]
      cases Prog.run o₁.st P <;> rfl

/-- **`Prog.execM_run` on the fragment**, by the generic `Handle.runDet`
(today 360 + 360 lines for `Stmt.exec_run` and `Stmt.execM_run`). -/
theorem prog_execM_run (M : CallerModel C) {Γ Γ' : Ctx} (P : Prog C Γ Γ') (hP : Prog.Frag P)
    (σ : State C Γ) :
    ExecPM M J σ P (.ofRes (P.run σ)) ∨ ExecPM M J σ P .violated := by
  rw [prog_iffM P hP, prog_iffM P hP, ← prog_runDet P hP σ]
  exact Handle.runDet (fun σ => M.allows_refl J σ) _

end Reproved

end Solidity.Scratch.ITree
