import Solidity.Calculus.Spec
import Solidity.Semantics.Mutability

/-!
# Function contracts

A call can be proved by its callee's contract instead of its body: prove the
callee's `requires`, forget what the callee may change, assume its
`ensures`.  This is KeY's `useOperationContract` at the box, in the shape of
`transferWithCallbackBox` (`Calculus/Callback.lean`), with the goals
`"pre"` and `"post"` of solkey's planned contract taclet (KeY's Java rule
labels them `Pre (f)` and `Post (f)`) and the parameters bound as the
inlining binds them (`uint x' = a;`, KeY's `{params := args}`):

```
  "pre":   Γ ⟹ [ params := args ] requires
  "post":  Γ ⟹ [ params := args ] {old := storage ‖ oldNet := net} {havoc}
             ∀ T r. (ensures → [ res = r; ..ω ] φ)
  ───────────────────────────────────────────────────────────────────────────
           Γ ⟹ [ fbs; ..ω ] φ
```

`{old := storage ‖ oldNet := net}` are the snapshots `\old` reads
(`find(old, count)`, `oldNet[a]`, as in `Calculus/Spec.lean`).  `{havoc}` is the anonymising update a callback
leaves (`State.havoc`: storage and ledger replaced, KeY's
`{storage := storageSk ‖ net := netSk}`), there for a `nonpayable` callee
only: a `pure` or `view` one changes neither (`Mutability.anon`,
`Semantics/Mutability.lean`).  `∀ T r` is KeY's result skolem constant:
the callee's return variable holds any value of its type
(`CallRet.binders`), and `res = r;` lands it where the call is
(`CallRet.result`).

**Soundness is from `Stmt.run`** (`FunContract.sound`).  A contract
(`FunContract`) is a fact about the callee's block `T r; body` run from any
state where `requires` holds, with `old` the storage and `oldNet` the
ledger; its obligation (`FunContract.obligation`, solkey's planned
`requires -> [g(args)@C] ensures`, with no contract invariant, since one may
be broken inside a transaction) is
`requires → {old := storage ‖ oldNet := net} [ T r; body ] (ensures ∧ typed(r))`,
a formula proved like any other (`FunContract.ofValid`).  It owes the result's type
(`CallRet.typed`, `rangeFml`), as KeY's `inUInt(result)` does.  The body's
mutability is checked on its syntax (`Prog.within`, by `rfl`) and bounds
what the run changed (`Prog.frame_of_within`).  The callee's locals are
fresh, and the side condition `CallRet.freshFor` (by `rfl`) says that
`ensures`, the result's landing and the rest of the program read none of
them but its return variables, and that only the contract mentions `old`.

The rule's goals are sequents of `⊢` and its conclusion is `⊨`
(`useContract`; `useContract_of_valid` takes the goals as `⊨`): `Proves` is
not extended, so a contract is used at the first statement of a goal, where
a walk would apply `internalCallExpand` (`functionBodyExpand` for a call
with targets): its `fbs` stands for any call, `ic` or `fbs`.  Box only: a diamond contract would
also owe termination.  The callee's parameters are the call's fresh locals
(`se1`, …), so a contract is stated at a call's names; recursion stays out,
as it does for inlining.
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-- `old`, the storage variable `\old` reads (`Calculus/Spec.lean`'s
`oldVar`), written as the constructor, so that the kernel compares it with
the program's locals without parsing a name. -/
def oldLocal : Var := .user "old"

/-- `oldNet`, the ledger variable `\old(net(a))` reads (`oldNetVar`). -/
def oldNetLocal : Var := .user "oldNet"

/-! ## The callee's result -/

/-- The return variables a call declares, at their types: what "Post"
quantifies.  (A memory reference is returned through the caller's locals,
`CallRet.none`, and declared in the body.) -/
def CallRet.binders : CallRet → List (PrimTy × Var)
  | .none => []
  | .val p r _ => [(p, r)]
  | .rets rs => rs

/-- Each return variable holds a value of its type. -/
def CallRet.Fits (ret : CallRet) (τ : State) : Prop :=
  ∀ b ∈ ret.binders, ∃ v, τ.getEnv b.2 = .ok (.val v) ∧ b.1.admits v

/-- The return variables are values of their types, as a formula
(`rangeFml`: `0 <= r <= 2^256 - 1` for a `uint`). -/
def CallRet.typed (ret : CallRet) : Fml C :=
  Fml.conj (ret.binders.map fun b => rangeFml (.pv b.2) b.1)

/-- The callee's locals that "Post" forgets: those its block writes, but its
return variables, which "Post" quantifies. -/
def CallRet.scratch (ret : CallRet) (body : Prog C) : List Var :=
  (Prog.writes (ret.decl ++ body)).filter fun x => !(ret.binders.map (·.2)).contains x

/-- **The side condition**: the postcondition, the result's landing and the
rest of the program read none of the callee's scratch locals; and the
snapshots `old` and `oldNet` are the contract's alone: neither the callee
nor the rest mentions them. -/
def CallRet.freshFor (ret : CallRet) (body : Prog C) (ens : Fml C) (ω : Prog C) (φ : Fml C) :
    Bool :=
  (ens.vars ++ Prog.vars (ret.result ++ ω) ++ φ.vars).all (fun x => !(ret.scratch body).contains x) &&
    (Prog.vars (ret.decl ++ body) ++ Prog.vars (ret.result ++ ω) ++ φ.vars).all
      (fun x => ![oldLocal, oldNetLocal].contains x)

/-- What "Post" forgets of the contract's state: storage and ledger, for a
`nonpayable` callee (`{havoc}`); nothing for a `pure` or `view` one. -/
def Mutability.anon (μ : Mutability) (φ : Fml C) : Fml C :=
  match μ with
  | .nonpayable => .havoc φ
  | .pure | .view => φ

/-! ## Contracts -/

/-- `{old := storage ‖ oldNet := net}`: the snapshots `\old` reads, taken
where the callee is entered, as solkey's obligation takes them. -/
def snapOld : Upd C := [.store oldLocal .storage, .saveNet oldNetLocal]

/-- The state `snapOld` leaves. -/
def Semantics.State.snapOld (σ : State) : State :=
  (σ.setEnv oldLocal (.store σ.storage)).setEnv oldNetLocal (.ledger σ.net)

theorem snapOld_apply (σ : State) : (snapOld (C := C)).apply σ = .ok σ.snapOld := rfl

/-- **A function contract**, `requires` and `ensures` over the state and the
callee's locals (its parameters, bound to the arguments, and its return
variables), `\old` read at `old` and `oldNet`: from a state where
`requires` holds, the callee's block (its return variables declared, then
its body), entered with `old` the storage and `oldNet` the ledger, does not
panic and, if it returns, ends where `ensures` holds, its return variables
values of their types. -/
def FunContract (ret : CallRet) (body : Prog C) (req ens : Fml C) : Prop :=
  ∀ σ, holds σ req →
    Modality.box.afterRun (fun τ => holds τ ens ∧ ret.Fits τ) (Prog.run σ.snapOld (ret.decl ++ body))

/-- **The obligation of a contract**, solkey's planned
`requires -> [g(args)@C] ensures` for the callee's block:
`requires → {old := storage ‖ oldNet := net} [ T r; body ] (ensures ∧ typed(r))`,
the parameters free locals (the call's "pre" and "post" bind them to the
arguments). -/
def FunContract.obligation (ret : CallRet) (body : Prog C) (req ens : Fml C) : Fml C :=
  .imp req (.upd .box snapOld (.modal .box (ret.decl ++ body) (.and ens ret.typed)))

theorem holds_rangeFml_pv {σ : State} {r : Var} :
    (p : PrimTy) → holds σ (rangeFml (C := C) (.pv r) p) →
      ∃ v, σ.getEnv r = .ok (.val v) ∧ p.admits v := by
  intro p h
  cases p with
  | bool =>
    obtain ⟨x, hx, -⟩ := holds_eqD_iff.1 h
    simp only [Tm.eval, Op1.eval, bind, Except.bind] at hx
    cases hg : σ.getEnv r with
    | error e => simp only [hg, reduceCtorEq] at hx
    | ok b =>
      cases b <;> simp only [hg, pure, Except.pure, reduceCtorEq] at hx
      rename_i v
      refine ⟨v, rfl, ?_⟩
      cases v with
      | bool => trivial
      | int n => simp only [applyUnOp, bind, Except.bind, Value.asBool, reduceCtorEq] at hx
  | uint =>
    obtain ⟨x, hx, hl⟩ := holds_eqD_iff.1 h.1
    obtain ⟨y, hy, hl'⟩ := holds_eqD_iff.1 h.2
    simp only [Tm.eval, Op2.eval, Op0.eval, bind, Except.bind] at hx hy hl hl'
    cases hl; cases hl'
    cases hg : σ.getEnv r with
    | error e => simp only [hg, reduceCtorEq] at hy
    | ok b =>
      cases b <;> simp only [pure, Except.pure, hg, reduceCtorEq] at hx hy
      rename_i v
      refine ⟨v, rfl, ?_⟩
      cases v with
      | bool => simp only [evalBinop, bind, Except.bind, applyBinOp, Value.asInt, reduceCtorEq] at hy
      | int n =>
        simp only [evalBinop, bind, Except.bind, applyBinOp, Value.asInt, checkArith,
          Except.ok.injEq, PrimVal.bool.injEq, decide_eq_true_eq] at hx hy
        exact ⟨hx, by omega⟩
  | int =>
    obtain ⟨x, hx, hl⟩ := holds_eqD_iff.1 h.1
    obtain ⟨y, hy, hl'⟩ := holds_eqD_iff.1 h.2
    simp only [Tm.eval, Op2.eval, Op0.eval, bind, Except.bind] at hx hy hl hl'
    cases hl; cases hl'
    cases hg : σ.getEnv r with
    | error e => simp only [hg, reduceCtorEq] at hy
    | ok b =>
      cases b <;> simp only [pure, Except.pure, hg, reduceCtorEq] at hx hy
      rename_i v
      refine ⟨v, rfl, ?_⟩
      cases v with
      | bool => simp only [evalBinop, bind, Except.bind, applyBinOp, Value.asInt, reduceCtorEq] at hy
      | int n =>
        simp only [evalBinop, bind, Except.bind, applyBinOp, Value.asInt, checkArith,
          Except.ok.injEq, PrimVal.bool.injEq, decide_eq_true_eq] at hx hy
        exact ⟨hx, by omega⟩

theorem CallRet.fits_of_typed (ret : CallRet) {τ : State} (h : holds τ (ret.typed (C := C))) :
    ret.Fits τ := by
  intro b hb
  rw [CallRet.typed, holds_conj] at h
  exact holds_rangeFml_pv b.1 (h _ (List.mem_map.2 ⟨b, hb, rfl⟩))

/-- A contract from a derivation of its obligation. -/
theorem FunContract.ofValid {ret : CallRet} {body : Prog C} {req ens : Fml C}
    (h : ⊨ FunContract.obligation ret body req ens) : FunContract ret body req ens := by
  intro σ hreq
  have h' : Modality.box.afterRun (holds · (.and ens ret.typed))
      (Prog.run σ.snapOld (ret.decl ++ body)) := h σ hreq
  obtain ⟨ha, hp⟩ := h'
  refine ⟨?_, hp⟩
  revert ha
  cases Prog.run σ.snapOld (ret.decl ++ body) with
  | error _ => exact id
  | ok τ => exact fun ha => ⟨ha.1, ret.fits_of_typed ha.2⟩

/-! ## Soundness -/

section Sound

open SemanticsProperties Mutability

/-- The return variables bound, as "Post"'s `∀ T r` binds them, to what the
callee left in them: a state that agrees with what it left off the scratch
locals alone. -/
theorem binds_of_fits {τ : State} : (xs : List (PrimTy × Var)) → ∀ {W : List Var} {σ : State},
    (∀ b ∈ xs, ∃ v, τ.getEnv b.2 = .ok (.val v) ∧ b.1.admits v) → EnvAgreeExcept W σ τ →
      ∃ σ', Binds xs σ σ' ∧ EnvAgreeExcept (W.filter fun x => !(xs.map (·.2)).contains x) σ' τ
  | [], W, σ, _, h => ⟨σ, ⟨[], rfl⟩, agree_mono (fun x hx => by
    simp only [List.map_nil, List.contains_eq_mem, List.not_mem_nil, decide_false, Bool.not_false,
      List.mem_filter, hx, and_self]) h⟩
  | (p, x) :: xs, W, σ, hfit, h => by
    obtain ⟨v, hv, hadm⟩ := hfit (p, x) (List.mem_cons_self ..)
    have hτ : lookupBy x τ.env = some (.val v) := by
      unfold State.getEnv at hv
      split at hv <;> first | (cases hv; assumption) | cases hv
    have h₁ : EnvAgreeExcept (W.filter fun y => !([x].contains y)) (σ.setEnv x (.val v)) τ :=
      ⟨h.storage, h.heap, h.nextId, h.net, fun n hn => by
        by_cases hnx : n = x
        · subst hnx
          simp only [State.setEnv, lookupBy_setBy_self, hτ]
        · simp only [State.setEnv, lookupBy_setBy_ne hnx]
          exact h.env n fun hw => hn (by
            simp only [List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false,
              List.mem_filter, hw, hnx, decide_false, Bool.not_false, and_self]),
        h.selfBalance, h.tx⟩
    obtain ⟨σ', ⟨vs, hb⟩, h'⟩ := binds_of_fits xs (fun b hb => hfit b (List.mem_cons_of_mem _ hb)) h₁
    refine ⟨σ', ⟨v :: vs, ?_⟩, agree_mono (fun y hy => ?_) h'⟩
    · have hf : v.fits p = true := (PrimTy.admits_iff_fits p v).1 hadm
      simp only [bindData, hf, if_true]
      exact hb
    · simp only [List.mem_filter, List.contains_cons, List.contains_nil, Bool.or_false,
        Bool.not_eq_eq_eq_not, Bool.not_true, List.map_cons] at hy ⊢
      simp only [Bool.or_eq_false_iff]
      exact ⟨hy.1.1, hy.1.2, hy.2⟩

theorem avoids_of_all {vs ns : List Var} (h : (vs.all fun x => !ns.contains x) = true) :
    Avoids vs ns := by
  intro x hx hn
  have hx' : (!ns.contains x) = true := List.all_eq_true.1 h x hx
  simp_all only [List.contains_eq_mem, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not]

/-- **A contract is sound**, at a state: "Pre" and "Post" there give the
call and the rest. -/
theorem FunContract.sound {μ : Mutability} {f : Name} {args : List (Arg C)}
    {hsep : Arg.separatedFrom [] args = true} {ret : CallRet} {body : Prog C} {ω : Prog C}
    {φ req ens : Fml C} (hc : FunContract ret body req ens)
    (hμ : Prog.within μ (ret.decl ++ body) = true) (hfr : ret.freshFor body ens ω φ = true)
    {σ : State} (hpre : holds σ (.modal .box (args.map Arg.decl) req))
    (hpost : holds σ (.modal .box (args.map Arg.decl) (.upd .box snapOld
      (μ.anon (.alls ret.binders (.imp ens (.modal .box (ret.result ++ ω) φ)))))))
    : holds σ (.modal .box (.call f args hsep ret body :: ω) φ) := by
  simp only [CallRet.freshFor, Bool.and_eq_true] at hfr
  have hS : Avoids (ens.vars ++ Prog.vars (ret.result ++ ω) ++ φ.vars) (ret.scratch body) :=
    avoids_of_all hfr.1
  have hO : Avoids (Prog.vars (ret.decl ++ body) ++ Prog.vars (ret.result ++ ω) ++ φ.vars)
      [oldLocal, oldNetLocal] := avoids_of_all hfr.2
  have hrun : Prog.run σ (.call f args hsep ret body :: ω) =
      (do let σ₁ ← Prog.run σ (args.map Arg.decl)
          let τ ← Prog.run σ₁ (ret.decl ++ body)
          Prog.run τ (ret.result ++ ω)) := by
    simp only [Prog.run_cons, Stmt.run_call_expand, Stmt.expandBody, Prog.run_append, bind_assoc]
  simp only [holds] at hpre hpost ⊢
  rw [hrun]
  cases hP : Prog.run σ (args.map Arg.decl) with
  | error e =>
    rw [hP] at hpre
    exact hpre
  | ok σ₁ =>
    rw [hP] at hpre hpost
    have hreq : holds σ₁ req := hpre.1
    have hsnap : holds σ₁.snapOld
        (μ.anon (.alls ret.binders (.imp ens (.modal .box (ret.result ++ ω) φ)))) := hpost.1
    have hag0 : EnvAgreeExcept [oldLocal, oldNetLocal] σ₁ σ₁.snapOld :=
      Mutability.agree_trans (Mutability.agree_setEnv (List.mem_cons_self ..) σ₁ _)
        (Mutability.agree_setEnv (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ _)
    have hra : ResultsAgree [oldLocal, oldNetLocal] (Prog.run σ₁ (ret.decl ++ body))
        (Prog.run σ₁.snapOld (ret.decl ++ body)) := Prog.run_frame hag0 _ hO.left.left
    have hct : Modality.box.afterRun (fun τ => holds τ ens ∧ ret.Fits τ)
        (Prog.run σ₁.snapOld (ret.decl ++ body)) := hc σ₁ hreq
    simp only [bind, Except.bind]
    cases hB : Prog.run σ₁ (ret.decl ++ body) with
    | error e =>
      rw [hB] at hra
      cases hB0 : Prog.run σ₁.snapOld (ret.decl ++ body) with
      | error e' =>
        rw [hB0] at hra hct
        cases hra
        exact hct
      | ok _ => rw [hB0] at hra; exact hra.elim
    | ok τ =>
      rw [hB] at hra
      cases hB0 : Prog.run σ₁.snapOld (ret.decl ++ body) with
      | error _ => rw [hB0] at hra; exact hra.elim
      | ok τ₀ =>
        rw [hB0] at hra hct
        obtain ⟨⟨hens, hfits⟩, -⟩ := hct
        have hfr0 : μ.Frame (Prog.writes (ret.decl ++ body)) σ₁.snapOld τ₀ :=
          Prog.frame_of_within _ hμ hB0
        obtain ⟨σ₂, hA, hE⟩ : ∃ σ₂, holds σ₂ (.alls ret.binders (.imp ens (.modal .box (ret.result ++ ω) φ)))
            ∧ EnvAgreeExcept (Prog.writes (ret.decl ++ body)) σ₂ τ₀ := by
          cases μ with
          | pure => exact ⟨_, hsnap, hfr0⟩
          | view => exact ⟨_, hsnap, hfr0⟩
          | nonpayable => exact ⟨_, hsnap τ₀.storage τ₀.net, hfr0⟩
        obtain ⟨σ', hb, hE'⟩ := binds_of_fits ret.binders hfits hE
        have hI : holds σ' (.imp ens (.modal .box (ret.result ++ ω) φ)) := (holds_alls.1 hA) σ' hb
        have hens' : holds σ' ens := (holds_frame ens hS.left.left hE').2 hens
        have hm : Modality.box.afterRun (holds · φ) (Prog.run σ' (ret.result ++ ω)) := hI hens'
        have h₀ : Modality.box.afterRun (holds · φ) (Prog.run τ₀ (ret.result ++ ω)) :=
          (Modality.afterRun_frame .box (Prog.run_frame hE' _ hS.left.right)
            (fun _ _ hab => holds_frame φ hS.right hab)).1 hm
        exact (Modality.afterRun_frame .box (Prog.run_frame hra _ hO.left.right)
          (fun _ _ hab => holds_frame φ hO.right hab)).2 h₀

end Sound

/-! ## The rule -/

/-- `useContract` with its goals proved valid rather than derived: what a
goal closed by `sol_symex; sol_close` gives. -/
theorem useContract_of_valid {Γ : List (Hyp C)} {μ : Mutability} {f : Name}
    {args : List (Arg C)} {hsep : Arg.separatedFrom [] args = true} {ret : CallRet}
    {body ω : Prog C} {φ req ens : Fml C} (hc : FunContract ret body req ens)
    («pre» : ⊨ Hyp.wrap Γ dl_schema{ [ ..(args.map Arg.decl) ] req })
    («post» : ⊨ Hyp.wrap Γ dl_schema{ [ ..(args.map Arg.decl) ]
      ‹.upd .box snapOld (μ.anon (.alls ret.binders dl_schema{ ens → [ ..(ret.result ++ ω) ] φ }))› })
    (hμ : Prog.within μ (ret.decl ++ body) = true := by rfl)
    (hfr : ret.freshFor body ens ω φ = true := by rfl) :
    ⊨ Hyp.wrap Γ dl_schema{ [ fbs; ..ω ] φ } :=
  fun σ => Hyp.wrap_mono₂ (fun _ h₁ h₂ => FunContract.sound hc hμ hfr h₁ h₂) Γ σ («pre» σ) («post» σ)

/-- **`useContract`**: a call proved by its callee's contract, KeY's
`useOperationContract` at the box, with the goals `"pre"` and `"post"`:

```
  "pre":   Γ ⟹ [ params := args ] requires
  "post":  Γ ⟹ [ params := args ] {old := storage ‖ oldNet := net} {havoc}
             ∀ T r. (ensures → [ res = r; ..ω ] φ)
  ───────────────────────────────────────────────────────────────────────────
           Γ ⟹ [ fbs; ..ω ] φ
```

`{havoc}` only for a `nonpayable` callee (`Mutability.anon`); the side
conditions, the body's mutability and the freshness of what "post" forgets,
are computed (`rfl`). -/
theorem useContract {R : RuleSet} {Γ : List (Hyp C)} {μ : Mutability} {f : Name}
    {args : List (Arg C)} {hsep : Arg.separatedFrom [] args = true} {ret : CallRet}
    {body ω : Prog C} {φ req ens : Fml C} (hc : FunContract ret body req ens)
    («pre» : dl{ ..Γ ⟹[R] [ ..(args.map Arg.decl) ] req })
    («post» : dl{ ..Γ ⟹[R] [ ..(args.map Arg.decl) ]
      ‹.upd .box snapOld (μ.anon (.alls ret.binders dl_schema{ ens → [ ..(ret.result ++ ω) ] φ }))› })
    (hμ : Prog.within μ (ret.decl ++ body) = true := by rfl)
    (hfr : ret.freshFor body ens ω φ = true := by rfl) :
    ⊨ Hyp.wrap Γ dl_schema{ [ fbs; ..ω ] φ } :=
  useContract_of_valid hc «pre».sound «post».sound hμ hfr

end Solidity
