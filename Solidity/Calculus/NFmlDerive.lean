import Solidity.Calculus.DecideComplete
import Solidity.Calculus.Closer
import Solidity.Calculus.TheoryRewrite
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.TreeData

/-!
# The closer's walk as one kernel evaluation: `sol_prove` on a leaf

A leaf the scoped strategy leaves (`Calculus/Derive.lean`,
`Calculus/ProvesDerive.lean`) is erased to a sequent of
`Logic.lean`'s calculus and handed here.  `Derive.residue` runs that
calculus's walk as a function: on a sequent `Γ ⟹ φ` it drops an empty
modality, moves a precondition, a quantified local or an update into the
context, and leaves what none of these fits as a leaf, dropped when the
closer accepts it.  What is left is the residue.  `Proves.of_residue` says
once that a residue whose leaves are proved proves the sequent, so a leaf
is one evaluation the kernel checks.  The program rules went with today's
rule table (W4 `calc-del`, `docs/intrinsic.md`): a program left in a leaf
stays a leaf.

The default closer (`Derive.synClose`) is `LFml.close` on the reduction
(`Calculus/Closer.lean`): it closes a leaf inside the `Bool`, reading an
obligation's `wt(storage)` premise as the layout the storage holds
(`Derive.topWt`).  A parallel update is split first (`NFml.seqUpd`), and a
leaf past `Derive.closeSize` nodes, or whose reduction is past
`Derive.elimSize`, is not attempted, by the closer nor by `sol_prove?`'s
reducing steps.  A leaf it does not close is left for a
tactic.

Neither the compiled run nor the kernel check heeds `maxHeartbeats`, so
the walk carries its own budget (`Derive.budget`).

* `sol_prove` computes the residue by compiled code, checks it in the
  kernel (`Derive.proves` when nothing is left,
  `Derive.residue … = some (ls, b)` otherwise, each an auxiliary lemma as
  `decide +kernel` makes one), and
  leaves one goal per residual leaf, `leaf1`, `leaf2`, … .  It searches
  nothing, so it is its own replay.  The statement is never unfolded by the
  elaborator: `Proves` is an inductive, and the proof term is assembled
  directly.
* `sol_prove?` runs `sol_prove`, tries `sol_decide`'s steps after
  `LFml.syn` (which the closer subsumes), then `sol_close`, then
  `sol_spec_close` (`omega`, `grind`) on each leaf, each try with its own
  heartbeats, and suggests the replay: `sol_prove` and one `case` per leaf.
  A leaf none of them closes stays a goal and is reported.
-/

namespace Solidity

open Semantics

variable {C : Contract}

namespace NFml.Derive

/-- A goal left over: a context and a formula. -/
abbrev Leaf (C : Contract) := List (Hyp C) × NFml C

/-- **The residue** of `Γ ⟹ φ`: the connectives in front of the goal moved
into the context, the leaves `close` accepts dropped, and the budget left.
`n` bounds the steps, so that the recursion is structural; `b` bounds the
steps of the whole walk.  `none` when either runs out. -/
def residue : Nat → (List (Hyp C) → NFml C → Bool) → Nat → List (Hyp C) → NFml C →
    Option (List (Leaf C) × Nat)
  | 0, _, _, _, _ => none
  | _ + 1, _, 0, _, _ => none
  | n + 1, close, b + 1, Γ, .imp a ψ => residue n close b (Γ ++ [.pre a]) ψ
  | n + 1, close, b + 1, Γ, .all x p ψ => residue n close b (Γ ++ [.all x p]) ψ
  | n + 1, close, b + 1, Γ, .upd m U ψ => residue n close b (Γ ++ [.upd m U]) ψ
  | _ + 1, close, b + 1, Γ, ψ => if close Γ ψ then some ([], b) else some ([(Γ, ψ)], b)

/-- Nothing is left. -/
def closes (n : Nat) (close : List (Hyp C) → NFml C → Bool) (b : Nat) (Γ : List (Hyp C))
    (φ : NFml C) : Bool :=
  match residue n close b Γ φ with
  | some ([], _) => true
  | _ => false

/-- A precondition the closer sets aside as a formula: `wt(storage)`, an
obligation's premise (`Calculus/Problem.lean`), which the fragment does not
read (the closer reads it as a layout, `Derive.topWt`).  Dropping a
precondition only weakens what is to be shown (`Derive.wrap_dropWt`). -/
def isWt : Hyp C → Bool
  | .pre (.defined (.app1 (.wt _) _)) => true
  | _ => false

/-- The context without its `wt` premises. -/
def dropWt (Γ : List (Hyp C)) : List (Hyp C) := Γ.filter (!isWt ·)

/-! ### Parallel updates, one element at a time

A rule may leave a parallel update, `{ x := x + 1 ‖ r := x + 1 }` of
`r = ++x;`, which `NFml.toL` does not read.  Where its last element binds a
local the others neither read nor write, it is the same as that element
first and the others after it (KeY's `sequentialToParallel`, read
backwards): `{ r := x + 1 }{ x := x + 1 }`.  `NFml.seqUpd` splits every such
update before the closer runs; it only has to imply the leaf. -/

/-- The local an update element binds, for the two kinds the split moves. -/
def _root_.Solidity.Surface.UpdElem.target? : Surface.UpdElem C → Option Var
  | .val x _ | .path x _ => some x
  | _ => none

/-- A parallel update, its elements reversed (`rs`), as one update per
element from the last, while the last binds a local the rest does not
mention; the rest as one parallel update. -/
def seqRev (m : Modality) (ψ : NFml C) : List (Surface.UpdElem C) → NFml C
  | [] => .upd m [] ψ
  | [e] => .upd m [e] ψ
  | e :: rest =>
    match e.target? with
    | some x => if x ∈ Surface.Upd.vars rest.reverse then .upd m (e :: rest).reverse ψ
      else .upd m [e] (seqRev m ψ rest)
    | none => .upd m (e :: rest).reverse ψ

/-! ### The alias a push returns

`T storage x = arr.push();` leaves `{ storage := extend(storage, arr) ‖
x := arr[arr.length] }`: the alias names the slot past the old end, which
the push makes live.  `pushAlias?` reads it as the push, then the alias to
the last slot (`lastSlot`), the length read after the push; the two agree
where the path to the array reads the storage only to check its indices
(`Tm.stablePath`). -/

section PushAlias

open SemanticsProperties

/-- A key that reads no storage: a local or a literal. -/
def _root_.Solidity.Surface.Tm.keyFree {s : Srt} : Surface.Tm C s → Bool
  | .pvV _ | .app0 (.lit _) => true
  | _ => false

/-- A path that reads the storage only to check its indices: roots,
aliases, members, and indices by locals or literals.  A write below it
leaves it naming the same location (`stable_eval`). -/
def _root_.Solidity.Surface.Tm.stablePath {s : Srt} : Surface.Tm C s → Bool
  | .app0 (.root _) | .pvP _ => true
  | .app1 (.field _) q => q.stablePath
  | .app2 .at q k => q.stablePath && k.keyFree
  | _ => false
termination_by structural t => t

theorem keyFree_eval {σ τ : Semantics.State} (henv : τ.env = σ.env) :
    (k : Surface.Tm C .val) → k.keyFree = true → k.eval τ = k.eval σ
  | .pvV x, _ => by simp only [Surface.Tm.eval, State.getEnv, henv]
  | .app0 (.lit _), _ => rfl

theorem saveStorage_state {σ τ : Semantics.State} {r : Name} {P : List Seg} {X : Semantics.SVal}
    (h : σ.saveStorage r P X = .ok τ) : τ = { σ with storage := τ.storage } := by
  unfold State.saveStorage at h
  split at h
  · obtain ⟨_, _, he⟩ := Res.bind_eq_ok.1 h; cases he; rfl
  · cases h

/-- **A path below which the storage was written names the same
location**: its checks are of locations above the write. -/
theorem stable_eval {σ τ : Semantics.State} {r : Name} {P : List Seg} {X : Semantics.SVal}
    (hsv : σ.saveStorage r P X = .ok τ) :
    (p : Surface.Tm C .path) → p.stablePath = true → ∀ {r' : Name} {segs : List Seg},
      p.eval σ = .ok (r', segs) → (r' = r → ∃ rest, P = segs ++ rest) →
        p.eval τ = .ok (r', segs)
  | .app0 (.root _), _, _, _, h, _ => h
  | .pvP x, _, _, _, h, _ => by
    rw [saveStorage_state hsv]
    simpa only [Surface.Tm.eval, Semantics.aliasPath, State.getEnv] using h
  | .app1 (.field f) q, hp, r', segs, h, hpre => by
    simp only [Surface.Tm.stablePath] at hp
    rw [Close.PTerm.eval_field] at h ⊢
    obtain ⟨⟨r₀, segs₀⟩, h₀, he⟩ := Res.bind_eq_ok.1 h
    cases he
    rw [stable_eval hsv q hp h₀ fun hr => by
      obtain ⟨rest, hrest⟩ := hpre hr
      exact ⟨.field f :: rest, by simp only [hrest, List.append_assoc, List.cons_append,
          List.nil_append]⟩]
    rfl
  | .app2 .at q k, hp, r', segs, h, hpre => by
    simp only [Surface.Tm.stablePath, Bool.and_eq_true] at hp
    rw [Close.PTerm.eval_at] at h ⊢
    obtain ⟨⟨r₀, segs₀⟩, h₀, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨i, hi, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨_, hc, he⟩ := Res.bind_eq_ok.1 h
    cases he
    have henv : τ.env = σ.env := by rw [saveStorage_state hsv]
    rw [stable_eval hsv q hp.1 h₀ fun hr => by
      obtain ⟨rest, hrest⟩ := hpre hr
      exact ⟨.at i :: rest, by simp only [hrest, List.append_assoc, List.cons_append,
          List.nil_append]⟩, Res.ok_bind, keyFree_eval henv k hp.2, hi,
      Res.ok_bind, Close.checkIndex_saveStorage_apart i hsv ?_, hc, Res.ok_bind]
    by_cases hr : r₀ = r
    · subst hr
      obtain ⟨rest, hrest⟩ := hpre rfl
      refine .inr fun hpf => ?_
      have hl := congrArg List.length (Close.prefix_append hpf)
      rw [hrest] at hl
      simp only [List.length_append, List.length_cons, List.length_nil] at hl
      omega
    · exact .inl hr
  | .app1 .next _, h, _, _, _, _ | .app2 .nextIn _ _, h, _, _, _, _
  | .app3 .atIn _ _ _, h, _, _, _, _ => by simp only [Surface.Tm.stablePath, Bool.false_eq_true] at h


/-- Where `p = arr.push();` leaves its alias: the last slot, once the push
is made (`arr[arr.length - 1]`, the length unchecked). -/
def lastSlot (P : PTerm C) : PTerm C :=
  .at P (.binop .sub .bool (.len .storage P) (.lit (.int 1)))

/-- **The last slot after the push is the slot past the end before it.** -/
theorem lastSlot_eval {P : PTerm C} (hP : P.stablePath = true) {E : Ty} {σ τ : Semantics.State}
    (hs : (STerm.extend .storage P E).eval σ = .ok τ) :
    (lastSlot P).eval τ = (PTerm.next P).eval σ := by
  rw [Decide.STerm.eval_extend] at hs
  simp only [Close.STerm.eval_storage, Res.ok_bind] at hs
  obtain ⟨⟨r, segs⟩, hp, hs⟩ := Res.bind_eq_ok.1 hs
  obtain ⟨c, hc, hs⟩ := Res.bind_eq_ok.1 hs
  cases c with
  | array es sh fx =>
    simp only [Close.pushOn_array, pure, Except.pure, Res.ok_bind] at hs
    have hp' := stable_eval hs P hP hp (fun _ => ⟨[], by simp only [List.append_nil]⟩)
    have hf := State.findStorage_saveStorage_same hs
    rw [Close.PTerm.eval_next, hp, Res.ok_bind, hc, Res.ok_bind]
    simp only [lastSlot, Close.PTerm.eval_at, hp', Close.Term.eval_binop,
      Close.Term.eval_len, Close.STerm.eval_storage, hf, Close.arrLen, Close.Term.eval_lit,
      evalBinop, applyBinOp, Value.asInt, bind, Except.bind, checkArith, BinOp.retTy,
      BinOp.isArith, Close.checkIndex_eq, Close.pastEnd, List.length_append, List.length_singleton]
    simp only [↓reduceIte, Int.natCast_add, Int.cast_ofNat_Int, Int.add_sub_cancel, Close.idxOk,
      Int.ofNat_zero_le, Int.toNat_natCast, List.length_append, List.length_cons, List.length_nil,
      Nat.zero_add, Nat.lt_add_one, and_self]
  | prim _ | struct _ | map _ _ => simp only [Close.pushOn, reduceCtorEq] at hs

/-- `{ storage := extend(storage, p) ‖ x := p[p.length] }` of
`T storage x = p.push();`: the push, then the alias to its last slot. -/
def pushAlias? : Surface.Upd C → Option (STerm C × Var × PTerm C)
  | [.storage s, .path x n] =>
    match s, n with
    | .app2 (.extend _) (.app0 .storage) P, .app1 .next P' =>
      if P.stablePath && decide (P = P') then some (s, x, lastSlot P) else none
    | _, _ => none
  | _ => none

theorem pushAlias?_sound {U : Surface.Upd C} {s : STerm C} {x : Var} {Q : PTerm C}
    (h : pushAlias? U = some (s, x, Q)) {m : Modality} {ψ : NFml C} {σ : Semantics.State}
    (hh : holds σ (.upd m [.storage s] (.upd m [.path x Q] ψ))) : holds σ (.upd m U ψ) := by
  unfold pushAlias? at h
  split at h
  · rename_i s₀ x₀ n
    split at h
    · rename_i E P P'
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨hP, rfl⟩ := hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have h' : m.after (fun τ => m.after (fun ρ => holds ρ ψ) (Surface.Upd.apply [.path x₀ (lastSlot P)] τ))
          (Surface.Upd.apply [.storage (STerm.extend .storage P E)] σ) := hh
        change m.after (fun ρ => holds ρ ψ) (Surface.Upd.apply [.storage (STerm.extend .storage P E),
          .path x₀ (PTerm.next P)] σ)
        simp only [Surface.Upd.apply, List.foldlM_cons, List.foldlM_nil, Surface.UpdElem.write, bind_pure] at h' ⊢
        cases hs : (STerm.extend .storage P E).eval σ with
        | error e =>
          rw [hs] at h'
          simp only [Res.error_bind] at h' ⊢
          exact h'
        | ok τ =>
          rw [hs] at h'
          simp only [Res.ok_bind, pure, Except.pure, Modality.after] at h' ⊢
          have hτ : { σ with storage := τ.storage } = τ := by
            rw [Decide.STerm.eval_extend] at hs
            simp only [Close.STerm.eval_storage, Res.ok_bind] at hs
            obtain ⟨_, _, hs⟩ := Res.bind_eq_ok.1 hs
            obtain ⟨c, _, hs⟩ := Res.bind_eq_ok.1 hs
            cases c with
            | array es sh fx =>
              simp only [Close.pushOn_array, pure, Except.pure, Res.ok_bind] at hs
              rw [saveStorage_state hs]
            | prim _ | struct _ | map _ _ => simp only [Close.pushOn, reduceCtorEq] at hs
          rw [hτ] at h' ⊢
          rw [lastSlot_eval hP hs] at h'
          exact h'
      · cases h
    · cases h
  · cases h

end PushAlias

/-! ### An allocation, kept whole

`T memory x;` leaves `{ x := freshId(addM(memory)) ‖ memory :=
addM(memory) }`.  The object `x` names exists only in the memory after the
allocation, so the pair stays one update: `NFml.toL` reads it as one
(`Decide.pairL`), KeY's single Skolem `freshIdp`. -/

/-- `{ x := i ‖ memory := m }`: an allocation's pair, which `seqUpd` keeps. -/
def memAlloc? : Surface.Upd C → Bool
  | [.mref _ _, .memory _] => true
  | _ => false

/-- Every parallel update split where `seqRev` can, in the positions a leaf
proves (not in a premise). -/
def _root_.Solidity.NFml.seqUpd : NFml C → NFml C
  | .upd m U φ =>
    match pushAlias? U with
    | some (s, x, Q) => .upd m [.storage s] (.upd m [.path x Q] φ.seqUpd)
    | none =>
      if memAlloc? U then .upd m U φ.seqUpd else seqRev m φ.seqUpd U.reverse
  | .imp a φ => .imp a φ.seqUpd
  | .and φ ψ => .and φ.seqUpd ψ.seqUpd
  | .all x p φ => .all x p φ.seqUpd
  | φ => φ

theorem afterImp {m : Modality} {p q : Semantics.State → Prop} {r : Res Semantics.State} (h : ∀ τ, p τ → q τ) :
    m.after p r → m.after q r := by
  cases r with
  | ok τ => exact h τ
  | error _ => exact id

theorem Upd.apply_single (e : Surface.UpdElem C) (σ : Semantics.State) : Surface.Upd.apply [e] σ = e.write σ σ := by
  simp only [Surface.Upd.apply, List.foldlM_cons, List.foldlM_nil, bind_pure]

theorem Upd.apply_append_single (P : Surface.Upd C) (e : Surface.UpdElem C) (σ : Semantics.State) :
    Surface.Upd.apply (P ++ [e]) σ = Surface.Upd.apply P σ >>= fun ρ => e.write σ ρ := by
  simp only [Surface.Upd.apply, List.foldlM_append, List.foldlM_cons, List.foldlM_nil, bind_pure]

/-- **The last element first**: `{e}{P}ψ` implies `{P ‖ e}ψ` where `e`
binds a local `P` does not mention. -/
theorem peel_sound {m : Modality} {P : Surface.Upd C} {e : Surface.UpdElem C} {x : Var}
    (he : e.target? = some x) (hx : x ∉ Surface.Upd.vars P) {ψ : NFml C} {σ : Semantics.State}
    (h : holds σ (.upd m [e] (.upd m P ψ))) : holds σ (.upd m (P ++ [e]) ψ) := by
  -- the element writes `x := b`, `b` read in the state it starts from
  obtain ⟨bnd, hw⟩ : ∃ bnd : Semantics.State → Res Binding, ∀ σ₀ τ,
      e.write σ₀ τ = bnd σ₀ >>= fun b => .ok (τ.setEnv x b) := by
    unfold Surface.UpdElem.target? at he
    split at he
    · rename_i y t
      cases he
      exact ⟨fun σ₀ => t.eval σ₀ >>= fun v => .ok (.val v), fun σ₀ τ => by
        simp only [Surface.UpdElem.write, bind, Except.bind, pure, Except.pure]
        split <;> rfl⟩
    · rename_i y p
      cases he
      exact ⟨fun σ₀ => p.eval σ₀ >>= fun rs => .ok (.spath rs.1 rs.2), fun σ₀ τ => by
        simp only [Surface.UpdElem.write, bind, Except.bind, pure, Except.pure]
        split <;> rfl⟩
    · cases he
  have h' : m.after (fun τ => m.after (fun ρ => holds ρ ψ) (Surface.Upd.apply P τ)) (Surface.Upd.apply [e] σ) := h
  change m.after (fun ρ => holds ρ ψ) (Surface.Upd.apply (P ++ [e]) σ)
  rw [Upd.apply_single, hw] at h'
  rw [Upd.apply_append_single]
  simp only [hw]
  cases hb : bnd σ with
  | error eb =>
    rw [hb] at h'
    cases Surface.Upd.apply P σ with
    | error _ => exact h'
    | ok _ => exact h'
  | ok b =>
    rw [hb] at h'
    have h'' : m.after (fun ρ => holds ρ ψ) (Surface.Upd.apply P (σ.setEnv x b)) := h'
    have hag : EnvAgreeExcept [x] σ (σ.setEnv x b) :=
      EnvAgreeExcept.setEnv_right ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl⟩
        (List.mem_singleton_self x) b
    have hr := Surface.Upd.apply_frame hag P (fun y hy hm => by
      rw [List.mem_singleton] at hm; subst hm; exact hx hy)
    have hl : ∀ ρ₁, Surface.Upd.apply P (σ.setEnv x b) = .ok ρ₁ →
        lookupBy x ρ₁.env = lookupBy x (σ.setEnv x b).env :=
      fun ρ₁ h₁ => Surface.Upd.foldl_lookup P hx h₁
    revert h'' hr hl
    generalize Surface.Upd.apply P σ = r₀
    generalize Surface.Upd.apply P (σ.setEnv x b) = r₁
    intro h'' hr hl
    match r₀, r₁, hr with
    | .error _, .error _, _ => exact h''
    | .ok _, .error _, hr | .error _, .ok _, hr => exact (nomatch hr)
    | .ok ρ₀, .ok ρ₁, hr =>
      have hl₁ := hl ρ₁ rfl
      have hag' : EnvAgreeExcept [] ρ₁ (ρ₀.setEnv x b) :=
        ⟨hr.storage.symm, hr.heap.symm, hr.nextId.symm, hr.net.symm, fun n _ => by
          by_cases hn : n = x
          · subst hn
            simp only [hl₁, State.setEnv, SemanticsProperties.lookupBy_setBy_self]
          · simp only [State.setEnv, SemanticsProperties.lookupBy_setBy_ne hn]
            exact (hr.env n (by
              simpa only [List.mem_cons, List.not_mem_nil, or_false] using hn)).symm,
          hr.selfBalance.symm, hr.tx.symm⟩
      exact (holds_frame ψ (by intro _ _ hm; simp only [List.not_mem_nil] at hm) hag').1 h''

theorem seqRev_sound {m : Modality} {ψ ψ' : NFml C} (hψ : ∀ σ, holds σ ψ' → holds σ ψ) :
    (rs : List (Surface.UpdElem C)) → ∀ σ, holds σ (seqRev m ψ' rs) → holds σ (.upd m rs.reverse ψ)
  | [], σ, h => by
    simp only [seqRev, holds, Surface.Upd.apply, List.reverse_nil, List.foldlM_nil] at h ⊢
    exact hψ σ h
  | [e], σ, h => by
    simp only [seqRev, holds, List.reverse_cons, List.reverse_nil, List.nil_append] at h ⊢
    exact afterImp (fun τ => hψ τ) h
  | e :: e' :: rest, σ, h => by
    simp only [seqRev] at h
    split at h
    · rename_i x hx
      split at h
      · exact Hyp.wrap_mono hψ [.upd m _] σ h
      · rename_i hm
        rw [List.reverse_cons]
        refine peel_sound hx hm ?_
        simp only [holds] at h ⊢
        exact afterImp (fun τ hτ => seqRev_sound hψ (e' :: rest) τ hτ) h
    · exact Hyp.wrap_mono hψ [.upd m _] σ h

theorem NFml.seqUpd_sound : (φ : NFml C) → ∀ σ, holds σ φ.seqUpd → holds σ φ
  | .upd m U φ, σ, h => by
    simp only [NFml.seqUpd] at h
    split at h
    · rename_i s x Q hU
      refine pushAlias?_sound hU ?_
      simp only [holds] at h ⊢
      exact afterImp (fun τ hτ => afterImp (fun ρ hρ => NFml.seqUpd_sound φ ρ hρ) hτ) h
    · split at h
      · simp only [holds] at h ⊢
        exact afterImp (fun τ hτ => NFml.seqUpd_sound φ τ hτ) h
      · have := seqRev_sound (m := m) (fun τ => NFml.seqUpd_sound φ τ) U.reverse σ h
        rwa [List.reverse_reverse] at this
  | .imp a φ, σ, h => fun ha => NFml.seqUpd_sound φ σ (h ha)
  | .and φ ψ, σ, h => ⟨NFml.seqUpd_sound φ σ h.1, NFml.seqUpd_sound ψ σ h.2⟩
  | .all x p φ, σ, h => fun v hv => NFml.seqUpd_sound φ _ (h v hv)
  | .tt, _, h | .eq .., _, h | .defined _, _, h | .not _, _, h
  | .havoc _, _, h | .anon .., _, h => h

/-- The roots `wt(storage)` names. -/
def wtRoots? : NFml C → Option (List (Name × Ty))
  | .defined (.wt vs .storage) => some vs
  | _ => none

/-- The roots a leaf's first `wt(storage)` premise holds, where only
quantifiers and preconditions come before it (so it speaks of the storage
the leaf starts from); none otherwise. -/
def topWt : List (Hyp C) → List (Name × Ty)
  | [] => []
  | .pre a :: Γ =>
    match wtRoots? a with
    | some vs => vs
    | none => topWt Γ
  | .all _ _ :: Γ => topWt Γ
  | .upd _ _ :: _ | .havoc :: _ | .anon _ :: _ => []

/-- The closer's input is within bounds: the leaf `l` within `closeSize`
nodes, and its reduction within `elimSize`.  Both counts stop at their
bound, so the test costs at most their sum in steps; the reduction is
built first in compiled code, but as a graph that shares the reads it
repeats, and the kernel builds only the nodes the count visits. -/
def fitsClose (l : Decide.LFml) : Bool :=
  (l.fits closeSize).isSome && (l.elim.fits elimSize).isSome

/-- The default closer: in `sol_decide`'s fragment,
parallel updates split (`NFml.seqUpd`), within `fitsClose`, and its
reduction closed by `LFml.close` (`Calculus/Closer.lean`), the `wt`
premises set aside as formulas and read as the layout their storage holds
(`topWt`).  A leaf past the bounds is left open, not attempted. -/
def synClose (Γ : List (Hyp C)) (φ : NFml C) : Bool :=
  let v := Hyp.wrap (dropWt Γ) φ
  let w := v.seqUpd
  let l := w.toL Decide.Sym.empty
  fitsClose l && w.inL Decide.Sym.empty && Decide.LFml.close (topWt Γ) l.elim

/-- `synClose`'s bounds alone (`synClose_fits`): what `sol_prove?` asks
before it tries a step that reduces the leaf, since the reduction, its
quoting and its kernel check heed no heartbeats. -/
def leafFits (Γ : List (Hyp C)) (φ : NFml C) : Bool :=
  fitsClose ((Hyp.wrap (dropWt Γ) φ).seqUpd.toL Decide.Sym.empty)

/-- `leafFits` measures what `synClose` measures. -/
theorem synClose_fits {Γ : List (Hyp C)} {φ : NFml C} (h : synClose Γ φ = true) :
    leafFits Γ φ = true := by
  simp only [synClose, Bool.and_eq_true] at h
  exact h.1.1

/-- The steps `sol_prove` allows, over the whole derivation and so down any
one path: a runaway (a program whose `if`s double the paths) stops here, in
compiled code, before the kernel sees it. -/
def budget : Nat := 20000

/-- `sol_prove`'s check when nothing is left. -/
def proves (Γ : List (Hyp C)) (φ : NFml C) : Bool := closes budget synClose budget Γ φ

/-- The residue quoted, for the tactic: each leaf's context and formula as
the expressions that build them, the contract named by `c`; and the budget
left. -/
def residueQuote (c : Lean.Expr) (Γ : List (Hyp C)) (φ : NFml C) :
    Option (List (Lean.Expr × Lean.Expr) × Nat) :=
  (residue budget synClose budget Γ φ).map fun (ls, b) =>
    (ls.map fun l => (Hyp.quoteList c l.1, NFml.quote c l.2), b)

/-! ## Soundness -/

theorem leaves_nil : ∀ l ∈ ([] : List (Leaf C)), Proves .all l.1 l.2 :=
  fun _ h => nomatch h

theorem leaves_cons {Γ : List (Hyp C)} {φ : NFml C} {ls : List (Leaf C)} (h : Proves .all Γ φ)
    (t : ∀ l ∈ ls, Proves .all l.1 l.2) : ∀ l ∈ (Γ, φ) :: ls, Proves .all l.1 l.2 := by
  intro l hl
  rcases List.mem_cons.1 hl with rfl | hl
  · exact h
  · exact t l hl

/-- Setting the `wt` premises aside only weakens a formula. -/
theorem wrap_dropWt {φ : NFml C} : (Γ : List (Hyp C)) →
    ∀ σ, holds σ (Hyp.wrap (dropWt Γ) φ) → holds σ (Hyp.wrap Γ φ)
  | [] => fun _ => id
  | h :: Γ => by
    have ihh := wrap_dropWt (φ := φ) Γ
    cases hw : isWt h with
    | true =>
      have hd : dropWt (h :: Γ) = dropWt Γ := by
        simp only [dropWt, List.filter_cons, hw, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [hd]
      match h, hw with
      | .pre (.defined (.app1 (.wt _) _)), _ => exact fun σ hs _ => ihh σ hs
    | false =>
      have hd : dropWt (h :: Γ) = h :: dropWt Γ := by
        simp only [dropWt, List.filter_cons, hw, Bool.not_false, ↓reduceIte]
      rw [hd]
      cases h with
      | pre a => exact fun σ hs ha => ihh σ (hs ha)
      | upd m U => exact fun σ hs => Hyp.wrap_mono ihh [.upd m U] σ hs
      | havoc => exact fun σ hs => Hyp.wrap_mono ihh [.havoc] σ hs
      | all x p => exact fun σ hs => Hyp.wrap_mono ihh [.all x p] σ hs
      | anon xs => exact fun σ hs => Hyp.wrap_mono ihh [.anon xs] σ hs

/-- `Proves.close` with the `wt` premises set aside: a leaf of an
obligation, closed by a tactic that does not read `wt`. -/
theorem _root_.Solidity.NFml.Proves.close_dropWt {R : RuleSet} {Γ : List (Hyp C)} {φ : NFml C}
    (h : Valid (Hyp.wrap (dropWt Γ) φ)) : Proves R Γ φ :=
  Proves.close (fun σ => wrap_dropWt Γ σ (h σ))

/-- A `wt(storage)` premise holds of a storage that holds its layout. -/
theorem layoutOk_of_wt {σ : Semantics.State} {vs : List (Name × Ty)}
    (h : holds σ (.defined (Term.wt vs (C := C) .storage))) : Decide.LayoutOk vs σ := by
  have hw : storageWtB vs σ.storage = true := by
    simp only [holds, Surface.Tm.eval, Op1.eval, Op0.eval, pure, Except.pure, bind, Except.bind] at h
    revert h
    cases storageWtB vs σ.storage with
    | true => exact fun _ => rfl
    | false => exact fun ⟨_, h⟩ => (nomatch h)
  simp only [storageWtB, storageShapeB, Bool.and_eq_true, List.all_eq_true] at hw
  intro r T hT
  have := hw.1.2 (r, T) (SemanticsProperties.lookupBy_eq_some_mem hT)
  revert this
  split
  · rename_i v hv
    simp only [Bool.and_eq_true]
    exact fun h => ⟨v, hv, h.1⟩
  · exact fun h => nomatch h

theorem wtRoots?_isWt {a : NFml C} {vs : List (Name × Ty)} (h : wtRoots? a = some vs) :
    isWt (C := C) (.pre a) = true := by
  unfold wtRoots? at h
  split at h
  · rfl
  · cases h

theorem wtRoots?_layout {a : NFml C} {vs : List (Name × Ty)} (h : wtRoots? a = some vs) {σ : Semantics.State}
    (ha : holds σ a) : Decide.LayoutOk vs σ := by
  unfold wtRoots? at h
  split at h
  · cases h; exact layoutOk_of_wt ha
  · cases h

/-- Reading the `wt` premise as a layout: a leaf whose context without them
holds wherever the storage holds the layout holds. -/
theorem wrap_topWt {φ : NFml C} : (Γ : List (Hyp C)) → ∀ σ,
    (Decide.LayoutOk (topWt Γ) σ → holds σ (Hyp.wrap (dropWt Γ) φ)) → holds σ (Hyp.wrap Γ φ)
  | [], σ, h => h fun _ _ hT => nomatch hT
  | .pre a :: Γ, σ, h => by
    simp only [topWt] at h
    cases hr : wtRoots? a with
    | some vs =>
      have hd : dropWt (.pre a :: Γ) = dropWt Γ := by
        simp only [dropWt, List.filter_cons, wtRoots?_isWt hr, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte]
      rw [hr, hd] at h
      exact fun ha => wrap_dropWt Γ σ (h (wtRoots?_layout hr ha))
    | none =>
      rw [hr] at h
      cases hw : isWt (C := C) (.pre a) with
      | true =>
        have hd : dropWt (.pre a :: Γ) = dropWt Γ := by
          simp only [dropWt, List.filter_cons, hw, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rw [hd] at h
        exact fun _ => wrap_topWt Γ σ h
      | false =>
        have hd : dropWt (.pre a :: Γ) = .pre a :: dropWt Γ := by
          simp only [dropWt, List.filter_cons, hw, Bool.not_false, ↓reduceIte]
        rw [hd] at h
        exact fun ha => wrap_topWt Γ σ fun hL => h hL ha
  | .all x p :: Γ, σ, h => fun v hv => wrap_topWt Γ _ fun hL => h hL v hv
  | .upd m U :: Γ, σ, h => wrap_dropWt (.upd m U :: Γ) σ (h fun _ _ hT => nomatch hT)
  | .havoc :: Γ, σ, h => wrap_dropWt (.havoc :: Γ) σ (h fun _ _ hT => nomatch hT)
  | .anon xs :: Γ, σ, h => wrap_dropWt (.anon xs :: Γ) σ (h fun _ _ hT => nomatch hT)

/-- The default closer is sound: what it accepts, `Proves.close` proves. -/
theorem synClose_sound {Γ : List (Hyp C)} {φ : NFml C} (h : synClose Γ φ = true) :
    Proves .all Γ φ := by
  simp only [synClose, Bool.and_eq_true] at h
  obtain ⟨⟨-, hf⟩, hs⟩ := h
  refine Proves.close (fun σ => wrap_topWt Γ σ fun hL => NFml.seqUpd_sound _ σ ?_)
  rw [Decide.NFml.toL_holds _ (Decide.Rel.empty σ) hf, ← Decide.LFml.elim_holds σ]
  exact Decide.LFml.close_holds hL hs

end NFml.Derive

open NFml.Derive in
/-- **A residue whose leaves are proved proves the sequent.** -/
theorem NFml.Proves.of_residue {close : List (Hyp C) → NFml C → Bool}
    (hclose : ∀ Γ φ, close Γ φ = true → NFml.Proves .all Γ φ) :
    ∀ {n b : Nat} {Γ : List (Hyp C)} {φ : NFml C} {ls : List (Leaf C)} {b' : Nat},
      residue n close b Γ φ = some (ls, b') → (∀ l ∈ ls, NFml.Proves .all l.1 l.2) →
      NFml.Proves .all Γ φ
  | 0, _, _, _, _, _, h, _ => nomatch h
  | _ + 1, 0, _, _, _, _, h, _ => nomatch h
  | n + 1, b + 1, Γ, φ, ls, b', h, hl => by
    have ih : ∀ b Γ φ ls b', residue n close b Γ φ = some (ls, b') →
        (∀ l ∈ ls, NFml.Proves .all l.1 l.2) → NFml.Proves .all Γ φ :=
      fun _ _ _ _ _ h' hl' => NFml.Proves.of_residue hclose h' hl'
    match φ, h with
    | .imp a ψ, h => exact .intro (ih _ _ _ _ _ h hl)
    | .all x p ψ, h => exact .allIntro (ih _ _ _ _ _ h hl)
    | .upd m U ψ, h => exact .updIntro (ih _ _ _ _ _ h hl)
    | .tt, h | .eq _ _, h | .defined _, h | .not _, h | .and _ _, h | .havoc _, h | .anon _ _, h =>
      simp only [residue] at h
      split at h
      · exact hclose _ _ ‹_›
      · cases h
        exact hl _ (List.mem_singleton_self _)

open NFml.Derive in
/-- Nothing left: the strategy and the closer prove the sequent. -/
theorem NFml.Proves.of_closes {n : Nat} {close : List (Hyp C) → NFml C → Bool}
    (hclose : ∀ Γ φ, close Γ φ = true → NFml.Proves .all Γ φ) {b : Nat} {Γ : List (Hyp C)}
    {φ : NFml C} (h : closes n close b Γ φ = true) : NFml.Proves .all Γ φ := by
  simp only [closes] at h
  split at h
  · exact NFml.Proves.of_residue hclose ‹_› leaves_nil
  · cases h

/-- `sol_prove`'s proof when nothing is left. -/
theorem NFml.Proves.of_proves {Γ : List (Hyp C)} {φ : NFml C} (h : NFml.Derive.proves Γ φ = true) :
    NFml.Proves .all Γ φ :=
  NFml.Proves.of_closes (fun _ _ => NFml.Derive.synClose_sound) h

/-- `sol_prove`'s proof when leaves are left. -/
theorem NFml.Proves.of_synResidue {Γ : List (Hyp C)} {φ : NFml C} {ls : List (NFml.Derive.Leaf C)}
    {b' : Nat} (h : NFml.Derive.residue NFml.Derive.budget NFml.Derive.synClose NFml.Derive.budget Γ φ = some (ls, b'))
    (hl : ∀ l ∈ ls, NFml.Proves .all l.1 l.2) : NFml.Proves .all Γ φ :=
  NFml.Proves.of_residue (fun _ _ => NFml.Derive.synClose_sound) h hl

/-! ## The tactics -/

namespace NFml.Derive

open Lean Elab Tactic Meta

/-- `⊢ φ` over the contract `C` as `⊢` elaborates it, `Proves C .all [] φ`:
the one builder of it, for `sol_prove` and the commands that state or
compare an obligation (`Frontend/Problems.lean`). -/
def provesNil (C φ : Expr) : Expr :=
  mkAppN (mkConst ``Proves) #[C, mkConst ``RuleSet.all,
    mkApp (mkConst ``List.nil [0]) (mkApp (mkConst ``Hyp) C), φ]

/-- `sol_prove` on the goal `g`: the goals it leaves, one per residual leaf. -/
def prove (g : MVarId) : MetaM (List MVarId) := do
  let ty ← instantiateMVars (← g.getType)
  let (g, ty) ← match_expr ty with
    | Valid C φ =>
      let ty' := provesNil C φ
      let g' ← mkFreshExprSyntheticOpaqueMVar ty' (← g.getTag)
      g.assign (mkApp3 (mkConst ``Proves.valid) C φ g')
      pure (g'.mvarId!, ty')
    | _ => pure (g, ty)
  let_expr Proves C R Γ φ := ty | throwError "sol_prove: expected a goal `Γ ⊢ φ` or `⊨ φ`"
  unless R.isConstOf ``RuleSet.all do throwError "sol_prove: proves `⊢`, not `⊢ₖ`"
  let some n := C.constName? | throwError "sol_prove: the contract is not a named constant"
  if Γ.hasFVar || Γ.hasMVar || φ.hasFVar || φ.hasMVar then
    throwError "sol_prove: the sequent mentions a local hypothesis or a metavariable"
  let resTy := mkApp (mkConst ``Option [0]) (mkApp2 (mkConst ``Prod [0, 0])
    (mkApp (mkConst ``List [0])
      (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Expr) (mkConst ``Expr)))
    (mkConst ``Nat))
  let some (leaves, left) ← unsafe evalExpr (Option (List (Expr × Expr) × Nat)) resTy
      (mkAppN (mkConst ``residueQuote) #[C, quoteConstName n, Γ, φ])
    | throwError "sol_prove: the derivation takes more than {budget} steps \
        (`Derive.budget`); `sol_derive` builds it one step at a time"
  let bool := mkConst ``Bool
  if leaves.isEmpty then
    let type := mkApp3 (mkConst ``Eq [1]) bool (mkApp3 (mkConst ``proves) C Γ φ)
      (mkConst ``Bool.true)
    let h ← try kernelLemma type (mkApp2 (mkConst ``Eq.refl [1]) bool (mkConst ``Bool.true))
      catch e => throwError "sol_prove: the kernel rejects the derivation:{indentD e.toMessageData}"
    g.assign (mkApp4 (mkConst ``Proves.of_proves) C Γ φ h)
    return []
  let hyp := mkApp (mkConst ``Hyp) C
  let leafTy := mkApp2 (mkConst ``Prod [0, 0]) (mkApp (mkConst ``List [0]) hyp)
    (mkApp (mkConst ``NFml) C)
  let pairs := leaves.map fun (Γ', φ') =>
    mkAppN (mkConst ``Prod.mk [0, 0]) #[mkApp (mkConst ``List [0]) hyp, mkApp (mkConst ``NFml) C,
      Γ', φ']
  let ls ← mkListLit leafTy pairs
  let resTy := mkApp2 (mkConst ``Prod [0, 0]) (mkApp (mkConst ``List [0]) leafTy) (mkConst ``Nat)
  let optTy := mkApp (mkConst ``Option [0]) resTy
  let someLs := mkApp2 (mkConst ``Option.some [0]) resTy
    (mkAppN (mkConst ``Prod.mk [0, 0]) #[mkApp (mkConst ``List [0]) leafTy, mkConst ``Nat, ls,
      mkRawNatLit left])
  let type := mkApp3 (mkConst ``Eq [1]) optTy
    (mkAppN (mkConst ``residue)
      #[C, mkConst ``budget, mkApp (mkConst ``synClose) C, mkConst ``budget, Γ, φ]) someLs
  let h ← try kernelLemma type (mkApp2 (mkConst ``Eq.refl [1]) optTy someLs)
    catch e => throwError "sol_prove: the kernel rejects the residue:{indentD e.toMessageData}"
  let mut goals : Array MVarId := #[]
  let mut proofs : Array Expr := #[]
  for (Γ', φ') in leaves, i in [1:leaves.length + 1] do
    let gi ← mkFreshExprSyntheticOpaqueMVar
      (mkAppN (mkConst ``Proves) #[C, mkConst ``RuleSet.all, Γ', φ']) (Name.mkSimple s!"leaf{i}")
    goals := goals.push gi.mvarId!
    proofs := proofs.push gi
  let mut hl := mkApp (mkConst ``leaves_nil) C
  let mut rest := mkApp (mkConst ``List.nil [0]) leafTy
  for (Γ', φ') in leaves.reverse, p in proofs.reverse do
    hl := mkAppN (mkConst ``leaves_cons) #[C, Γ', φ', rest, p, hl]
    rest := mkAppN (mkConst ``List.cons [0]) #[leafTy,
      mkAppN (mkConst ``Prod.mk [0, 0]) #[mkApp (mkConst ``List [0]) hyp, mkApp (mkConst ``NFml) C,
        Γ', φ'], rest]
  g.assign (mkAppN (mkConst ``Proves.of_synResidue) #[C, Γ, φ, ls, mkRawNatLit left, h, hl])
  return goals.toList

/-- The tactics `sol_prove?` tries on a leaf, in order, each a sequence of
lines.  On a leaf the scoped walk left (`isScoped`), the scoped ones only:
`sol_leaf` (the sequent as `⊨ ψ`, `Calculus/ProvesDerive.lean`), then
`sol_decide` on the scoped leaf (its layout read from `wt(storage)`), then
`sol_close` and `sol_spec_close` (`Calculus/CloseScoped.lean`).  On a leaf
of the closer's own sequent, today's, on the erasure: `sol_decide`'s two
steps after its `LFml.syn` try, which the closer subsumes, each on its own
so that the replay does not try the other; then `sol_close` and
`sol_spec_close` (`omega`, `grind`).  A leaf past `fitsClose` (`small =
false`) gets no step that reduces it, only `sol_close` and
`sol_spec_close`, whose `simp`, `omega` and `grind` heed heartbeats. -/
def leafTacs (wt : Bool := false) (small : Bool := true) (isScoped : Bool := false) :
    Array (Array String) :=
  if isScoped then
    (if small then #[#["sol_leaf", "sol_decide"]] else #[]) ++
      #[#["sol_leaf", "sol_close"], #["sol_leaf", "sol_spec_close"]]
  else
    let pre := #[if wt then "refine NFml.Proves.close_dropWt ?_" else "refine NFml.Proves.close ?_",
      "sol_symex"]
    let red := pre ++ #["refine (NFml.valid_iff_reduce _ (by decide +kernel)).2 ?_", "sol_reduce"]
    (if small then #[red.push "sol_decide_cons", red.push "sol_decide_heuristic"] else #[]) ++
      #[pre.push "sol_close", pre.push "sol_spec_close"]

open Lean Meta in
/-- `leafFits` on the leaf goal `l`, run as compiled code; `true` on a goal
that is not a closed `Γ ⊢ φ`. -/
def goalFits (l : MVarId) : MetaM Bool := do
  let ty ← instantiateMVars (← l.getType)
  let_expr Proves C _ Γ φ := ty | return true
  if ty.hasFVar || ty.hasMVar then return true
  unsafe evalExpr Bool (mkConst ``Bool) (mkAppN (mkConst ``leafFits) #[C, Γ, φ])

end NFml.Derive

open Lean Elab Tactic Meta in
/-- `sol_prove`: the strategy as one kernel evaluation (`Proves.of_residue`),
on a goal `Γ ⊢ φ` or `⊨ φ`; one goal `leafᵢ` per leaf the closer leaves. -/
elab_rules : tactic
  | `(tactic| sol_prove) => withMainContext do
    let g ← getMainGoal
    let rest ← getUnsolvedGoals
    let leaves ← NFml.Derive.prove g
    setGoals (leaves ++ rest.erase g)

namespace NFml.Derive

open Lean Elab Tactic Meta

/-- The first of `leafTacs` that closes the leaf `l`, with the raw
heartbeats it used; `none` when none does.  Each try runs with its own
heartbeats and its state rolled back when it fails.  A leaf under a `wt`
premise is closed with it set aside (`Proves.close_dropWt`); one past
`fitsClose` is not reduced (`fits`: `goalFits`, or the scoped leaf's
`Seq.goalFits`, `Calculus/ProvesDerive.lean`). -/
def searchLeaf (l : MVarId) (fits : MVarId → MetaM Bool := goalFits) :
    TacticM (Option (Array String × Nat)) := do
  let env ← getEnv
  let ty ← instantiateMVars (← l.getType)
  let wt := (ty.find? fun e => e.isConstOf ``Term.wt || e.isConstOf ``Op1.wt).isSome
  for src in leafTacs wt (← fits l) (ty.isAppOfArity ``Solidity.Proves 6) do
    let t ← src.mapM fun line =>
      match Parser.runParserCategory env `tactic line with
      | .ok stx => pure (⟨stx⟩ : TSyntax `tactic)
      | .error e => throwError "sol_prove?: {e}"
    let s ← saveState
    let h0 ← IO.getNumHeartbeats
    let ok ← tryCatchRuntimeEx
      (withCurrHeartbeats do
        setGoals [l]
        for x in t do Term.withoutErrToSorry (withoutRecover (evalTactic x))
        pure (← getUnsolvedGoals).isEmpty)
      fun _ => pure false
    if ok then return some (src, (← IO.getNumHeartbeats) - h0)
    s.restore
  return none

/-- What `proveSearch` found: each leaf's name and lines (`sorry` for one
no try closes), the leaves no try closes, and the raw heartbeats the replay
needs, `prove`'s and the closing tries' (the failed tries are not
replayed). -/
structure Search where
  found : List (Lean.Name × Array String)
  open_ : List MVarId
  heartbeats : Nat

/-- `sol_prove` on `g` (or the walk `prove` given, as `#solkey_derive?`'s
scoped one), then `searchLeaf` on each leaf it leaves, the open ones left
as goals; with `stopAtOpen`, the search ends at the first open leaf.  The
one loop of `sol_prove?` and `#solkey_derive?`. -/
def proveSearch (g : MVarId) (stopAtOpen : Bool := false)
    (prove : MVarId → MetaM (List MVarId) := prove) (fits : MVarId → MetaM Bool := goalFits) :
    TacticM Search := do
  let h0 ← IO.getNumHeartbeats
  let leaves ← prove g
  let mut hb : Nat := (← IO.getNumHeartbeats) - h0
  let mut found : List (Lean.Name × Array String) := []
  let mut open_ : List MVarId := []
  for l in leaves do
    let name ← l.getTag
    match ← searchLeaf l fits with
    | some (t, h) =>
      found := found ++ [(name, t)]
      hb := hb + h
    | none =>
      open_ := open_ ++ [l]
      found := found ++ [(name, #["sorry"])]
      if stopAtOpen then break
  return { found, open_, heartbeats := hb }

/-- Whether a replay of `hb` raw heartbeats fits in one declaration's
`maxHeartbeats`.  Each try ran with heartbeats of its own; the replay runs
them all in one declaration, so their sum is what it needs, up to the
elaboration of the statement and the `case` lines. -/
def _root_.Solidity.Derive.replayFits (hb : Nat) : CoreM Bool := do
  let max := (← read).maxHeartbeats
  return max == 0 || hb ≤ max

/-- The replay of a `sol_prove` whose leaves are closed by `found`:
`sol_prove`, then each leaf's lines, under `case leafᵢ =>` when there are
several. -/
def replayLines (found : List (Lean.Name × Array String)) : Array String :=
  match found with
  | [(_, body)] => #["sol_prove"] ++ body
  | _ => found.foldl (fun ls (n, body) =>
      (ls.push s!"case {n} =>") ++ body.map ("  " ++ ·)) #["sol_prove"]

end NFml.Derive

open Lean Elab Tactic Meta in
/-- `sol_prove?`: `sol_prove`, each leaf closed by the first of
`Derive.leafTacs` that closes it (`Derive.proveSearch`); suggests the
replay.  A leaf none closes stays a goal, and the first is reported; a
replay past `maxHeartbeats` as one declaration (`Derive.replayFits`) is
warned of. -/
elab_rules : tactic
  | `(tactic| sol_prove?%$tk) => withMainContext do
    let g ← getMainGoal
    let rest ← getUnsolvedGoals
    let s ← NFml.Derive.proveSearch g
    if let some l := s.open_.head? then
      logInfo m!"sol_prove?: no tactic closes {← l.getTag}:{indentExpr (← l.getType)}"
    else unless ← Derive.replayFits s.heartbeats do
      logWarning m!"sol_prove?: the replay needs about {s.heartbeats / 1000} heartbeats in one \
        declaration, past `maxHeartbeats`"
    setGoals (s.open_ ++ rest.erase g)
    ProofTree.suggest tk (NFml.Derive.replayLines s.found)

end Solidity
